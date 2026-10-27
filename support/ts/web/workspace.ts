// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Shared workspace abstraction and session state.  The in-memory project
// remains the content model; a workspace is only an I/O backend.

import {
  classify,
  type Project,
} from "./project";

export type WorkspaceKind =
  | "virtual"
  | "memory"
  | "directory"
  | "site"
  | "github"
  | "gitlab"
  | "gitea"
  | "dropbox";

export interface WorkspaceCapabilities {
  write: boolean;
  remove: boolean;
  structural: boolean;
  refresh: boolean;
  commit: boolean;
  autoSave: boolean;
}

export type WorkspaceEntryReason = "unsupported" | "too-large" | "unreadable";

export interface WorkspaceEntry {
  path: string;
  kind: "file" | "directory";
  openable: boolean;
  reason?: WorkspaceEntryReason;
}

export type WorkspaceErrorCode =
  | "cancelled"
  | "permission-denied"
  | "not-found"
  | "unsupported"
  | "conflict"
  | "unavailable"
  | "io";

export class WorkspaceError extends Error {
  readonly code: WorkspaceErrorCode;
  readonly status?: number;

  constructor(code: WorkspaceErrorCode, message: string, status?: number) {
    super(message);
    this.name = "WorkspaceError";
    this.code = code;
    this.status = status;
  }
}

export type CommitResult =
  | { status: "committed"; revision: string }
  | { status: "conflict"; message: string };

export interface Workspace {
  readonly kind: WorkspaceKind;
  readonly name: string;
  readonly capabilities: WorkspaceCapabilities;
  entries(): Promise<WorkspaceEntry[]>;
  read(path: string): Promise<string>;
  write(path: string, text: string): Promise<void>;
  remove?(path: string): Promise<void>;
  refresh?(): Promise<void>;
  commit?(message: string): Promise<CommitResult>;
  baseRevision?: string;
  close?(): void;
}

export function workspaceErrorOf(
  error: unknown,
  fallback: WorkspaceErrorCode = "io"
): WorkspaceError {
  if (error instanceof WorkspaceError) return error;
  if (error instanceof Error && error.message) {
    return new WorkspaceError(fallback, error.message);
  }
  return new WorkspaceError(fallback, String(error));
}

export function workspaceMessage(error: unknown): string {
  return workspaceErrorOf(error).message;
}

function unsupported(operation: string): WorkspaceError {
  return new WorkspaceError(
    "unsupported",
    `${operation} is not supported by this workspace.`
  );
}

export class MemoryWorkspace implements Workspace {
  constructor(
    readonly kind: WorkspaceKind,
    readonly name: string,
    readonly project: Project,
    readonly capabilities: WorkspaceCapabilities
  ) {}

  async entries(): Promise<WorkspaceEntry[]> {
    return [...this.project.files.keys()].map((path) => ({
      path,
      kind: "file" as const,
      openable: true,
    }));
  }

  async read(path: string): Promise<string> {
    const file = this.project.files.get(path);
    if (!file) {
      throw new WorkspaceError("not-found", `File not found: ${path}`);
    }
    return file.text;
  }

  async write(path: string, text: string): Promise<void> {
    if (!this.capabilities.write) throw unsupported("Writing files");
    const file = this.project.files.get(path);
    if (file) file.text = text;
    else this.project.files.set(path, { text, kind: classify(path) });
  }

  async remove(path: string): Promise<void> {
    if (!this.capabilities.remove) throw unsupported("Removing files");
    this.project.files.delete(path);
  }

  close(): void {
    // The project map owns the contents; there is nothing to release.
  }
}

export function virtualWorkspace(project: Project): MemoryWorkspace {
  return new MemoryWorkspace("virtual", "Virtual project", project, {
    write: true,
    remove: true,
    structural: true,
    refresh: false,
    commit: false,
    autoSave: true,
  });
}

export function readOnlyWorkspace(
  kind: WorkspaceKind,
  name: string,
  project: Project
): MemoryWorkspace {
  return new MemoryWorkspace(kind, name, project, {
    write: false,
    remove: false,
    structural: false,
    refresh: false,
    commit: false,
    autoSave: false,
  });
}

export interface SaveReport {
  saved: number;
  cancelled: number;
  failures: { path: string; message: string }[];
}

export interface WorkspaceSessionOptions {
  persist?: (project: Project, workspace: Workspace) => void;
}

export class WorkspaceSession {
  readonly project: Project;
  readonly workspace: Workspace;
  private dirty = new Set<string>();
  private saved = new Map<string, string>();
  private persistTimer?: ReturnType<typeof setTimeout>;
  private persist?: (project: Project, workspace: Workspace) => void;

  constructor(
    project: Project,
    workspace: Workspace,
    options: WorkspaceSessionOptions = {}
  ) {
    this.project = project;
    this.workspace = workspace;
    this.persist = options.persist;
    for (const [path, file] of project.files) {
      this.saved.set(path, file.text);
    }
  }

  get kind(): WorkspaceKind {
    return this.workspace.kind;
  }

  get name(): string {
    return this.workspace.name;
  }

  get capabilities(): WorkspaceCapabilities {
    return this.workspace.capabilities;
  }

  get isDetachedDirectory(): boolean {
    return this.kind === "directory" && !this.capabilities.write;
  }

  markDirty(path: string): void {
    if (!this.capabilities.autoSave) {
      const current = this.project.files.get(path)?.text;
      if (current !== undefined && this.saved.get(path) === current) {
        this.dirty.delete(path);
      } else {
        this.dirty.add(path);
      }
    }
    this.schedulePersist();
  }

  isDirty(path: string): boolean {
    return this.dirty.has(path);
  }

  savedText(path: string): string | undefined {
    return this.saved.get(path);
  }

  private markSaved(path: string, text: string): void {
    this.saved.set(path, text);
    this.dirty.delete(path);
  }

  hasDirty(): boolean {
    return this.dirty.size > 0;
  }

  dirtyPaths(): string[] {
    return [...this.dirty];
  }

  clearDirty(path: string): void {
    this.dirty.delete(path);
  }

  private cachedEntries: WorkspaceEntry[] = [];

  async loadEntries(): Promise<WorkspaceEntry[]> {
    this.cachedEntries = await this.workspace.entries();
    return this.entries();
  }

  entries(): WorkspaceEntry[] {
    return [...this.cachedEntries];
  }

  hasEntry(path: string): boolean {
    return this.cachedEntries.some((entry) => entry.path === path);
  }

  private addParentDirectories(path: string): void {
    const parts = path.split("/");
    parts.pop();
    for (let depth = 1; depth <= parts.length; depth++) {
      const directory = parts.slice(0, depth).join("/");
      if (!this.hasEntry(directory)) {
        this.cachedEntries.push({
          path: directory,
          kind: "directory",
          openable: true,
        });
      }
    }
  }

  private updateEntriesAfterCreate(path: string): void {
    this.cachedEntries = this.cachedEntries.filter(
      (entry) => entry.path !== path
    );
    this.cachedEntries.push({
      path,
      kind: "file",
      openable: true,
    });
    this.addParentDirectories(path);
  }

  private updateEntriesAfterRemove(path: string): void {
    this.cachedEntries = this.cachedEntries.filter(
      (entry) => entry.path !== path
    );
  }

  async createFile(path: string, text: string): Promise<void> {
    if (!this.capabilities.structural) {
      throw new WorkspaceError(
        "unsupported",
        "Creating files is not supported by this workspace."
      );
    }
    await this.workspace.write(path, text);
    this.updateEntriesAfterCreate(path);
    if (this.capabilities.commit) {
      this.dirty.add(path);
    } else {
      this.markSaved(path, text);
    }
    this.persistNow();
  }

  async removeFile(path: string): Promise<void> {
    if (!this.capabilities.structural || !this.workspace.remove) {
      throw new WorkspaceError(
        "unsupported",
        "Deleting files is not supported by this workspace."
      );
    }
    const wasSaved = this.saved.has(path);
    await this.workspace.remove(path);
    this.updateEntriesAfterRemove(path);
    if (this.capabilities.commit) {
      if (wasSaved) this.dirty.add(path);
      else this.dirty.delete(path);
    } else {
      this.saved.delete(path);
      this.dirty.delete(path);
    }
    this.persistNow();
  }

  async renameFiles(
    renames: { from: string; to: string; text: string }[]
  ): Promise<void> {
    if (!this.capabilities.structural || !this.workspace.remove) {
      throw new WorkspaceError(
        "unsupported",
        "Renaming files is not supported by this workspace."
      );
    }
    for (const rename of renames) {
      await this.workspace.write(rename.to, rename.text);
    }
    const failures: string[] = [];
    for (const rename of renames) {
      try {
        await this.workspace.remove(rename.from);
        this.updateEntriesAfterRemove(rename.from);
        this.updateEntriesAfterCreate(rename.to);
        if (this.capabilities.commit) {
          this.dirty.delete(rename.from);
          this.dirty.add(rename.to);
        } else {
          this.saved.delete(rename.from);
          this.markSaved(rename.to, rename.text);
        }
      } catch (error) {
        failures.push(workspaceMessage(error));
      }
    }
    this.persistNow();
    if (failures.length > 0) {
      throw new WorkspaceError(
        "io",
        "The new file was written, but the old file could not be removed: " +
          failures.join("; ")
      );
    }
  }

  async applyChangedFiles(
    changed: ReadonlyMap<string, string>
  ): Promise<void> {
    if (changed.size === 0) return;
    for (const [path, text] of changed) {
      await this.workspace.write(path, text);
      if (this.capabilities.commit) this.dirty.add(path);
      else this.markSaved(path, text);
    }
    this.persistNow();
  }

  schedulePersist(): void {
    if (!this.persist) return;
    if (this.persistTimer !== undefined) clearTimeout(this.persistTimer);
    this.persistTimer = setTimeout(() => this.persistNow(), 250);
  }

  persistNow(): void {
    if (this.persistTimer !== undefined) {
      clearTimeout(this.persistTimer);
      this.persistTimer = undefined;
    }
    this.persist?.(this.project, this.workspace);
  }

  async save(path: string, text: string): Promise<"saved" | "cancelled"> {
    try {
      await this.workspace.write(path, text);
    } catch (error) {
      if (error instanceof WorkspaceError && error.code === "cancelled") {
        return "cancelled";
      }
      throw error;
    }
    this.markSaved(path, text);
    this.persistNow();
    return "saved";
  }

  async saveAll(
    paths: Iterable<string>,
    textFor: (path: string) => string | undefined
  ): Promise<SaveReport> {
    const report: SaveReport = { saved: 0, cancelled: 0, failures: [] };
    for (const path of paths) {
      const text = textFor(path);
      if (text === undefined) continue;
      try {
        await this.workspace.write(path, text);
        this.markSaved(path, text);
        report.saved++;
      } catch (error) {
        if (error instanceof WorkspaceError && error.code === "cancelled") {
          report.cancelled++;
        } else {
          report.failures.push({ path, message: workspaceMessage(error) });
          if (
            error instanceof WorkspaceError &&
            (error.code === "permission-denied" ||
              error.code === "unavailable")
          ) {
            break;
          }
        }
      }
    }
    if (report.saved > 0) this.persistNow();
    return report;
  }

  async commit(message: string): Promise<CommitResult> {
    if (!this.workspace.commit) {
      throw new WorkspaceError(
        "unsupported",
        "This workspace cannot commit changes."
      );
    }
    const result = await this.workspace.commit(message);
    if (result.status === "committed") {
      this.dirty.clear();
      this.saved = new Map(
        [...this.project.files].map(([path, file]) => [path, file.text])
      );
      this.persistNow();
    }
    return result;
  }

  close(): void {
    if (this.persistTimer !== undefined) {
      clearTimeout(this.persistTimer);
      this.persistTimer = undefined;
    }
    this.workspace.close?.();
  }
}
