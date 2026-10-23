// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Best-effort local-directory backend using the File System Access API.
// The prover keeps seeing the same in-memory project map; this module
// only reads a folder into that map and writes edits back.

import {
  classify,
  sortPaths,
  type Project,
  type ProjectTextFile,
} from "./project";

const MAX_FILE_BYTES = 512 * 1024;
const MAX_FILES = 500;
const MAX_DEPTH = 8;
const MAX_MANIFEST_BYTES = 64 * 1024;

const TEXT_EXTENSIONS = new Set([
  ".md",
  ".markdown",
  ".txt",
  ".text",
  ".rst",
  ".org",
]);

const TEXT_BASENAMES = new Set([
  "readme",
  "license",
  "licence",
  "copying",
  "notes",
  "changes",
  "authors",
]);

const SKIPPED_DIRECTORIES = new Set([
  "node_modules",
  "_build",
  "__pycache__",
  "target",
  "dist",
]);

interface WritableFileStream {
  write(data: string): Promise<void>;
  close(): Promise<void>;
  abort?(): Promise<void>;
}

export interface DirectoryFileHandle {
  kind: "file";
  name: string;
  getFile(): Promise<File>;
  createWritable(options?: {
    keepExistingData?: boolean;
  }): Promise<WritableFileStream>;
}

export interface DirectoryHandle {
  kind: "directory";
  name: string;
  entries(): AsyncIterableIterator<
    [string, DirectoryHandle | DirectoryFileHandle]
  >;
  queryPermission?(descriptor?: {
    mode?: "read" | "readwrite";
  }): Promise<PermissionState>;
  requestPermission?(descriptor?: {
    mode?: "read" | "readwrite";
  }): Promise<PermissionState>;
  getDirectoryHandle(
    name: string,
    options?: { create?: boolean }
  ): Promise<DirectoryHandle>;
  getFileHandle(
    name: string,
    options?: { create?: boolean }
  ): Promise<DirectoryFileHandle>;
}

type PickerWindow = Window & {
  showDirectoryPicker?: (options?: {
    mode?: "read" | "readwrite";
  }) => Promise<DirectoryHandle>;
};

export class DirectoryUnavailableError extends Error {}
export class DirectoryPermissionError extends Error {}
export class DirectoryEmptyError extends Error {}

export interface OpenedDirectory {
  project: Project;
  workspace: DirectoryWorkspace;
  truncated: boolean;
  skipped: number;
}

export interface SaveReport {
  saved: number;
  cancelled: number;
  failures: { path: string; message: string }[];
}

export function directoryPickerSupported(): boolean {
  return typeof (window as PickerWindow).showDirectoryPicker === "function";
}

export function isSkippedDirectory(name: string): boolean {
  return name.startsWith(".") || SKIPPED_DIRECTORIES.has(name);
}

export function isCandidateFile(path: string): boolean {
  const name = path.slice(path.lastIndexOf("/") + 1);
  if (name === "" || name.startsWith(".")) return false;
  const dot = name.lastIndexOf(".");
  const extension = dot < 0 ? "" : name.slice(dot).toLowerCase();
  if (extension === ".thm" || extension === ".sig" || extension === ".mod") {
    return true;
  }
  if (TEXT_EXTENSIONS.has(extension)) return true;
  return dot < 0 && TEXT_BASENAMES.has(name.toLowerCase());
}

function baseName(path: string): string {
  return path.slice(path.lastIndexOf("/") + 1).toLowerCase();
}

export function chooseRoot(
  paths: string[],
  folderName: string,
  manifestRoot?: string
): string | undefined {
  if (
    manifestRoot &&
    paths.includes(manifestRoot) &&
    manifestRoot.toLowerCase().endsWith(".thm")
  ) {
    return manifestRoot;
  }
  const theorems = sortPaths(
    paths.filter((path) => path.toLowerCase().endsWith(".thm"))
  );
  if (theorems.length === 0) return undefined;
  if (theorems.length === 1) return theorems[0];
  const main = theorems.find((path) => baseName(path) === "main.thm");
  if (main) return main;
  const folder = `${folderName.toLowerCase()}.thm`;
  const named = theorems.find((path) => baseName(path) === folder);
  return named ?? theorems[0];
}

function stripBom(text: string): string {
  return text.charCodeAt(0) === 0xfeff ? text.slice(1) : text;
}

function domName(error: unknown): string | undefined {
  if (typeof error !== "object" || error === null || !("name" in error)) {
    return undefined;
  }
  const name = (error as { name: unknown }).name;
  return typeof name === "string" ? name : undefined;
}

function isAbort(error: unknown): boolean {
  return domName(error) === "AbortError";
}

function isPermissionDenied(error: unknown): boolean {
  const name = domName(error);
  return name === "NotAllowedError" || name === "SecurityError";
}

export function messageOf(error: unknown): string {
  if (error instanceof Error && error.message) return error.message;
  return String(error);
}

interface ReadState {
  files: Map<string, ProjectTextFile>;
  handles: Map<string, DirectoryFileHandle>;
  lastModified: Map<string, number>;
  truncated: boolean;
  skipped: number;
}

async function readManifestRoot(
  handle: DirectoryHandle
): Promise<string | undefined> {
  try {
    const fileHandle = await handle.getFileHandle("project.json");
    const file = await fileHandle.getFile();
    if (file.size > MAX_MANIFEST_BYTES) return undefined;
    const data = JSON.parse(await file.text()) as { root?: unknown };
    return typeof data.root === "string" ? data.root : undefined;
  } catch {
    return undefined;
  }
}

async function readDirectory(
  directory: DirectoryHandle,
  prefix: string,
  depth: number,
  state: ReadState
): Promise<void> {
  for await (const [name, entry] of directory.entries()) {
    if (state.files.size >= MAX_FILES) {
      state.truncated = true;
      return;
    }
    const path = prefix ? `${prefix}/${name}` : name;
    if (entry.kind === "directory") {
      if (depth >= MAX_DEPTH || isSkippedDirectory(name)) continue;
      await readDirectory(entry, path, depth + 1, state);
      continue;
    }
    if (!isCandidateFile(path)) continue;
    let file: File;
    try {
      file = await entry.getFile();
    } catch {
      state.skipped++;
      continue;
    }
    if (file.size > MAX_FILE_BYTES) {
      state.skipped++;
      continue;
    }
    let text: string;
    try {
      text = await file.text();
    } catch {
      state.skipped++;
      continue;
    }
    state.files.set(path, { text: stripBom(text), kind: classify(path) });
    state.handles.set(path, entry);
    state.lastModified.set(path, file.lastModified);
  }
}

export async function openDirectoryProject(
  confirmReplace?: (folderName: string) => boolean
): Promise<OpenedDirectory | undefined> {
  const picker = (window as PickerWindow).showDirectoryPicker;
  if (!picker) {
    throw new DirectoryUnavailableError(
      "This browser cannot open local folders. Use Import zip instead."
    );
  }
  let handle: DirectoryHandle;
  try {
    handle = await picker({ mode: "readwrite" });
  } catch (error) {
    if (isAbort(error)) return undefined;
    if (isPermissionDenied(error)) {
      throw new DirectoryPermissionError(
        "Permission to open the folder was denied. Use Import zip instead."
      );
    }
    throw error;
  }
  // The picker needs the click's transient activation, so the replacement
  // prompt must run after it rather than before it.
  if (confirmReplace && !confirmReplace(handle.name)) return undefined;

  const state: ReadState = {
    files: new Map(),
    handles: new Map(),
    lastModified: new Map(),
    truncated: false,
    skipped: 0,
  };
  await readDirectory(handle, "", 0, state);
  const manifestRoot = await readManifestRoot(handle);
  const root = chooseRoot([...state.files.keys()], handle.name, manifestRoot);
  if (!root) {
    throw new DirectoryEmptyError(
      "That folder does not contain a .thm reasoning file."
    );
  }
  return {
    project: { files: state.files, root, active: root },
    workspace: new DirectoryWorkspace(
      handle,
      state.handles,
      state.lastModified
    ),
    truncated: state.truncated,
    skipped: state.skipped,
  };
}

export class DirectoryWorkspace {
  readonly folderName: string;
  private handle: DirectoryHandle;
  private handles: Map<string, DirectoryFileHandle>;
  private lastModified: Map<string, number>;
  private dirty = new Set<string>();

  constructor(
    handle: DirectoryHandle,
    handles: Map<string, DirectoryFileHandle>,
    lastModified: Map<string, number>
  ) {
    this.handle = handle;
    this.folderName = handle.name;
    this.handles = handles;
    this.lastModified = lastModified;
  }

  isDirty(path: string): boolean {
    return this.dirty.has(path);
  }

  hasDirty(): boolean {
    return this.dirty.size > 0;
  }

  dirtyPaths(): string[] {
    return [...this.dirty];
  }

  markDirty(path: string): void {
    this.dirty.add(path);
  }

  async save(
    path: string,
    text: string,
    confirmOverwrite: (path: string) => boolean
  ): Promise<"saved" | "cancelled"> {
    await this.ensureWritable();
    const existing = this.handles.get(path);
    if (existing) {
      let file: File | undefined;
      try {
        file = await existing.getFile();
      } catch {
        file = undefined;
      }
      const known = this.lastModified.get(path);
      if (
        file &&
        known !== undefined &&
        file.lastModified !== known &&
        !confirmOverwrite(path)
      ) {
        return "cancelled";
      }
    }
    const handle = existing ?? (await this.createFileHandle(path));
    const writable = await handle.createWritable();
    try {
      await writable.write(text);
      await writable.close();
    } catch (error) {
      try {
        await writable.abort?.();
      } catch {
        // The original write error is more useful.
      }
      throw error;
    }
    this.handles.set(path, handle);
    try {
      const after = await handle.getFile();
      this.lastModified.set(path, after.lastModified);
    } catch {
      this.lastModified.delete(path);
    }
    this.dirty.delete(path);
    return "saved";
  }

  async saveAll(
    paths: Iterable<string>,
    textFor: (path: string) => string | undefined,
    confirmOverwrite: (path: string) => boolean
  ): Promise<SaveReport> {
    const report: SaveReport = { saved: 0, cancelled: 0, failures: [] };
    for (const path of paths) {
      const text = textFor(path);
      if (text === undefined) continue;
      try {
        const result = await this.save(path, text, confirmOverwrite);
        if (result === "saved") report.saved++;
        else report.cancelled++;
      } catch (error) {
        report.failures.push({ path, message: messageOf(error) });
        if (error instanceof DirectoryPermissionError) break;
      }
    }
    return report;
  }

  private async ensureWritable(): Promise<void> {
    if (!this.handle.queryPermission) return;
    let permission: PermissionState;
    try {
      permission = await this.handle.queryPermission({ mode: "readwrite" });
    } catch {
      return;
    }
    if (permission === "granted") return;
    if (permission === "prompt" && this.handle.requestPermission) {
      try {
        permission = await this.handle.requestPermission({ mode: "readwrite" });
      } catch {
        permission = "denied";
      }
    }
    if (permission !== "granted") {
      throw new DirectoryPermissionError(
        "Permission to write to the folder was denied. " +
          "Use Download zip to keep your work."
      );
    }
  }

  private async createFileHandle(path: string): Promise<DirectoryFileHandle> {
    const parts = path.split("/");
    const name = parts.pop();
    if (!name) throw new Error(`Invalid file path: ${path}`);
    let directory = this.handle;
    for (const part of parts) {
      directory = await directory.getDirectoryHandle(part, { create: true });
    }
    return directory.getFileHandle(name, { create: true });
  }
}
