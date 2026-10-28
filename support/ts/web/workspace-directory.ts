// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Best-effort local-directory backend using the File System Access API.
// The prover keeps seeing the same in-memory project map; this module
// only reads a folder into that map and writes edits back.

import {
  classify,
  explicitEntry,
  normalizeNewlines,
  type Project,
  type ProjectTextFile,
} from "./project";
import {
  WorkspaceError,
  type Workspace,
  type WorkspaceCapabilities,
  type WorkspaceEntry,
  type WorkspaceKind,
} from "./workspace";

export const MAX_FILE_BYTES = 512 * 1024;
export const MAX_FILES = 500;
export const MAX_ENTRIES = 2000;
export const MAX_DEPTH = 8;
export const MAX_MANIFEST_BYTES = 64 * 1024;

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
  removeEntry?(name: string, options?: { recursive?: boolean }): Promise<void>;
}

type PickerWindow = Window & {
  showDirectoryPicker?: (options?: {
    mode?: "read" | "readwrite";
  }) => Promise<DirectoryHandle>;
};

export class DirectoryUnavailableError extends WorkspaceError {
  constructor(message: string) {
    super("unavailable", message);
  }
}

export class DirectoryPermissionError extends WorkspaceError {
  constructor(message: string) {
    super("permission-denied", message);
  }
}

export interface OpenedDirectory {
  project: Project;
  workspace: DirectoryWorkspace;
  truncated: boolean;
  listingTruncated: boolean;
  skipped: number;
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

function permissionError(): DirectoryPermissionError {
  return new DirectoryPermissionError(
    "Permission to use the folder was denied. " +
      "Use Download zip to keep your work."
  );
}

async function ensurePermission(
  handle: DirectoryHandle,
  mode: "read" | "readwrite"
): Promise<void> {
  // Call requestPermission first so a click's transient activation is not
  // consumed by an intervening queryPermission await.
  if (handle.requestPermission) {
    let requested: PermissionState | undefined;
    try {
      requested = await handle.requestPermission({ mode });
    } catch {
      requested = undefined;
    }
    if (requested === "granted") return;
    if (requested === "denied") throw permissionError();
  }
  if (!handle.queryPermission) return;
  let permission: PermissionState;
  try {
    permission = await handle.queryPermission({ mode });
  } catch {
    return;
  }
  if (permission !== "granted") throw permissionError();
}

interface ReadState {
  files: Map<string, ProjectTextFile>;
  handles: Map<string, DirectoryFileHandle>;
  lastModified: Map<string, number>;
  entries: WorkspaceEntry[];
  truncated: boolean;
  listingTruncated: boolean;
  skipped: number;
}

async function readManifestEntry(
  handle: DirectoryHandle
): Promise<string | undefined> {
  try {
    const fileHandle = await handle.getFileHandle("project.json");
    const file = await fileHandle.getFile();
    if (file.size > MAX_MANIFEST_BYTES) return undefined;
    const data = JSON.parse(await file.text()) as { entry?: unknown };
    return typeof data.entry === "string" ? data.entry : undefined;
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
    if (state.entries.length >= MAX_ENTRIES) {
      state.listingTruncated = true;
      return;
    }
    const path = prefix ? `${prefix}/${name}` : name;
    if (entry.kind === "directory") {
      if (depth >= MAX_DEPTH || isSkippedDirectory(name)) continue;
      state.entries.push({
        path,
        kind: "directory",
        openable: true,
      });
      await readDirectory(entry, path, depth + 1, state);
      continue;
    }
    if (name.startsWith(".")) continue;
    if (!isCandidateFile(path)) {
      state.entries.push({
        path,
        kind: "file",
        openable: false,
        reason: "unsupported",
      });
      continue;
    }
    const record: WorkspaceEntry = {
      path,
      kind: "file",
      openable: true,
    };
    state.entries.push(record);
    if (state.files.size >= MAX_FILES) {
      state.truncated = true;
      record.openable = false;
      record.reason = "unreadable";
      continue;
    }
    let file: File;
    try {
      file = await entry.getFile();
    } catch {
      record.openable = false;
      record.reason = "unreadable";
      state.skipped++;
      continue;
    }
    if (file.size > MAX_FILE_BYTES) {
      record.openable = false;
      record.reason = "too-large";
      state.skipped++;
      continue;
    }
    let text: string;
    try {
      text = await file.text();
    } catch {
      record.openable = false;
      record.reason = "unreadable";
      state.skipped++;
      continue;
    }
    state.files.set(path, {
      text: normalizeNewlines(stripBom(text)),
      kind: classify(path),
    });
    state.handles.set(path, entry);
    state.lastModified.set(path, file.lastModified);
  }
}

export async function readDirectoryHandle(
  handle: DirectoryHandle,
  confirmOverwrite: (path: string) => boolean,
  confirmReplace?: (folderName: string) => boolean
): Promise<OpenedDirectory> {
  await ensurePermission(handle, "readwrite");
  if (confirmReplace && !confirmReplace(handle.name)) {
    throw new WorkspaceError("cancelled", "Folder reconnect cancelled.");
  }
  const state: ReadState = {
    files: new Map(),
    handles: new Map(),
    lastModified: new Map(),
    entries: [],
    truncated: false,
    listingTruncated: false,
    skipped: 0,
  };
  await readDirectory(handle, "", 0, state);
  const manifestEntry = await readManifestEntry(handle);
  const entry = explicitEntry(state.files, manifestEntry);
  const project: Project = {
    files: state.files,
    entry,
    active: entry,
  };
  return {
    project,
    workspace: new DirectoryWorkspace(
      handle,
      state.files,
      state.handles,
      state.lastModified,
      state.entries,
      confirmOverwrite
    ),
    truncated: state.truncated,
    listingTruncated: state.listingTruncated,
    skipped: state.skipped,
  };
}

export async function openDirectoryProject(
  confirmReplace: (folderName: string) => boolean,
  confirmOverwrite: (path: string) => boolean
): Promise<OpenedDirectory | undefined> {
  const picker = (window as PickerWindow).showDirectoryPicker;
  if (!picker) {
    throw new DirectoryUnavailableError(
      "This browser cannot open local folders with a picker."
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
  if (!confirmReplace(handle.name)) return undefined;
  return readDirectoryHandle(handle, confirmOverwrite);
}

export class DirectoryWorkspace implements Workspace {
  readonly kind: WorkspaceKind = "directory";
  readonly name: string;
  readonly capabilities: WorkspaceCapabilities = {
    write: true,
    remove: true,
    structural: true,
    refresh: false,
    commit: false,
    autoSave: false,
  };
  readonly handle: DirectoryHandle;

  private files: Map<string, ProjectTextFile>;
  private handles: Map<string, DirectoryFileHandle>;
  private lastModified: Map<string, number>;
  private entriesList: WorkspaceEntry[];
  private confirmOverwrite: (path: string) => boolean;

  constructor(
    handle: DirectoryHandle,
    files: Map<string, ProjectTextFile>,
    handles: Map<string, DirectoryFileHandle>,
    lastModified: Map<string, number>,
    entries: WorkspaceEntry[],
    confirmOverwrite: (path: string) => boolean
  ) {
    this.handle = handle;
    this.name = handle.name;
    this.files = files;
    this.handles = handles;
    this.lastModified = lastModified;
    this.entriesList = entries;
    this.confirmOverwrite = confirmOverwrite;
  }

  async entries(): Promise<WorkspaceEntry[]> {
    return [...this.entriesList];
  }

  async read(path: string): Promise<string> {
    const file = this.files.get(path);
    if (!file) {
      throw new WorkspaceError("not-found", `File not found: ${path}`);
    }
    return file.text;
  }

  async write(path: string, text: string): Promise<void> {
    await ensurePermission(this.handle, "readwrite");
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
        !this.confirmOverwrite(path)
      ) {
        throw new WorkspaceError(
          "cancelled",
          `${path} was not overwritten.`
        );
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
    this.files.set(path, { text, kind: classify(path) });
    if (!this.entriesList.some((entry) => entry.path === path)) {
      this.entriesList.push({ path, kind: "file", openable: true });
      const parts = path.split("/");
      parts.pop();
      for (let depth = 1; depth <= parts.length; depth++) {
        const directory = parts.slice(0, depth).join("/");
        if (!this.entriesList.some((entry) => entry.path === directory)) {
          this.entriesList.push({
            path: directory,
            kind: "directory",
            openable: true,
          });
        }
      }
    }
    try {
      const after = await handle.getFile();
      this.lastModified.set(path, after.lastModified);
    } catch {
      this.lastModified.delete(path);
    }
  }

  async remove(path: string): Promise<void> {
    await ensurePermission(this.handle, "readwrite");
    const parts = path.split("/");
    const name = parts.pop();
    if (!name) throw new WorkspaceError("io", `Invalid file path: ${path}`);
    let directory = this.handle;
    for (const part of parts) {
      directory = await directory.getDirectoryHandle(part);
    }
    if (!directory.removeEntry) {
      throw new WorkspaceError(
        "unsupported",
        "This browser cannot remove files from a folder."
      );
    }
    await directory.removeEntry(name);
    this.handles.delete(path);
    this.lastModified.delete(path);
    this.files.delete(path);
    this.entriesList = this.entriesList.filter((entry) => entry.path !== path);
  }

  close(): void {
    this.handles.clear();
    this.lastModified.clear();
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
