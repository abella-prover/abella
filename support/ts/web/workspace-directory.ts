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
import {
  WorkspaceError,
  type Workspace,
  type WorkspaceCapabilities,
  type WorkspaceFileEntry,
  type WorkspaceKind,
} from "./workspace";

export const MAX_FILE_BYTES = 512 * 1024;
export const MAX_FILES = 500;
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

export class DirectoryEmptyError extends WorkspaceError {
  constructor(message: string) {
    super("not-found", message);
  }
}

export interface OpenedDirectory {
  project: Project;
  workspace: DirectoryWorkspace;
  truncated: boolean;
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
  const project: Project = { files: state.files, root, active: root };
  return {
    project,
    workspace: new DirectoryWorkspace(
      handle,
      state.files,
      state.handles,
      state.lastModified,
      confirmOverwrite
    ),
    truncated: state.truncated,
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
    remove: false,
    structural: false,
    refresh: false,
    commit: false,
    autoSave: false,
  };
  readonly handle: DirectoryHandle;

  private files: Map<string, ProjectTextFile>;
  private handles: Map<string, DirectoryFileHandle>;
  private lastModified: Map<string, number>;
  private confirmOverwrite: (path: string) => boolean;

  constructor(
    handle: DirectoryHandle,
    files: Map<string, ProjectTextFile>,
    handles: Map<string, DirectoryFileHandle>,
    lastModified: Map<string, number>,
    confirmOverwrite: (path: string) => boolean
  ) {
    this.handle = handle;
    this.name = handle.name;
    this.files = files;
    this.handles = handles;
    this.lastModified = lastModified;
    this.confirmOverwrite = confirmOverwrite;
  }

  async list(): Promise<WorkspaceFileEntry[]> {
    return [...this.files.entries()].map(([path, file]) => ({
      path,
      kind: file.kind,
    }));
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
    try {
      const after = await handle.getFile();
      this.lastModified.set(path, after.lastModified);
    } catch {
      this.lastModified.delete(path);
    }
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
