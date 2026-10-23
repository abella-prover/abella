// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Read-only workspace built from <input type="file" webkitdirectory>.

import { classify, type Project, type ProjectTextFile } from "./project";
import {
  MAX_FILES,
  MAX_FILE_BYTES,
  chooseRoot,
  isCandidateFile,
  isSkippedDirectory,
} from "./workspace-directory";
import {
  WorkspaceError,
  readOnlyWorkspace,
  type Workspace,
} from "./workspace";

export interface OpenedMemoryFolder {
  project: Project;
  workspace: Workspace;
  skipped: number;
}

function relativePath(file: File): string {
  const raw =
    (file as File & { webkitRelativePath?: string }).webkitRelativePath ||
    file.name;
  const parts = raw.split("/").filter(Boolean);
  return parts.length > 1 ? parts.slice(1).join("/") : parts[0] ?? file.name;
}

function folderName(file: File): string {
  const raw =
    (file as File & { webkitRelativePath?: string }).webkitRelativePath || "";
  const first = raw.split("/").find(Boolean);
  return first ?? "Read-only folder";
}

function ignoredPath(path: string): boolean {
  return path
    .split("/")
    .slice(0, -1)
    .some((part) => isSkippedDirectory(part));
}

function stripBom(text: string): string {
  return text.charCodeAt(0) === 0xfeff ? text.slice(1) : text;
}

export async function openMemoryFolder(
  files: FileList | File[]
): Promise<OpenedMemoryFolder> {
  const list = Array.from(files);
  if (list.length === 0) {
    throw new WorkspaceError("cancelled", "No folder was selected.");
  }
  const name = folderName(list[0]);
  const filesByName = new Map<string, ProjectTextFile>();
  let skipped = 0;
  for (let index = 0; index < list.length; index++) {
    if (filesByName.size >= MAX_FILES) {
      skipped += list.length - index;
      break;
    }
    const file = list[index];
    const path = relativePath(file);
    if (path === "" || ignoredPath(path) || !isCandidateFile(path)) {
      continue;
    }
    if (file.size > MAX_FILE_BYTES) {
      skipped++;
      continue;
    }
    try {
      const text = stripBom(await file.text());
      filesByName.set(path, { text, kind: classify(path) });
    } catch {
      skipped++;
    }
  }
  const root = chooseRoot([...filesByName.keys()], name);
  if (!root) {
    throw new WorkspaceError(
      "not-found",
      "That folder does not contain a .thm reasoning file."
    );
  }
  const project: Project = { files: filesByName, root, active: root };
  return {
    project,
    workspace: readOnlyWorkspace("memory", name, project),
    skipped,
  };
}
