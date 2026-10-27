// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { ProjectFile } from "./types";

export type FileKind = "abella" | "text";

export interface ProjectTextFile {
  text: string;
  kind: FileKind;
}

export interface Project {
  files: Map<string, ProjectTextFile>;
  entry?: string;
  active?: string;
  example?: string;
}

export const STORAGE_KEY = "abella.web.v1.project";

export function classify(path: string): FileKind {
  return /\.(thm|sig|mod)$/i.test(path) ? "abella" : "text";
}

export function isExecutable(path: string | undefined): boolean {
  return path !== undefined && path.toLowerCase().endsWith(".thm");
}

/**
 * CodeMirror only stores `\n` line breaks, so project text must use the
 * same convention or command offsets drift from editor offsets.
 */
export function normalizeNewlines(text: string): string {
  return text.replace(/\r\n?/g, "\n");
}

export function sortPaths(paths: string[]): string[] {
  return [...paths].sort((a, b) => a.localeCompare(b));
}

export function abellaFiles(project: Project): ProjectFile[] {
  return [...project.files.entries()]
    .filter(([, file]) => file.kind === "abella")
    .map(([path, file]) => ({ path, contents: file.text }));
}

export function entryText(project: Project): string {
  return project.entry ? project.files.get(project.entry)?.text ?? "" : "";
}

export function setFileText(project: Project, path: string, text: string): void {
  const file = project.files.get(path);
  if (file) file.text = normalizeNewlines(text);
}

export function scratchProject(): Project {
  const files = new Map<string, ProjectTextFile>();
  files.set("empty.sig", { text: "sig empty.\n", kind: "abella" });
  files.set("empty.mod", { text: "module empty.\n", kind: "abella" });
  files.set("main.thm", {
    text: 'Specification "empty".\n',
    kind: "abella",
  });
  return { files, entry: "main.thm", active: "main.thm" };
}

export function projectFromBundle(
  bundle: unknown,
  id: string
): Project | undefined {
  const data = bundle as {
    examples?: { id: string; entry: string; files?: string[] }[];
    files?: Record<string, string>;
  };
  if (!data?.examples || !data.files) return undefined;
  const example = data.examples.find((entry) => entry.id === id);
  if (!example) return undefined;
  const files = new Map<string, ProjectTextFile>();
  const paths = example.files ?? Object.keys(data.files);
  for (const path of paths) {
    const text = data.files[path];
    if (typeof text === "string") {
      files.set(path, {
        text: normalizeNewlines(text),
        kind: classify(path),
      });
    }
  }
  if (!isExecutable(example.entry) || !files.has(example.entry)) {
    return undefined;
  }
  return {
    files,
    entry: example.entry,
    active: example.entry,
    example: id,
  };
}

export interface WorkspaceDescriptor {
  kind: string;
  name: string;
}

interface SavedProject {
  version: 2;
  files: Record<string, string>;
  entry?: string;
  active?: string;
  example?: string;
  workspace?: WorkspaceDescriptor;
}

export interface LoadedProject {
  project: Project;
  workspace?: WorkspaceDescriptor;
}

export type ProjectLoadResult =
  | { status: "loaded"; project: Project; workspace?: WorkspaceDescriptor }
  | { status: "rejected"; message: string }
  | { status: "empty" };

function firstPath(files: Map<string, ProjectTextFile>): string | undefined {
  return sortPaths([...files.keys()])[0];
}

export function fallbackEntry(
  files: Map<string, ProjectTextFile>
): string | undefined {
  const theorems = sortPaths(
    [...files.keys()].filter((path) => isExecutable(path))
  );
  if (theorems.length === 0) return undefined;
  return (
    theorems.find(
      (path) =>
        path.slice(path.lastIndexOf("/") + 1).toLowerCase() === "main.thm"
    ) ?? theorems[0]
  );
}

export function saveProject(
  project: Project,
  workspace?: WorkspaceDescriptor
): string | undefined {
  const data: SavedProject = {
    version: 2,
    files: Object.fromEntries(
      [...project.files.entries()].map(([path, file]) => [path, file.text])
    ),
    entry: project.entry,
    active: project.active,
    example: project.example,
    workspace,
  };
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(data));
    return undefined;
  } catch (error) {
    return `Could not save the project: ${String(error)}`;
  }
}

export function loadProjectRecord(): ProjectLoadResult {
  let raw: string | null = null;
  try {
    raw = localStorage.getItem(STORAGE_KEY);
  } catch {
    return { status: "empty" };
  }
  if (!raw) return { status: "empty" };
  try {
    const data = JSON.parse(raw) as Partial<SavedProject>;
    if (
      typeof data.files !== "object" ||
      data.files === null ||
      Array.isArray(data.files)
    ) {
      return { status: "rejected", message: "Unsupported project record." };
    }
    if (data.version !== 2) {
      return {
        status: "rejected",
        message:
          "The saved project uses an older format and was discarded. " +
          "Starting from scratch.",
      };
    }
    const files = new Map<string, ProjectTextFile>();
    for (const [path, text] of Object.entries(data.files)) {
      if (typeof text === "string") {
        files.set(path, {
          text: normalizeNewlines(text),
          kind: classify(path),
        });
      }
    }
    const entry =
      typeof data.entry === "string" &&
      isExecutable(data.entry) &&
      files.has(data.entry)
        ? data.entry
        : fallbackEntry(files);
    const active =
      typeof data.active === "string" && files.has(data.active)
        ? data.active
        : entry ?? firstPath(files);
    return {
      status: "loaded",
      project: {
        files,
        entry,
        active,
        example: data.example,
      },
      workspace:
        data.workspace && typeof data.workspace.kind === "string"
          ? {
              kind: data.workspace.kind,
              name:
                typeof data.workspace.name === "string"
                  ? data.workspace.name
                  : "",
            }
          : undefined,
    };
  } catch {
    return { status: "rejected", message: "Unreadable project record." };
  }
}

export function loadProject(): Project | undefined {
  const result = loadProjectRecord();
  return result.status === "loaded" ? result.project : undefined;
}

export function clearSavedProject(): void {
  try {
    localStorage.removeItem(STORAGE_KEY);
  } catch {
    // ignore
  }
}
