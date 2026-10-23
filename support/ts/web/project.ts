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
  root: string;
  active: string;
  example?: string;
}

export const STORAGE_KEY = "abella.web.v1.project";

export function classify(path: string): FileKind {
  return /\.(thm|sig|mod)$/i.test(path) ? "abella" : "text";
}

export function sortPaths(paths: string[]): string[] {
  return [...paths].sort((a, b) => a.localeCompare(b));
}

export function abellaFiles(project: Project): ProjectFile[] {
  return [...project.files.entries()]
    .filter(([, file]) => file.kind === "abella")
    .map(([path, file]) => ({ path, contents: file.text }));
}

export function rootText(project: Project): string {
  return project.files.get(project.root)?.text ?? "";
}

export function setFileText(project: Project, path: string, text: string): void {
  const file = project.files.get(path);
  if (file) file.text = text;
}

export function scratchProject(): Project {
  const files = new Map<string, ProjectTextFile>();
  files.set("empty.sig", { text: "sig empty.\n", kind: "abella" });
  files.set("empty.mod", { text: "module empty.\n", kind: "abella" });
  files.set("main.thm", {
    text: 'Specification "empty".\n',
    kind: "abella",
  });
  return { files, root: "main.thm", active: "main.thm" };
}

export function projectFromBundle(
  bundle: unknown,
  id: string
): Project | undefined {
  const data = bundle as {
    examples?: { id: string; root: string; files?: string[] }[];
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
      files.set(path, { text, kind: classify(path) });
    }
  }
  if (!files.has(example.root)) return undefined;
  return {
    files,
    root: example.root,
    active: example.root,
    example: id,
  };
}

export interface WorkspaceDescriptor {
  kind: string;
  name: string;
}

interface SavedProject {
  version: 1;
  files: Record<string, string>;
  root: string;
  active?: string;
  example?: string;
  workspace?: WorkspaceDescriptor;
}

export interface LoadedProject {
  project: Project;
  workspace?: WorkspaceDescriptor;
}

export function saveProject(
  project: Project,
  workspace?: WorkspaceDescriptor
): string | undefined {
  const data: SavedProject = {
    version: 1,
    files: Object.fromEntries(
      [...project.files.entries()].map(([path, file]) => [path, file.text])
    ),
    root: project.root,
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

export function loadProjectRecord(): LoadedProject | undefined {
  let raw: string | null = null;
  try {
    raw = localStorage.getItem(STORAGE_KEY);
  } catch {
    return undefined;
  }
  if (!raw) return undefined;
  try {
    const data = JSON.parse(raw) as SavedProject;
    if (data.version !== 1 || typeof data.files !== "object") return undefined;
    const files = new Map<string, ProjectTextFile>();
    for (const [path, text] of Object.entries(data.files)) {
      if (typeof text === "string") {
        files.set(path, { text, kind: classify(path) });
      }
    }
    if (!files.has(data.root)) return undefined;
    return {
      project: {
        files,
        root: data.root,
        active: files.has(data.active ?? "") ? data.active! : data.root,
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
    return undefined;
  }
}

export function loadProject(): Project | undefined {
  return loadProjectRecord()?.project;
}

export function clearSavedProject(): void {
  try {
    localStorage.removeItem(STORAGE_KEY);
  } catch {
    // ignore
  }
}
