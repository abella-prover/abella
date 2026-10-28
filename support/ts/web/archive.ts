// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { strFromU8, strToU8, unzipSync, zipSync } from "fflate";
import {
  classify,
  explicitEntry,
  normalizeNewlines,
  type Project,
  type ProjectTextFile,
} from "./project";
import { isCandidateFile } from "./workspace-directory";

interface Manifest {
  version: 2;
  entry?: string;
  files: string[];
}

export function downloadProject(project: Project): void {
  const manifest: Manifest = {
    version: 2,
    entry: project.entry,
    files: [...project.files.keys()].sort(),
  };
  const archive: Record<string, Uint8Array> = {
    "project.json": strToU8(JSON.stringify(manifest, null, 2)),
  };
  for (const [path, file] of project.files) {
    archive[path] = strToU8(file.text);
  }
  const bytes = zipSync(archive, { level: 6 });
  const blob = new Blob([bytes], { type: "application/zip" });
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = url;
  link.download = "abella-web.zip";
  link.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

export interface ImportedProject {
  project: Project;
  skipped: number;
}

export async function importProject(file: File): Promise<ImportedProject> {
  const bytes = new Uint8Array(await file.arrayBuffer());
  let entries: Record<string, Uint8Array>;
  try {
    entries = unzipSync(bytes);
  } catch {
    throw new Error("That file is not a readable zip archive.");
  }
  const manifestBytes = entries["project.json"];
  if (!manifestBytes) {
    throw new Error("The archive does not contain project.json.");
  }
  const manifest = JSON.parse(strFromU8(manifestBytes)) as Partial<Manifest>;
  if (manifest.version !== 2 || !Array.isArray(manifest.files)) {
    throw new Error(
      "This archive was written by an incompatible version of Abella Web. " +
        "Export it again from the current version."
    );
  }
  const files = new Map<string, ProjectTextFile>();
  const names = manifest.files;
  let skipped = 0;
  for (const path of names) {
    const data = entries[path];
    if (!data) continue;
    if (!isCandidateFile(path)) {
      skipped++;
      continue;
    }
    files.set(path, {
      text: normalizeNewlines(strFromU8(data)),
      kind: classify(path),
    });
  }
  const entry = explicitEntry(files, manifest.entry);
  return {
    project: {
      files,
      entry,
      active: entry,
    },
    skipped,
  };
}
