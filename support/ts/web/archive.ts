// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { strFromU8, strToU8, unzipSync, zipSync } from "fflate";
import {
  classify,
  explicitEntry,
  normalizeNewlines,
  parseProjectManifest,
  type Project,
  type ProjectManifest,
  type ProjectTextFile,
} from "./project";
import { isCandidateFile } from "./workspace-directory";

export function downloadProject(project: Project): void {
  const manifest: ProjectManifest = {
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
  const manifest = parseProjectManifest(strFromU8(manifestBytes));
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
