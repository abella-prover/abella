// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { strFromU8, strToU8, unzipSync, zipSync } from "fflate";
import { classify, type Project, type ProjectTextFile } from "./project";

interface Manifest {
  version: 1;
  root: string;
  files: string[];
}

export function downloadProject(project: Project): void {
  const manifest: Manifest = {
    version: 1,
    root: project.root,
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

export async function importProject(file: File): Promise<Project> {
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
  const manifest = JSON.parse(strFromU8(manifestBytes)) as Manifest;
  if (manifest.version !== 1 || !manifest.root) {
    throw new Error("Unsupported project.json.");
  }
  const files = new Map<string, ProjectTextFile>();
  const names = manifest.files?.length
    ? manifest.files
    : Object.keys(entries).filter((path) => path !== "project.json");
  for (const path of names) {
    const data = entries[path];
    if (!data) continue;
    files.set(path, { text: strFromU8(data), kind: classify(path) });
  }
  if (!files.has(manifest.root)) {
    throw new Error("The root file is missing from the archive.");
  }
  return {
    files,
    root: manifest.root,
    active: manifest.root,
  };
}
