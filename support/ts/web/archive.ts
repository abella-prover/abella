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
import {
  MAX_FILE_BYTES,
  MAX_FILES,
  isCandidateFile,
} from "./workspace-directory";

export const MAX_ARCHIVE_BYTES = 16 * 1024 * 1024;
export const MAX_UNCOMPRESSED_BYTES = 32 * 1024 * 1024;

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

interface CentralEntry {
  name: string;
  uncompressed: number;
}

function readU16(bytes: Uint8Array, offset: number): number {
  if (offset < 0 || offset + 2 > bytes.length) return Number.NaN;
  return bytes[offset] | (bytes[offset + 1] << 8);
}

function readU32(bytes: Uint8Array, offset: number): number {
  if (offset < 0 || offset + 4 > bytes.length) return Number.NaN;
  return (
    (bytes[offset] |
      (bytes[offset + 1] << 8) |
      (bytes[offset + 2] << 16) |
      (bytes[offset + 3] * 0x1000000)) >>>
    0
  );
}

function centralDirectory(bytes: Uint8Array): CentralEntry[] {
  const minimum = Math.max(0, bytes.length - 22 - 0xffff);
  let end = -1;
  for (let offset = bytes.length - 22; offset >= minimum; offset -= 1) {
    if (readU32(bytes, offset) === 0x06054b50) {
      end = offset;
      break;
    }
  }
  if (end < 0) {
    throw new Error("That file is not a readable zip archive.");
  }

  const count = readU16(bytes, end + 10);
  const size = readU32(bytes, end + 12);
  const offset = readU32(bytes, end + 16);
  if (
    !Number.isFinite(count) ||
    !Number.isFinite(size) ||
    !Number.isFinite(offset) ||
    count === 0xffff ||
    size === 0xffffffff ||
    offset === 0xffffffff
  ) {
    throw new Error("ZIP64 archives are not supported.");
  }
  if (count > MAX_FILES + 1) {
    throw new Error(
      `The archive lists more than ${MAX_FILES} files.`
    );
  }
  if (offset + size > bytes.length) {
    throw new Error("That file is not a readable zip archive.");
  }

  const entries: CentralEntry[] = [];
  let cursor = offset;
  let total = 0;
  for (let index = 0; index < count; index += 1) {
    if (
      readU32(bytes, cursor) !== 0x02014b50 ||
      cursor + 46 > bytes.length
    ) {
      throw new Error("That file is not a readable zip archive.");
    }
    const uncompressed = readU32(bytes, cursor + 24);
    const nameLength = readU16(bytes, cursor + 28);
    const extraLength = readU16(bytes, cursor + 30);
    const commentLength = readU16(bytes, cursor + 32);
    const nameStart = cursor + 46;
    const nameEnd = nameStart + nameLength;
    if (
      !Number.isFinite(uncompressed) ||
      !Number.isFinite(nameLength) ||
      !Number.isFinite(extraLength) ||
      !Number.isFinite(commentLength) ||
      nameEnd > bytes.length
    ) {
      throw new Error("That file is not a readable zip archive.");
    }
    const name = new TextDecoder().decode(
      bytes.subarray(nameStart, nameEnd)
    );
    if (!safeArchivePath(name)) {
      throw new Error(`The archive contains an unsafe path: ${name}`);
    }
    total += uncompressed;
    if (total > MAX_UNCOMPRESSED_BYTES) {
      throw new Error(
        `The archive expands to more than ${MAX_UNCOMPRESSED_BYTES} bytes.`
      );
    }
    if (isCandidateFile(name) && uncompressed > MAX_FILE_BYTES) {
      throw new Error(`${name} is larger than the per-file limit.`);
    }
    entries.push({ name, uncompressed });
    cursor = nameEnd + extraLength + commentLength;
  }
  return entries;
}

function safeArchivePath(path: string): boolean {
  // Archives are imported into memory, never extracted, so a `..` is
  // legitimate: abella_doc uses it for siblings of the theorem page.
  return path !== "" && !path.startsWith("/") && !path.includes("\\");
}

function stripBom(text: string): string {
  return text.charCodeAt(0) === 0xfeff ? text.slice(1) : text;
}

export async function importProjectBytes(
  bytes: Uint8Array
): Promise<ImportedProject> {
  if (bytes.byteLength > MAX_ARCHIVE_BYTES) {
    throw new Error(
      `The archive is larger than ${MAX_ARCHIVE_BYTES} bytes.`
    );
  }
  centralDirectory(bytes);

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
  if (manifest.files.length > MAX_FILES) {
    throw new Error(
      `The archive lists more than ${MAX_FILES} files.`
    );
  }

  const files = new Map<string, ProjectTextFile>();
  let skipped = 0;
  for (const path of manifest.files) {
    const data = entries[path];
    if (!data) continue;
    if (!isCandidateFile(path)) {
      skipped++;
      continue;
    }
    files.set(path, {
      text: normalizeNewlines(stripBom(strFromU8(data))),
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

export async function importProject(file: File): Promise<ImportedProject> {
  return importProjectBytes(new Uint8Array(await file.arrayBuffer()));
}
