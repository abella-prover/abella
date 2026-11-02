// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { strToU8, zipSync } from "fflate";
import {
  MAX_ARCHIVE_BYTES,
  importProject,
  importProjectBytes,
} from "./archive";
import { MAX_FILE_BYTES, MAX_FILES } from "./workspace-directory";

function archiveFile(
  manifest: unknown,
  files: Record<string, string>
): File {
  const archive: Record<string, Uint8Array> = {
    "project.json": strToU8(JSON.stringify(manifest)),
  };
  for (const [path, text] of Object.entries(files)) {
    archive[path] = strToU8(text);
  }
  const bytes = zipSync(archive);
  return {
    arrayBuffer: async () =>
      bytes.buffer.slice(
        bytes.byteOffset,
        bytes.byteOffset + bytes.byteLength
      ),
  } as File;
}

test("version 2 archives round-trip the entry", async () => {
  const imported = await importProject(
    archiveFile(
      { version: 2, entry: "main.thm", files: ["main.thm", "notes.md"] },
      {
        "main.thm": "Specification \"x\".\n",
        "notes.md": "# Notes\n",
      }
    )
  );
  assert.equal(imported.project.entry, "main.thm");
  assert.equal(imported.project.active, "main.thm");
  assert.equal(imported.skipped, 0);
  assert.deepEqual(
    [...imported.project.files.keys()].sort(),
    ["main.thm", "notes.md"]
  );
});

test("version 1 archives are rejected", async () => {
  await assert.rejects(
    () =>
      importProject(
        archiveFile(
          { version: 1, root: "main.thm", files: ["main.thm"] },
          { "main.thm": "Specification \"x\".\n" }
        )
      ),
    /incompatible version/
  );
});

test("unsupported archive entries are skipped and counted", async () => {
  const imported = await importProject(
    archiveFile(
      {
        version: 2,
        entry: "main.thm",
        files: ["main.thm", "logo.png", "data.bin"],
      },
      {
        "main.thm": "Specification \"x\".\n",
        "logo.png": "not text",
        "data.bin": "binary",
      }
    )
  );
  assert.equal(imported.skipped, 2);
  assert.deepEqual([...imported.project.files.keys()], ["main.thm"]);
});

test("unknown keys are ignored and a missing entry starts empty", async () => {
  const imported = await importProject(
    archiveFile(
      {
        version: 2,
        root: "notes.md",
        files: ["a.thm", "main.thm"],
      },
      {
        "a.thm": "Specification \"a\".\n",
        "main.thm": "Specification \"m\".\n",
      }
    )
  );
  assert.equal(imported.project.entry, undefined);
  assert.equal(imported.project.active, undefined);
});

test("importProjectBytes accepts the same version 2 archive", async () => {
  const bytes = zipSync({
    "project.json": strToU8(
      JSON.stringify({
        version: 2,
        entry: "main.thm",
        files: ["main.thm"],
      })
    ),
    "main.thm": strToU8('Specification "x".\n'),
  });
  const imported = await importProjectBytes(bytes);
  assert.equal(imported.project.entry, "main.thm");
  assert.equal(
    imported.project.files.get("main.thm")?.text,
    'Specification "x".\n'
  );
});

test("archives without a manifest are rejected", async () => {
  const bytes = zipSync({ "main.thm": strToU8('Specification "x".\n') });
  await assert.rejects(() => importProjectBytes(bytes), /project\.json/);
});

test("absolute archive paths are rejected", async () => {
  const bytes = zipSync({
    "project.json": strToU8(
      JSON.stringify({ version: 2, files: ["/evil.thm"] })
    ),
    "/evil.thm": strToU8("x"),
  });
  await assert.rejects(() => importProjectBytes(bytes), /unsafe path/);
});

test("sibling paths are allowed because the archive stays in memory", async () => {
  const bytes = zipSync({
    "project.json": strToU8(
      JSON.stringify({ version: 2, files: ["../sibling.thm"] })
    ),
    "../sibling.thm": strToU8('Specification "x".\n'),
  });
  const imported = await importProjectBytes(bytes);
  assert.ok(imported.project.files.has("../sibling.thm"));
});

test("oversized individual files are rejected", async () => {
  const bytes = zipSync({
    "project.json": strToU8(
      JSON.stringify({ version: 2, files: ["big.thm"] })
    ),
    "big.thm": new Uint8Array(MAX_FILE_BYTES + 1),
  });
  await assert.rejects(
    () => importProjectBytes(bytes),
    /larger than the per-file limit/
  );
});

test("archives with too many entries are rejected", async () => {
  const archive: Record<string, Uint8Array> = {
    "project.json": strToU8(JSON.stringify({ version: 2, files: [] })),
  };
  for (let index = 0; index <= MAX_FILES; index += 1) {
    archive[`f${index}.thm`] = strToU8("x");
  }
  const bytes = zipSync(archive);
  await assert.rejects(
    () => importProjectBytes(bytes),
    /more than 500 files/
  );
});

test("compressed archives over the cap are rejected", async () => {
  const bytes = new Uint8Array(MAX_ARCHIVE_BYTES + 1);
  await assert.rejects(
    () => importProjectBytes(bytes),
    /larger than/
  );
});
