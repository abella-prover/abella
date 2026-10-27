// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { strToU8, zipSync } from "fflate";
import { importProject } from "./archive";

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

test("unknown keys are ignored and a missing entry falls back", async () => {
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
  assert.equal(imported.project.entry, "main.thm");
});
