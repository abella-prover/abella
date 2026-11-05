// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  classify,
  STORAGE_KEY,
  loadProjectRecord,
  parseProjectManifest,
  projectFromBundle,
  saveProject,
  scratchProject,
  type Project,
} from "./project";

class MemoryStorage {
  values = new Map<string, string>();
  getItem(key: string): string | null {
    return this.values.get(key) ?? null;
  }
  setItem(key: string, value: string): void {
    this.values.set(key, value);
  }
  removeItem(key: string): void {
    this.values.delete(key);
  }
}

const storage = new MemoryStorage();
Object.defineProperty(globalThis, "localStorage", {
  value: storage,
  configurable: true,
});

function project(): Project {
  return {
    files: new Map([
      ["main.thm", { text: 'Specification "x".\n', kind: "abella" }],
      ["notes.md", { text: "# Notes\n", kind: "text" }],
    ]),
    entry: "main.thm",
    active: "notes.md",
  };
}

test("version 2 save/load keeps the entry and active file", () => {
  storage.values.clear();
  assert.equal(saveProject(project()), undefined);
  const loaded = loadProjectRecord();
  assert.equal(loaded.status, "loaded");
  if (loaded.status !== "loaded") return;
  assert.equal(loaded.project.entry, "main.thm");
  assert.equal(loaded.project.active, "notes.md");
});

test("a missing stored project loads empty", () => {
  storage.values.clear();
  assert.equal(loadProjectRecord().status, "empty");
});

test("version 1 projects are rejected", () => {
  storage.setItem(
    STORAGE_KEY,
    JSON.stringify({
      version: 1,
      root: "main.thm",
      files: { "main.thm": "Specification \"x\".\n" },
    })
  );
  const loaded = loadProjectRecord();
  assert.equal(loaded.status, "rejected");
});

test("unknown keys including root are ignored on load", () => {
  storage.setItem(
    STORAGE_KEY,
    JSON.stringify({
      version: 2,
      root: "other.thm",
      unknown: true,
      files: { "a.thm": "Specification \"a\".\n" },
    })
  );
  const loaded = loadProjectRecord();
  assert.equal(loaded.status, "loaded");
  if (loaded.status !== "loaded") return;
  assert.equal(loaded.project.entry, undefined);
  assert.equal(loaded.project.active, undefined);
});

test("an invalid entry does not fall back to a theorem", () => {
  storage.setItem(
    STORAGE_KEY,
    JSON.stringify({
      version: 2,
      entry: "notes.md",
      files: {
        "a.thm": "Specification \"a\".\n",
        "main.thm": "Specification \"m\".\n",
      },
    })
  );
  const loaded = loadProjectRecord();
  assert.equal(loaded.status, "loaded");
  if (loaded.status !== "loaded") return;
  assert.equal(loaded.project.entry, undefined);
  assert.equal(loaded.project.active, undefined);
});

test("a stored thmod entry is kept", () => {
  storage.setItem(
    STORAGE_KEY,
    JSON.stringify({
      version: 2,
      entry: "List.thmod",
      files: { "List.thmod": "Module List.\nEnd List.\n" },
    })
  );
  const loaded = loadProjectRecord();
  assert.equal(loaded.status, "loaded");
  if (loaded.status !== "loaded") return;
  assert.equal(loaded.project.entry, "List.thmod");
  assert.equal(loaded.project.active, "List.thmod");
});

test("a project without a theorem has no entry", () => {
  storage.setItem(
    STORAGE_KEY,
    JSON.stringify({
      version: 2,
      files: { "notes.md": "# Notes\n" },
    })
  );
  const loaded = loadProjectRecord();
  assert.equal(loaded.status, "loaded");
  if (loaded.status !== "loaded") return;
  assert.equal(loaded.project.entry, undefined);
  assert.equal(loaded.project.active, undefined);
});

test("scratch projects start from main.thm", () => {
  const scratch = scratchProject();
  assert.equal(scratch.entry, "main.thm");
  assert.equal(scratch.active, "main.thm");
});

test("example bundles are read from entry", () => {
  const loaded = projectFromBundle(
    {
      examples: [{ id: "demo", entry: "demo/main.thm" }],
      files: {
        "demo/main.thm": "Specification \"demo\".\n",
        "demo/notes.md": "# Notes\n",
      },
    },
    "demo"
  );
  assert.ok(loaded);
  assert.equal(loaded.entry, "demo/main.thm");
  assert.equal(loaded.active, "demo/main.thm");
});

test("example bundles may open a text entry without a prover entry", () => {
  const loaded = projectFromBundle(
    {
      examples: [{ id: "modules", entry: "examples/modules/README.md" }],
      files: {
        "examples/modules/README.md": "# Modules\n",
        "examples/modules/ListUse.thm": "Specification \"demo\".\n",
      },
    },
    "modules"
  );
  assert.ok(loaded);
  assert.equal(loaded.entry, undefined);
  assert.equal(loaded.active, "examples/modules/README.md");
});

test("example bundles may use a thmod entry", () => {
  const loaded = projectFromBundle(
    {
      examples: [{ id: "modules", entry: "examples/modules/List.thmod" }],
      files: {
        "examples/modules/List.thmod": "Module List[T].\nEnd List.\n",
      },
    },
    "modules"
  );
  assert.ok(loaded);
  assert.equal(loaded.entry, "examples/modules/List.thmod");
  assert.equal(loaded.active, "examples/modules/List.thmod");
});

test("example bundles with a root key are rejected", () => {
  const loaded = projectFromBundle(
    {
      examples: [{ id: "demo", root: "main.thm" }],
      files: { "main.thm": "Specification \"demo\".\n" },
    },
    "demo"
  );
  assert.equal(loaded, undefined);
});

test("project manifests parse version 2 documents", () => {
  const manifest = parseProjectManifest(
    JSON.stringify({ version: 2, entry: "main.thm", files: ["main.thm"] })
  );
  assert.equal(manifest.version, 2);
  assert.equal(manifest.entry, "main.thm");
  assert.deepEqual(manifest.files, ["main.thm"]);
});

test("project manifests reject old versions and missing file lists", () => {
  assert.throws(
    () => parseProjectManifest(JSON.stringify({ version: 1, files: [] })),
    /incompatible version/
  );
  assert.throws(
    () => parseProjectManifest(JSON.stringify({ version: 2 })),
    /missing its file list/
  );
  assert.throws(() => parseProjectManifest("not json"), /not valid JSON/);
});

test("classifies thmod files as Abella sources", () => {
  assert.equal(classify("foo.thmod"), "abella");
  assert.equal(classify("foo.thm"), "abella");
  assert.equal(classify("foo.thmodc"), "text");
});
