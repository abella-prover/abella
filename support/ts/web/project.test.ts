// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  STORAGE_KEY,
  loadProjectRecord,
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
  assert.equal(loaded.project.entry, "a.thm");
});

test("an invalid entry falls back to main.thm", () => {
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
  assert.equal(loaded.project.entry, "main.thm");
  assert.equal(loaded.project.active, "main.thm");
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
  assert.equal(loaded.project.active, "notes.md");
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
