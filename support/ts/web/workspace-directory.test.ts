// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  chooseEntry,
  isCandidateFile,
  isSkippedDirectory,
} from "./workspace-directory";
import { workspaceMessage } from "./workspace";

test("keeps Abella and small text files", () => {
  for (const path of [
    "main.thm",
    "spec.sig",
    "spec.mod",
    "sub/Proof.THM",
    "README",
    "LICENSE",
    "NOTES.txt",
    "docs/guide.md",
    "notes.markdown",
  ]) {
    assert.equal(isCandidateFile(path), true, path);
  }
});

test("skips caches, binaries, manifests, and hidden files", () => {
  for (const path of [
    "main.thc",
    "logo.png",
    "project.json",
    "package.json",
    ".notes.txt",
    "archive.zip",
  ]) {
    assert.equal(isCandidateFile(path), false, path);
  }
});

test("skips build and hidden directories only", () => {
  for (const name of [".git", "node_modules", "_build", "dist"]) {
    assert.equal(isSkippedDirectory(name), true, name);
  }
  assert.equal(isSkippedDirectory("src"), false);
  assert.equal(isSkippedDirectory("examples"), false);
});

test("uses a manifest entry when it names a loaded theorem", () => {
  const paths = ["a.thm", "b.thm"];
  assert.equal(chooseEntry(paths, "project", "b.thm"), "b.thm");
  assert.equal(chooseEntry(paths, "project", "missing.thm"), "a.thm");
});

test("prefers main.thm then the folder name among several theorems", () => {
  assert.equal(chooseEntry(["a.thm", "main.thm"], "project"), "main.thm");
  assert.equal(chooseEntry(["a.thm", "project.thm"], "project"), "project.thm");
  assert.equal(chooseEntry(["b.thm", "a.thm"], "project"), "a.thm");
});

test("returns no entry without a theorem", () => {
  assert.equal(chooseEntry(["spec.sig", "README.md"], "project"), undefined);
  assert.equal(chooseEntry([], "project"), undefined);
});

test("formats errors", () => {
  assert.equal(workspaceMessage(new Error("nope")), "nope");
  assert.equal(workspaceMessage("nope"), "nope");
});

import {
  MAX_FILE_BYTES,
  readDirectoryHandle,
  type DirectoryFileHandle,
  type DirectoryHandle,
} from "./workspace-directory";

class FakeFileHandle implements DirectoryFileHandle {
  readonly kind = "file" as const;
  data: string;
  modified = 1;

  constructor(readonly name: string, data: string) {
    this.data = data;
  }

  async getFile(): Promise<File> {
    return new File([this.data], this.name, {
      lastModified: this.modified,
    });
  }

  async createWritable(): Promise<{
    write(data: string): Promise<void>;
    close(): Promise<void>;
  }> {
    const file = this;
    return {
      async write(data: string) {
        file.data = data;
        file.modified++;
      },
      async close() {
        // The write is already applied.
      },
    };
  }
}

class FakeDirectory implements DirectoryHandle {
  readonly kind = "directory" as const;
  children = new Map<string, FakeDirectory | FakeFileHandle>();

  constructor(
    readonly name: string,
    entries: [string, FakeDirectory | FakeFileHandle][] = []
  ) {
    for (const [entryName, entry] of entries) {
      this.children.set(entryName, entry);
    }
  }

  async *entries(): AsyncIterableIterator<
    [string, DirectoryHandle | DirectoryFileHandle]
  > {
    for (const entry of this.children) yield entry;
  }

  async getDirectoryHandle(
    name: string,
    options?: { create?: boolean }
  ): Promise<DirectoryHandle> {
    const existing = this.children.get(name);
    if (existing instanceof FakeDirectory) return existing;
    if (existing || !options?.create) {
      throw new Error(`Missing directory ${name}`);
    }
    const created = new FakeDirectory(name);
    this.children.set(name, created);
    return created;
  }

  async getFileHandle(
    name: string,
    options?: { create?: boolean }
  ): Promise<DirectoryFileHandle> {
    const existing = this.children.get(name);
    if (existing instanceof FakeFileHandle) return existing;
    if (existing || !options?.create) {
      throw new Error(`Missing file ${name}`);
    }
    const created = new FakeFileHandle(name, "");
    this.children.set(name, created);
    return created;
  }

  async removeEntry(name: string): Promise<void> {
    this.children.delete(name);
  }
}

function folderFixture(): FakeDirectory {
  return new FakeDirectory("project", [
    ["main.thm", new FakeFileHandle("main.thm", 'Specification "x".\n')],
    ["notes.md", new FakeFileHandle("notes.md", "# Notes\n")],
    ["logo.png", new FakeFileHandle("logo.png", "binary")],
    [".hidden", new FakeFileHandle(".hidden", "secret")],
    ["node_modules", new FakeDirectory("node_modules", [
      ["pkg.js", new FakeFileHandle("pkg.js", "ignored")],
    ])],
    ["empty", new FakeDirectory("empty")],
    [
      "big.thm",
      new FakeFileHandle("big.thm", "x".repeat(MAX_FILE_BYTES + 1)),
    ],
  ]);
}

test("a folder enumerates inert entries, skips hidden and ignored dirs", async () => {
  const handle = folderFixture();
  const opened = await readDirectoryHandle(handle, () => true);
  assert.equal(opened.project.entry, "main.thm");
  assert.deepEqual(
    [...opened.project.files.keys()].sort(),
    ["main.thm", "notes.md"]
  );
  const entries = await opened.workspace.entries();
  const byPath = new Map(entries.map((entry) => [entry.path, entry]));
  assert.equal(byPath.has(".hidden"), false);
  assert.equal(byPath.has("node_modules"), false);
  assert.equal(byPath.get("empty")?.kind, "directory");
  assert.equal(byPath.get("logo.png")?.openable, false);
  assert.equal(byPath.get("logo.png")?.reason, "unsupported");
  assert.equal(byPath.get("big.thm")?.openable, false);
  assert.equal(byPath.get("big.thm")?.reason, "too-large");
  assert.equal(byPath.get("main.thm")?.openable, true);
});

test("a folder without a theorem opens with no entry", async () => {
  const handle = new FakeDirectory("project", [
    ["notes.md", new FakeFileHandle("notes.md", "# Notes\n")],
    ["spec.sig", new FakeFileHandle("spec.sig", "sig spec.\n")],
  ]);
  const opened = await readDirectoryHandle(handle, () => true);
  assert.equal(opened.project.entry, undefined);
  assert.equal(opened.project.active, "notes.md");
});

test("folder writes create nested files and removes delete them", async () => {
  const handle = folderFixture();
  const opened = await readDirectoryHandle(handle, () => true);
  const workspace = opened.workspace;
  await workspace.write("sub/new.thm", "Theorem t : True.\n");
  assert.equal(opened.project.files.has("sub/new.thm"), true);
  assert.equal(
    (await workspace.entries()).some(
      (entry) => entry.path === "sub" && entry.kind === "directory"
    ),
    true
  );
  await workspace.remove("main.thm");
  assert.equal(opened.project.files.has("main.thm"), false);
  assert.equal(handle.children.has("main.thm"), false);
});

test("folder manifests read entry and ignore root", async () => {
  const withEntry = new FakeDirectory("project", [
    [
      "project.json",
      new FakeFileHandle(
        "project.json",
        JSON.stringify({ root: "a.thm", entry: "b.thm", extra: true })
      ),
    ],
    ["a.thm", new FakeFileHandle("a.thm", "Specification \"a\".\n")],
    ["b.thm", new FakeFileHandle("b.thm", "Specification \"b\".\n")],
  ]);
  const opened = await readDirectoryHandle(withEntry, () => true);
  assert.equal(opened.project.entry, "b.thm");

  const legacy = new FakeDirectory("project", [
    [
      "project.json",
      new FakeFileHandle("project.json", JSON.stringify({ root: "b.thm" })),
    ],
    ["a.thm", new FakeFileHandle("a.thm", "Specification \"a\".\n")],
    ["b.thm", new FakeFileHandle("b.thm", "Specification \"b\".\n")],
  ]);
  const legacyOpened = await readDirectoryHandle(legacy, () => true);
  assert.equal(legacyOpened.project.entry, "a.thm");
});
