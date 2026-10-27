// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { allDirectories, buildTree, normalizeNewPath } from "./files";
import type { WorkspaceEntry } from "./workspace";

function entry(
  path: string,
  kind: "file" | "directory" = "file",
  openable = true,
  reason?: WorkspaceEntry["reason"]
): WorkspaceEntry {
  return { path, kind, openable, reason };
}

test("tree sorts directories before files at every level", () => {
  const tree = buildTree([
    entry("b.thm"),
    entry("a/z.thm"),
    entry("a/a.thm"),
    entry("c/notes.md"),
  ]);
  assert.deepEqual(
    tree.map((node) => node.path),
    ["a", "c", "b.thm"]
  );
  assert.deepEqual(
    tree[0].children.map((node) => node.path),
    ["a/a.thm", "a/z.thm"]
  );
});

test("derives directories from file paths and compacts chains", () => {
  const tree = buildTree([entry("a/b/c.thm")]);
  assert.equal(tree[0].path, "a/b");
  assert.equal(tree[0].name, "a/b");
  assert.equal(tree[0].kind, "directory");
  assert.equal(tree[0].children[0].path, "a/b/c.thm");
});

test("does not compact a folder that also contains files", () => {
  const tree = buildTree([
    entry("a/README.md"),
    entry("a/b/c.thm"),
  ]);
  assert.equal(tree[0].path, "a");
  assert.equal(tree[0].children[0].path, "a/b");
  assert.equal(tree[0].children[0].name, "b");
});

test("keeps explicit empty directories", () => {
  const tree = buildTree([entry("empty", "directory")]);
  assert.equal(tree[0].path, "empty");
  assert.equal(tree[0].kind, "directory");
  assert.deepEqual(tree[0].children, []);
});

test("carries inert flags and reasons", () => {
  const tree = buildTree([
    entry("logo.png", "file", false, "unsupported"),
    entry("big.thm", "file", false, "too-large"),
  ]);
  const byPath = new Map(tree.map((node) => [node.path, node]));
  assert.equal(byPath.get("logo.png")?.openable, false);
  assert.equal(byPath.get("logo.png")?.reason, "unsupported");
  assert.equal(byPath.get("big.thm")?.reason, "too-large");
});

test("allDirectories includes explicit and derived directories", () => {
  const directories = allDirectories([
    entry("empty", "directory"),
    entry("a/b/c.thm"),
  ]);
  assert.deepEqual([...directories].sort(), ["a", "a/b", "empty"]);
});

test("ties break deterministically on the full path", () => {
  const tree = buildTree([
    entry("a/Proof.thm"),
    entry("b/proof.thm"),
  ]);
  assert.deepEqual(
    tree.map((node) => node.path),
    ["a", "b"]
  );
});

test("new paths are normalized and traversal is rejected", () => {
  assert.equal(normalizeNewPath(" sub/a.thm "), "sub/a.thm");
  assert.equal(normalizeNewPath("sub\\a.thm"), "sub/a.thm");
  assert.equal(normalizeNewPath("./notes.md"), "notes.md");
  assert.equal(normalizeNewPath(""), undefined);
  assert.equal(normalizeNewPath("/abs.thm"), undefined);
  assert.equal(normalizeNewPath("a/../b.thm"), undefined);
  assert.equal(normalizeNewPath("a//b.thm"), undefined);
});
