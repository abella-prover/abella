// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  chooseRoot,
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

test("uses a manifest root when it names a loaded theorem", () => {
  const paths = ["a.thm", "b.thm"];
  assert.equal(chooseRoot(paths, "project", "b.thm"), "b.thm");
  assert.equal(chooseRoot(paths, "project", "missing.thm"), "a.thm");
});

test("prefers main.thm then the folder name among several theorems", () => {
  assert.equal(chooseRoot(["a.thm", "main.thm"], "project"), "main.thm");
  assert.equal(chooseRoot(["a.thm", "project.thm"], "project"), "project.thm");
  assert.equal(chooseRoot(["b.thm", "a.thm"], "project"), "a.thm");
});

test("returns no root without a theorem", () => {
  assert.equal(chooseRoot(["spec.sig", "README.md"], "project"), undefined);
  assert.equal(chooseRoot([], "project"), undefined);
});

test("formats errors", () => {
  assert.equal(workspaceMessage(new Error("nope")), "nope");
  assert.equal(workspaceMessage("nope"), "nope");
});
