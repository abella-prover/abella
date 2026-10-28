// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  addTab,
  closeTabAt,
  reconcileTabState,
  remapTabs,
  tabLabels,
} from "./tabs";

test("opening an existing tab does not duplicate it", () => {
  assert.deepEqual(addTab(["a.thm"], "a.thm"), ["a.thm"]);
  assert.deepEqual(addTab(["a.thm"], "b.thm"), ["a.thm", "b.thm"]);
});

test("closing the active tab picks the right neighbour, then the left", () => {
  assert.deepEqual(closeTabAt(["a", "b", "c"], "b", "b"), {
    tabs: ["a", "c"],
    active: "c",
  });
  assert.deepEqual(closeTabAt(["a", "b", "c"], "c", "c"), {
    tabs: ["a", "b"],
    active: "b",
  });
  assert.deepEqual(closeTabAt(["a"], "a", "a"), {
    tabs: [],
    active: undefined,
  });
});

test("closing an inactive tab keeps the active tab", () => {
  assert.deepEqual(closeTabAt(["a", "b", "c"], "b", "a"), {
    tabs: ["a", "c"],
    active: "a",
  });
  assert.deepEqual(closeTabAt(["a"], "missing", "a"), {
    tabs: ["a"],
    active: "a",
  });
});

test("rename remaps tabs in place", () => {
  const renames = new Map([
    ["a.thm", "b.thm"],
    ["dir/a.sig", "dir/a2.sig"],
  ]);
  assert.deepEqual(remapTabs(["a.thm", "x.md", "dir/a.sig"], renames), [
    "b.thm",
    "x.md",
    "dir/a2.sig",
  ]);
});

test("duplicate basenames get the shortest unique suffix", () => {
  const labels = tabLabels(["a/notes.md", "b/notes.md", "main.thm"]);
  assert.equal(labels.get("a/notes.md"), "a/notes.md");
  assert.equal(labels.get("b/notes.md"), "b/notes.md");
  assert.equal(labels.get("main.thm"), "main.thm");
});

test("unique basenames stay basenames", () => {
  const labels = tabLabels(["main.thm", "spec.sig", "docs/notes.md"]);
  assert.equal(labels.get("main.thm"), "main.thm");
  assert.equal(labels.get("spec.sig"), "spec.sig");
  assert.equal(labels.get("docs/notes.md"), "notes.md");
});

test("reconcile drops stale tabs and heals a missing active tab", () => {
  const files = new Set(["a", "b", "c"]);
  assert.deepEqual(
    reconcileTabState(["a", "gone", "b", "a"], (path) => files.has(path), "gone", "b"),
    { tabs: ["a", "b"], active: "b" }
  );
});

test("reconcile clears the active tab when nothing remains", () => {
  assert.deepEqual(
    reconcileTabState(["gone"], () => false, "gone", "also-gone"),
    { tabs: [], active: undefined }
  );
});

test("reconcile keeps a valid active file even if it lost its tab", () => {
  assert.deepEqual(
    reconcileTabState(["a"], (path) => path === "a" || path === "b", "b"),
    { tabs: ["a", "b"], active: "b" }
  );
});
