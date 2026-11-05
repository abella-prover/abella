// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { ChangeSet } from "@codemirror/state";
import { CommandOutputStore } from "./command-output";
import type { OutputEntry } from "./session";

const info = (message: string): OutputEntry => ({
  severity: "info",
  message,
});

const error = (message: string): OutputEntry => ({
  severity: "error",
  message,
});

test("stores one group per command and replaces on recheck", () => {
  const store = new CommandOutputStore();
  store.set({ from: 5, to: 10, position: 10 }, [info("first")]);
  store.set({ from: 5, to: 10, position: 10 }, [info("second")]);

  assert.deepEqual(
    store.values().map((output) => output.entries.map((e) => e.message)),
    [["second"]]
  );
});

test("empty entries remove the command output", () => {
  const store = new CommandOutputStore();
  store.set({ from: 5, to: 10, position: 10 }, [error("bad")]);
  store.set({ from: 5, to: 10, position: 10 }, []);

  assert.equal(store.values().length, 0);
  assert.equal(store.get(5), undefined);
});

test("pruning drops output after the checked tip", () => {
  const store = new CommandOutputStore();
  store.set({ from: 5, to: 10, position: 10 }, [info("early")]);
  store.set({ from: 15, to: 20, position: 20 }, [info("late")]);

  assert.equal(store.prune(10), true);
  assert.deepEqual(
    store.values().map((output) => output.entries[0].message),
    ["early"]
  );
  assert.equal(store.prune(10), false);
});

test("edits before a command shift its marker", () => {
  const store = new CommandOutputStore();
  store.set({ from: 5, to: 10, position: 10 }, [info("kept")]);
  const changes = ChangeSet.of({ from: 0, insert: "abc" }, 12);

  assert.equal(store.remap(changes), true);
  const [output] = store.values();
  assert.equal(output.from, 8);
  assert.equal(output.to, 13);
  assert.equal(output.position, 13);
});

test("edits inside a command drop its stale output", () => {
  const store = new CommandOutputStore();
  store.set({ from: 5, to: 10, position: 10 }, [info("stale")]);
  const changes = ChangeSet.of({ from: 7, insert: "x" }, 12);

  assert.equal(store.remap(changes), true);
  assert.equal(store.values().length, 0);
});

test("edits after a command leave its output in place", () => {
  const store = new CommandOutputStore();
  store.set({ from: 5, to: 10, position: 10 }, [info("kept")]);
  const changes = ChangeSet.of({ from: 11, insert: "x" }, 12);

  assert.equal(store.remap(changes), false);
  assert.deepEqual(store.get(5), {
    from: 5,
    to: 10,
    position: 10,
    entries: [info("kept")],
  });
});
