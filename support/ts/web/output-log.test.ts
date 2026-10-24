// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { OutputLog } from "./output-log";
import type { OutputEntry } from "./session";

const info = (message: string): OutputEntry => ({
  severity: "info",
  message,
});

const error = (message: string): OutputEntry => ({
  severity: "error",
  message,
});

test("orders positioned output and keeps manual messages last", () => {
  const log = new OutputLog();
  log.append([info("manual")]);
  log.append([info("second")], { from: 15, position: 20 });
  log.append([info("first")], { from: 5, position: 10 });

  assert.deepEqual(
    log.ordered.map((record) => record.entry.message),
    ["first", "second", "manual"]
  );
  assert.deepEqual(log.ordered[0].location, { from: 5, position: 10 });
  assert.equal(log.count, 3);
});

test("entries at the same position keep insertion order", () => {
  const log = new OutputLog();
  log.append(
    [info("first"), info("second")],
    { from: 5, position: 10 }
  );
  log.append([info("third")], { from: 9, position: 10 });

  assert.deepEqual(
    log.ordered.map((record) => record.entry.message),
    ["first", "second", "third"]
  );
});

test("pruning drops positioned entries after the tip", () => {
  const log = new OutputLog();
  log.append([info("early")], { from: 5, position: 10 });
  log.append([info("late")], { from: 8, position: 20 });
  log.append([info("manual")]);

  assert.equal(log.prune(10), 1);
  assert.deepEqual(
    log.ordered.map((record) => record.entry.message),
    ["early", "manual"]
  );
});

test("pruning clears the error flag when no errors remain", () => {
  const log = new OutputLog();
  log.append([info("ok")], { from: 5, position: 10 });
  log.append([error("bad")], { from: 15, position: 20 });
  assert.equal(log.hasError, true);

  log.prune(10);
  assert.equal(log.hasError, false);
});

test("reappending a command replaces its earlier output", () => {
  const log = new OutputLog();
  log.append([error("first failure")], { from: 5, position: 5 });
  log.append([error("second failure")], { from: 5, position: 5 });

  assert.deepEqual(
    log.ordered.map((record) => record.entry.message),
    ["second failure"]
  );

  log.append([], { from: 5, position: 5 });
  assert.equal(log.count, 0);
});

test("clear removes every entry", () => {
  const log = new OutputLog();
  log.append([info("manual")]);
  log.append([info("positioned")], { from: 5, position: 10 });
  log.clear();

  assert.equal(log.count, 0);
  assert.deepEqual(log.ordered, []);
});
