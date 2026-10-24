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
  log.append([info("second")], 20);
  log.append([info("first")], 10);

  assert.deepEqual(
    log.ordered.map((record) => record.entry.message),
    ["first", "second", "manual"]
  );
  assert.equal(log.count, 3);
});

test("entries at the same position keep insertion order", () => {
  const log = new OutputLog();
  log.append([info("first"), info("second")], 10);
  log.append([info("third")], 10);

  assert.deepEqual(
    log.ordered.map((record) => record.entry.message),
    ["first", "second", "third"]
  );
});

test("pruning drops positioned entries after the tip", () => {
  const log = new OutputLog();
  log.append([info("early")], 10);
  log.append([info("late")], 20);
  log.append([info("manual")]);

  assert.equal(log.prune(10), 1);
  assert.deepEqual(
    log.ordered.map((record) => record.entry.message),
    ["early", "manual"]
  );
});

test("pruning clears the error flag when no errors remain", () => {
  const log = new OutputLog();
  log.append([info("ok")], 10);
  log.append([error("bad")], 20);
  assert.equal(log.hasError, true);

  log.prune(10);
  assert.equal(log.hasError, false);
});

test("clear removes every entry", () => {
  const log = new OutputLog();
  log.append([info("manual")]);
  log.append([info("positioned")], 10);
  log.clear();

  assert.equal(log.count, 0);
  assert.deepEqual(log.ordered, []);
});
