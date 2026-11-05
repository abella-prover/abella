// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { NotificationLog } from "./notifications";

test("tracks unread messages until marked read", () => {
  const log = new NotificationLog();
  log.add([{ severity: "info", message: "saved" }]);
  log.add([{ severity: "error", message: "failed" }]);

  assert.equal(log.count, 2);
  assert.equal(log.unread, 2);
  assert.equal(log.hasError, true);

  log.markRead();
  assert.equal(log.unread, 0);
  assert.equal(log.count, 2);
});

test("clearing removes messages and unread state", () => {
  const log = new NotificationLog();
  log.add([{ severity: "info", message: "saved" }]);
  log.clear();

  assert.equal(log.count, 0);
  assert.equal(log.unread, 0);
  assert.equal(log.hasError, false);
});
