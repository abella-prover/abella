// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { Text } from "@codemirror/state";
import {
  commandOutputLines,
  processedDecorations,
} from "./editor";
import type { CommandOutput } from "./command-output";

interface Decorated {
  from: number;
  to: number;
  cls: string | undefined;
}

function decorations(text: string, tip: number): Decorated[] {
  const set = processedDecorations(Text.of(text.split("\n")), tip);
  const found: Decorated[] = [];
  for (let iter = set.iter(); iter.value; iter.next()) {
    found.push({
      from: iter.from,
      to: iter.to,
      cls: iter.value.spec.class,
    });
  }
  return found;
}

test("a checked line ending at the tip is not filled across", () => {
  const doc = "Kind nat type.\nType z nat.\n";
  const line = doc.indexOf("Type");
  const tip = line + "Type z nat.".length;

  const found = decorations(doc, tip);
  assert.deepEqual(
    found.filter((item) => item.cls === "cm-processed-line"),
    [{ from: 0, to: 0, cls: "cm-processed-line" }]
  );
  assert.deepEqual(
    found.filter((item) => item.cls === "cm-processed-partial-line"),
    [{ from: line, to: line, cls: "cm-processed-partial-line" }]
  );
  assert.deepEqual(
    found.filter((item) => item.cls === "cm-processed"),
    [{ from: line, to: tip, cls: "cm-processed" }]
  );
});

test("trailing whitespace is left outside the checked region", () => {
  const doc = "Type z nat.   \n";
  const tip = "Type z nat.".length;

  const found = decorations(doc, tip);
  assert.deepEqual(
    found.filter((item) => item.cls === "cm-processed"),
    [{ from: 0, to: tip, cls: "cm-processed" }]
  );
});

test("command output markers group by command end line", () => {
  const doc = "Kind nat type.\nType z nat. Type y nat.\n";
  const first = doc.indexOf("Type");
  const second = doc.indexOf("Type y");
  const outputs: CommandOutput[] = [
    {
      from: 0,
      to: "Kind nat type.".length,
      position: "Kind nat type.".length,
      entries: [{ severity: "info", message: "warning" }],
    },
    {
      from: first,
      to: first + "Type z nat.".length,
      position: first + "Type z nat.".length,
      entries: [{ severity: "error", message: "failure" }],
    },
    {
      from: second,
      to: second + "Type y nat.".length,
      position: second + "Type y nat.".length,
      entries: [{ severity: "info", message: "note" }],
    },
  ];

  assert.deepEqual(
    commandOutputLines(Text.of(doc.split("\n")), outputs),
    [1, 2]
  );
});
