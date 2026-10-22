// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { scanCommands, ScanError, sourcePos, utf8Offset } from "./commands";

test("scans simple commands", () => {
  const doc = "Kind tm type.\nType app tm -> tm -> tm.\n";
  const commands = scanCommands(doc);
  assert.deepEqual(commands.map((c) => c.text), [
    "Kind tm type.",
    "Type app tm -> tm -> tm.",
  ]);
  assert.equal(commands[0].from, 0);
  assert.equal(commands[1].from, 14);
  assert.equal(commands[1].endLine, 2);
});

test("ignores dots in line and nested block comments", () => {
  const doc = [
    "% a dot . here",
    "/* outer . /* inner . */ still . */",
    "Theorem t : forall A, A = A.",
  ].join("\n");
  const commands = scanCommands(doc);
  assert.equal(commands.length, 1);
  assert.match(commands[0].text, /^Theorem t/);
});

test("clause-name markers are skipped to end of line", () => {
  const doc = [
    "Define p : prop by",
    "%:name-for-p: rule . ignored",
    "  p.",
  ].join("\n");
  const commands = scanCommands(doc);
  assert.equal(commands.length, 1);
  assert.match(commands[0].text, /^Define p/);
  assert.match(commands[0].text, /p\.$/);
});

test("strings may contain dots and percent signs", () => {
  const doc = 'Theorem t : forall A, A = A. % trailing . comment\n';
  assert.equal(scanCommands(doc).length, 1);
  const doc2 = 'Import "a.b".\n';
  assert.equal(scanCommands(doc2).length, 1);
  assert.equal(scanCommands(doc2)[0].text, 'Import "a.b".');
});

test("starts at an offset and handles multi-line commands", () => {
  const doc = "Kind a type.\nTheorem t :\n  forall A,\n  A = A.\n";
  const commands = scanCommands(doc, doc.indexOf("Theorem"));
  assert.equal(commands.length, 1);
  assert.equal(commands[0].endLine, 4);
  assert.equal(scanCommands(doc, doc.length).length, 0);
});

test("rejects unclosed comments, strings, and missing dots", () => {
  assert.throws(() => scanCommands("/* nope"), ScanError);
  assert.throws(() => scanCommands('Theorem "nope'), ScanError);
  assert.throws(() => scanCommands("Kind tm type"), ScanError);
});

test("converts UTF-16 offsets to UTF-8 bytes", () => {
  const doc = 'Theorem "λ".';
  assert.equal(utf8Offset(doc, doc.length), Buffer.byteLength(doc, "utf8"));
  const pos = sourcePos(doc, doc.indexOf("λ"));
  assert.equal(pos.offset, 9);
  assert.equal(pos.bol, 0);
});

test("source positions are one-based and line-local", () => {
  const doc = "Kind tm type.\nType app tm -> tm -> tm.\n";
  const pos = sourcePos(doc, doc.indexOf("Type"));
  assert.deepEqual(pos, { offset: 14, line: 2, bol: 14 });
});
