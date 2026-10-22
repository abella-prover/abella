// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Scanner for Abella commands.  Offsets are JavaScript/CodeMirror offsets
// (UTF-16 code units), not Abella's UTF-8 byte offsets.

export interface Command {
  text: string;
  from: number;
  to: number;
  endLine: number;
}

export class ScanError extends Error {
  constructor(message: string) {
    super(message);
    this.name = "ScanError";
  }
}

const isSpace = (c: string) => c === " " || c === "\t" || c === "\r" || c === "\n";

/**
 * Return complete commands from `fromOffset` to the end of the document.
 * Throws ScanError for an unclosed comment/string or a final command that
 * is missing its terminating dot.
 */
export function scanCommands(doc: string, fromOffset = 0): Command[] {
  const commands: Command[] = [];
  const length = doc.length;
  let i = Math.max(0, Math.min(fromOffset, length));

  while (i < length) {
    // Skip whitespace and comments between commands. Comments inside a
    // command are kept in its text (Abella ignores them).
    let advanced = true;
    while (advanced && i < length) {
      advanced = false;
      while (i < length && isSpace(doc[i])) {
        i++;
        advanced = true;
      }
      if (doc[i] === "/" && doc[i + 1] === "*") {
        let depth = 1;
        i += 2;
        while (i < length && depth > 0) {
          if (doc[i] === "/" && doc[i + 1] === "*") {
            depth++;
            i += 2;
          } else if (doc[i] === "*" && doc[i + 1] === "/") {
            depth--;
            i += 2;
          } else {
            i++;
          }
        }
        if (depth > 0) {
          throw new ScanError(
            `Unclosed comment before line ${lineOf(doc, i)}.`
          );
        }
        advanced = true;
      } else if (doc[i] === "%") {
        while (i < length && doc[i] !== "\n") i++;
        advanced = true;
      }
    }
    if (i >= length) break;

    const from = i;
    let commentDepth = 0;
    let inString = false;
    let terminated = false;

    while (i < length) {
      const c = doc[i];

      if (inString) {
        if (c === '"') inString = false;
        i++;
        continue;
      }

      if (commentDepth > 0) {
        if (c === "/" && doc[i + 1] === "*") {
          commentDepth++;
          i += 2;
        } else if (c === "*" && doc[i + 1] === "/") {
          commentDepth--;
          i += 2;
        } else {
          i++;
        }
        continue;
      }

      if (c === '"') {
        inString = true;
        i++;
        continue;
      }

      if (c === "/" && doc[i + 1] === "*") {
        commentDepth = 1;
        i += 2;
        continue;
      }

      if (c === "%") {
        while (i < length && doc[i] !== "\n") i++;
        continue;
      }

      if (c === ".") {
        i++;
        const text = doc.slice(from, i).trim();
        commands.push({
          text,
          from,
          to: i,
          endLine: lineOf(doc, i),
        });
        terminated = true;
        break;
      }

      i++;
    }

    if (inString) {
      throw new ScanError(
        `Unclosed string in the command starting on line ${lineOf(doc, from)}.`
      );
    }
    if (commentDepth > 0) {
      throw new ScanError(
        `Unclosed comment in the command starting on line ${lineOf(doc, from)}.`
      );
    }
    if (!terminated) {
      throw new ScanError(
        `The command starting on line ${lineOf(doc, from)} is missing its terminating dot.`
      );
    }
  }

  return commands;
}

export function lineOf(doc: string, offset: number): number {
  let line = 1;
  for (let i = 0; i < offset && i < doc.length; i++) {
    if (doc[i] === "\n") line++;
  }
  return line;
}

/** The UTF-8 byte offset of a JavaScript string offset. */
export function utf8Offset(doc: string, jsOffset: number): number {
  let bytes = 0;
  const end = Math.max(0, Math.min(jsOffset, doc.length));
  for (let i = 0; i < end; i++) {
    const code = doc.charCodeAt(i);
    if (code < 0x80) {
      bytes += 1;
    } else if (code < 0x800) {
      bytes += 2;
    } else if (code >= 0xd800 && code <= 0xdbff) {
      const next = doc.charCodeAt(i + 1);
      if (next >= 0xdc00 && next <= 0xdfff) {
        bytes += 4;
        i++;
      } else {
        bytes += 3;
      }
    } else {
      bytes += 3;
    }
  }
  return bytes;
}

/** Line number (1-based) and byte offset of the start of that line. */
export function sourcePos(doc: string, jsOffset: number) {
  const offset = Math.max(0, Math.min(jsOffset, doc.length));
  const lineStart = doc.lastIndexOf("\n", offset - 1) + 1;
  return {
    offset: utf8Offset(doc, offset),
    line: lineOf(doc, offset),
    bol: utf8Offset(doc, lineStart),
  };
}
