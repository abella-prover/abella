// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import {
  HighlightStyle,
  LanguageSupport,
  StreamLanguage,
  type StreamParser,
} from "@codemirror/language";
import { tags as t } from "@lezer/highlight";

const topLevelKeywords = [
  "Close",
  "CoDefine",
  "Define",
  "Import",
  "Kind",
  "Query",
  "Quit",
  "Set",
  "Show",
  "Specification",
  "Split",
  "Suspend",
  "Theorem",
  "Type",
];

const tacticKeywords = [
  "abbrev",
  "abort",
  "accum_sig",
  "accumulate",
  "all",
  "apply",
  "as",
  "assert",
  "backchain",
  "by",
  "case",
  "clear",
  "coinduction",
  "compute",
  "cut",
  "end",
  "exists",
  "false",
  "forall",
  "from",
  "induction",
  "inst",
  "intros",
  "keep",
  "kind",
  "left",
  "module",
  "monotone",
  "nabla",
  "on",
  "permute",
  "rename",
  "right",
  "search",
  "sig",
  "skip",
  "split",
  "split*",
  "to",
  "true",
  "type",
  "unabbrev",
  "undo",
  "unfold",
  "with",
  "witness",
];

const lprologKeywords = [
  "accum_sig",
  "accumulate",
  "exportdef",
  "import",
  "infix",
  "infixl",
  "infixr",
  "kind",
  "local",
  "localkind",
  "module",
  "postfix",
  "prefix",
  "sig",
  "type",
  "typeabbrev",
  "use_sig",
  "useonly",
];

interface TokenState {
  commentDepth: number;
}

const identifierStart = /[A-Za-z_$?='`-]/;
const identifierPart = /[A-Za-z0-9_\/@+!#~*'`?=$-]/;

function makeParser(keywords: readonly string[]): StreamParser<TokenState> {
  const keywordSet = new Set(keywords);
  return {
    startState: () => ({ commentDepth: 0 }),
    token(stream, state) {
      if (state.commentDepth > 0) {
        while (!stream.eol()) {
          if (stream.match("/*")) {
            state.commentDepth++;
          } else if (stream.match("*/")) {
            state.commentDepth--;
            if (state.commentDepth === 0) return "comment";
          } else {
            stream.next();
          }
        }
        return "comment";
      }

      if (stream.eatSpace()) return null;

      if (stream.match("/*")) {
        state.commentDepth = 1;
        return "comment";
      }

      if (stream.peek() === "%") {
        if (stream.match(/^%:[A-Za-z][A-Za-z0-9_']*:/)) {
          stream.skipToEnd();
          return "meta";
        }
        stream.skipToEnd();
        return "comment";
      }

      if (stream.peek() === '"') {
        stream.next();
        while (!stream.eol()) {
          if (stream.next() === '"') break;
        }
        return "string";
      }

      if (stream.match(/^[0-9]+/)) return "number";

      const next = stream.peek() ?? "";
      if (next && identifierStart.test(next)) {
        let word = "";
        while (!stream.eol()) {
          const c = stream.peek() ?? "";
          if (!identifierPart.test(c)) break;
          word += stream.next();
        }
        if (keywordSet.has(word)) return "keyword";
        if (/^[A-Z]/.test(word)) return "typeName";
        return "variableName";
      }

      if (stream.match(/^(=>|<=|:-|:=|\|-|->|\\\/|\/\\|::)/)) {
        return "operator";
      }
      if (stream.match(/^[\\&*@#+]+/)) return "operator";
      if (stream.match(/^[.,;:()[\]]/)) return "punctuation";

      stream.next();
      return null;
    },
  };
}

export const abellaLanguage = new LanguageSupport(
  StreamLanguage.define(makeParser([...topLevelKeywords, ...tacticKeywords]))
);

export const lprologLanguage = new LanguageSupport(
  StreamLanguage.define(makeParser([...lprologKeywords, "true", "false"]))
);

export const abellaHighlightStyle = HighlightStyle.define([
  { tag: t.comment, color: "var(--cm-comment)" },
  { tag: t.keyword, color: "var(--cm-keyword)", fontWeight: "600" },
  { tag: t.typeName, color: "var(--cm-type)" },
  { tag: t.variableName, color: "var(--cm-variable)" },
  { tag: t.string, color: "var(--cm-string)" },
  { tag: t.number, color: "var(--cm-number)" },
  { tag: t.operator, color: "var(--cm-operator)" },
  { tag: t.punctuation, color: "var(--cm-punctuation)" },
  { tag: t.meta, color: "var(--cm-meta)", fontStyle: "italic" },
]);
