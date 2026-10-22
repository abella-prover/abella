// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { closeBrackets } from "@codemirror/autocomplete";
import {
  defaultKeymap,
  history,
  historyKeymap,
  indentWithTab,
} from "@codemirror/commands";
import { markdown } from "@codemirror/lang-markdown";
import {
  bracketMatching,
  indentOnInput,
  syntaxHighlighting,
} from "@codemirror/language";
import {
  setDiagnostics,
  lintGutter,
  type Diagnostic,
} from "@codemirror/lint";
import { highlightActiveLine, highlightActiveLineGutter } from "@codemirror/view";
import { searchKeymap } from "@codemirror/search";
import {
  EditorState,
  StateEffect,
  StateField,
  type Extension,
} from "@codemirror/state";
import {
  Decoration,
  EditorView,
  drawSelection,
  keymap,
  lineNumbers,
  type DecorationSet,
} from "@codemirror/view";
import {
  abellaHighlightStyle,
  abellaLanguage,
  lprologLanguage,
} from "./abella-lang";

const setProcessedTipEffect = StateEffect.define<number>();

const processedMark = Decoration.mark({ class: "cm-processed" });

const processedField = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(decorations, transaction) {
    let next = decorations.map(transaction.changes);
    for (const effect of transaction.effects) {
      if (effect.is(setProcessedTipEffect)) {
        const tip = Math.max(0, Math.min(effect.value, transaction.newDoc.length));
        next =
          tip > 0
            ? Decoration.set([processedMark.range(0, tip)])
            : Decoration.none;
      }
    }
    return next;
  },
  provide: (field) => EditorView.decorations.from(field),
});

const editorTheme = EditorView.theme({
  "&": {
    height: "100%",
    color: "var(--ink)",
    backgroundColor: "var(--surface)",
    fontSize: "14px",
  },
  ".cm-scroller": {
    fontFamily: "var(--mono)",
    lineHeight: "1.5",
  },
  ".cm-content": { padding: "10px 0" },
  ".cm-gutters": {
    backgroundColor: "var(--surface-2)",
    color: "var(--muted)",
    border: "none",
  },
  ".cm-activeLine": { backgroundColor: "var(--active-line)" },
  ".cm-activeLineGutter": { backgroundColor: "var(--active-line)" },
  ".cm-processed": { backgroundColor: "var(--processed)" },
  ".cm-selectionBackground, &.cm-focused .cm-selectionBackground": {
    backgroundColor: "var(--selection) !important",
  },
});

function baseExtensions(
  path: string,
  onChange: (path: string, update: import("@codemirror/view").ViewUpdate) => void,
  onProcess: (blocking: boolean) => void
): Extension[] {
  const listener = EditorView.updateListener.of((update) => {
    if (update.docChanged) onChange(path, update);
  });
  const processKeys = [
    {
      key: "Mod-Enter",
      run: () => {
        onProcess(false);
        return true;
      },
    },
    {
      key: "Mod-Shift-Enter",
      run: () => {
        onProcess(true);
        return true;
      },
    },
  ];
  const language = languageFor(path);
  return [
    lineNumbers(),
    highlightActiveLineGutter(),
    history(),
    drawSelection(),
    highlightActiveLine(),
    bracketMatching(),
    closeBrackets(),
    indentOnInput(),
    EditorView.lineWrapping,
    EditorState.tabSize.of(2),
    syntaxHighlighting(abellaHighlightStyle),
    keymap.of([
      ...processKeys,
      ...defaultKeymap,
      ...historyKeymap,
      ...searchKeymap,
      indentWithTab,
    ]),
    editorTheme,
    processedField,
    lintGutter(),
    ...(language ? [language] : []),
    listener,
  ];
}

export function languageFor(path: string): Extension | null {
  if (path.endsWith(".thm")) return abellaLanguage;
  if (path.endsWith(".sig") || path.endsWith(".mod")) return lprologLanguage;
  if (path.endsWith(".md") || path.endsWith(".markdown")) return markdown();
  return null;
}

export class EditorManager {
  private parent: HTMLElement;
  private view: EditorView;
  private states = new Map<string, EditorState>();
  private tips = new Map<string, number>();
  private diagnostics = new Map<string, readonly Diagnostic[]>();
  private activePath: string | null = null;
  private onChange: (
    path: string,
    update: import("@codemirror/view").ViewUpdate
  ) => void;
  private onProcess: (blocking: boolean) => void;

  constructor(
    parent: HTMLElement,
    onChange: (
      path: string,
      update: import("@codemirror/view").ViewUpdate
    ) => void,
    onProcess: (blocking: boolean) => void
  ) {
    this.parent = parent;
    this.onChange = onChange;
    this.onProcess = onProcess;
    this.view = new EditorView({ parent });
  }

  private createState(path: string, doc: string): EditorState {
    return EditorState.create({
      doc,
      extensions: baseExtensions(
        path,
        (changedPath, update) => {
          this.states.set(changedPath, update.state);
          this.onChange(changedPath, update);
        },
        this.onProcess
      ),
    });
  }

  open(path: string, doc: string): void {
    if (this.activePath) {
      this.states.set(this.activePath, this.view.state);
    }
    let state = this.states.get(path);
    if (!state) {
      state = this.createState(path, doc);
      this.states.set(path, state);
    }
    this.activePath = path;
    this.view.setState(state);
    this.applyTip(path);
    this.applyDiagnostics(path);
    this.view.requestMeasure();
  }

  remove(path: string): void {
    this.states.delete(path);
    this.tips.delete(path);
    this.diagnostics.delete(path);
  }

  rename(from: string, to: string): void {
    const state = this.states.get(from);
    if (state) {
      this.states.delete(from);
      this.states.set(to, state);
    }
    const tip = this.tips.get(from);
    if (tip !== undefined) {
      this.tips.delete(from);
      this.tips.set(to, tip);
    }
    const diagnostics = this.diagnostics.get(from);
    if (diagnostics) {
      this.diagnostics.delete(from);
      this.diagnostics.set(to, diagnostics);
    }
    if (this.activePath === from) this.activePath = to;
  }

  reset(): void {
    this.states.clear();
    this.tips.clear();
    this.diagnostics.clear();
    this.activePath = null;
    this.view.setState(EditorState.create({ doc: "", extensions: [] }));
  }

  setProcessedTip(path: string, tip: number): void {
    this.tips.set(path, tip);
    if (this.activePath === path) this.applyTip(path);
  }

  private applyTip(path: string): void {
    const tip = this.tips.get(path);
    if (tip === undefined) return;
    this.view.dispatch({ effects: setProcessedTipEffect.of(tip) });
  }

  setDiagnostics(path: string, diagnostics: readonly Diagnostic[]): void {
    this.diagnostics.set(path, diagnostics);
    if (this.activePath === path) this.applyDiagnostics(path);
  }

  private applyDiagnostics(path: string): void {
    const diagnostics = this.diagnostics.get(path) ?? [];
    this.view.dispatch(setDiagnostics(this.view.state, diagnostics));
  }

  clearDiagnostics(path: string): void {
    this.setDiagnostics(path, []);
  }

  focus(): void {
    this.view.focus();
  }

  get text(): string {
    return this.view.state.doc.toString();
  }

  get active(): string | null {
    return this.activePath;
  }

  cursorFor(path: string): number {
    if (path === this.activePath) return this.view.state.selection.main.head;
    const state = this.states.get(path);
    return state ? state.selection.main.head : 0;
  }

  get cursor(): number {
    return this.view.state.selection.main.head;
  }
}
