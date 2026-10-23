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
const markdownConfiguredEffect = StateEffect.define<null>();

const processedMark = Decoration.mark({ class: "cm-processed" });

const markdownConfiguredField = StateField.define<boolean>({
  create: () => false,
  update(configured, transaction) {
    let next = configured;
    for (const effect of transaction.effects) {
      if (effect.is(markdownConfiguredEffect)) next = true;
    }
    return next;
  },
});

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
  ".cm-content": { padding: "10px 0", caretColor: "var(--ink)" },
  ".cm-cursor, .cm-dropCursor": {
    borderLeftColor: "var(--ink)",
  },
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

export interface EditorActions {
  process(): void;
  stepForward(): void;
  stepBackward(): void;
  jumpToTip(): void;
}

function baseExtensions(
  path: string,
  onChange: (path: string, update: import("@codemirror/view").ViewUpdate) => void,
  actions: EditorActions
): Extension[] {
  const listener = EditorView.updateListener.of((update) => {
    if (update.docChanged) onChange(path, update);
  });
  const processKeys = [
    {
      key: "Mod-Enter",
      run: () => {
        actions.process();
        return true;
      },
    },
    {
      key: "Ctrl-]",
      run: () => {
        actions.stepForward();
        return true;
      },
    },
    {
      key: "Ctrl-[",
      run: () => {
        actions.stepBackward();
        return true;
      },
    },
    {
      key: "Ctrl-.",
      run: () => {
        actions.jumpToTip();
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
    markdownConfiguredField,
    lintGutter(),
    ...(language ? [language] : []),
    listener,
  ];
}

export function languageFor(path: string): Extension | null {
  if (path.endsWith(".thm")) return abellaLanguage;
  if (path.endsWith(".sig") || path.endsWith(".mod")) return lprologLanguage;
  return null;
}

function isMarkdown(path: string): boolean {
  return path.endsWith(".md") || path.endsWith(".markdown");
}

let markdownExtension: Promise<Extension> | undefined;

function loadMarkdown(): Promise<Extension> {
  markdownExtension ??= import("@codemirror/lang-markdown").then(
    ({ markdown }) => markdown(),
    (error) => {
      markdownExtension = undefined;
      throw error;
    }
  );
  return markdownExtension;
}

export class EditorManager {
  private parent: HTMLElement;
  private view: EditorView;
  private states = new Map<string, EditorState>();
  private tips = new Map<string, number>();
  private diagnostics = new Map<string, readonly Diagnostic[]>();
  private markdownPending = new Set<string>();
  private activePath: string | null = null;
  private onChange: (
    path: string,
    update: import("@codemirror/view").ViewUpdate
  ) => void;
  private onProcess: EditorActions;

  constructor(
    parent: HTMLElement,
    onChange: (
      path: string,
      update: import("@codemirror/view").ViewUpdate
    ) => void,
    actions: EditorActions
  ) {
    this.parent = parent;
    this.onChange = onChange;
    this.onProcess = actions;
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
    this.ensureMarkdown(path);
    this.view.requestMeasure();
  }

  remove(path: string): void {
    this.states.delete(path);
    this.tips.delete(path);
    this.diagnostics.delete(path);
    this.markdownPending.delete(path);
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
    this.markdownPending.delete(from);
    if (this.activePath === from) this.activePath = to;
    this.ensureMarkdown(to);
  }

  reset(): void {
    this.states.clear();
    this.tips.clear();
    this.diagnostics.clear();
    this.markdownPending.clear();
    this.activePath = null;
    this.view.setState(EditorState.create({ doc: "", extensions: [] }));
  }

  private ensureMarkdown(path: string): void {
    if (!isMarkdown(path) || this.markdownPending.has(path)) return;
    const state = this.states.get(path);
    if (!state || state.field(markdownConfiguredField)) return;
    this.markdownPending.add(path);
    void loadMarkdown().then(
      (extension) => {
        this.markdownPending.delete(path);
        const current = this.states.get(path);
        if (!current || current.field(markdownConfiguredField)) return;
        const next = current.update({
          effects: [
            StateEffect.appendConfig.of(extension),
            markdownConfiguredEffect.of(null),
          ],
        }).state;
        this.states.set(path, next);
        if (this.activePath === path) {
          this.view.setState(next);
          this.view.requestMeasure();
        }
      },
      () => {
        this.markdownPending.delete(path);
      }
    );
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

  setCursor(path: string, offset: number, scroll = false): void {
    const state = this.states.get(path);
    if (!state) return;
    const position = Math.max(0, Math.min(offset, state.doc.length));
    if (this.activePath === path) {
      this.view.dispatch({
        selection: { anchor: position },
        effects: scroll
          ? EditorView.scrollIntoView(position, { y: "center" })
          : undefined,
      });
      this.view.focus();
    } else {
      this.states.set(
        path,
        state.update({ selection: { anchor: position } }).state
      );
    }
  }

  requestMeasure(): void {
    this.view.requestMeasure();
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
