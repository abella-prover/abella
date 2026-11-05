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
import { highlightActiveLine, highlightActiveLineGutter } from "@codemirror/view";
import { searchKeymap } from "@codemirror/search";
import {
  EditorState,
  RangeSet,
  StateEffect,
  StateField,
  type Extension,
  type Range,
  type Text,
} from "@codemirror/state";
import {
  Decoration,
  EditorView,
  GutterMarker,
  drawSelection,
  gutter,
  hoverTooltip,
  keymap,
  lineNumbers,
  type DecorationSet,
} from "@codemirror/view";
import {
  abellaHighlightStyle,
  abellaLanguage,
  lprologLanguage,
} from "./abella-lang";
import type { CommandOutput } from "./command-output";

const setProcessedTipEffect = StateEffect.define<number>();
const markdownConfiguredEffect = StateEffect.define<null>();
const setRunLockedEffect = StateEffect.define<boolean>();

const runLockedField = StateField.define<boolean>({
  create: () => false,
  update(locked, transaction) {
    for (const effect of transaction.effects) {
      if (effect.is(setRunLockedEffect)) return effect.value;
    }
    return locked;
  },
});

const runLockedExtensions: Extension[] = [
  runLockedField,
  EditorState.readOnly.compute([runLockedField], (state) =>
    state.field(runLockedField)
  ),
];

const processedMark = Decoration.mark({ class: "cm-processed" });
const processedLine = Decoration.line({ class: "cm-processed-line" });
const processedPartialLine = Decoration.line({
  class: "cm-processed-partial-line",
});

export function processedDecorations(
  doc: Text,
  tip: number
): DecorationSet {
  const clamped = Math.max(0, Math.min(tip, doc.length));
  if (clamped === 0) return Decoration.none;
  const endLine = doc.lineAt(clamped);
  const decorations: Range<Decoration>[] = [];
  for (let number = 1; number < endLine.number; number++) {
    decorations.push(processedLine.range(doc.line(number).from));
  }
  if (endLine.from < clamped) {
    decorations.push(processedPartialLine.range(endLine.from));
    decorations.push(processedMark.range(endLine.from, clamped));
  }
  return Decoration.set(decorations);
}

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
        next = processedDecorations(transaction.newDoc, effect.value);
      }
    }
    return next;
  },
  provide: (field) => EditorView.decorations.from(field),
});

const setCommandOutputsEffect =
  StateEffect.define<readonly CommandOutput[]>();

const commandOutputField = StateField.define<readonly CommandOutput[]>({
  create: () => [],
  update(outputs, transaction) {
    let next: readonly CommandOutput[] = outputs.map((output) => ({
      from: transaction.changes.mapPos(output.from, 1),
      to: transaction.changes.mapPos(output.to, -1),
      position: transaction.changes.mapPos(output.position, -1),
      entries: output.entries,
    }));
    for (const effect of transaction.effects) {
      if (effect.is(setCommandOutputsEffect)) next = effect.value;
    }
    return next;
  },
});

function commandOutputGroups(
  doc: Text,
  outputs: readonly CommandOutput[]
): Map<number, CommandOutput[]> {
  const groups = new Map<number, CommandOutput[]>();
  for (const output of outputs) {
    if (output.entries.length === 0) continue;
    const position = Math.min(output.to, doc.length);
    const line = doc.lineAt(position).number;
    const group = groups.get(line);
    if (group) group.push(output);
    else groups.set(line, [output]);
  }
  return groups;
}

export function commandOutputLines(
  doc: Text,
  outputs: readonly CommandOutput[]
): number[] {
  return [...commandOutputGroups(doc, outputs).keys()].sort((a, b) => a - b);
}

class CommandOutputGutterMarker extends GutterMarker {
  private line: number;
  private outputs: readonly CommandOutput[];

  constructor(line: number, outputs: readonly CommandOutput[]) {
    super();
    this.line = line;
    this.outputs = outputs;
  }

  eq(other: CommandOutputGutterMarker): boolean {
    if (this.line !== other.line) return false;
    if (this.outputs.length !== other.outputs.length) return false;
    return this.outputs.every((output, index) => {
      const peer = other.outputs[index];
      return (
        output.from === peer.from &&
        output.to === peer.to &&
        output.entries === peer.entries
      );
    });
  }

  toDOM(): HTMLElement {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "cm-command-output-gutter-marker";
    button.dataset.line = String(this.line);
    const messages = this.outputs.reduce(
      (count, output) => count + output.entries.length,
      0
    );
    const hasError = this.outputs.some((output) =>
      output.entries.some((entry) => entry.severity === "error")
    );
    button.dataset.severity = hasError ? "error" : "info";
    button.textContent = hasError ? "!" : "i";
    if (messages > 1) {
      const count = document.createElement("span");
      count.className = "cm-command-output-gutter-count";
      count.textContent = String(messages);
      button.append(count);
    }
    const label = `Show ${messages} message` +
      `${messages === 1 ? "" : "s"} from line ${this.line}`;
    button.setAttribute("aria-label", label);
    return button;
  }
}

function commandOutputGutterMarkers(
  state: EditorState
): RangeSet<GutterMarker> {
  const ranges: Range<GutterMarker>[] = [];
  for (const [line, outputs] of commandOutputGroups(
    state.doc,
    state.field(commandOutputField)
  )) {
    ranges.push(
      new CommandOutputGutterMarker(line, outputs).range(
        state.doc.line(line).from
      )
    );
  }
  return RangeSet.of(ranges);
}

const commandOutputGutter = gutter({
  class: "cm-command-output-gutter",
  markers: (view) => commandOutputGutterMarkers(view.state),
});

const setErrorRangeEffect =
  StateEffect.define<{ from: number; to: number } | null>();

const errorRangeMark = Decoration.mark({ class: "cm-error-range" });

const errorRangeField = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(decorations, transaction) {
    let next = decorations.map(transaction.changes);
    for (const effect of transaction.effects) {
      if (!effect.is(setErrorRangeEffect)) continue;
      next = effect.value
        ? Decoration.set([
            errorRangeMark.range(effect.value.from, effect.value.to),
          ])
        : Decoration.none;
    }
    return next;
  },
  provide: (field) => EditorView.decorations.from(field),
});

function commandOutputAt(
  outputs: readonly CommandOutput[],
  position: number
): CommandOutput | undefined {
  return outputs.find(
    (output) => position >= output.from && position <= output.to + 1
  );
}

function commandOutputTooltip() {
  return hoverTooltip((view, position) => {
    const output = commandOutputAt(
      view.state.field(commandOutputField),
      position
    );
    if (!output || output.entries.length === 0) return null;
    return {
      pos: output.from,
      end: Math.min(output.to + 1, view.state.doc.length),
      above: true,
      create() {
        const dom = document.createElement("div");
        dom.className = "cm-command-output-tooltip";
        for (const entry of output.entries) {
          const line = document.createElement("div");
          line.className = "output-entry";
          line.dataset.severity = entry.severity;
          line.textContent = entry.message;
          dom.append(line);
        }
        return { dom };
      },
    };
  });
}

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
  ".cm-processed": {
    backgroundColor: "var(--processed)",
    // CodeMirror lines have 6px of left padding; extend the partial
    // highlight over it without moving the text.
    padding: "2px 0 2px 6px",
    marginLeft: "-6px",
  },
  ".cm-processed-line": { backgroundColor: "var(--processed)" },
  ".cm-activeLine.cm-processed-line": {
    backgroundColor: "var(--processed)",
  },
  ".cm-activeLine.cm-processed-partial-line": {
    backgroundColor: "transparent",
  },
  ".cm-error-range": {
    textDecoration: "underline wavy var(--red)",
    textUnderlineOffset: "2px",
  },
  ".cm-command-output-gutter": {
    width: "1.2rem",
  },
  ".cm-command-output-gutter-marker": {
    display: "inline-flex",
    alignItems: "center",
    justifyContent: "center",
    gap: "0.05rem",
    width: "1.05rem",
    height: "1rem",
    margin: "1px auto",
    padding: "0",
    border: "1px solid var(--border)",
    borderRadius: "999px",
    background: "var(--surface-2)",
    color: "var(--muted)",
    fontFamily: "var(--sans)",
    fontSize: "0.58rem",
    fontWeight: "700",
    lineHeight: "1",
    cursor: "pointer",
  },
  ".cm-command-output-gutter-marker[data-severity='error']": {
    borderColor: "var(--red)",
    color: "var(--red)",
  },
  ".cm-command-output-gutter-marker:focus-visible": {
    outline: "2px solid var(--rose)",
    outlineOffset: "1px",
  },
  ".cm-command-output-gutter-count": {
    fontSize: "0.52rem",
  },
  ".cm-command-output-tooltip": {
    maxWidth: "min(34rem, 80vw)",
    maxHeight: "18rem",
    overflow: "auto",
    padding: "0.45rem 0.6rem",
    fontFamily: "var(--mono)",
    fontSize: "0.76rem",
    lineHeight: "1.4",
  },
  ".cm-selectionBackground, &.cm-focused .cm-selectionBackground": {
    backgroundColor: "var(--selection) !important",
  },
});

export interface EditorActions {
  process(): void;
  stepForward(): void;
  stepBackward(): void;
  showOutput(): void;
  help(): void;
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
      key: "Ctrl-Space",
      run: () => {
        actions.showOutput();
        return true;
      },
    },
    {
      key: "Ctrl-Alt-o",
      run: () => {
        actions.showOutput();
        return true;
      },
    },
    {
      key: "Ctrl-?",
      run: () => {
        actions.help();
        return true;
      },
    },
  ];
  const language = languageFor(path);
  return [
    lineNumbers(),
    highlightActiveLineGutter(),
    commandOutputGutter,
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
    commandOutputField,
    errorRangeField,
    commandOutputTooltip(),
    markdownConfiguredField,
    ...runLockedExtensions,
    ...(language ? [language] : []),
    listener,
  ];
}

export function languageFor(path: string): Extension | null {
  if (path.endsWith(".thm") || path.endsWith(".thmod")) return abellaLanguage;
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
  private errors = new Map<string, { from: number; to: number }>();
  private commandOutputs = new Map<string, readonly CommandOutput[]>();
  private markdownPending = new Set<string>();
  private activePath: string | null = null;
  private runLocked = false;
  private onChange: (
    path: string,
    update: import("@codemirror/view").ViewUpdate
  ) => void;
  private onProcess: EditorActions;
  private onShowLineOutput: (path: string, line: number) => void;

  constructor(
    parent: HTMLElement,
    onChange: (
      path: string,
      update: import("@codemirror/view").ViewUpdate
    ) => void,
    actions: EditorActions,
    onShowLineOutput: (path: string, line: number) => void
  ) {
    this.parent = parent;
    this.onChange = onChange;
    this.onProcess = actions;
    this.onShowLineOutput = onShowLineOutput;
    this.view = new EditorView({ parent });
    this.view.dom.addEventListener("click", (event) => {
      const target = (event.target as HTMLElement).closest<HTMLElement>(
        ".cm-command-output-gutter-marker"
      );
      if (!target || !this.activePath) return;
      const line = Number(target.dataset.line);
      if (!Number.isFinite(line)) return;
      event.preventDefault();
      this.onShowLineOutput(this.activePath, line);
    });
  }

  private createState(path: string, doc: string): EditorState {
    const state = EditorState.create({
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
    return this.applyRunLock(state);
  }

  private applyRunLock(state: EditorState): EditorState {
    const current = state.field(runLockedField, false);
    if (current === undefined || current === this.runLocked) return state;
    return state.update({
      effects: setRunLockedEffect.of(this.runLocked),
    }).state;
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
    state = this.applyRunLock(state);
    this.states.set(path, state);
    this.activePath = path;
    this.view.setState(state);
    this.applyTip(path);
    this.applyError(path);
    this.applyCommandOutputs(path);
    this.ensureMarkdown(path);
    this.view.requestMeasure();
  }

  remove(path: string): void {
    this.states.delete(path);
    this.tips.delete(path);
    this.errors.delete(path);
    this.commandOutputs.delete(path);
    this.markdownPending.delete(path);
  }

  /** Drop the editor state for `path`, leaving other tabs untouched. */
  close(path: string): void {
    this.remove(path);
    if (this.activePath === path) this.activePath = null;
  }

  /** Show the empty state without discarding any editor state. */
  clearActive(): void {
    this.activePath = null;
    this.view.setState(EditorState.create({ doc: "", extensions: [] }));
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
    const error = this.errors.get(from);
    if (error) {
      this.errors.delete(from);
      this.errors.set(to, error);
    }
    const outputs = this.commandOutputs.get(from);
    if (outputs) {
      this.commandOutputs.delete(from);
      this.commandOutputs.set(to, outputs);
    }
    this.markdownPending.delete(from);
    if (this.activePath === from) this.activePath = to;
    this.ensureMarkdown(to);
  }

  reset(): void {
    this.states.clear();
    this.tips.clear();
    this.errors.clear();
    this.commandOutputs.clear();
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

  replaceText(path: string, text: string): void {
    if (this.runLocked) return;
    const state = this.states.get(path);
    if (!state || state.doc.toString() === text) return;
    this.commandOutputs.delete(path);
    this.errors.delete(path);
    const next = state.update({
      changes: { from: 0, to: state.doc.length, insert: text },
      effects: [
        setCommandOutputsEffect.of([]),
        setErrorRangeEffect.of(null),
      ],
    }).state;
    this.states.set(path, next);
    if (this.activePath === path) {
      this.view.setState(next);
      this.view.requestMeasure();
    }
  }

  setRunLocked(locked: boolean): void {
    if (this.runLocked === locked) return;
    this.runLocked = locked;
    for (const [path, state] of this.states) {
      if (path === this.activePath) continue;
      this.states.set(
        path,
        state.update({
          effects: setRunLockedEffect.of(locked),
        }).state
      );
    }
    if (this.activePath) {
      this.view.dispatch({
        effects: setRunLockedEffect.of(locked),
      });
      this.states.set(this.activePath, this.view.state);
      this.view.requestMeasure();
    }
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

  setError(path: string, from: number, to: number): void {
    this.errors.set(path, { from, to });
    if (this.activePath === path) this.applyError(path);
  }

  private applyError(path: string): void {
    const error = this.errors.get(path);
    this.view.dispatch({
      effects: setErrorRangeEffect.of(
        error && error.from < error.to ? error : null
      ),
    });
  }

  clearError(path: string): void {
    if (!this.errors.delete(path)) return;
    if (this.activePath === path) this.applyError(path);
  }

  setCommandOutputs(
    path: string,
    outputs: readonly CommandOutput[]
  ): void {
    this.commandOutputs.set(path, outputs);
    if (this.activePath === path) this.applyCommandOutputs(path);
  }

  clearCommandOutputs(path: string): void {
    if (!this.commandOutputs.delete(path)) return;
    if (this.activePath === path) this.applyCommandOutputs(path);
  }

  private applyCommandOutputs(path: string): void {
    this.view.dispatch({
      effects: setCommandOutputsEffect.of(
        this.commandOutputs.get(path) ?? []
      ),
    });
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
