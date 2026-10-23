// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { ChangeSet } from "@codemirror/state";
import type { Command } from "./commands";
import { ScanError, scanCommands, sourcePos } from "./commands";
import type { Driver } from "./driver";
import type { ProofState, RawMessage, RunResult } from "./types";
import {
  abellaFiles,
  classify,
  rootText,
  type Project,
} from "./project";

export type SessionStatus =
  | "idle"
  | "ready"
  | "processing"
  | "compiling"
  | "ok"
  | "error";

export type ProofStatus =
  | "completed"
  | "completed-skip"
  | "aborted"
  | "not-completed";

/** Abella's message is kept verbatim; the theorem label is separate. */
export interface ProofOutcome {
  theorem?: string;
  status: ProofStatus;
  message: string;
}

export interface OutputEntry {
  severity: "info" | "error";
  message: string;
}

export interface Step {
  from: number;
  to: number;
  tip: number;
  startsTheorem: boolean;
  theorem?: string;
  endState?: ProofState;
  outcome?: ProofOutcome;
}

export interface SessionEvents {
  onStatus(status: SessionStatus, detail?: string): void;
  onTip(tip: number): void;
  onGoal(state: ProofState | undefined): void;
  onOutcome(outcome: ProofOutcome | undefined): void;
  onOutput(entries: OutputEntry[], command?: Command): void;
  onResult(result: RunResult, command?: Command): void;
  onError(message: string, from: number, to: number): void;
  onCursor(offset: number): void;
}

function endState(messages: RawMessage[]): ProofState | undefined {
  let state: ProofState | undefined;
  for (const message of messages) {
    if (message.type === "proof_command" && message.end_state) {
      state = message.end_state;
    }
  }
  return state;
}

function theoremFrom(messages: RawMessage[]): string | undefined {
  let theorem: string | undefined;
  for (const message of messages) {
    if (message.type === "proof_command") theorem = message.theorem;
  }
  return theorem;
}

function proofOutcome(messages: RawMessage[]): ProofOutcome | undefined {
  let outcome: ProofOutcome | undefined;
  for (const message of messages) {
    if (message.type !== "system_message") continue;
    const text = message.message;
    if (text.startsWith("Proof completed *** USING skip ***")) {
      outcome = { status: "completed-skip", message: text };
    } else if (text.startsWith("Proof completed")) {
      outcome = { status: "completed", message: text };
    } else if (text.startsWith("Proof ABORTED")) {
      outcome = { status: "aborted", message: text };
    } else if (text.startsWith("Proof NOT Completed")) {
      outcome = { status: "not-completed", message: text };
    }
  }
  return outcome;
}

function isProofLifecycle(message: RawMessage): boolean {
  return (
    message.type === "system_message" &&
    (message.message.startsWith("Proof completed") ||
      message.message.startsWith("Proof ABORTED") ||
      message.message.startsWith("Proof NOT Completed"))
  );
}

function outputEntries(messages: RawMessage[]): OutputEntry[] {
  const entries: OutputEntry[] = [];
  for (const message of messages) {
    if (message.type !== "system_message") continue;
    if (isProofLifecycle(message)) continue;
    if (message.message.startsWith("Welcome to Abella")) continue;
    entries.push({
      severity: message.severity,
      message: message.message,
    });
  }
  return entries;
}

function errorText(messages: RawMessage[]): string {
  for (let i = messages.length - 1; i >= 0; i--) {
    const message = messages[i];
    if (message.type === "system_message" && message.severity === "error") {
      return message.message;
    }
  }
  return "Abella reported an error.";
}

function startsTheorem(command: Command): boolean {
  return /^Theorem\b/.test(command.text);
}

function firstChangedOffset(changes: ChangeSet): number | undefined {
  let first: number | undefined;
  changes.iterChangedRanges((fromA) => {
    if (first === undefined || fromA < first) first = fromA;
  });
  return first;
}

interface StepBounds {
  from: number;
  to: number;
  tip: number;
}

export class Session {
  private project: Project;
  private driver: Driver;
  private events: SessionEvents;
  private steps: Step[] = [];
  private tip = 0;
  private dirty = true;
  private initialized = false;
  private lastState?: ProofState;
  private lastOutcome?: ProofOutcome;
  private currentTheorem?: string;
  private generation = 0;
  private queue: Promise<unknown> = Promise.resolve();
  private pendingEdits: ChangeSet[] = [];
  private editTask?: Promise<void>;

  constructor(driver: Driver, project: Project, events: SessionEvents) {
    this.driver = driver;
    this.project = project;
    this.events = events;
    driver.onProgress = (module) =>
      this.events.onStatus("compiling", module);
  }

  get currentTip(): number {
    return this.tip;
  }

  get currentState(): ProofState | undefined {
    return this.lastState;
  }

  get outcome(): ProofOutcome | undefined {
    return this.lastOutcome;
  }

  get stepsCount(): number {
    return this.steps.length;
  }

  private exclusive<T>(task: () => Promise<T>): Promise<T> {
    const result = this.queue.then(task, task);
    this.queue = result.then(
      () => undefined,
      () => undefined
    );
    return result;
  }

  private emitView(): void {
    this.events.onGoal(this.lastState);
    this.events.onOutcome(this.lastOutcome);
  }

  /** Recompute goal and outcome from the surviving steps. */
  private recomputeView(): void {
    let boundary = -1;
    for (let i = this.steps.length - 1; i >= 0; i--) {
      if (this.steps[i].startsTheorem) {
        boundary = i;
        break;
      }
    }
    const start = boundary >= 0 ? boundary + 1 : 0;
    let state: ProofState | undefined;
    let outcome: ProofOutcome | undefined;
    let theorem: string | undefined;
    for (let i = this.steps.length - 1; i >= start; i--) {
      const step = this.steps[i];
      if (!state && step.endState) state = step.endState;
      if (!outcome && step.outcome) outcome = step.outcome;
      if (!theorem && step.theorem) theorem = step.theorem;
    }
    this.lastState = state;
    this.lastOutcome = outcome;
    this.currentTheorem = theorem;
    this.emitView();
  }

  private clearSessionState(): void {
    this.steps = [];
    this.tip = 0;
    this.lastState = undefined;
    this.lastOutcome = undefined;
    this.currentTheorem = undefined;
    this.events.onTip(0);
    this.emitView();
  }

  private async initialize(): Promise<boolean> {
    const result = await this.driver.init(
      abellaFiles(this.project),
      this.project.root
    );
    this.clearSessionState();
    this.dirty = false;
    this.initialized = result.status === "ok";
    const entries = outputEntries(result.messages);
    if (entries.length > 0) this.events.onOutput(entries);
    this.events.onResult(result);
    this.events.onStatus(this.initialized ? "ready" : "error");
    return this.initialized;
  }

  private async ensureInitialized(): Promise<boolean> {
    if (this.initialized && !this.dirty) return true;
    return this.initialize();
  }

  async init(): Promise<void> {
    await this.exclusive(async () => {
      this.dirty = true;
      await this.ensureInitialized();
    });
  }

  async reset(): Promise<void> {
    await this.exclusive(async () => {
      const result = await this.driver.reset(
        abellaFiles(this.project),
        this.project.root
      );
      this.clearSessionState();
      this.dirty = false;
      this.initialized = result.status === "ok";
      const entries = outputEntries(result.messages);
      if (entries.length > 0) this.events.onOutput(entries);
      this.events.onResult(result);
      this.events.onStatus(this.initialized ? "ready" : "error");
    });
  }

  /** Terminate the current prover worker and abandon the session state. */
  stop(): void {
    this.generation++;
    if (this.driver.restart) this.driver.restart();
    else this.driver.terminate();
    this.clearSessionState();
    this.initialized = false;
    this.dirty = true;
    this.events.onStatus("ready");
  }

  private async processCommand(
    doc: string,
    command: Command,
    generation = this.generation
  ): Promise<boolean> {
    if (generation !== this.generation) return false;
    const start = sourcePos(doc, command.from);
    let result: RunResult;
    try {
      result = await this.driver.process(command.text, start);
    } catch (error) {
      if (generation !== this.generation) return false;
      this.events.onStatus("error");
      this.events.onError(String(error), command.from, command.to);
      return false;
    }
    if (generation !== this.generation) return false;
    this.events.onResult(result, command);
    const entries = outputEntries(result.messages);
    if (entries.length > 0) this.events.onOutput(entries, command);
    if (result.status === "error") {
      const message = errorText(result.messages);
      if (entries.length === 0) {
        this.events.onOutput([{ severity: "error", message }], command);
      }
      this.tip = command.from;
      this.events.onTip(this.tip);
      this.events.onStatus("error");
      return false;
    }

    const state = endState(result.messages);
    const theorem = theoremFrom(result.messages);
    const rawOutcome = proofOutcome(result.messages);
    const outcome = rawOutcome
      ? { ...rawOutcome, theorem: theorem ?? this.currentTheorem }
      : undefined;
    const beginsTheorem = startsTheorem(command);
    this.steps.push({
      from: command.from,
      to: command.to,
      tip: command.to,
      startsTheorem: beginsTheorem,
      theorem,
      endState: state,
      outcome,
    });
    this.tip = command.to;
    this.events.onTip(this.tip);

    if (beginsTheorem) {
      this.currentTheorem = undefined;
      this.lastState = undefined;
      this.lastOutcome = undefined;
    } else {
      if (theorem) this.currentTheorem = theorem;
      if (state) this.lastState = state;
      if (outcome) this.lastOutcome = outcome;
    }
    this.emitView();
    return true;
  }

  async processTo(cursor: number): Promise<void> {
    await this.exclusive(async () => {
      if (!(await this.ensureInitialized())) return;
      if (cursor < this.tip) {
        await this.rewindToLeftOfUnlocked(cursor);
        return;
      }
      const doc = rootText(this.project);
      let commands: Command[];
      try {
        commands = scanCommands(doc, this.tip);
      } catch (error) {
        const message =
          error instanceof ScanError ? error.message : String(error);
        this.events.onStatus("error");
        this.events.onError(message, this.tip, doc.length);
        return;
      }
      const targets = commands.filter(
        (command) => command.from < cursor
      );
      if (targets.length === 0) {
        this.events.onStatus("ready");
        return;
      }
      this.events.onStatus("processing");
      const generation = this.generation;
      for (const command of targets) {
        if (generation !== this.generation) return;
        if (!(await this.processCommand(doc, command, generation))) return;
      }
      if (generation !== this.generation) return;
      this.events.onStatus("ok");
    });
  }

  async processAll(): Promise<void> {
    const doc = rootText(this.project);
    await this.processTo(doc.length);
  }

  private async undoFrom(index: number, newTip: number): Promise<number> {
    const count = this.steps.length - index;
    if (count <= 0) {
      this.tip = newTip;
      this.events.onTip(this.tip);
      this.recomputeView();
      this.events.onStatus("ready");
      return 0;
    }
    const first = this.steps[index];
    const result = await this.driver.back(count);
    if (result.status === "error") {
      this.events.onStatus("error");
      this.events.onError(errorText(result.messages), first.from, first.to);
      return 0;
    }
    this.steps.splice(index);
    this.tip = newTip;
    this.recomputeView();
    this.events.onTip(this.tip);
    this.events.onStatus("ready");
    return count;
  }

  /** Rewind for an edit: `offset` becomes the new tip. */
  async rewindTo(offset: number): Promise<number> {
    return this.exclusive(async () => {
      if (offset >= this.tip) return 0;
      if (!this.initialized) {
        this.clearSessionState();
        return 0;
      }
      const index = this.steps.findIndex((step) => offset < step.to);
      if (index < 0) {
        const last = this.steps[this.steps.length - 1];
        return this.undoFrom(this.steps.length, last ? last.to : 0);
      }
      return this.undoFrom(index, this.steps[index].from);
    });
  }

  /**
   * Rewind to a command boundary for Ctrl-Enter: keep only steps whose
   * `to <= cursor`; the cursor itself does not move.
   */
  private async rewindToLeftOfUnlocked(cursor: number): Promise<number> {
    if (!this.initialized) {
      this.clearSessionState();
      return 0;
    }
    const index = this.steps.findIndex((step) => step.to > cursor);
    const from = index < 0 ? this.steps.length : index;
    const newTip = from > 0 ? this.steps[from - 1].to : 0;
    return this.undoFrom(from, newTip);
  }

  async rewindToLeftOf(cursor: number): Promise<number> {
    return this.exclusive(async () => {
      if (cursor >= this.tip) return 0;
      return this.rewindToLeftOfUnlocked(cursor);
    });
  }

  async stepForward(cursor: number): Promise<boolean> {
    return this.exclusive(async () => {
      if (!(await this.ensureInitialized())) return false;
      const atEnd = cursor >= this.tip;
      const doc = rootText(this.project);
      let commands: Command[];
      try {
        commands = scanCommands(doc, this.tip);
      } catch (error) {
        const message =
          error instanceof ScanError ? error.message : String(error);
        this.events.onStatus("error");
        this.events.onError(message, this.tip, doc.length);
        return false;
      }
      const command = commands[0];
      if (!command) {
        this.events.onStatus("ready");
        return false;
      }
      this.events.onStatus("processing");
      const generation = this.generation;
      const ok = await this.processCommand(doc, command, generation);
      if (!ok || generation !== this.generation) return false;
      if (atEnd) this.events.onCursor(command.to);
      this.events.onStatus("ok");
      return true;
    });
  }

  async stepBackward(cursor: number): Promise<boolean> {
    return this.exclusive(async () => {
      if (this.steps.length === 0) return false;
      const oldTip = this.tip;
      const last = this.steps[this.steps.length - 1];
      const moved = await this.undoFrom(
        this.steps.length - 1,
        last.from
      );
      if (moved > 0 && cursor >= oldTip) {
        this.events.onCursor(last.from);
      }
      return moved > 0;
    });
  }

  setProject(project: Project): void {
    this.project = project;
    this.dirty = true;
    this.initialized = false;
    this.clearSessionState();
    this.events.onStatus("ready");
  }

  /** Called after the editor changed `path`; offsets are JS offsets. */
  notifyEdit(path: string, changes: ChangeSet): Promise<void> {
    const kind = classify(path);
    if (path !== this.project.root) {
      if (kind === "abella") {
        this.dirty = true;
        this.events.onStatus("ready");
      }
      return Promise.resolve();
    }
    this.pendingEdits.push(changes);
    if (!this.editTask) {
      this.editTask = this.exclusive(async () => {
        this.editTask = undefined;
        const edits = this.pendingEdits.splice(0);
        await this.applyEdits(edits);
      });
    }
    return this.editTask;
  }

  /**
   * Remap the checked tip and surviving steps through a batch of edits.
   * Edits at or after the tip only shift offsets; an edit before the tip
   * invalidates the command it touches and every command after it.
   */
  private async applyEdits(edits: ChangeSet[]): Promise<void> {
    if (!this.initialized) {
      this.clearSessionState();
      return;
    }
    const bounds: StepBounds[] = this.steps.map((step) => ({
      from: step.from,
      to: step.to,
      tip: step.tip,
    }));
    let invalid = bounds.length;
    let candidate: number | undefined;
    let tip = this.tip;

    for (const changes of edits) {
      const offset = firstChangedOffset(changes);
      if (offset === undefined) continue;
      if (invalid === bounds.length) {
        const index = bounds.findIndex((bound) => bound.to > offset);
        if (index >= 0) invalid = index;
      }
      if (invalid < bounds.length) {
        candidate ??= bounds[invalid].from;
        candidate = changes.mapPos(candidate, -1);
        tip = candidate;
      } else {
        tip = changes.mapPos(tip, offset < tip ? 1 : -1);
      }
      for (let i = 0; i < invalid; i++) {
        bounds[i].from = changes.mapPos(bounds[i].from, 1);
        bounds[i].to = changes.mapPos(bounds[i].to, -1);
        bounds[i].tip = changes.mapPos(bounds[i].tip, -1);
      }
    }

    const commitBounds = () => {
      for (let i = 0; i < invalid; i++) {
        this.steps[i].from = bounds[i].from;
        this.steps[i].to = bounds[i].to;
        this.steps[i].tip = bounds[i].tip;
      }
    };

    if (invalid === bounds.length) {
      commitBounds();
      this.tip = tip;
      this.events.onTip(tip);
      return;
    }

    const first = this.steps[invalid];
    const count = this.steps.length - invalid;
    const result = await this.driver.back(count);
    if (result.status === "error") {
      this.events.onStatus("error");
      this.events.onError(errorText(result.messages), first.from, first.to);
      return;
    }
    this.steps.splice(invalid);
    commitBounds();
    this.tip = tip;
    this.recomputeView();
    this.events.onTip(tip);
    this.events.onStatus("ready");
  }
}
