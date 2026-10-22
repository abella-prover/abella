// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

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

export interface Step {
  from: number;
  to: number;
  tip: number;
  endState?: ProofState;
}

export interface SessionEvents {
  onStatus(status: SessionStatus, detail?: string): void;
  onTip(tip: number): void;
  onGoal(state: ProofState | undefined): void;
  onResult(result: RunResult, command?: Command): void;
  onError(message: string, from: number, to: number): void;
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

function errorText(messages: RawMessage[]): string {
  for (let i = messages.length - 1; i >= 0; i--) {
    const message = messages[i];
    if (message.type === "system_message" && message.severity === "error") {
      return message.message;
    }
  }
  return "Abella reported an error.";
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
  private queue: Promise<unknown> = Promise.resolve();

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

  private async initialize(): Promise<boolean> {
    const result = await this.driver.init(
      abellaFiles(this.project),
      this.project.root
    );
    this.steps = [];
    this.tip = 0;
    this.lastState = undefined;
    this.dirty = false;
    this.initialized = result.status === "ok";
    this.events.onTip(0);
    this.events.onGoal(undefined);
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
      this.steps = [];
      this.tip = 0;
      this.lastState = undefined;
      this.dirty = false;
      this.initialized = result.status === "ok";
      this.events.onTip(0);
      this.events.onGoal(undefined);
      this.events.onResult(result);
      this.events.onStatus(this.initialized ? "ready" : "error");
    });
  }

  async processTo(cursor: number, blocking = false): Promise<void> {
    await this.exclusive(async () => {
      if (!(await this.ensureInitialized())) return;
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
      const targets = commands.filter((command) =>
        blocking ? command.to < cursor : command.from <= cursor
      );
      if (targets.length === 0) {
        this.events.onStatus("ready");
        return;
      }
      this.events.onStatus("processing");
      for (const command of targets) {
        const start = sourcePos(doc, command.from);
        let result: RunResult;
        try {
          result = await this.driver.process(command.text, start);
        } catch (error) {
          this.events.onStatus("error");
          this.events.onError(String(error), command.from, command.to);
          return;
        }
        this.events.onResult(result, command);
        if (result.status === "error") {
          this.tip = command.from;
          this.events.onTip(this.tip);
          this.events.onStatus("error");
          this.events.onError(errorText(result.messages), command.from, command.to);
          return;
        }
        const state = endState(result.messages);
        this.steps.push({
          from: command.from,
          to: command.to,
          tip: command.to,
          endState: state,
        });
        this.tip = command.to;
        this.events.onTip(this.tip);
        if (state) {
          this.lastState = state;
          this.events.onGoal(state);
        }
      }
      this.events.onStatus("ok");
    });
  }

  async processAll(): Promise<void> {
    const doc = rootText(this.project);
    await this.processTo(doc.length, false);
  }

  /** Rewind so that the prover state is at `offset`; returns the count. */
  async rewindTo(offset: number): Promise<number> {
    return this.exclusive(async () => {
      if (offset >= this.tip) return 0;
      if (!this.initialized) {
        this.tip = 0;
        this.events.onTip(0);
        return 0;
      }
      const index = this.steps.findIndex((step) => offset < step.to);
      const from = index < 0 ? this.steps.length : index;
      const count = this.steps.length - from;
      const first = this.steps[from];
      if (count > 0) {
        const result = await this.driver.back(count);
        if (result.status === "error") {
          this.events.onStatus("error");
          this.events.onError(
            errorText(result.messages),
            first.from,
            first.to
          );
          return 0;
        }
        this.steps.splice(from);
      }
      this.tip = first ? first.from : 0;
      this.lastState =
        this.steps.length > 0
          ? this.steps[this.steps.length - 1].endState
          : undefined;
      this.events.onTip(this.tip);
      this.events.onGoal(this.lastState);
      this.events.onStatus("ready");
      return count;
    });
  }

  setProject(project: Project): void {
    this.project = project;
    this.steps = [];
    this.tip = 0;
    this.lastState = undefined;
    this.dirty = true;
    this.initialized = false;
    this.events.onTip(0);
    this.events.onGoal(undefined);
    this.events.onStatus("ready");
  }

  /** Called after the editor changed `path`; `minFrom` is a JS offset. */
  notifyEdit(path: string, minFrom: number): void {
    const kind = classify(path);
    if (path !== this.project.root) {
      if (kind === "abella") {
        this.dirty = true;
        this.events.onStatus("ready");
      }
      return;
    }
    if (minFrom < this.tip) {
      void this.rewindTo(minFrom);
    }
  }
}
