// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import type { Command } from "./commands";
import type { Driver } from "./driver";
import { classify, type Project, type ProjectTextFile } from "./project";
import { Session, type SessionEvents, type SessionStatus } from "./session";
import type { ProofState, RawMessage, RunResult, SourcePos } from "./types";

const state: ProofState = {
  name: "",
  vars: [],
  hyps: [],
  goal: "true",
  more: 0,
};

const ok = (messages: RawMessage[] = []): RunResult => ({
  status: "ok",
  messages,
});

class FakeDriver implements Driver {
  inits = 0;
  resets = 0;
  processed: string[] = [];
  backs: number[] = [];
  failAt = -1;
  onProgress?: (module: string) => void;

  async init(): Promise<RunResult> {
    this.inits++;
    return ok();
  }

  async reset(): Promise<RunResult> {
    this.resets++;
    return ok();
  }

  async process(command: string, _start: SourcePos): Promise<RunResult> {
    if (this.processed.length === this.failAt) {
      return {
        status: "error",
        messages: [
          {
            type: "system_message",
            id: 1,
            severity: "error",
            message: "synthetic failure",
          },
        ],
      };
    }
    this.processed.push(command);
    return ok([
      {
        type: "proof_command",
        id: 1,
        thm_id: 1,
        theorem: "t",
        command,
        start_state: state,
        end_state: state,
      },
    ]);
  }

  async back(count: number): Promise<RunResult> {
    this.backs.push(count);
    return ok();
  }

  terminate(): void {}
}

function makeProject(): Project {
  const files = new Map<string, ProjectTextFile>();
  const add = (path: string, text: string) =>
    files.set(path, { text, kind: classify(path) });
  add("empty.sig", "sig empty.\n");
  add("empty.mod", "module empty.\n");
  add(
    "main.thm",
    'Specification "empty".\nKind tm type.\nTheorem t : forall A, A = A.\n'
  );
  add("README.md", "notes\n");
  return { files, root: "main.thm", active: "main.thm" };
}

interface Captured {
  statuses: SessionStatus[];
  tips: number[];
  goals: (ProofState | undefined)[];
  results: RunResult[];
  errors: string[];
  commands: (Command | undefined)[];
}

function capture(): { events: SessionEvents; captured: Captured } {
  const captured: Captured = {
    statuses: [],
    tips: [],
    goals: [],
    results: [],
    errors: [],
    commands: [],
  };
  const events: SessionEvents = {
    onStatus: (status) => captured.statuses.push(status),
    onTip: (tip) => captured.tips.push(tip),
    onGoal: (goal) => captured.goals.push(goal),
    onResult: (result, command) => {
      captured.results.push(result);
      captured.commands.push(command);
    },
    onError: (message) => captured.errors.push(message),
  };
  return { events, captured };
}

function setup() {
  const project = makeProject();
  const driver = new FakeDriver();
  const { events, captured } = capture();
  const session = new Session(driver, project, events);
  return { project, driver, captured, session };
}

test("processes commands up to the cursor", async () => {
  const { project, driver, captured, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.indexOf("Kind"));
  assert.deepEqual(driver.processed, [
    'Specification "empty".',
    "Kind tm type.",
  ]);
  assert.equal(session.currentTip, doc.indexOf("Kind") + "Kind tm type.".length);
  assert.equal(session.stepsCount, 2);
  assert.deepEqual(captured.statuses, ["ready", "processing", "ok"]);
});

test("blocking mode leaves the command under the cursor", async () => {
  const { project, driver, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.indexOf("Theorem"), true);
  assert.equal(driver.processed.length, 2);
  assert.ok(!driver.processed[1].startsWith("Theorem"));
});

test("rewinds to the first affected command", async () => {
  const { project, driver, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.length);
  assert.equal(driver.processed.length, 3);
  await session.rewindTo(0);
  assert.deepEqual(driver.backs, [3]);
  assert.equal(session.currentTip, 0);
  assert.equal(session.stepsCount, 0);
});

test("stops at the first failing command", async () => {
  const { project, driver, captured, session } = setup();
  driver.failAt = 1;
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.length);
  assert.equal(driver.processed.length, 1);
  assert.equal(session.stepsCount, 1);
  assert.equal(session.currentTip, doc.indexOf("Kind"));
  assert.equal(captured.statuses.at(-1), "error");
  assert.deepEqual(captured.errors, ["synthetic failure"]);
});

test("editing a spec file forces re-initialization", async () => {
  const { driver, session } = setup();
  await session.init();
  assert.equal(driver.inits, 1);
  session.notifyEdit("empty.sig", 0);
  await session.processTo(0);
  assert.equal(driver.inits, 2);
});

test("editing a text file does not invalidate the session", async () => {
  const { driver, session } = setup();
  await session.init();
  session.notifyEdit("README.md", 0);
  await session.processTo(0);
  assert.equal(driver.inits, 1);
});

test("reset clears steps and reloads the project", async () => {
  const { driver, session } = setup();
  await session.init();
  await session.processTo(10000);
  await session.reset();
  assert.equal(driver.resets, 1);
  assert.equal(session.currentTip, 0);
  assert.equal(session.stepsCount, 0);
});
