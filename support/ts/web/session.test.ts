// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { ChangeSet } from "@codemirror/state";
import type { Command } from "./commands";
import type { Driver } from "./driver";
import { classify, type Project, type ProjectTextFile } from "./project";
import {
  Session,
  type OutputEntry,
  type OutputLocation,
  type ProofOutcome,
  type SessionEvents,
  type SessionStatus,
} from "./session";
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
  restarts = 0;
  processed: string[] = [];
  backs: number[] = [];
  failAt = -1;
  endOn?: string;
  warningOn?: string;
  onProgress?: (module: string) => void;

  async init(): Promise<RunResult> {
    this.inits++;
    return ok();
  }

  async reset(): Promise<RunResult> {
    this.resets++;
    return ok();
  }

  currentTheorem = "t";

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
    const messages: RawMessage[] = [];
    const theorem = /^Theorem\s+(\S+)/.exec(command)?.[1];
    if (theorem) this.currentTheorem = theorem;
    if (!/^(Specification|Kind|Type|Theorem)\b/.test(command)) {
      messages.push({
        type: "proof_command",
        id: 1,
        thm_id: 1,
        theorem: this.currentTheorem,
        command,
        start_state: state,
        end_state: state,
      });
    }
    if (this.warningOn === command) {
      messages.push({
        type: "system_message",
        id: 2,
        severity: "info",
        message: "Warning: synthetic warning",
      });
    }
    if (this.endOn === command) {
      messages.push({
        type: "system_message",
        id: 3,
        severity: "info",
        message: "Proof completed",
      });
    }
    return ok(messages);
  }

  async back(count: number): Promise<RunResult> {
    this.backs.push(count);
    return ok();
  }

  terminate(): void {}

  restart(): void {
    this.restarts++;
  }
}

function makeProject(): Project {
  const files = new Map<string, ProjectTextFile>();
  const add = (path: string, text: string) =>
    files.set(path, { text, kind: classify(path) });
  add("empty.sig", "sig empty.\n");
  add("empty.mod", "module empty.\n");
  add(
    "main.thm",
    'Specification "empty".\nKind tm type.\nTheorem t : forall A, A = A.\nintros.\n'
  );
  add("README.md", "notes\n");
  return { files, root: "main.thm", active: "main.thm" };
}

function makeTwoTheoremProject(): Project {
  const files = new Map<string, ProjectTextFile>();
  files.set("main.thm", {
    text:
      "Theorem a : forall A, A = A.\nintros a.\n" +
      "Theorem b : forall A, A = A.\nintros b.\n",
    kind: "abella",
  });
  return { files, root: "main.thm", active: "main.thm" };
}

interface Captured {
  statuses: SessionStatus[];
  tips: number[];
  goals: (ProofState | undefined)[];
  outcomes: (ProofOutcome | undefined)[];
  outputs: OutputEntry[][];
  outputLocations: (OutputLocation | undefined)[];
  results: RunResult[];
  errors: string[];
  commands: (Command | undefined)[];
  cursors: number[];
}

function capture(): { events: SessionEvents; captured: Captured } {
  const captured: Captured = {
    statuses: [],
    tips: [],
    goals: [],
    outcomes: [],
    outputs: [],
    outputLocations: [],
    results: [],
    errors: [],
    commands: [],
    cursors: [],
  };
  const events: SessionEvents = {
    onStatus: (status) => captured.statuses.push(status),
    onTip: (tip) => captured.tips.push(tip),
    onGoal: (goal) => captured.goals.push(goal),
    onOutcome: (outcome) => captured.outcomes.push(outcome),
    onOutput: (entries, location) => {
      captured.outputs.push(entries);
      captured.outputLocations.push(location);
    },
    onResult: (result, command) => {
      captured.results.push(result);
      captured.commands.push(command);
    },
    onError: (message) => captured.errors.push(message),
    onCursor: (offset) => captured.cursors.push(offset),
  };
  return { events, captured };
}

function setup(project = makeProject()) {
  const driver = new FakeDriver();
  const { events, captured } = capture();
  const session = new Session(driver, project, events);
  return { project, driver, captured, session };
}

test("reports an output location for every processed command", async () => {
  const { project, captured, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.length);

  assert.equal(captured.outputLocations.length, 4);
  assert.ok(
    captured.outputLocations.every((location) => location !== undefined)
  );
  assert.deepEqual(captured.outputLocations[0], {
    from: 0,
    position: 'Specification "empty".'.length,
  });
});

test("checks commands that start before the cursor", async () => {
  const { project, driver, captured, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.indexOf("Kind"));
  assert.deepEqual(driver.processed, ['Specification "empty".']);
  assert.equal(session.currentTip, doc.indexOf("Kind") - 1);
  assert.equal(session.stepsCount, 1);

  await session.processTo(doc.indexOf("Kind") + 1);
  assert.deepEqual(driver.processed, [
    'Specification "empty".',
    "Kind tm type.",
  ]);
  assert.equal(session.stepsCount, 2);
});

test("Ctrl-Enter inside the checked region rewinds to the command boundary", async () => {
  const { project, driver, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.length);
  assert.equal(driver.processed.length, 4);

  const insideTheorem = doc.indexOf("Theorem") + 2;
  await session.processTo(insideTheorem);
  assert.deepEqual(driver.backs, [2]);
  assert.equal(session.stepsCount, 2);
  assert.equal(session.currentTip, doc.indexOf("Kind") + "Kind tm type.".length);

  await session.processTo(insideTheorem);
  assert.equal(driver.processed.length, 5);
  assert.equal(session.stepsCount, 3);
});

test("Ctrl-Enter in whitespace keeps the previous complete command", async () => {
  const { project, driver, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.length);
  await session.processTo(doc.indexOf("Kind"));
  assert.deepEqual(driver.backs, [3]);
  assert.equal(session.stepsCount, 1);
  assert.equal(session.currentTip, doc.indexOf("Kind") - 1);
});

test("steps forward and back at the checked tip", async () => {
  const { project, driver, captured, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.stepForward(0);
  assert.deepEqual(driver.processed, ['Specification "empty".']);
  assert.deepEqual(captured.cursors, ['Specification "empty".'.length]);

  await session.stepBackward('Specification "empty".'.length);
  assert.deepEqual(driver.backs, [1]);
  assert.equal(session.stepsCount, 0);
  assert.deepEqual(captured.cursors, ['Specification "empty".'.length, 0]);
  assert.equal(session.currentTip, 0);
});

test("stepping back leaves the tip at the previous command end", async () => {
  const { project, captured, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.length);
  const theoremEnd =
    doc.indexOf("Theorem") + "Theorem t : forall A, A = A.".length;
  captured.cursors.length = 0;

  await session.stepBackward(doc.length);
  assert.equal(session.currentTip, theoremEnd);
  assert.equal(session.stepsCount, 3);
  assert.deepEqual(captured.cursors, [theoremEnd]);
});

test("stepping before the tip leaves the cursor alone", async () => {
  const { project, driver, captured, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.indexOf("Theorem"));
  captured.cursors.length = 0;

  await session.stepForward(0);
  assert.equal(driver.processed.length, 3);
  assert.deepEqual(captured.cursors, []);

  await session.stepBackward(0);
  assert.equal(driver.backs.at(-1), 1);
  assert.deepEqual(captured.cursors, []);
});

test("rewinds to the first affected command on edit", async () => {
  const { project, driver, session } = setup();
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.length);
  assert.equal(driver.processed.length, 4);
  await session.rewindTo(0);
  assert.deepEqual(driver.backs, [4]);
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
  assert.deepEqual(captured.errors, []);
  assert.ok(
    captured.outputs
      .flat()
      .some(
        (entry) =>
          entry.severity === "error" &&
          entry.message === "synthetic failure"
      )
  );
});

test("records proof outcomes verbatim and clears them on rewind", async () => {
  const { project, driver, session } = setup();
  driver.endOn = "intros.";
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.length);
  assert.deepEqual(session.outcome, {
    theorem: "t",
    status: "completed",
    message: "Proof completed",
  });
  await session.rewindTo(0);
  assert.equal(session.outcome, undefined);
});

test("a new theorem hides the previous outcome", async () => {
  const { project, driver, session } = setup(makeTwoTheoremProject());
  driver.endOn = "intros a.";
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.indexOf("Theorem b"));
  assert.equal(session.outcome?.theorem, "a");
  await session.processTo(doc.length);
  assert.equal(session.outcome, undefined);
});

test("proof lifecycle messages are not output entries", async () => {
  const { project, driver, captured, session } = setup();
  driver.endOn = "intros.";
  driver.warningOn = "Kind tm type.";
  await session.init();
  const doc = project.files.get(project.root)!.text;
  await session.processTo(doc.length);
  const output = captured.outputs.flat();
  assert.ok(output.some((entry) => entry.message.includes("synthetic warning")));
  assert.ok(!output.some((entry) => entry.message === "Proof completed"));
});

test("editing a spec file forces re-initialization", async () => {
  const { driver, session } = setup();
  await session.init();
  assert.equal(driver.inits, 1);
  const text = "sig empty.\n";
  await session.notifyEdit(
    "empty.sig",
    ChangeSet.of({ from: 0, insert: "" }, text.length)
  );
  await session.processTo(0);
  assert.equal(driver.inits, 2);
});

test("editing a text file does not invalidate the session", async () => {
  const { driver, session } = setup();
  await session.init();
  const text = "notes\n";
  await session.notifyEdit(
    "README.md",
    ChangeSet.of({ from: 0, insert: "" }, text.length)
  );
  await session.processTo(0);
  assert.equal(driver.inits, 1);
});

test("editing and deleting before the tip keeps checked steps", async () => {
  const text =
    'Specification "empty".\nKind tm type.\n' +
    "Theorem t : forall A, A = A.\nintros.\n  search.\n  case H1.\n";
  const files = new Map<string, ProjectTextFile>([
    ["main.thm", { text, kind: "abella" }],
  ]);
  const project: Project = {
    files,
    root: "main.thm",
    active: "main.thm",
  };
  const { driver, captured, session } = setup(project);
  await session.init();
  await session.processTo(text.length);
  const checked = session.stepsCount;
  assert.equal(checked, 6);

  const rootFile = project.files.get("main.thm")!;
  const searchEnd = text.indexOf("search.") + "search.".length;
  const spaced = text.slice(0, searchEnd) + " " + text.slice(searchEnd);

  rootFile.text = spaced;
  await session.notifyEdit(
    "main.thm",
    ChangeSet.of({ from: searchEnd, insert: " " }, text.length)
  );
  assert.equal(session.stepsCount, checked - 1);
  assert.equal(session.currentTip, searchEnd);

  rootFile.text = text;
  await session.notifyEdit(
    "main.thm",
    ChangeSet.of(
      { from: searchEnd, to: searchEnd + 1, insert: "" },
      spaced.length
    )
  );
  assert.equal(session.stepsCount, checked - 1);
  assert.equal(session.currentTip, searchEnd);
  assert.deepEqual(driver.backs, [1]);

  await session.stepForward(searchEnd);
  assert.equal(driver.processed.at(-1), "case H1.");
  assert.deepEqual(captured.errors, []);
});

test("inserted commands stay unchecked until explicitly stepped", async () => {
  const text =
    'Specification "empty".\nKind tm type.\n' +
    "Theorem t : forall A, A = A.\nintros.\n  search.\n  case H1.\n";
  const files = new Map<string, ProjectTextFile>([
    ["main.thm", { text, kind: "abella" }],
  ]);
  const project: Project = {
    files,
    root: "main.thm",
    active: "main.thm",
  };
  const { driver, captured, session } = setup(project);
  await session.init();
  await session.processTo(text.length);
  const checked = session.stepsCount;

  const rootFile = project.files.get("main.thm")!;
  const searchEnd = text.indexOf("search.") + "search.".length;
  const spaced = text.slice(0, searchEnd) + " " + text.slice(searchEnd);
  rootFile.text = spaced;
  await session.notifyEdit(
    "main.thm",
    ChangeSet.of({ from: searchEnd, insert: " " }, text.length)
  );
  assert.equal(session.currentTip, searchEnd);
  assert.equal(session.stepsCount, checked - 1);

  const withAbort =
    spaced.slice(0, searchEnd + 1) +
    "abort. " +
    spaced.slice(searchEnd + 1);
  rootFile.text = withAbort;
  await session.notifyEdit(
    "main.thm",
    ChangeSet.of({ from: searchEnd + 1, insert: "abort. " }, spaced.length)
  );
  assert.equal(session.currentTip, searchEnd);
  assert.equal(session.stepsCount, checked - 1);

  await session.stepForward(searchEnd);
  assert.equal(driver.processed.at(-1), "abort.");
  assert.equal(session.stepsCount, checked);
  assert.deepEqual(captured.errors, []);
});

test("stop abandons the session and reinitializes on the next request", async () => {
  const { driver, session } = setup();
  await session.init();
  await session.processTo(10000);
  session.stop();
  assert.equal(driver.restarts, 1);
  assert.equal(session.currentTip, 0);
  assert.equal(session.stepsCount, 0);
  await session.processTo(0);
  assert.equal(driver.inits, 2);
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
