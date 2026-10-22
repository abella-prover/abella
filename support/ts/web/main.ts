// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { downloadProject, importProject } from "./archive";
import { WorkerDriver, loadEngine } from "./driver";
import { EditorManager } from "./editor";
import {
  fillExampleSelect,
  loadBundle,
  type Bundle,
} from "./examples";
import { renderFiles } from "./files";
import {
  clearSavedProject,
  loadProject,
  projectFromBundle,
  saveProject,
  scratchProject,
  setFileText,
  type Project,
} from "./project";
import { Session, type SessionEvents, type SessionStatus } from "./session";
import { appendMessages, renderSequent } from "./trace";
import type { ProofState, RawMessage } from "./types";

function byId<T extends HTMLElement>(id: string): T {
  const element = document.getElementById(id);
  if (!element) throw new Error(`Missing #${id}`);
  return element as T;
}

const statusBadge = byId<HTMLSpanElement>("status");
const statusDetail = byId<HTMLSpanElement>("status-detail");
const fileList = byId<HTMLDivElement>("file-list");
const goalPanel = byId<HTMLDivElement>("goal");
const messagesPanel = byId<HTMLDivElement>("messages");
const exampleSelect = byId<HTMLSelectElement>("example-select");
const zipInput = byId<HTMLInputElement>("zip-input");
const processButton = byId<HTMLButtonElement>("process");
const processAllButton = byId<HTMLButtonElement>("process-all");
const resetButton = byId<HTMLButtonElement>("reset");

let project: Project = loadProject() ?? scratchProject();
let bundle: Bundle | undefined;
let editor: EditorManager;
let session: Session;
let saveTimer: number | undefined;

const statusText: Record<SessionStatus, string> = {
  idle: "Starting…",
  ready: "Ready",
  processing: "Processing…",
  compiling: "Compiling import…",
  ok: "Commands processed",
  error: "Error",
};

function setStatus(status: SessionStatus, detail?: string): void {
  statusBadge.dataset.status = status;
  statusBadge.textContent =
    status === "ok"
      ? `${session?.stepsCount ?? 0} commands processed`
      : statusText[status];
  statusDetail.textContent = detail ?? "";
  const busy = status === "processing" || status === "compiling";
  processButton.disabled = busy;
  processAllButton.disabled = busy;
  resetButton.disabled = busy;
}

function scheduleSave(): void {
  window.clearTimeout(saveTimer);
  saveTimer = window.setTimeout(() => saveProject(project), 250);
}

function info(message: string): void {
  appendMessages(messagesPanel, [
    { type: "system_message", id: -1, severity: "info", message },
  ]);
}

function refreshFiles(): void {
  renderFiles(fileList, project, project.active, openFile);
}

function openFile(path: string): void {
  const file = project.files.get(path);
  if (!file) return;
  project.active = path;
  editor.open(path, file.text);
  refreshFiles();
  scheduleSave();
  editor.focus();
}

function goal(state: ProofState | undefined): void {
  goalPanel.replaceChildren();
  if (state) {
    goalPanel.append(renderSequent(state));
  } else {
    const empty = document.createElement("div");
    empty.className = "goal-empty";
    empty.textContent = "No proof state yet.";
    goalPanel.append(empty);
  }
}

function errorDiagnostic(message: string, from: number, to: number): void {
  const doc = project.files.get(project.root)?.text ?? "";
  const end = Math.max(0, Math.min(to, doc.length));
  const start = Math.max(0, Math.min(from, end));
  editor.setDiagnostics(project.root, [
    { from: start, to: end, severity: "error", message },
  ]);
}

const events: SessionEvents = {
  onStatus: setStatus,
  onTip(tip) {
    editor.setProcessedTip(project.root, tip);
  },
  onGoal: goal,
  onResult(result, command) {
    appendMessages(messagesPanel, result.messages);
    if (result.status === "ok") {
      editor.clearDiagnostics(project.root);
    } else if (command) {
      errorDiagnostic(
        result.messages
          .filter(
            (message): message is Extract<RawMessage, { type: "system_message" }> =>
              message.type === "system_message" &&
              message.severity === "error"
          )
          .map((message) => message.message)
          .join("\n") || "Abella reported an error.",
        command.from,
        command.to
      );
    }
  },
  onError(message, from, to) {
    appendMessages(messagesPanel, [
      { type: "system_message", id: -1, severity: "error", message },
    ]);
    errorDiagnostic(message, from, to);
  },
};

async function startProject(next: Project, keepMessages = false): Promise<void> {
  project = next;
  if (!keepMessages) messagesPanel.replaceChildren();
  editor.reset();
  refreshFiles();
  openFile(project.active);
  session.setProject(project);
  scheduleSave();
  try {
    await session.init();
  } catch (error) {
    setStatus("error", String(error));
  }
}

async function processToCursor(blocking: boolean): Promise<void> {
  if (editor.active !== project.root) {
    info(`Processing the root reasoning file ${project.root}.`);
    openFile(project.root);
  }
  const cursor = editor.cursorFor(project.root);
  await session.processTo(cursor, blocking);
}

async function main(): Promise<void> {
  editor = new EditorManager(
    byId<HTMLDivElement>("editor"),
    (path, update) => {
      setFileText(project, path, update.state.doc.toString());
      project.active = path;
      scheduleSave();
      editor.clearDiagnostics(path);
      let minFrom = Number.POSITIVE_INFINITY;
      update.changes.iterChangedRanges((fromA, _toA, fromB) => {
        minFrom = Math.min(minFrom, fromA, fromB);
      });
      if (minFrom !== Number.POSITIVE_INFINITY) {
        session.notifyEdit(path, minFrom);
      }
      refreshFiles();
    },
    (blocking) => void processToCursor(blocking)
  );

  const engine = await loadEngine();
  const driver = new WorkerDriver(engine, (module) =>
    setStatus("compiling", module)
  );
  session = new Session(driver, project, events);

  bundle = await loadBundle();
  if (bundle) {
    fillExampleSelect(exampleSelect, bundle);
  } else {
    exampleSelect.disabled = true;
    exampleSelect.title = "Could not load examples/bundle.json";
  }

  refreshFiles();
  openFile(project.active);
  setStatus("idle");
  try {
    await session.init();
  } catch (error) {
    setStatus("error", String(error));
  }

  processButton.addEventListener("click", () => void processToCursor(false));
  processAllButton.addEventListener("click", () => void session.processAll());
  resetButton.addEventListener("click", () => {
    messagesPanel.replaceChildren();
    void session.reset();
  });

  exampleSelect.addEventListener("change", () => {
    const id = exampleSelect.value;
    if (!id || !bundle) return;
    const next = projectFromBundle(bundle, id);
    if (!next) {
      info(`Could not load example ${id}.`);
      return;
    }
    void startProject(next);
  });

  byId<HTMLButtonElement>("scratch").addEventListener("click", () => {
    clearSavedProject();
    void startProject(scratchProject());
  });

  byId<HTMLButtonElement>("download-zip").addEventListener("click", () => {
    downloadProject(project);
  });
  byId<HTMLButtonElement>("import-zip").addEventListener("click", () => {
    zipInput.click();
  });
  zipInput.addEventListener("change", async () => {
    const file = zipInput.files?.[0];
    zipInput.value = "";
    if (!file) return;
    try {
      const imported = await importProject(file);
      await startProject(imported);
    } catch (error) {
      info(`Could not import the archive: ${String(error)}`);
    }
  });
}
void main();
