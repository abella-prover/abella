// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { downloadProject, importProject } from "./archive";
import type { Command } from "./commands";
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
  classify,
  loadProject,
  projectFromBundle,
  saveProject,
  scratchProject,
  setFileText,
  type Project,
} from "./project";
import {
  Session,
  type OutputEntry,
  type ProofOutcome,
  type SessionEvents,
  type SessionStatus,
} from "./session";
import { appendOutput, renderSequent } from "./trace";
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
const outputPanel = byId<HTMLDivElement>("output");
const outputDisclosure = byId<HTMLDetailsElement>("output-disclosure");
const outputSummary = byId<HTMLElement>("output-summary");
const exampleSelect = byId<HTMLSelectElement>("example-select");
const zipInput = byId<HTMLInputElement>("zip-input");
const processButton = byId<HTMLButtonElement>("process");
const processAllButton = byId<HTMLButtonElement>("process-all");
const stopButton = byId<HTMLButtonElement>("stop");
const resetButton = byId<HTMLButtonElement>("reset");
const addFileButton = byId<HTMLButtonElement>("add-file");
const renameFileButton = byId<HTMLButtonElement>("rename-file");
const deleteFileButton = byId<HTMLButtonElement>("delete-file");
const setRootButton = byId<HTMLButtonElement>("set-root");
const layout = document.querySelector(".layout") as HTMLElement;
const sidebar = byId<HTMLElement>("sidebar");
const splitter = byId<HTMLDivElement>("sidebar-splitter");
const SIDEBAR_KEY = "abella.web.v1.sidebar";
const DEFAULT_SIDEBAR_WIDTH = 224;
const MIN_SIDEBAR_WIDTH = 150;
const COLLAPSE_THRESHOLD = 100;

let project: Project = loadProject() ?? scratchProject();
let bundle: Bundle | undefined;
let editor: EditorManager;
let session: Session;
let saveTimer: number | undefined;
let measureTimer: number | undefined;
let saveWarningShown = false;
let sidebarWidth = DEFAULT_SIDEBAR_WIDTH;
let sidebarCollapsed = false;
let lastGoalState: ProofState | undefined;
let currentOutcome: ProofOutcome | undefined;
let outputCount = 0;

interface SidebarPref {
  width: number;
  collapsed: boolean;
}

function loadSidebarPref(): SidebarPref {
  try {
    const raw = localStorage.getItem(SIDEBAR_KEY);
    if (raw === "closed") {
      return { width: DEFAULT_SIDEBAR_WIDTH, collapsed: true };
    }
    if (raw === "open") {
      return { width: DEFAULT_SIDEBAR_WIDTH, collapsed: false };
    }
    if (raw) {
      const parsed = JSON.parse(raw) as Partial<SidebarPref>;
      if (typeof parsed.width === "number") {
        return {
          width: parsed.width,
          collapsed: Boolean(parsed.collapsed),
        };
      }
    }
  } catch {
    // Fall through to the default.
  }
  return {
    width: DEFAULT_SIDEBAR_WIDTH,
    collapsed: window.matchMedia("(max-width: 900px)").matches,
  };
}

function maxSidebarWidth(): number {
  return Math.max(
    MIN_SIDEBAR_WIDTH,
    Math.min(window.innerWidth * 0.5, 560)
  );
}

function scheduleMeasure(): void {
  window.clearTimeout(measureTimer);
  measureTimer = window.setTimeout(() => editor?.requestMeasure(), 80);
}

function renderSidebar(collapsed: boolean, width: number): void {
  sidebarCollapsed = collapsed;
  if (!collapsed) {
    sidebarWidth = Math.max(
      MIN_SIDEBAR_WIDTH,
      Math.min(width, maxSidebarWidth())
    );
  }
  layout.style.setProperty(
    "--sidebar-width",
    collapsed ? "0px" : `${sidebarWidth}px`
  );
  layout.classList.toggle("sidebar-collapsed", collapsed);
  sidebar.toggleAttribute("inert", collapsed);
  sidebar.setAttribute("aria-hidden", String(collapsed));
  splitter.setAttribute(
    "aria-valuenow",
    collapsed ? "0" : String(Math.round(sidebarWidth))
  );
  splitter.setAttribute("aria-valuemax", String(Math.round(maxSidebarWidth())));
  splitter.setAttribute(
    "aria-valuetext",
    collapsed ? "collapsed" : `${Math.round(sidebarWidth)} pixels`
  );
  splitter.title = collapsed
    ? "Drag right or double-click to show the project sidebar"
    : "Drag to resize; drag far left or double-click to collapse";
  scheduleMeasure();
}

function saveSidebar(): void {
  try {
    localStorage.setItem(
      SIDEBAR_KEY,
      JSON.stringify({
        width: Math.round(sidebarWidth),
        collapsed: sidebarCollapsed,
      })
    );
  } catch {
    // Persistence is optional.
  }
}

function setSidebar(collapsed: boolean, width: number): void {
  renderSidebar(collapsed, width);
  saveSidebar();
}

function toggleSidebar(): void {
  setSidebar(!sidebarCollapsed, sidebarWidth);
}

function installSplitter(): void {
  let dragging = false;
  let startX = 0;
  let startWidth = 0;
  let lastWidth = 0;

  const finish = (): void => {
    if (!dragging) return;
    dragging = false;
    layout.classList.remove("resizing");
    splitter.classList.remove("dragging");
    document.body.classList.remove("resizing");
    if (lastWidth < COLLAPSE_THRESHOLD) {
      setSidebar(true, sidebarWidth);
    } else {
      setSidebar(false, Math.max(MIN_SIDEBAR_WIDTH, lastWidth));
    }
  };

  splitter.addEventListener("pointerdown", (event) => {
    if (event.button !== 0) return;
    dragging = true;
    startX = event.clientX;
    startWidth = sidebarCollapsed ? 0 : sidebarWidth;
    lastWidth = startWidth;
    layout.classList.add("resizing");
    splitter.classList.add("dragging");
    document.body.classList.add("resizing");
    splitter.setPointerCapture(event.pointerId);
    event.preventDefault();
  });

  splitter.addEventListener("pointermove", (event) => {
    if (!dragging) return;
    const raw = Math.max(
      0,
      Math.min(startWidth + event.clientX - startX, maxSidebarWidth())
    );
    lastWidth = raw;
    if (raw < COLLAPSE_THRESHOLD) {
      renderSidebar(true, sidebarWidth);
    } else {
      renderSidebar(false, raw);
    }
  });

  splitter.addEventListener("pointerup", finish);
  splitter.addEventListener("pointercancel", finish);
  splitter.addEventListener("dblclick", toggleSidebar);

  splitter.addEventListener("keydown", (event) => {
    const step = 16;
    switch (event.key) {
      case "ArrowLeft":
        event.preventDefault();
        if (sidebarCollapsed) {
          toggleSidebar();
        } else if (sidebarWidth - step < COLLAPSE_THRESHOLD) {
          setSidebar(true, sidebarWidth);
        } else {
          setSidebar(false, sidebarWidth - step);
        }
        break;
      case "ArrowRight": {
        event.preventDefault();
        const base = sidebarCollapsed
          ? Math.max(MIN_SIDEBAR_WIDTH, sidebarWidth)
          : sidebarWidth;
        setSidebar(false, base + step);
        break;
      }
      case "Home":
        event.preventDefault();
        setSidebar(true, sidebarWidth);
        break;
      case "End":
        event.preventDefault();
        setSidebar(false, maxSidebarWidth());
        break;
      case "Enter":
      case " ":
        event.preventDefault();
        toggleSidebar();
        break;
    }
  });

  window.addEventListener("resize", () => {
    if (!sidebarCollapsed) {
      renderSidebar(false, Math.min(sidebarWidth, maxSidebarWidth()));
    }
  });
}

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
  stopButton.disabled = !busy;
  layout.setAttribute("aria-busy", busy ? "true" : "false");
  if (
    (status === "ok" || status === "error") &&
    window.matchMedia("(max-width: 900px)").matches
  ) {
    window.requestAnimationFrame(() =>
      goalPanel.scrollIntoView({ block: "nearest", behavior: "smooth" })
    );
  }
}

function persistProject(): void {
  const error = saveProject(project);
  if (error) {
    if (!saveWarningShown) {
      saveWarningShown = true;
      appendEntries([{ severity: "error", message: `Warning: ${error}` }]);
    }
  } else {
    saveWarningShown = false;
  }
}

function scheduleSave(): void {
  window.clearTimeout(saveTimer);
  saveTimer = window.setTimeout(persistProject, 250);
}

function updateOutputSummary(): void {
  outputSummary.textContent = `Warnings and output (${outputCount})`;
}

function clearOutput(): void {
  outputCount = 0;
  outputPanel.replaceChildren();
  outputDisclosure.open = false;
  updateOutputSummary();
}

function appendEntries(entries: OutputEntry[], command?: Command): void {
  if (entries.length === 0) return;
  appendOutput(outputPanel, entries);
  outputCount += entries.length;
  updateOutputSummary();
  const autoOpen =
    entries.some(
      (entry) =>
        entry.severity === "error" || entry.message.startsWith("Warning")
    ) ||
    (command !== undefined && /^(Show|Query)\b/.test(command.text));
  if (autoOpen) outputDisclosure.open = true;
}

function info(message: string): void {
  appendEntries([{ severity: "info", message }]);
}

function refreshFiles(): void {
  renderFiles(fileList, project, project.active, openFile);
  const active = project.files.get(project.active);
  renameFileButton.disabled = !active;
  deleteFileButton.disabled = !active;
  setRootButton.disabled =
    !active ||
    !project.active.endsWith(".thm") ||
    project.active === project.root;
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

function normalizeNewPath(input: string | null): string | undefined {
  if (input === null) return undefined;
  const path = input.trim().replace(/\\/g, "/").replace(/^\.\//, "");
  if (
    path === "" ||
    path.startsWith("/") ||
    path.split("/").some((part) => part === "" || part === "." || part === "..")
  ) {
    return undefined;
  }
  return path;
}

function specName(path: string): string {
  const base = path.slice(path.lastIndexOf("/") + 1);
  return base.replace(/\.(sig|mod)$/, "");
}

function projectStructureChanged(): void {
  lastGoalState = undefined;
  currentOutcome = undefined;
  renderGoal();
  session.setProject(project);
  editor.clearDiagnostics(project.root);
}

function addFile(): void {
  const path = normalizeNewPath(
    window.prompt("New file path (for example helper.thm or notes.md):")
  );
  if (!path) return;
  if (project.files.has(path)) {
    window.alert(`A file named ${path} already exists.`);
    return;
  }
  const kind = classify(path);
  let text = "";
  if (path.endsWith(".sig")) {
    text = `sig ${specName(path)}.\n`;
  } else if (path.endsWith(".mod")) {
    text = `module ${specName(path)}.\n`;
  }
  project.files.set(path, { text, kind });
  openFile(path);
  if (kind === "abella") projectStructureChanged();
  persistProject();
}

function renameFile(): void {
  const from = project.active;
  const file = project.files.get(from);
  if (!file) return;
  const to = normalizeNewPath(window.prompt("Rename file to:", from));
  if (!to || to === from) return;
  if (from === project.root && !to.endsWith(".thm")) {
    window.alert("The root reasoning file must have a .thm extension.");
    return;
  }
  if (project.files.has(to)) {
    window.alert(`A file named ${to} already exists.`);
    return;
  }
  const nextKind = classify(to);
  project.files.delete(from);
  project.files.set(to, { text: file.text, kind: nextKind });
  if (project.root === from) project.root = to;
  if (project.active === from) project.active = to;
  if (file.kind === nextKind) {
    editor.rename(from, to);
  } else {
    editor.remove(from);
  }
  refreshFiles();
  if (file.kind !== nextKind) openFile(to);
  if (file.kind === "abella" || nextKind === "abella") {
    projectStructureChanged();
  }
  persistProject();
}

function deleteFile(): void {
  const path = project.active;
  const file = project.files.get(path);
  if (!file) return;
  let newRoot = project.root;
  if (path === project.root) {
    const candidate = [...project.files.keys()].find(
      (other) => other.endsWith(".thm") && other !== path
    );
    if (!candidate) {
      window.alert("Cannot delete the only .thm file in the project.");
      return;
    }
    if (
      !window.confirm(
        `Delete ${path} and make ${candidate} the root reasoning file?`
      )
    ) {
      return;
    }
    newRoot = candidate;
  } else if (!window.confirm(`Delete ${path}?`)) {
    return;
  }
  project.files.delete(path);
  editor.remove(path);
  project.root = newRoot;
  if (project.active === path) project.active = project.root;
  refreshFiles();
  openFile(project.active);
  if (file.kind === "abella") projectStructureChanged();
  persistProject();
}

function setRoot(): void {
  const path = project.active;
  if (!path.endsWith(".thm") || path === project.root) return;
  editor.setProcessedTip(project.root, 0);
  project.root = path;
  refreshFiles();
  projectStructureChanged();
  persistProject();
}

function renderGoal(): void {
  goalPanel.replaceChildren();
  if (lastGoalState) {
    goalPanel.append(renderSequent(lastGoalState));
  } else {
    const empty = document.createElement("div");
    empty.className = "goal-empty";
    empty.textContent = "No proof state yet.";
    goalPanel.append(empty);
  }
  if (currentOutcome) {
    const block = document.createElement("div");
    block.className = "goal-outcome";
    block.dataset.status = currentOutcome.status;
    block.setAttribute("role", "status");
    if (currentOutcome.theorem) {
      const theorem = document.createElement("div");
      theorem.className = "goal-outcome-theorem";
      theorem.textContent = `Theorem ${currentOutcome.theorem}`;
      block.append(theorem);
    }
    const message = document.createElement("div");
    message.className = "goal-outcome-message";
    message.textContent = currentOutcome.message;
    block.append(message);
    goalPanel.append(block);
  }
  goalPanel.scrollTop = goalPanel.scrollHeight;
}

function goal(state: ProofState | undefined): void {
  lastGoalState = state;
  renderGoal();
}

function outcome(value: ProofOutcome | undefined): void {
  currentOutcome = value;
  renderGoal();
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
  onOutcome: outcome,
  onOutput: appendEntries,
  onCursor(offset) {
    if (editor.active !== project.root) openFile(project.root);
    editor.setCursor(project.root, offset, true);
  },
  onResult(result, command) {
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
    appendEntries([{ severity: "error", message }]);
    errorDiagnostic(message, from, to);
  },
};

async function startProject(next: Project): Promise<void> {
  project = next;
  clearOutput();
  lastGoalState = undefined;
  currentOutcome = undefined;
  renderGoal();
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

function rootCursor(): number {
  if (editor.active !== project.root) {
    info(`Processing the root reasoning file ${project.root}.`);
    openFile(project.root);
  }
  return editor.cursorFor(project.root);
}

async function processToCursor(): Promise<void> {
  const cursor = rootCursor();
  await session.processTo(cursor);
}

async function stepForward(): Promise<void> {
  const cursor = rootCursor();
  await session.stepForward(cursor);
}

async function stepBackward(): Promise<void> {
  const cursor = rootCursor();
  await session.stepBackward(cursor);
}

function jumpToTip(): void {
  rootCursor();
  editor.setCursor(project.root, session.currentTip, true);
  editor.focus();
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
    {
      process: () => void processToCursor(),
      stepForward: () => void stepForward(),
      stepBackward: () => void stepBackward(),
      jumpToTip: () => jumpToTip(),
    }
  );

  const engine = await loadEngine();
  const driver = new WorkerDriver(engine, (module) =>
    setStatus("compiling", module)
  );
  session = new Session(driver, project, events);
  const pref = loadSidebarPref();
  renderSidebar(pref.collapsed, pref.width);
  installSplitter();
  byId<HTMLButtonElement>("sidebar-mobile-toggle").addEventListener(
    "click",
    toggleSidebar
  );
  document.addEventListener("keydown", (event) => {
    if (
      (event.ctrlKey || event.metaKey) &&
      event.key.toLowerCase() === "b" &&
      !(event.target as HTMLElement).closest("input, select, textarea")
    ) {
      event.preventDefault();
      toggleSidebar();
    }
  });

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

  processButton.addEventListener("click", () => void processToCursor());
  processAllButton.addEventListener("click", () => void session.processAll());
  stopButton.addEventListener("click", () => {
    session.stop();
    editor.clearDiagnostics(project.root);
    appendEntries([{ severity: "info", message: "Stopped." }]);
  });
  resetButton.addEventListener("click", () => {
    clearOutput();
    void session.reset();
  });
  addFileButton.addEventListener("click", addFile);
  renameFileButton.addEventListener("click", renameFile);
  deleteFileButton.addEventListener("click", deleteFile);
  setRootButton.addEventListener("click", setRoot);

  exampleSelect.addEventListener("change", () => {
    const id = exampleSelect.value;
    if (!id || !bundle) return;
    const next = projectFromBundle(bundle, id);
    if (!next) {
      appendEntries([
        { severity: "error", message: `Could not load example ${id}.` },
      ]);
      return;
    }
    void startProject(next);
  });

  byId<HTMLButtonElement>("scratch").addEventListener("click", () => {
    if (!window.confirm("Discard the current project and start from scratch?")) {
      return;
    }
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
      if (!window.confirm("Replace the current project with this archive?")) {
        return;
      }
      await startProject(imported);
    } catch (error) {
      appendEntries([
        { severity: "error", message: `Could not import the archive: ${String(error)}` },
      ]);
    }
  });
}
void main();
