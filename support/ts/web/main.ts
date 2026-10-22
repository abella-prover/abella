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
let sidebarWidth = DEFAULT_SIDEBAR_WIDTH;
let sidebarCollapsed = false;

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
