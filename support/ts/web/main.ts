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
  loadProjectRecord,
  projectFromBundle,
  saveProject,
  scratchProject,
  setFileText,
  type Project,
  type WorkspaceDescriptor,
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
import {
  WorkspaceError,
  WorkspaceSession,
  virtualWorkspace,
  readOnlyWorkspace,
  workspaceMessage,
  type Workspace,
  type WorkspaceKind,
} from "./workspace";
import {
  directoryPickerSupported,
  openDirectoryProject,
  readDirectoryHandle,
  type DirectoryHandle,
} from "./workspace-directory";
import { openMemoryFolder } from "./workspace-memory";
import {
  loadDirectoryHandle,
  storeDirectoryHandle,
} from "./workspace-storage";

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
const processAllButton = byId<HTMLButtonElement>("process-all");
const stopButton = byId<HTMLButtonElement>("stop");
const resetButton = byId<HTMLButtonElement>("reset");
const addFileButton = byId<HTMLButtonElement>("add-file");
const renameFileButton = byId<HTMLButtonElement>("rename-file");
const deleteFileButton = byId<HTMLButtonElement>("delete-file");
const setRootButton = byId<HTMLButtonElement>("set-root");
const openFolderButton = byId<HTMLButtonElement>("open-folder");
const saveFileButton = byId<HTMLButtonElement>("save-file");
const saveAllButton = byId<HTMLButtonElement>("save-all");
const reconnectFolderButton = byId<HTMLButtonElement>("reconnect-folder");
const workspaceName = byId<HTMLSpanElement>("workspace-name");
const folderInput = byId<HTMLInputElement>("folder-input");
const sidebarTitle = byId<HTMLElement>("sidebar-title");
const settingsButton = byId<HTMLButtonElement>("settings");
const settingsDialog = byId<HTMLDialogElement>("settings-dialog");
const themeToggle = byId<HTMLInputElement>("theme-toggle");
const THEME_KEY = "abella.web.v1.theme";
const layout = document.querySelector(".layout") as HTMLElement;
const sidebar = byId<HTMLElement>("sidebar");
const splitter = byId<HTMLDivElement>("sidebar-splitter");
const SIDEBAR_KEY = "abella.web.v1.sidebar";
const DEFAULT_SIDEBAR_WIDTH = 224;
const MIN_SIDEBAR_WIDTH = 150;
const COLLAPSE_THRESHOLD = 100;

const savedProject = loadProjectRecord();
let project: Project = savedProject?.project ?? scratchProject();
let savedWorkspace: WorkspaceDescriptor | undefined =
  savedProject?.workspace;
let bundle: Bundle | undefined;
let editor: EditorManager;
let session: Session;
let lastDirectoryHandle: DirectoryHandle | undefined;
let measureTimer: number | undefined;
let saveWarningShown = false;
let saving = false;

function initialWorkspaceFor(
  project: Project,
  descriptor?: WorkspaceDescriptor
): Workspace {
  if (!descriptor || descriptor.kind === "virtual") {
    return virtualWorkspace(project);
  }
  const kind = descriptor.kind as WorkspaceKind;
  const name = descriptor.name || "Folder";
  return readOnlyWorkspace(kind, name, project);
}

let workspaceSession = new WorkspaceSession(
  project,
  initialWorkspaceFor(project, savedWorkspace),
  { persist: persistProject }
);

type Theme = "light" | "dark";

function loadTheme(): Theme {
  try {
    const saved = localStorage.getItem(THEME_KEY);
    if (saved === "dark" || saved === "light") return saved;
  } catch {
    // Fall through to the system preference.
  }
  return window.matchMedia("(prefers-color-scheme: dark)").matches
    ? "dark"
    : "light";
}

function applyTheme(theme: Theme, persist: boolean): void {
  document.documentElement.dataset.theme = theme;
  themeToggle.checked = theme === "dark";
  if (persist) {
    try {
      localStorage.setItem(THEME_KEY, theme);
    } catch {
      // Preferences are optional.
    }
  }
}
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

function persistProject(project: Project, workspace: Workspace): void {
  const error = saveProject(project, {
    kind: workspace.kind,
    name: workspace.name,
  });
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
  workspaceSession.schedulePersist();
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

function workspaceLabel(session: WorkspaceSession): string {
  if (session.kind === "virtual") return "Virtual project";
  if (session.kind === "directory") {
    return session.capabilities.write
      ? `Folder: ${session.name}`
      : `Read-only copy: ${session.name}`;
  }
  if (session.kind === "memory") {
    return `Read-only folder: ${session.name}`;
  }
  return `${session.kind}: ${session.name}`;
}

function updateWorkspaceUi(): void {
  const capabilities = workspaceSession.capabilities;
  const explicitSave = capabilities.write && !capabilities.autoSave;
  const picker = directoryPickerSupported();
  openFolderButton.hidden = false;
  openFolderButton.textContent = picker
    ? "Open folder"
    : "Open folder (read-only)";
  openFolderButton.title = picker
    ? "Open a local folder"
    : "Open a folder read-only; use Download zip to keep changes";
  saveFileButton.hidden = !explicitSave;
  saveAllButton.hidden = !explicitSave;
  saveFileButton.disabled =
    saving || !explicitSave || !workspaceSession.isDirty(project.active);
  saveAllButton.disabled =
    saving || !explicitSave || !workspaceSession.hasDirty();
  if (explicitSave) {
    saveFileButton.title = workspaceSession.isDirty(project.active)
      ? `Save ${project.active}`
      : "No unsaved changes in this file";
    saveAllButton.title = workspaceSession.hasDirty()
      ? "Save all changed files"
      : "No unsaved changes";
  } else {
    saveFileButton.removeAttribute("title");
    saveAllButton.removeAttribute("title");
  }
  workspaceName.textContent = workspaceLabel(workspaceSession);
  workspaceName.title = workspaceSession.name;
  reconnectFolderButton.hidden = !workspaceSession.isDetachedDirectory;
  reconnectFolderButton.disabled = !lastDirectoryHandle;
  reconnectFolderButton.title = lastDirectoryHandle
    ? "Reconnect to the saved folder"
    : "No saved folder handle; use Open folder";
  sidebarTitle.textContent = "Project";
  sidebarTitle.title = "";
}

function confirmDiscardWorkspaceChanges(): boolean {
  if (!workspaceSession.hasDirty()) return true;
  return window.confirm(
    `Discard unsaved changes in ${workspaceSession.name}?`
  );
}

function confirmOverwrite(path: string): boolean {
  return window.confirm(
    `${path} changed on disk since it was opened. ` +
      "Overwrite it with the browser copy?"
  );
}

async function savePath(path: string): Promise<void> {
  if (
    saving ||
    !workspaceSession.capabilities.write ||
    workspaceSession.capabilities.autoSave
  ) {
    return;
  }
  const file = project.files.get(path);
  if (!file) return;
  saving = true;
  updateWorkspaceUi();
  try {
    const result = await workspaceSession.save(path, file.text);
    if (result === "saved") {
      info(`Saved ${path}.`);
    } else {
      info(`Save cancelled for ${path}.`);
    }
  } catch (error) {
    appendEntries([
      {
        severity: "error",
        message: `Could not save ${path}: ${workspaceMessage(error)}`,
      },
    ]);
  } finally {
    saving = false;
    refreshFiles();
  }
}

async function saveAll(): Promise<void> {
  if (
    saving ||
    !workspaceSession.capabilities.write ||
    workspaceSession.capabilities.autoSave
  ) {
    return;
  }
  const paths = workspaceSession.dirtyPaths();
  if (paths.length === 0) return;
  saving = true;
  updateWorkspaceUi();
  try {
    const report = await workspaceSession.saveAll(
      paths,
      (path) => project.files.get(path)?.text
    );
    for (const failure of report.failures) {
      appendEntries([
        {
          severity: "error",
          message: `Could not save ${failure.path}: ${failure.message}`,
        },
      ]);
    }
    if (report.saved > 0) {
      info(`Saved ${report.saved} file${report.saved === 1 ? "" : "s"}.`);
    }
    if (report.cancelled > 0) {
      info(
        `Left ${report.cancelled} changed file` +
          `${report.cancelled === 1 ? "" : "s"} unsaved.`
      );
    }
  } finally {
    saving = false;
    refreshFiles();
  }
}

async function openFolder(): Promise<void> {
  if (!directoryPickerSupported()) {
    folderInput.click();
    return;
  }
  try {
    const opened = await openDirectoryProject(
      (folderName) => {
        const message = workspaceSession.hasDirty()
          ? `Discard unsaved changes in ${workspaceSession.name} ` +
            `and replace the project with ${folderName}?`
          : `Replace the current project with the folder ${folderName}?`;
        return window.confirm(message);
      },
      confirmOverwrite
    );
    if (!opened) return;
    lastDirectoryHandle = opened.workspace.handle;
    const stored = await storeDirectoryHandle(opened.workspace.handle);
    await startProject(opened.project, opened.workspace);
    info(
      `Opened folder ${opened.workspace.name} ` +
        `(${opened.project.files.size} files).`
    );
    if (!stored) {
      info(
        "Warning: this browser could not remember the folder for reload."
      );
    }
    if (opened.truncated) {
      appendEntries([
        {
          severity: "info",
          message:
            "Warning: the folder was truncated at the file limit; " +
            "not every file was loaded.",
        },
      ]);
    }
    if (opened.skipped > 0) {
      appendEntries([
        {
          severity: "info",
          message:
            `Warning: skipped ${opened.skipped} file` +
            `${opened.skipped === 1 ? "" : "s"} that were too large ` +
            "or unreadable.",
        },
      ]);
    }
  } catch (error) {
    appendEntries([
      {
        severity: "error",
        message: `Could not open the folder: ${workspaceMessage(error)}`,
      },
    ]);
  }
}

async function openReadOnlyFolder(): Promise<void> {
  const files = folderInput.files ? Array.from(folderInput.files) : [];
  folderInput.value = "";
  if (files.length === 0) return;
  const message = workspaceSession.hasDirty()
    ? `Discard unsaved changes in ${workspaceSession.name} ` +
      "and replace the project with the selected read-only folder?"
    : "Replace the current project with the selected read-only folder?";
  if (!window.confirm(message)) return;
  try {
    const opened = await openMemoryFolder(files);
    await startProject(opened.project, opened.workspace);
    info(
      `Opened read-only folder ${opened.workspace.name} ` +
        `(${opened.project.files.size} files).`
    );
    if (opened.skipped > 0) {
      appendEntries([
        {
          severity: "info",
          message:
            `Warning: skipped ${opened.skipped} file` +
            `${opened.skipped === 1 ? "" : "s"} that were too large ` +
            "or unsupported.",
        },
      ]);
    }
  } catch (error) {
    appendEntries([
      {
        severity: "error",
        message: `Could not open the folder: ${workspaceMessage(error)}`,
      },
    ]);
  }
}

async function reconnectFolder(): Promise<void> {
  if (!workspaceSession.isDetachedDirectory) return;
  if (!lastDirectoryHandle) {
    appendEntries([
      {
        severity: "error",
        message:
          "No saved folder handle was found. Use Open folder to pick it again.",
      },
    ]);
    return;
  }
  try {
    const opened = await readDirectoryHandle(
      lastDirectoryHandle,
      confirmOverwrite,
      (folderName) => {
        const message = workspaceSession.hasDirty()
          ? `Discard unsaved changes in ${workspaceSession.name} ` +
            `and reconnect to ${folderName}?`
          : `Reconnect to the folder ${folderName}?`;
        return window.confirm(message);
      }
    );
    await startProject(opened.project, opened.workspace);
    info(`Reconnected to ${opened.workspace.name}.`);
  } catch (error) {
    if (error instanceof WorkspaceError && error.code === "cancelled") return;
    appendEntries([
      {
        severity: "error",
        message: `Could not reconnect the folder: ${workspaceMessage(error)}`,
      },
    ]);
  }
}

function refreshFiles(): void {
  renderFiles(
    fileList,
    project,
    project.active,
    openFile,
    workspaceSession.dirtyPaths()
  );
  const active = project.files.get(project.active);
  const structural = workspaceSession.capabilities.structural;
  addFileButton.disabled = !structural;
  renameFileButton.disabled = !structural || !active;
  deleteFileButton.disabled = !structural || !active;
  setRootButton.disabled =
    !active ||
    !project.active.endsWith(".thm") ||
    project.active === project.root;
  const note = structural
    ? ""
    : "File actions are not available for this workspace.";
  addFileButton.title = note;
  renameFileButton.title = note;
  deleteFileButton.title = note;
  updateWorkspaceUi();
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
  if (!workspaceSession.capabilities.structural) return;
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
  workspaceSession.persistNow();
}

function renameFile(): void {
  if (!workspaceSession.capabilities.structural) return;
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
  workspaceSession.persistNow();
}

function deleteFile(): void {
  if (!workspaceSession.capabilities.structural) return;
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
  workspaceSession.persistNow();
}

function setRoot(): void {
  const path = project.active;
  if (!path.endsWith(".thm") || path === project.root) return;
  editor.setProcessedTip(project.root, 0);
  project.root = path;
  refreshFiles();
  projectStructureChanged();
  workspaceSession.persistNow();
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

async function startProject(
  next: Project,
  workspace: Workspace
): Promise<void> {
  workspaceSession.close();
  workspaceSession = new WorkspaceSession(next, workspace, {
    persist: persistProject,
  });
  project = workspaceSession.project;
  clearOutput();
  lastGoalState = undefined;
  currentOutcome = undefined;
  renderGoal();
  editor.reset();
  refreshFiles();
  openFile(project.active);
  session.setProject(project);
  workspaceSession.schedulePersist();
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
      workspaceSession.markDirty(path);
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
  if (workspaceSession.isDetachedDirectory) {
    try {
      lastDirectoryHandle = await loadDirectoryHandle();
    } catch {
      lastDirectoryHandle = undefined;
    }
  }
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
  workspaceSession.schedulePersist();
  setStatus("idle");
  try {
    await session.init();
  } catch (error) {
    setStatus("error", String(error));
  }

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
  openFolderButton.addEventListener("click", () => void openFolder());
  reconnectFolderButton.addEventListener(
    "click",
    () => void reconnectFolder()
  );
  saveFileButton.addEventListener("click", () => void savePath(project.active));
  saveAllButton.addEventListener("click", () => void saveAll());
  folderInput.addEventListener("change", () => void openReadOnlyFolder());
  window.addEventListener("beforeunload", (event) => {
    if (!workspaceSession.hasDirty()) return;
    event.preventDefault();
    event.returnValue = "";
  });
  settingsButton.addEventListener("click", () => {
    themeToggle.checked =
      document.documentElement.dataset.theme === "dark";
    settingsDialog.showModal();
  });
  themeToggle.addEventListener("change", () => {
    applyTheme(themeToggle.checked ? "dark" : "light", true);
  });
  settingsDialog.addEventListener("click", (event) => {
    if (event.target === settingsDialog) settingsDialog.close();
  });

  exampleSelect.addEventListener("change", () => {
    const id = exampleSelect.value;
    if (!id || !bundle) return;
    if (!confirmDiscardWorkspaceChanges()) {
      exampleSelect.value = "";
      return;
    }
    const next = projectFromBundle(bundle, id);
    if (!next) {
      appendEntries([
        { severity: "error", message: `Could not load example ${id}.` },
      ]);
      return;
    }
    void startProject(next, virtualWorkspace(next));
  });

  byId<HTMLButtonElement>("scratch").addEventListener("click", () => {
    const message = workspaceSession.hasDirty()
      ? `Discard unsaved changes in ${workspaceSession.name} ` +
        "and start from scratch?"
      : "Discard the current project and start from scratch?";
    if (!window.confirm(message)) {
      return;
    }
    clearSavedProject();
    lastDirectoryHandle = undefined;
    const next = scratchProject();
    void startProject(next, virtualWorkspace(next));
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
      const message = workspaceSession.hasDirty()
        ? "Replace the current project with this archive? " +
          "Unsaved changes will be lost."
        : "Replace the current project with this archive?";
      if (!window.confirm(message)) {
        return;
      }
      await startProject(imported, virtualWorkspace(imported));
    } catch (error) {
      appendEntries([
        {
          severity: "error",
          message: `Could not import the archive: ${workspaceMessage(error)}`,
        },
      ]);
    }
  });
}
applyTheme(loadTheme(), false);
void main();
