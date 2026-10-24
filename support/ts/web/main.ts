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
import { OutputLog } from "./output-log";
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
  type OutputLocation,
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
  GitHubWorkspace,
  loadGitHubRepository,
  parseGitHubInput,
} from "./workspace-github";
import {
  clearGitHubToken,
  loadGitHubToken,
  loadGitHubTokenMeta,
  saveGitHubToken,
  saveGitHubTokenMeta,
} from "./github-auth";
import {
  createOAuthRequest,
  exchangeGitHubCode,
  fetchGitHubOAuthConfig,
  validateGitHubToken,
  type GitHubOAuthConfig,
  type GitHubOAuthScope,
} from "./github-oauth";
import { GITHUB_OAUTH_WORKER } from "./github-oauth-config";
import { isOAuthCallback } from "./oauth-callback";
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
const goalTab = byId<HTMLButtonElement>("goal-tab");
const outputTab = byId<HTMLButtonElement>("output-tab");
const outputCountBadge = byId<HTMLElement>("output-count");
const outputErrorBadge = byId<HTMLElement>("output-error");
const panelTabs = document.querySelector(".panel-tabs") as HTMLElement;
const exampleSelect = byId<HTMLSelectElement>("example-select");
const zipInput = byId<HTMLInputElement>("zip-input");
const processCursorButton = byId<HTMLButtonElement>("process-cursor");
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
const githubButton = byId<HTMLButtonElement>("github");
const commitButton = byId<HTMLButtonElement>("commit");
const githubDialog = byId<HTMLDialogElement>("github-dialog");
const githubForm = byId<HTMLFormElement>("github-form");
const githubTitle = byId<HTMLElement>("github-title");
const githubRepoField = byId<HTMLElement>("github-repo-field");
const githubRepoInput = byId<HTMLInputElement>("github-repo");
const githubTokenInput = byId<HTMLInputElement>("github-token");
const githubOAuthSection = byId<HTMLElement>("github-oauth-section");
const githubLoadButton = byId<HTMLButtonElement>("github-load");
const githubOAuthButton = byId<HTMLButtonElement>("github-oauth");
const githubPrivateCheckbox = byId<HTMLInputElement>("github-private");
const githubPatDetails = byId<HTMLDetailsElement>("github-pat");
const githubStatus = byId<HTMLElement>("github-status");
const githubRevokeRow = byId<HTMLElement>("github-revoke-row");
const githubRevokeLink = byId<HTMLAnchorElement>("github-revoke");
const githubReconnectPrivateButton =
  byId<HTMLButtonElement>("github-reconnect-private");
const githubNote = byId<HTMLElement>("github-note");
const githubError = byId<HTMLElement>("github-error");
const githubSubmitButton = byId<HTMLButtonElement>("github-submit");
const githubDisconnectButton = byId<HTMLButtonElement>("github-disconnect");
const githubCloseButton = byId<HTMLButtonElement>("github-close");
const commitDialog = byId<HTMLDialogElement>("commit-dialog");
const commitForm = byId<HTMLFormElement>("commit-form");
const commitMessageInput = byId<HTMLTextAreaElement>("commit-message");
const commitNote = byId<HTMLElement>("commit-note");
const commitError = byId<HTMLElement>("commit-error");
const commitSubmitButton = byId<HTMLButtonElement>("commit-submit");
const commitCancelButton = byId<HTMLButtonElement>("commit-cancel");
const commitCloseButton = byId<HTMLButtonElement>("commit-close");
const sidebarTitle = byId<HTMLElement>("sidebar-title");
const settingsButton = byId<HTMLButtonElement>("settings");
const settingsDialog = byId<HTMLDialogElement>("settings-dialog");
const helpButton = byId<HTMLButtonElement>("help");
const helpDialog = byId<HTMLDialogElement>("help-dialog");
const themeToggle = byId<HTMLInputElement>("theme-toggle");
const THEME_KEY = "abella.web.v1.theme";
const layout = document.querySelector(".layout") as HTMLElement;
const panelsElement = document.querySelector(".panels") as HTMLElement;
const sidebar = byId<HTMLElement>("sidebar");
const splitter = byId<HTMLDivElement>("sidebar-splitter");
const panelSplitter = byId<HTMLDivElement>("panel-splitter");
const SIDEBAR_KEY = "abella.web.v1.sidebar";
const PANEL_KEY = "abella.web.v1.panels";
const DEFAULT_SIDEBAR_WIDTH = 224;
const MIN_SIDEBAR_WIDTH = 150;
const COLLAPSE_THRESHOLD = 100;
const MIN_PANEL_HEIGHT = 128;
const EDITOR_MIN_HEIGHT = 160;

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

type OAuthConfigState = "unknown" | "loading" | "ready" | "unavailable";

interface PendingOAuth {
  state: string;
  verifier: string;
  popup: Window;
  intent: "connect" | "commit";
  repoInput?: string;
  commitMessage?: string;
  requestedScope: GitHubOAuthScope;
  createdAt: number;
  messageReceived: boolean;
  cancelled: boolean;
  timeoutTimer: number;
  closeTimer: number;
}

const savedGitHubMeta = loadGitHubTokenMeta();
let githubToken = loadGitHubToken();
let githubScope = savedGitHubMeta.scope;
let githubLogin = savedGitHubMeta.login;
let githubDialogMode: "connect" | "commit" = "connect";
let pendingCommitMessage: string | undefined;
let oauthConfigState: OAuthConfigState = "unknown";
let oauthConfig: GitHubOAuthConfig | undefined;
let oauthConfigPromise: Promise<void> | undefined;
let pendingOAuth: PendingOAuth | undefined;
let oauthBusy = false;
let oauthStatus: string | undefined;
let oauthStartId = 0;
let githubBusy = false;
const OAUTH_FLOW_TIMEOUT_MS = 10 * 60 * 1000;
const GITHUB_INPUT_KEY = "abella.web.v1.github.input";
let lastGitHubInput = loadLastGitHubInput();

function loadLastGitHubInput(): string {
  try {
    return localStorage.getItem(GITHUB_INPUT_KEY) ?? "";
  } catch {
    return "";
  }
}

function saveLastGitHubInput(input: string): void {
  try {
    localStorage.setItem(GITHUB_INPUT_KEY, input);
  } catch {
    // Preferences are optional.
  }
}

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
const outputLog = new OutputLog();
let outputCount = 0;
let outputHasError = false;
let activePanel: "goal" | "output" = "goal";
let panelHeight: number | undefined;

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

function maxPanelHeight(): number {
  return Math.max(
    MIN_PANEL_HEIGHT,
    layout.clientHeight - EDITOR_MIN_HEIGHT
  );
}

function defaultPanelHeight(): number {
  return Math.max(
    MIN_PANEL_HEIGHT,
    Math.round(window.innerHeight * 0.28)
  );
}

function loadPanelHeight(): number | undefined {
  try {
    const raw = localStorage.getItem(PANEL_KEY);
    if (!raw) return undefined;
    const value = Number(raw);
    return Number.isFinite(value) ? value : undefined;
  } catch {
    return undefined;
  }
}

function renderPanelHeight(height: number | undefined): void {
  if (height === undefined) {
    panelHeight = undefined;
    layout.style.removeProperty("--panel-height");
  } else {
    panelHeight = Math.max(
      MIN_PANEL_HEIGHT,
      Math.min(height, maxPanelHeight())
    );
    layout.style.setProperty("--panel-height", `${panelHeight}px`);
  }
  const shown = Math.round(panelHeight ?? defaultPanelHeight());
  panelSplitter.setAttribute(
    "aria-valuemax",
    String(Math.round(maxPanelHeight()))
  );
  panelSplitter.setAttribute("aria-valuenow", String(shown));
  panelSplitter.setAttribute("aria-valuetext", `${shown} pixels`);
  scheduleMeasure();
}

function savePanelHeight(): void {
  if (panelHeight === undefined) return;
  try {
    localStorage.setItem(PANEL_KEY, String(Math.round(panelHeight)));
  } catch {
    // Persistence is optional.
  }
}

function installPanelSplitter(): void {
  let dragging = false;
  let startY = 0;
  let startHeight = 0;
  let lastHeight = 0;

  const finish = (): void => {
    if (!dragging) return;
    dragging = false;
    layout.classList.remove("resizing");
    panelSplitter.classList.remove("dragging");
    document.body.classList.remove("resizing-row");
    renderPanelHeight(lastHeight);
    savePanelHeight();
  };

  panelSplitter.addEventListener("pointerdown", (event) => {
    if (event.button !== 0) return;
    dragging = true;
    startY = event.clientY;
    startHeight = panelsElement.getBoundingClientRect().height;
    lastHeight = startHeight;
    layout.classList.add("resizing");
    panelSplitter.classList.add("dragging");
    document.body.classList.add("resizing-row");
    panelSplitter.setPointerCapture(event.pointerId);
    event.preventDefault();
  });

  panelSplitter.addEventListener("pointermove", (event) => {
    if (!dragging) return;
    lastHeight = startHeight - (event.clientY - startY);
    renderPanelHeight(lastHeight);
  });

  panelSplitter.addEventListener("pointerup", finish);
  panelSplitter.addEventListener("pointercancel", finish);
  panelSplitter.addEventListener("dblclick", () => {
    renderPanelHeight(undefined);
    try {
      localStorage.removeItem(PANEL_KEY);
    } catch {
      // Persistence is optional.
    }
  });

  panelSplitter.addEventListener("keydown", (event) => {
    const step = 16;
    const base = panelHeight ?? defaultPanelHeight();
    switch (event.key) {
      case "ArrowUp":
        event.preventDefault();
        renderPanelHeight(base + step);
        savePanelHeight();
        break;
      case "ArrowDown":
        event.preventDefault();
        renderPanelHeight(base - step);
        savePanelHeight();
        break;
      case "Home":
        event.preventDefault();
        renderPanelHeight(MIN_PANEL_HEIGHT);
        savePanelHeight();
        break;
      case "End":
        event.preventDefault();
        renderPanelHeight(maxPanelHeight());
        savePanelHeight();
        break;
      case "Enter":
      case " ":
        event.preventDefault();
        renderPanelHeight(undefined);
        try {
          localStorage.removeItem(PANEL_KEY);
        } catch {
          // Persistence is optional.
        }
        break;
    }
  });

  window.addEventListener("resize", () => {
    if (panelHeight !== undefined) {
      renderPanelHeight(panelHeight);
    } else {
      const shown = Math.round(defaultPanelHeight());
      panelSplitter.setAttribute(
        "aria-valuemax",
        String(Math.round(maxPanelHeight()))
      );
      panelSplitter.setAttribute("aria-valuenow", String(shown));
      panelSplitter.setAttribute("aria-valuetext", `${shown} pixels`);
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
  processCursorButton.disabled = busy;
  processAllButton.disabled = busy;
  resetButton.disabled = busy;
  stopButton.disabled = !busy;
  layout.setAttribute("aria-busy", busy ? "true" : "false");
  if (
    (status === "ok" || status === "error") &&
    window.matchMedia("(max-width: 900px)").matches
  ) {
    const target = activePanel === "output" ? outputPanel : goalPanel;
    window.requestAnimationFrame(() =>
      target.scrollIntoView({ block: "nearest", behavior: "smooth" })
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

function updateOutputTab(): void {
  outputCountBadge.textContent = String(outputCount);
  outputCountBadge.hidden = outputCount === 0;
  outputErrorBadge.hidden = !outputHasError;
  outputTab.dataset.error = String(outputHasError);
}

function jumpToOutput(from: number): void {
  if (editor.active !== project.root) openFile(project.root);
  editor.setCursor(project.root, from, true);
  editor.focus();
}

function renderOutput(): void {
  outputPanel.replaceChildren();
  appendOutput(
    outputPanel,
    outputLog.ordered.map((record) => ({
      entry: record.entry,
      from: record.location?.from,
    })),
    jumpToOutput
  );
  outputCount = outputLog.count;
  updateOutputTab();
}

function pruneOutput(tip: number): void {
  if (outputLog.prune(tip) === 0) return;
  if (!outputLog.hasError) outputHasError = false;
  renderOutput();
}

function selectPanel(panel: "goal" | "output", focus = false): void {
  activePanel = panel;
  const goalActive = panel === "goal";
  goalTab.setAttribute("aria-selected", String(goalActive));
  outputTab.setAttribute("aria-selected", String(!goalActive));
  goalTab.tabIndex = goalActive ? 0 : -1;
  outputTab.tabIndex = goalActive ? -1 : 0;
  goalPanel.hidden = !goalActive;
  outputPanel.hidden = goalActive;
  if (!goalActive) outputHasError = false;
  updateOutputTab();
  if (focus) (goalActive ? goalTab : outputTab).focus();
}

function clearOutput(): void {
  outputLog.clear();
  outputCount = 0;
  outputHasError = false;
  outputPanel.replaceChildren();
  selectPanel("goal");
}

function appendEntries(
  entries: OutputEntry[],
  location?: OutputLocation
): void {
  if (!location && entries.length === 0) return;
  outputLog.append(entries, location);
  const hasError = entries.some((entry) => entry.severity === "error");
  if (hasError && activePanel !== "output") {
    outputHasError = true;
  } else if (!outputLog.hasError) {
    outputHasError = false;
  }
  renderOutput();
}

function closeMenus(): void {
  for (const menu of document.querySelectorAll<HTMLDetailsElement>(
    ".menu[open]"
  )) {
    menu.open = false;
  }
}

function installMenus(): void {
  const menus = [
    ...document.querySelectorAll<HTMLDetailsElement>(".menu"),
  ];
  for (const menu of menus) {
    menu.addEventListener("toggle", () => {
      if (!menu.open) return;
      for (const other of menus) {
        if (other !== menu) other.open = false;
      }
    });
    menu.addEventListener("click", (event) => {
      if ((event.target as HTMLElement).closest("button")) menu.open = false;
    });
  }
  document.addEventListener("pointerdown", (event) => {
    if (!(event.target as HTMLElement).closest(".menu")) closeMenus();
  });
  document.addEventListener("keydown", (event) => {
    if (event.key !== "Escape") return;
    const open = document.querySelector<HTMLDetailsElement>(".menu[open]");
    if (!open) return;
    closeMenus();
    open.querySelector("summary")?.focus();
  });
}

function installTabs(): void {
  goalTab.addEventListener("click", () => selectPanel("goal"));
  outputTab.addEventListener("click", () => selectPanel("output"));
  panelTabs.addEventListener("keydown", (event) => {
    switch (event.key) {
      case "ArrowLeft":
      case "ArrowRight":
        event.preventDefault();
        selectPanel(activePanel === "goal" ? "output" : "goal", true);
        break;
      case "Home":
        event.preventDefault();
        selectPanel("goal", true);
        break;
      case "End":
        event.preventDefault();
        selectPanel("output", true);
        break;
    }
  });
}

function openHelp(): void {
  closeMenus();
  if (helpDialog.open) return;
  if (document.querySelector("dialog[open]")) return;
  helpDialog.showModal();
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
  if (session.kind === "github") {
    const label = session.capabilities.commit
      ? `GitHub: ${session.name}`
      : `Read-only GitHub: ${session.name}`;
    return githubLogin ? `${label} (${githubLogin})` : label;
  }
  return `${session.kind}: ${session.name}`;
}

function updateWorkspaceUi(): void {
  const capabilities = workspaceSession.capabilities;
  const explicitSave =
    capabilities.write && !capabilities.autoSave && !capabilities.commit;
  const showCommit = capabilities.commit;
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
  commitButton.hidden = !showCommit;
  commitButton.disabled =
    saving || !showCommit || !workspaceSession.hasDirty();
  githubButton.disabled = saving;
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
  commitButton.title = workspaceSession.hasDirty()
    ? "Commit changed files"
    : "No changes to commit";
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
    workspaceSession.capabilities.autoSave ||
    workspaceSession.capabilities.commit
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
    workspaceSession.capabilities.autoSave ||
    workspaceSession.capabilities.commit
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

function githubScopeIncludesPrivate(scope: string | undefined): boolean {
  if (!scope) return false;
  return scope.split(/[ ,]+/).includes("repo");
}

function githubNoteText(): string {
  if (githubToken) {
    const account = githubLogin
      ? ` Signed in as ${githubLogin}.`
      : "";
    const action =
      githubDialogMode === "commit"
        ? "Authorize commit"
        : "Load repository";
    return (
      `A token is saved for this tab.${account} ` +
      `Use ${action} to reuse it, or Disconnect to load ` +
      "without a token."
    );
  }
  if (oauthConfigState === "unavailable") {
    return (
      "GitHub sign-in is unavailable. Use a personal access token " +
      "below."
    );
  }
  if (githubDialogMode === "commit") {
    return (
      "Enter a fine-grained token with Contents: Read and write, or " +
      "sign in with GitHub."
    );
  }
  return (
    "Public repositories need no token. Private repositories need " +
    "Contents: Read."
  );
}

function syncGitHubDialogUi(): void {
  const unavailable = oauthConfigState === "unavailable";
  githubOAuthSection.hidden = unavailable;
  if (unavailable) githubPatDetails.open = true;
  githubRevokeRow.hidden = oauthConfig === undefined;
  if (oauthConfig !== undefined) {
    githubRevokeLink.href =
      "https://github.com/settings/connections/applications/" +
      encodeURIComponent(oauthConfig.clientId);
  }
  const busy = oauthBusy || pendingOAuth !== undefined || githubBusy;
  const ready = oauthConfigState === "ready";
  const hasToken = Boolean(githubToken);
  githubLoadButton.hidden = !hasToken;
  githubLoadButton.disabled = busy || !hasToken;
  githubLoadButton.textContent =
    githubDialogMode === "commit" ? "Authorize commit" : "Load repository";
  githubOAuthButton.textContent = hasToken
    ? "Reconnect with GitHub"
    : "Sign in with GitHub";
  githubOAuthButton.classList.toggle("primary-button", !hasToken);
  githubLoadButton.classList.toggle("primary-button", hasToken);
  githubOAuthButton.disabled = busy || !ready;
  githubPrivateCheckbox.disabled = busy || !ready;
  githubSubmitButton.disabled = busy;
  githubReconnectPrivateButton.disabled = busy || !ready;
  githubDisconnectButton.hidden = !hasToken;
  githubNote.textContent = githubNoteText();
  if (githubError.textContent !== "") {
    githubStatus.textContent = "";
  } else if (oauthStatus !== undefined) {
    githubStatus.textContent = oauthStatus;
  } else if (pendingOAuth !== undefined) {
    githubStatus.textContent = "Waiting for GitHub...";
  } else if (oauthConfigState === "unknown" || oauthConfigState === "loading") {
    githubStatus.textContent = "Checking GitHub sign-in...";
  } else if (githubToken && githubLogin) {
    githubStatus.textContent = `Signed in as ${githubLogin}.`;
  } else {
    githubStatus.textContent = "";
  }
}

function ensureOAuthConfig(): Promise<void> {
  if (oauthConfigState === "ready" || oauthConfigState === "unavailable") {
    return Promise.resolve();
  }
  if (oauthConfigPromise) return oauthConfigPromise;
  oauthConfigState = "loading";
  syncGitHubDialogUi();
  oauthConfigPromise = fetchGitHubOAuthConfig(GITHUB_OAUTH_WORKER)
    .then((config) => {
      oauthConfig = config;
      oauthConfigState = "ready";
    })
    .catch(() => {
      oauthConfig = undefined;
      oauthConfigState = "unavailable";
    })
    .finally(() => {
      oauthConfigPromise = undefined;
      if (githubDialog.open) syncGitHubDialogUi();
    });
  return oauthConfigPromise;
}

function setGitHubError(message: string): void {
  oauthStatus = undefined;
  githubError.textContent = message;
  githubStatus.textContent = "";
  githubReconnectPrivateButton.hidden = true;
  syncGitHubDialogUi();
}

function showGitHubError(error: unknown): void {
  if (error instanceof WorkspaceError && error.status === 401) {
    clearGitHubAuth();
  }
  setGitHubError(workspaceMessage(error));
}

function saveGitHubAuth(
  token: string,
  scope: string | undefined,
  login: string | undefined
): void {
  githubToken = token;
  githubScope = scope || undefined;
  githubLogin = login;
  saveGitHubToken(token);
  saveGitHubTokenMeta({ scope: githubScope, login });
  updateWorkspaceUi();
  syncGitHubDialogUi();
}

function clearGitHubAuth(): void {
  clearGitHubToken();
  githubToken = undefined;
  githubScope = undefined;
  githubLogin = undefined;
  const workspace = workspaceSession.workspace;
  if (workspace instanceof GitHubWorkspace) workspace.clearToken();
  githubTokenInput.value = "";
  githubPrivateCheckbox.checked = false;
  githubReconnectPrivateButton.hidden = true;
  updateWorkspaceUi();
  syncGitHubDialogUi();
}

function clearOAuthTimers(pending: PendingOAuth): void {
  window.clearTimeout(pending.timeoutTimer);
  window.clearInterval(pending.closeTimer);
}

function cancelOAuth(): void {
  const pending = pendingOAuth;
  pendingOAuth = undefined;
  if (pending !== undefined) pending.cancelled = true;
  oauthStartId++;
  oauthBusy = false;
  oauthStatus = undefined;
  if (pending !== undefined) {
    clearOAuthTimers(pending);
    try {
      pending.popup.close();
    } catch {
      // The popup is already closed.
    }
  }
  syncGitHubDialogUi();
}

function failOAuth(message: string): void {
  const pending = pendingOAuth;
  pendingOAuth = undefined;
  oauthStartId++;
  oauthBusy = false;
  oauthStatus = undefined;
  if (pending !== undefined) {
    pending.cancelled = true;
    clearOAuthTimers(pending);
    try {
      pending.popup.close();
    } catch {
      // The popup is already closed.
    }
  }
  setGitHubError(message);
}

function maybeOfferPrivateReconnect(
  error: unknown,
  intent: "connect" | "commit"
): void {
  if (intent !== "connect") return;
  if (oauthConfigState !== "ready" || !githubToken) return;
  if (githubScopeIncludesPrivate(githubScope)) return;
  if (!(error instanceof WorkspaceError) || error.code !== "not-found") {
    return;
  }
  githubReconnectPrivateButton.hidden = false;
  githubError.textContent =
    workspaceMessage(error) +
    " Reconnect with private repository access, or check the URL.";
}

async function loadGitHubConnect(
  input: string,
  token: string | undefined,
  login?: string
): Promise<void> {
  const opened = await loadGitHubRepository(input, token);
  lastGitHubInput = input;
  saveLastGitHubInput(input);
  await startProject(opened.project, opened.workspace);
  const account = opened.login ?? login;
  info(
    `Loaded GitHub repository ${opened.workspace.name}` +
      `${account ? ` as ${account}` : ""}.`
  );
  if (opened.truncated) {
    appendEntries([
      {
        severity: "info",
        message:
          "Warning: the repository tree was truncated; " +
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
          "or unsupported.",
      },
    ]);
  }
  githubDialog.close();
}

async function runGitHubIntent(
  token: string,
  scope: string,
  intent: "connect" | "commit"
): Promise<void> {
  githubError.textContent = "";
  githubStatus.textContent = "";
  oauthStatus = undefined;
  githubReconnectPrivateButton.hidden = true;
  if (intent === "commit") {
    if (!(workspaceSession.workspace instanceof GitHubWorkspace)) {
      setGitHubError("This project is not connected to GitHub.");
      return;
    }
  } else {
    const input = githubRepoInput.value.trim();
    if (!parseGitHubInput(input)) {
      setGitHubError(
        "Enter a GitHub URL such as https://github.com/owner/repo."
      );
      return;
    }
    if (
      workspaceSession.hasDirty() &&
      !window.confirm(
        `Discard unsaved changes in ${workspaceSession.name} ` +
          "and load a GitHub repository?"
      )
    ) {
      return;
    }
  }
  githubBusy = true;
  syncGitHubDialogUi();
  try {
    await applyGitHubToken(token, scope, intent);
  } catch (error) {
    showGitHubError(error);
    maybeOfferPrivateReconnect(error, intent);
  } finally {
    githubBusy = false;
    syncGitHubDialogUi();
  }
}

async function applyGitHubToken(
  token: string,
  scope: string,
  intent: "connect" | "commit"
): Promise<void> {
  if (intent === "commit") {
    const workspace = workspaceSession.workspace;
    if (!(workspace instanceof GitHubWorkspace)) {
      throw new WorkspaceError(
        "io",
        "This project is not connected to GitHub."
      );
    }
    const user = await workspace.authorize(token);
    saveGitHubAuth(token, scope, user.login);
    const message = pendingCommitMessage;
    pendingCommitMessage = undefined;
    githubDialog.close();
    info(`Signed in to GitHub as ${user.login}.`);
    if (message !== undefined) await performCommit(message);
    return;
  }
  const input = githubRepoInput.value.trim();
  const user = await validateGitHubToken(token);
  saveGitHubAuth(token, scope, user.login);
  if (!input) {
    oauthStatus =
      `Signed in as ${user.login}. Enter a repository to load.`;
    syncGitHubDialogUi();
    return;
  }
  if (!parseGitHubInput(input)) {
    oauthStatus =
      `Signed in as ${user.login}. Enter a valid repository URL.`;
    syncGitHubDialogUi();
    return;
  }
  await loadGitHubConnect(input, token, user.login);
}

async function startGitHubOAuth(
  intent: "connect" | "commit",
  options: { repoInput?: string; scope?: GitHubOAuthScope } = {}
): Promise<void> {
  if (oauthConfig === undefined) {
    setGitHubError(
      "GitHub sign-in is unavailable. Use a personal access token below."
    );
    githubPatDetails.open = true;
    return;
  }
  const repoInput =
    intent === "connect"
      ? (options.repoInput ?? githubRepoInput.value.trim()) || undefined
      : undefined;
  if (intent === "connect") {
    const ref =
      repoInput === undefined ? undefined : parseGitHubInput(repoInput);
    if (
      ref !== undefined &&
      workspaceSession.hasDirty() &&
      !window.confirm(
        `Discard unsaved changes in ${workspaceSession.name} ` +
          "and load a GitHub repository?"
      )
    ) {
      return;
    }
  } else if (!(workspaceSession.workspace instanceof GitHubWorkspace)) {
    setGitHubError("This project is not connected to GitHub.");
    return;
  }
  if (pendingOAuth !== undefined) cancelOAuth();
  githubReconnectPrivateButton.hidden = true;
  githubError.textContent = "";
  const scope =
    options.scope ??
    (githubPrivateCheckbox.checked ? "repo" : "public_repo");
  const startId = ++oauthStartId;
  const popup = window.open(
    "",
    "abella-github-oauth",
    "popup,width=520,height=640"
  );
  if (!popup) {
    setGitHubError("Allow popups for this site, or use a token below.");
    githubPatDetails.open = true;
    return;
  }
  oauthBusy = true;
  oauthStatus = "Waiting for GitHub...";
  syncGitHubDialogUi();
  let request: { state: string; verifier: string; url: string };
  try {
    request = await createOAuthRequest(oauthConfig, scope);
  } catch (error) {
    try {
      popup.close();
    } catch {
      // The popup is already closed.
    }
    if (startId === oauthStartId) {
      oauthBusy = false;
      oauthStatus = undefined;
      showGitHubError(error);
    }
    return;
  }
  if (startId !== oauthStartId) {
    try {
      popup.close();
    } catch {
      // The popup is already closed.
    }
    return;
  }
  try {
    popup.location.href = request.url;
  } catch {
    try {
      popup.close();
    } catch {
      // The popup is already closed.
    }
    oauthBusy = false;
    oauthStatus = undefined;
    setGitHubError(
      "Could not open the GitHub sign-in page. Try again."
    );
    return;
  }
  const pending: PendingOAuth = {
    state: request.state,
    verifier: request.verifier,
    popup,
    intent,
    repoInput,
    commitMessage:
      intent === "commit" ? pendingCommitMessage : undefined,
    requestedScope: scope,
    createdAt: Date.now(),
    messageReceived: false,
    cancelled: false,
    timeoutTimer: 0,
    closeTimer: 0,
  };
  pending.timeoutTimer = window.setTimeout(() => {
    if (pendingOAuth === pending) {
      failOAuth("GitHub sign-in timed out. Try again.");
    }
  }, OAUTH_FLOW_TIMEOUT_MS);
  pending.closeTimer = window.setInterval(() => {
    if (pendingOAuth !== pending || !pending.popup.closed) return;
    window.clearInterval(pending.closeTimer);
    pending.closeTimer = 0;
    window.setTimeout(() => {
      if (pendingOAuth === pending) {
        failOAuth("GitHub sign-in was cancelled.");
      }
    }, 500);
  }, 500);
  pendingOAuth = pending;
  oauthBusy = false;
  syncGitHubDialogUi();
}

function handleOAuthMessage(event: MessageEvent): void {
  const pending = pendingOAuth;
  if (pending === undefined || pending.messageReceived) return;
  if (event.origin !== window.location.origin) return;
  if (event.source !== pending.popup) return;
  const data = event.data;
  if (!isOAuthCallback(data)) return;
  if (data.state !== pending.state) {
    failOAuth("Sign-in state did not match. Try again.");
    return;
  }
  if (data.error !== undefined) {
    failOAuth(
      data.error === "access_denied"
        ? "GitHub sign-in was cancelled."
        : "GitHub sign-in failed. Try again."
    );
    return;
  }
  if (!data.code) {
    failOAuth("GitHub sign-in did not return a code. Try again.");
    return;
  }
  pending.messageReceived = true;
  clearOAuthTimers(pending);
  void completeOAuth(pending, data.code);
}

async function completeOAuth(
  pending: PendingOAuth,
  code: string
): Promise<void> {
  oauthBusy = true;
  oauthStatus = "Finishing GitHub sign-in...";
  syncGitHubDialogUi();
  try {
    const token = await exchangeGitHubCode(
      GITHUB_OAUTH_WORKER,
      code,
      pending.verifier
    );
    if (pendingOAuth !== pending || pending.cancelled) return;
    if (
      pending.requestedScope === "repo" &&
      !githubScopeIncludesPrivate(token.scope)
    ) {
      appendEntries([
        {
          severity: "info",
          message:
            "Warning: GitHub did not grant private repository access.",
        },
      ]);
    }
    if (pending.repoInput !== undefined) {
      githubRepoInput.value = pending.repoInput;
    }
    if (pending.commitMessage !== undefined) {
      pendingCommitMessage = pending.commitMessage;
    }
    await applyGitHubToken(token.token, token.scope, pending.intent);
  } catch (error) {
    if (pendingOAuth === pending && !pending.cancelled) {
      pendingOAuth = undefined;
      clearOAuthTimers(pending);
      try {
        pending.popup.close();
      } catch {
        // The popup is already closed.
      }
      showGitHubError(error);
      maybeOfferPrivateReconnect(error, pending.intent);
    }
  } finally {
    if (pendingOAuth === pending) {
      pendingOAuth = undefined;
      clearOAuthTimers(pending);
    }
    oauthBusy = false;
    if (oauthStatus === "Finishing GitHub sign-in...") {
      oauthStatus = undefined;
    }
    syncGitHubDialogUi();
  }
}

function openGitHubDialog(mode: "connect" | "commit"): void {
  if (pendingOAuth !== undefined) cancelOAuth();
  githubDialogMode = mode;
  githubTitle.textContent =
    mode === "commit" ? "Connect GitHub to commit" : "Load GitHub repository";
  githubRepoField.hidden = mode === "commit";
  githubSubmitButton.textContent =
    mode === "commit" ? "Authorize commit" : "Load repository";
  githubError.textContent = "";
  githubStatus.textContent = "";
  oauthStatus = undefined;
  githubTokenInput.value = "";
  githubPrivateCheckbox.checked = githubScopeIncludesPrivate(githubScope);
  githubReconnectPrivateButton.hidden = true;
  githubDisconnectButton.hidden = !githubToken;
  if (
    mode === "connect" &&
    githubRepoInput.value.trim() === "" &&
    lastGitHubInput !== ""
  ) {
    githubRepoInput.value = lastGitHubInput;
  }
  githubDialog.showModal();
  syncGitHubDialogUi();
  void ensureOAuthConfig();
}

async function handleGitHubSubmit(event: Event): Promise<void> {
  event.preventDefault();
  if (githubBusy || oauthBusy || pendingOAuth !== undefined) return;
  githubError.textContent = "";
  githubStatus.textContent = "";
  oauthStatus = undefined;
  githubReconnectPrivateButton.hidden = true;
  const enteredToken = githubTokenInput.value.trim();
  const token = enteredToken || githubToken;
  const intent = githubDialogMode;
  if (intent === "commit") {
    if (!(workspaceSession.workspace instanceof GitHubWorkspace)) {
      setGitHubError("This project is not connected to GitHub.");
      return;
    }
    if (!token) {
      setGitHubError(
        "Sign in with GitHub, or enter a fine-grained token with " +
          "Contents: Read and write."
      );
      return;
    }
    await runGitHubIntent(token, "", "commit");
    return;
  }
  const input = githubRepoInput.value.trim();
  if (!parseGitHubInput(input)) {
    setGitHubError(
      "Enter a GitHub URL such as https://github.com/owner/repo."
    );
    return;
  }
  if (token) {
    await runGitHubIntent(token, "", "connect");
    return;
  }
  if (
    workspaceSession.hasDirty() &&
    !window.confirm(
      `Discard unsaved changes in ${workspaceSession.name} ` +
        "and load a GitHub repository?"
    )
  ) {
    return;
  }
  githubBusy = true;
  syncGitHubDialogUi();
  try {
    await loadGitHubConnect(input, undefined);
  } catch (error) {
    showGitHubError(error);
  } finally {
    githubBusy = false;
    syncGitHubDialogUi();
  }
}

function disconnectGitHub(): void {
  clearGitHubAuth();
  githubError.textContent = "";
  githubStatus.textContent = "";
  oauthStatus = undefined;
  githubNote.textContent =
    "Disconnected. Public repositories can still be read.";
  info("Disconnected GitHub.");
}

function openCommitDialog(): void {
  if (!workspaceSession.capabilities.commit || !workspaceSession.hasDirty()) {
    return;
  }
  commitError.textContent = "";
  commitMessageInput.value = `Update ${project.root} from Abella Web`;
  commitNote.textContent =
    `${workspaceSession.dirtyPaths().length} changed file` +
    `${workspaceSession.dirtyPaths().length === 1 ? "" : "s"}.`;
  commitDialog.showModal();
  commitMessageInput.focus();
}

async function performCommit(message: string): Promise<void> {
  saving = true;
  updateWorkspaceUi();
  try {
    const result = await workspaceSession.commit(message);
    if (result.status === "committed") {
      info(`Committed ${result.revision.slice(0, 7)}.`);
    } else {
      appendEntries([{ severity: "error", message: result.message }]);
    }
  } catch (error) {
    if (error instanceof WorkspaceError && error.status === 401) {
      clearGitHubAuth();
    }
    appendEntries([
      {
        severity: "error",
        message: `Could not commit: ${workspaceMessage(error)}`,
      },
    ]);
    if (
      error instanceof WorkspaceError &&
      error.code === "permission-denied" &&
      workspaceSession.kind === "github"
    ) {
      pendingCommitMessage = message;
      openGitHubDialog("commit");
      setGitHubError(workspaceMessage(error));
    }
  } finally {
    saving = false;
    refreshFiles();
  }
}

async function handleCommitSubmit(event: Event): Promise<void> {
  event.preventDefault();
  const message = commitMessageInput.value.trim();
  if (message === "") {
    commitError.textContent = "Enter a commit message.";
    return;
  }
  commitSubmitButton.disabled = true;
  try {
    commitDialog.close();
    await performCommit(message);
  } finally {
    commitSubmitButton.disabled = false;
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
    pruneOutput(tip);
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
    appendEntries([{ severity: "error", message }], {
      from,
      position: from,
    });
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
        void session.notifyEdit(path, update.changes);
      }
      refreshFiles();
    },
    {
      process: () => void processToCursor(),
      stepForward: () => void stepForward(),
      stepBackward: () => void stepBackward(),
      jumpToTip: () => jumpToTip(),
      help: openHelp,
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
  renderPanelHeight(loadPanelHeight());
  installSplitter();
  installPanelSplitter();
  installMenus();
  installTabs();
  selectPanel("goal");
  byId<HTMLButtonElement>("sidebar-mobile-toggle").addEventListener(
    "click",
    toggleSidebar
  );
  helpButton.addEventListener("click", openHelp);
  helpDialog.addEventListener("click", (event) => {
    if (event.target === helpDialog) helpDialog.close();
  });
  document.addEventListener("keydown", (event) => {
    if (
      event.defaultPrevented ||
      !event.ctrlKey ||
      event.metaKey ||
      event.altKey ||
      event.key !== "?"
    ) {
      return;
    }
    event.preventDefault();
    openHelp();
  });
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

  processCursorButton.addEventListener(
    "click",
    () => void processToCursor()
  );
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
  githubButton.addEventListener("click", () => openGitHubDialog("connect"));
  githubForm.addEventListener("submit", (event) => {
    void handleGitHubSubmit(event);
  });
  githubLoadButton.addEventListener("click", () => {
    if (!githubToken) return;
    void runGitHubIntent(
      githubToken,
      githubScope ?? "",
      githubDialogMode
    );
  });
  githubOAuthButton.addEventListener("click", () => {
    void startGitHubOAuth(githubDialogMode);
  });
  githubReconnectPrivateButton.addEventListener("click", () => {
    githubPrivateCheckbox.checked = true;
    void startGitHubOAuth("connect", {
      repoInput: githubRepoInput.value.trim(),
      scope: "repo",
    });
  });
  window.addEventListener("message", handleOAuthMessage);
  githubCloseButton.addEventListener("click", () => githubDialog.close());
  githubDisconnectButton.addEventListener("click", disconnectGitHub);
  githubDialog.addEventListener("close", () => {
    if (pendingOAuth !== undefined) cancelOAuth();
    githubTokenInput.value = "";
    githubError.textContent = "";
    githubStatus.textContent = "";
    oauthStatus = undefined;
    githubReconnectPrivateButton.hidden = true;
    if (githubDialogMode === "commit") pendingCommitMessage = undefined;
  });
  commitButton.addEventListener("click", openCommitDialog);
  commitForm.addEventListener("submit", (event) => {
    void handleCommitSubmit(event);
  });
  commitCancelButton.addEventListener("click", () => commitDialog.close());
  commitCloseButton.addEventListener("click", () => commitDialog.close());
  commitDialog.addEventListener("close", () => {
    commitError.textContent = "";
  });
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
