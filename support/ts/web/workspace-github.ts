// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// GitHub workspace backend.  Octokit is loaded dynamically so it never
// enters the initial Abella Web bundle.

import { classify, type Project, type ProjectTextFile } from "./project";
import {
  MAX_FILE_BYTES,
  MAX_FILES,
  chooseRoot,
  isCandidateFile,
} from "./workspace-directory";
import {
  WorkspaceError,
  type CommitResult,
  type Workspace,
  type WorkspaceCapabilities,
  type WorkspaceFileEntry,
  type WorkspaceKind,
} from "./workspace";

type OctokitClient = import("@octokit/rest").Octokit;

const GITHUB_NAME = /^[A-Za-z0-9_.-]+$/;

const GITHUB_RESERVED = new Set([
  "issues",
  "pulls",
  "actions",
  "settings",
  "releases",
  "wiki",
  "commits",
  "network",
  "graphs",
  "archive",
  "raw",
  "blame",
  "edit",
  "find",
  "tags",
  "branches",
  "forks",
  "stargazers",
  "watchers",
  "discussions",
  "security",
  "projects",
  "pulse",
  "community",
  "apps",
]);

export interface GitHubRepoRef {
  owner: string;
  repo: string;
  branch?: string;
  path?: string;
}

export interface GitHubRepoInfo {
  defaultBranch: string;
  private?: boolean;
  canPush?: boolean;
}

export interface GitHubTreeEntry {
  path: string;
  type: string;
  sha: string;
  size?: number;
}

export interface GitHubTreeResult {
  sha: string;
  tree: GitHubTreeEntry[];
  truncated: boolean;
}

export interface GitHubTreeUpdate {
  path: string;
  mode: "100644";
  type: "blob";
  sha: string | null;
}

export interface GitHubApi {
  getRepo(owner: string, repo: string): Promise<GitHubRepoInfo>;
  getRef(
    owner: string,
    repo: string,
    branch: string
  ): Promise<{ sha: string }>;
  getTree(
    owner: string,
    repo: string,
    treeSha: string,
    recursive: boolean
  ): Promise<GitHubTreeResult>;
  getBlob(owner: string, repo: string, sha: string): Promise<string>;
  validateUser(): Promise<{ login: string }>;
  createBlob(
    owner: string,
    repo: string,
    content: string
  ): Promise<{ sha: string }>;
  createTree(
    owner: string,
    repo: string,
    baseTree: string,
    entries: GitHubTreeUpdate[]
  ): Promise<{ sha: string }>;
  createCommit(
    owner: string,
    repo: string,
    message: string,
    tree: string,
    parents: string[]
  ): Promise<{ sha: string }>;
  updateRef(
    owner: string,
    repo: string,
    branch: string,
    sha: string
  ): Promise<void>;
}

export type GitHubApiFactory = (token?: string) => Promise<GitHubApi>;

function decodeBase64(content: string): string {
  const binary = atob(content.replace(/\s/g, ""));
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return new TextDecoder().decode(bytes);
}

class OctokitApi implements GitHubApi {
  private octokit: OctokitClient;

  constructor(octokit: OctokitClient) {
    this.octokit = octokit;
  }

  async getRepo(owner: string, repo: string): Promise<GitHubRepoInfo> {
    const { data } = await this.octokit.rest.repos.get({ owner, repo });
    return {
      defaultBranch: data.default_branch,
      private: data.private,
      canPush: data.permissions?.push,
    };
  }

  async getRef(
    owner: string,
    repo: string,
    branch: string
  ): Promise<{ sha: string }> {
    const { data } = await this.octokit.rest.git.getRef({
      owner,
      repo,
      ref: `heads/${branch}`,
    });
    return { sha: data.object.sha };
  }

  async getTree(
    owner: string,
    repo: string,
    treeSha: string,
    recursive: boolean
  ): Promise<GitHubTreeResult> {
    const { data } = await this.octokit.rest.git.getTree({
      owner,
      repo,
      tree_sha: treeSha,
      recursive: recursive ? "1" : undefined,
    });
    return {
      sha: data.sha,
      tree: data.tree.map((entry) => ({
        path: entry.path,
        type: entry.type,
        sha: entry.sha,
        size: entry.size,
      })),
      truncated: data.truncated,
    };
  }

  async getBlob(owner: string, repo: string, sha: string): Promise<string> {
    const { data } = await this.octokit.rest.git.getBlob({
      owner,
      repo,
      file_sha: sha,
    });
    return data.encoding === "base64"
      ? decodeBase64(data.content)
      : data.content;
  }

  async validateUser(): Promise<{ login: string }> {
    const { data } = await this.octokit.rest.users.getAuthenticated();
    return { login: data.login };
  }

  async createBlob(
    owner: string,
    repo: string,
    content: string
  ): Promise<{ sha: string }> {
    const { data } = await this.octokit.rest.git.createBlob({
      owner,
      repo,
      content,
      encoding: "utf-8",
    });
    return { sha: data.sha };
  }

  async createTree(
    owner: string,
    repo: string,
    baseTree: string,
    entries: GitHubTreeUpdate[]
  ): Promise<{ sha: string }> {
    const { data } = await this.octokit.rest.git.createTree({
      owner,
      repo,
      base_tree: baseTree,
      tree: entries as never,
    });
    return { sha: data.sha };
  }

  async createCommit(
    owner: string,
    repo: string,
    message: string,
    tree: string,
    parents: string[]
  ): Promise<{ sha: string }> {
    const { data } = await this.octokit.rest.git.createCommit({
      owner,
      repo,
      message,
      tree,
      parents,
    });
    return { sha: data.sha };
  }

  async updateRef(
    owner: string,
    repo: string,
    branch: string,
    sha: string
  ): Promise<void> {
    await this.octokit.rest.git.updateRef({
      owner,
      repo,
      ref: `heads/${branch}`,
      sha,
      force: false,
    });
  }
}

export async function createGitHubApi(token?: string): Promise<GitHubApi> {
  const { Octokit } = await import("@octokit/rest");
  return new OctokitApi(new Octokit({ auth: token }));
}

function statusOf(error: unknown): number | undefined {
  if (typeof error !== "object" || error === null || !("status" in error)) {
    return undefined;
  }
  const status = (error as { status: unknown }).status;
  return typeof status === "number" ? status : undefined;
}

function headersOf(error: unknown): Record<string, string> {
  if (typeof error !== "object" || error === null || !("response" in error)) {
    return {};
  }
  const response = (error as { response: unknown }).response;
  if (typeof response !== "object" || response === null) return {};
  const headers = (response as { headers?: unknown }).headers;
  if (typeof headers !== "object" || headers === null) return {};
  return headers as Record<string, string>;
}

function errorMessage(error: unknown): string {
  if (error instanceof Error && error.message) return error.message;
  return String(error);
}

export function githubError(error: unknown, action: string): WorkspaceError {
  if (error instanceof WorkspaceError) return error;
  const status = statusOf(error);
  if (status === 401) {
    return new WorkspaceError(
      "permission-denied",
      "GitHub rejected the token. Reconnect GitHub and try again.",
      401
    );
  }
  if (status === 403) {
    if (headersOf(error)["x-ratelimit-remaining"] === "0") {
      const reset = headersOf(error)["x-ratelimit-reset"];
      let when = "";
      if (reset) {
        const date = new Date(Number(reset) * 1000);
        if (!Number.isNaN(date.getTime())) {
          when = ` Try again after ${date.toLocaleTimeString()}.`;
        }
      }
      return new WorkspaceError(
        "unavailable",
        `GitHub's rate limit was exceeded.${when} ` +
          "Connect a token for a higher limit.",
        403
      );
    }
    return new WorkspaceError(
      "permission-denied",
      "GitHub denied access. Check the token permissions and repository " +
        "access.",
      403
    );
  }
  if (status === 404) {
    return new WorkspaceError(
      "not-found",
      `GitHub could not find ${action}.`,
      404
    );
  }
  if (status === 422) {
    return new WorkspaceError(
      "conflict",
      "The branch moved on GitHub. Reload the repository and try again.",
      422
    );
  }
  return new WorkspaceError(
    "unavailable",
    `GitHub request failed while ${action}: ${errorMessage(error)}`,
    status
  );
}

export function parseGitHubInput(input: string): GitHubRepoRef | undefined {
  let raw = input.trim();
  if (raw === "") return undefined;
  if (raw.startsWith("github.com/")) raw = `https://${raw}`;

  if (/^https?:\/\//i.test(raw)) {
    let url: URL;
    try {
      url = new URL(raw);
    } catch {
      return undefined;
    }
    if (url.hostname !== "github.com" && url.hostname !== "www.github.com") {
      return undefined;
    }
    const parts = url.pathname
      .split("/")
      .filter(Boolean)
      .map((part) => decodeURIComponent(part));
    if (parts.length < 2) return undefined;
    const owner = parts[0];
    const repo = parts[1].replace(/\.git$/i, "");
    if (!GITHUB_NAME.test(owner) || !GITHUB_NAME.test(repo)) {
      return undefined;
    }
    const rest = parts.slice(2);
    if (rest[0] === "tree" && rest[1]) {
      return {
        owner,
        repo,
        branch: rest[1],
        path: rest.slice(2).join("/") || undefined,
      };
    }
    if (rest[0] === "blob" && rest[1]) {
      const file = rest.slice(2);
      return {
        owner,
        repo,
        branch: rest[1],
        path: file.length > 1 ? file.slice(0, -1).join("/") : undefined,
      };
    }
    if (rest[0] === "tree" || rest[0] === "blob") {
      return { owner, repo };
    }
    if (rest.length > 0 && GITHUB_RESERVED.has(rest[0])) {
      return undefined;
    }
    if (rest.length > 0) {
      return { owner, repo, path: rest.join("/") };
    }
    return { owner, repo };
  }

  const parts = raw.split("/").filter(Boolean);
  if (parts.length < 2) return undefined;
  const owner = parts[0];
  let repo = parts[1].replace(/\.git$/i, "");
  let branch: string | undefined;
  const at = repo.lastIndexOf("@");
  if (at > 0) {
    branch = repo.slice(at + 1);
    repo = repo.slice(0, at);
  }
  if (!GITHUB_NAME.test(owner) || !GITHUB_NAME.test(repo)) {
    return undefined;
  }
  return {
    owner,
    repo,
    branch,
    path: parts.slice(2).join("/") || undefined,
  };
}

export function githubWorkspaceName(
  owner: string,
  repo: string,
  branch: string,
  path?: string
): string {
  return `${owner}/${repo}@${branch}${path ? `:${path}` : ""}`;
}

function normalizeSubdir(path?: string): string {
  return (path ?? "")
    .replace(/\\/g, "/")
    .replace(/^\.?\//, "")
    .replace(/\/+$/, "");
}

function stripBom(text: string): string {
  return text.charCodeAt(0) === 0xfeff ? text.slice(1) : text;
}

export interface OpenedGitHub {
  project: Project;
  workspace: GitHubWorkspace;
  branch: string;
  login?: string;
  skipped: number;
  truncated: boolean;
}

interface SelectedFile {
  path: string;
  fullPath: string;
  sha: string;
  size?: number;
}

export type GitHubRawFetcher = (
  owner: string,
  repo: string,
  branch: string,
  path: string
) => Promise<string>;

async function fetchRawFile(
  owner: string,
  repo: string,
  branch: string,
  path: string
): Promise<string> {
  const encodedPath = path
    .split("/")
    .map((part) => encodeURIComponent(part))
    .join("/");
  const encodedBranch = branch
    .split("/")
    .map((part) => encodeURIComponent(part))
    .join("/");
  const url =
    `https://raw.githubusercontent.com/${encodeURIComponent(owner)}/` +
    `${encodeURIComponent(repo)}/${encodedBranch}/${encodedPath}`;
  let response: Response;
  try {
    response = await fetch(url, { headers: { Accept: "text/plain" } });
  } catch (error) {
    throw new WorkspaceError(
      "unavailable",
      `Could not fetch ${path} from GitHub: ${errorMessage(error)}`
    );
  }
  if (!response.ok) {
    if (response.status === 404) {
      throw new WorkspaceError(
        "not-found",
        `GitHub could not find ${path}.`,
        404
      );
    }
    throw new WorkspaceError(
      "unavailable",
      `GitHub raw content request failed for ${path} ` +
        `(HTTP ${response.status}).`,
      response.status
    );
  }
  return response.text();
}

export async function loadGitHubRepository(
  input: string,
  token?: string,
  apiFactory: GitHubApiFactory = createGitHubApi,
  rawFetcher: GitHubRawFetcher = fetchRawFile
): Promise<OpenedGitHub> {
  const ref = parseGitHubInput(input);
  if (!ref) {
    throw new WorkspaceError(
      "not-found",
      "Enter a GitHub repository URL such as " +
        "https://github.com/owner/repo."
    );
  }
  let api: GitHubApi;
  try {
    api = await apiFactory(token);
  } catch (error) {
    throw githubError(error, "starting the GitHub client");
  }
  let login: string | undefined;
  if (token) {
    try {
      login = (await api.validateUser()).login;
    } catch (error) {
      throw githubError(error, "validating the GitHub token");
    }
  }
  let info: GitHubRepoInfo;
  try {
    info = await api.getRepo(ref.owner, ref.repo);
  } catch (error) {
    if (statusOf(error) === 404) {
      throw new WorkspaceError(
        token ? "not-found" : "permission-denied",
        token
          ? "GitHub could not find the repository, or the token cannot " +
            "access it."
          : "Repository not found or private. Connect GitHub with a token.",
        404
      );
    }
    throw githubError(error, "the repository");
  }
  const branch = ref.branch || info.defaultBranch;
  let head: { sha: string };
  let tree: GitHubTreeResult;
  try {
    head = await api.getRef(ref.owner, ref.repo, branch);
    tree = await api.getTree(ref.owner, ref.repo, head.sha, true);
  } catch (error) {
    throw githubError(error, "the branch or repository tree");
  }

  const subdir = normalizeSubdir(ref.path);
  const selected: SelectedFile[] = [];
  let skipped = 0;
  let truncated = tree.truncated;
  for (const entry of tree.tree) {
    if (entry.type !== "blob") continue;
    if (
      subdir &&
      entry.path !== subdir &&
      !entry.path.startsWith(subdir + "/")
    ) {
      continue;
    }
    const path = subdir
      ? entry.path.slice(subdir.length + 1)
      : entry.path;
    if (!path || !isCandidateFile(path)) continue;
    if (entry.size !== undefined && entry.size > MAX_FILE_BYTES) {
      skipped++;
      continue;
    }
    if (selected.length >= MAX_FILES) {
      truncated = true;
      break;
    }
    selected.push({
      path,
      fullPath: entry.path,
      sha: entry.sha,
      size: entry.size,
    });
  }

  const useRaw = !token && info.private !== true;
  const files = new Map<string, ProjectTextFile>();
  let cursor = 0;
  let fatal: unknown;
  const workerCount = Math.min(6, selected.length);
  const workers = Array.from({ length: workerCount }, async () => {
    while (cursor < selected.length && fatal === undefined) {
      const item = selected[cursor++];
      try {
        const text = useRaw
          ? await rawFetcher(
              ref.owner,
              ref.repo,
              branch,
              item.fullPath
            )
          : await api.getBlob(ref.owner, ref.repo, item.sha);
        files.set(item.path, {
          text: stripBom(text),
          kind: classify(item.path),
        });
      } catch (error) {
        const status = statusOf(error);
        if (
          error instanceof WorkspaceError ||
          status === 401 ||
          status === 403 ||
          status === 404
        ) {
          fatal = error;
          return;
        }
        skipped++;
      }
    }
  });
  await Promise.all(workers);
  if (fatal !== undefined) {
    throw githubError(fatal, "a repository file");
  }

  const root = chooseRoot(
    [...files.keys()],
    subdir ? subdir.split("/").pop() ?? ref.repo : ref.repo
  );
  if (!root) {
    throw new WorkspaceError(
      "not-found",
      "That repository does not contain a .thm reasoning file."
    );
  }
  const project: Project = { files, root, active: root };
  const baseTexts = new Map(
    [...files.entries()].map(([path, file]) => [path, file.text])
  );
  const workspace = new GitHubWorkspace({
    api,
    token,
    owner: ref.owner,
    repo: ref.repo,
    branch,
    subdir,
    project,
    baseRevision: head.sha,
    baseTree: tree.sha,
    baseTexts,
  });
  return {
    project,
    workspace,
    branch,
    login,
    skipped,
    truncated,
  };
}

export interface GitHubWorkspaceOptions {
  api: GitHubApi;
  token?: string;
  owner: string;
  repo: string;
  branch: string;
  subdir?: string;
  project: Project;
  baseRevision: string;
  baseTree: string;
  baseTexts: Map<string, string>;
}

export class GitHubWorkspace implements Workspace {
  readonly kind: WorkspaceKind = "github";
  readonly name: string;
  readonly capabilities: WorkspaceCapabilities = {
    write: true,
    remove: false,
    structural: false,
    refresh: false,
    commit: true,
    autoSave: false,
  };
  baseRevision: string;

  private api: GitHubApi;
  private token?: string;
  private owner: string;
  private repo: string;
  private branch: string;
  private subdir: string;
  private project: Project;
  private baseTree: string;
  private baseTexts: Map<string, string>;

  constructor(options: GitHubWorkspaceOptions) {
    this.api = options.api;
    this.token = options.token;
    this.owner = options.owner;
    this.repo = options.repo;
    this.branch = options.branch;
    this.subdir = normalizeSubdir(options.subdir);
    this.project = options.project;
    this.baseRevision = options.baseRevision;
    this.baseTree = options.baseTree;
    this.baseTexts = options.baseTexts;
    this.name = githubWorkspaceName(
      this.owner,
      this.repo,
      this.branch,
      this.subdir || undefined
    );
  }

  get hasToken(): boolean {
    return Boolean(this.token);
  }

  async list(): Promise<WorkspaceFileEntry[]> {
    return [...this.project.files.entries()].map(([path, file]) => ({
      path,
      kind: file.kind,
    }));
  }

  async read(path: string): Promise<string> {
    const file = this.project.files.get(path);
    if (!file) {
      throw new WorkspaceError("not-found", `File not found: ${path}`);
    }
    return file.text;
  }

  async write(path: string, text: string): Promise<void> {
    const file = this.project.files.get(path);
    if (file) file.text = text;
    else this.project.files.set(path, { text, kind: classify(path) });
  }

  async authorize(token: string): Promise<{ login: string }> {
    let api: GitHubApi;
    try {
      api = await createGitHubApi(token);
    } catch (error) {
      throw githubError(error, "starting the GitHub client");
    }
    let user: { login: string };
    try {
      user = await api.validateUser();
    } catch (error) {
      throw githubError(error, "validating the GitHub token");
    }
    let info: GitHubRepoInfo;
    try {
      info = await api.getRepo(this.owner, this.repo);
    } catch (error) {
      throw githubError(error, "the repository");
    }
    if (info.canPush === false) {
      throw new WorkspaceError(
        "permission-denied",
        "That token can read this repository but cannot push to it. " +
          "Use a token with write access, or reconnect with an account " +
          "that can push.",
        403
      );
    }
    this.api = api;
    this.token = token;
    return user;
  }

  clearToken(): void {
    this.token = undefined;
  }

  async commit(message: string): Promise<CommitResult> {
    if (!this.token) {
      throw new WorkspaceError(
        "permission-denied",
        "Connect GitHub with a write-enabled token to commit."
      );
    }
    if (message.trim() === "") {
      throw new WorkspaceError("io", "Enter a commit message.");
    }
    let ref: { sha: string };
    try {
      ref = await this.api.getRef(this.owner, this.repo, this.branch);
    } catch (error) {
      throw githubError(error, "the branch");
    }
    if (ref.sha !== this.baseRevision) {
      return {
        status: "conflict",
        message:
          "The branch moved on GitHub since it was loaded. " +
          "Reload the repository and try again.",
      };
    }

    const changed = [...this.project.files.entries()].filter(
      ([path, file]) => this.baseTexts.get(path) !== file.text
    );
    const deleted = [...this.baseTexts.keys()].filter(
      (path) => !this.project.files.has(path)
    );
    if (changed.length === 0 && deleted.length === 0) {
      throw new WorkspaceError("io", "There are no changes to commit.");
    }

    const treeEntries: GitHubTreeUpdate[] = [];
    for (const [path, file] of changed) {
      let blob: { sha: string };
      try {
        blob = await this.api.createBlob(
          this.owner,
          this.repo,
          file.text
        );
      } catch (error) {
        throw githubError(error, `a blob for ${path}`);
      }
      treeEntries.push({
        path: this.fullPath(path),
        mode: "100644",
        type: "blob",
        sha: blob.sha,
      });
    }
    for (const path of deleted) {
      treeEntries.push({
        path: this.fullPath(path),
        mode: "100644",
        type: "blob",
        sha: null,
      });
    }

    let tree: { sha: string };
    try {
      tree = await this.api.createTree(
        this.owner,
        this.repo,
        this.baseTree,
        treeEntries
      );
    } catch (error) {
      throw githubError(error, "the commit tree");
    }
    let commit: { sha: string };
    try {
      commit = await this.api.createCommit(
        this.owner,
        this.repo,
        message,
        tree.sha,
        [this.baseRevision]
      );
    } catch (error) {
      throw githubError(error, "the commit");
    }
    try {
      await this.api.updateRef(
        this.owner,
        this.repo,
        this.branch,
        commit.sha
      );
    } catch (error) {
      if (statusOf(error) === 422) {
        return {
          status: "conflict",
          message:
            "The branch moved on GitHub while committing. " +
            "Reload the repository and try again.",
        };
      }
      throw githubError(error, "the branch");
    }

    this.baseRevision = commit.sha;
    this.baseTree = tree.sha;
    this.baseTexts = new Map(
      [...this.project.files.entries()].map(([path, file]) => [
        path,
        file.text,
      ])
    );
    return { status: "committed", revision: commit.sha };
  }

  close(): void {
    // The in-memory project owns the contents; nothing to release.
  }

  private fullPath(path: string): string {
    return this.subdir ? `${this.subdir}/${path}` : path;
  }
}
