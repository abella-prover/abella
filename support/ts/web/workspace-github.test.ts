// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import type { Project } from "./project";
import {
  GitHubWorkspace,
  loadGitHubRepository,
  parseGitHubInput,
  type GitHubApi,
  type GitHubTreeEntry,
  type GitHubTreeResult,
  type GitHubTreeUpdate,
} from "./workspace-github";
import { WorkspaceError as GitHubWorkspaceError } from "./workspace";

class FakeApi implements GitHubApi {
  refSha = "commit-base";
  updateError: unknown;
  treeEntries: GitHubTreeUpdate[] = [];
  commitMessage = "";
  commitParents: string[] = [];
  calls: string[] = [];
  private blobs = new Map<string, string>();
  private blobCounter = 0;

  constructor(
    private entries: GitHubTreeEntry[] = [
      {
        path: "sub/main.thm",
        type: "blob",
        sha: "main-blob",
      },
      {
        path: "sub/spec.sig",
        type: "blob",
        sha: "sig-blob",
      },
      {
        path: "sub/README.md",
        type: "blob",
        sha: "readme-blob",
      },
      {
        path: "sub/logo.png",
        type: "blob",
        sha: "image-blob",
      },
    ]
  ) {
    this.blobs.set("main-blob", 'Specification "spec".\n');
    this.blobs.set("sig-blob", "sig spec.\n");
    this.blobs.set("readme-blob", "# Demo\n");
    this.blobs.set("image-blob", "not text");
  }

  async getRepo(): Promise<{ defaultBranch: string }> {
    return { defaultBranch: "main" };
  }

  async getRef(): Promise<{ sha: string }> {
    return { sha: this.refSha };
  }

  async getTree(): Promise<GitHubTreeResult> {
    return { sha: "tree-base", tree: this.entries, truncated: false };
  }

  async getBlob(
    _owner: string,
    _repo: string,
    sha: string
  ): Promise<string> {
    return this.blobs.get(sha) ?? "";
  }

  async validateUser(): Promise<{ login: string }> {
    return { login: "tester" };
  }

  async createBlob(
    _owner: string,
    _repo: string,
    content: string
  ): Promise<{ sha: string }> {
    this.calls.push(`blob:${content}`);
    return { sha: `blob-${++this.blobCounter}` };
  }

  async createTree(
    _owner: string,
    _repo: string,
    _baseTree: string,
    entries: GitHubTreeUpdate[]
  ): Promise<{ sha: string }> {
    this.calls.push("tree");
    this.treeEntries = entries;
    return { sha: "tree-new" };
  }

  async createCommit(
    _owner: string,
    _repo: string,
    message: string,
    _tree: string,
    parents: string[]
  ): Promise<{ sha: string }> {
    this.calls.push("commit");
    this.commitMessage = message;
    this.commitParents = parents;
    return { sha: "commit-new" };
  }

  async updateRef(): Promise<void> {
    this.calls.push("update-ref");
    if (this.updateError !== undefined) throw this.updateError;
  }
}

function projectFixture(): Project {
  return {
    files: new Map([
      ["main.thm", { text: 'Specification "spec".\n', kind: "abella" }],
      ["spec.sig", { text: "sig spec.\n", kind: "abella" }],
    ]),
    root: "main.thm",
    active: "main.thm",
  };
}

function workspaceFixture(
  api: FakeApi,
  project: Project,
  token: string | undefined
): GitHubWorkspace {
  return new GitHubWorkspace({
    api,
    token,
    owner: "acme",
    repo: "demo",
    branch: "main",
    subdir: "sub",
    project,
    baseRevision: "commit-base",
    baseTree: "tree-base",
    baseTexts: new Map([
      ["main.thm", 'Specification "spec".\n'],
      ["spec.sig", "sig spec.\n"],
    ]),
  });
}

test("parses GitHub repository inputs", () => {
  assert.deepEqual(parseGitHubInput("https://github.com/acme/demo"), {
    owner: "acme",
    repo: "demo",
  });
  assert.deepEqual(
    parseGitHubInput("https://github.com/acme/demo/tree/dev/dir"),
    { owner: "acme", repo: "demo", branch: "dev", path: "dir" }
  );
  assert.deepEqual(
    parseGitHubInput("https://github.com/acme/demo/examples/logic"),
    { owner: "acme", repo: "demo", path: "examples/logic" }
  );
  assert.deepEqual(parseGitHubInput("github.com/acme/demo.git"), {
    owner: "acme",
    repo: "demo",
  });
  assert.deepEqual(parseGitHubInput("acme/demo@dev"), {
    owner: "acme",
    repo: "demo",
    branch: "dev",
    path: undefined,
  });
  assert.equal(parseGitHubInput("not a repository"), undefined);
  assert.equal(parseGitHubInput("https://example.com/acme/demo"), undefined);
});

test("loads a subdirectory and builds the project", async () => {
  const api = new FakeApi();
  const opened = await loadGitHubRepository(
    "https://github.com/acme/demo/tree/main/sub",
    "token",
    async () => api
  );
  assert.deepEqual(
    [...opened.project.files.keys()].sort(),
    ["README.md", "main.thm", "spec.sig"]
  );
  assert.equal(opened.project.root, "main.thm");
  assert.equal(opened.workspace.name, "acme/demo@main:sub");
  assert.equal(opened.workspace.baseRevision, "commit-base");
  assert.equal(opened.workspace.capabilities.commit, true);
  assert.equal(opened.workspace.capabilities.structural, false);
});

test("loads public files through raw content URLs", async () => {
  const api = new FakeApi();
  const rawPaths: string[] = [];
  const raw = new Map([
    ["sub/main.thm", 'Specification "spec".\n'],
    ["sub/spec.sig", "sig spec.\n"],
    ["sub/README.md", "# Demo\n"],
  ]);
  const opened = await loadGitHubRepository(
    "https://github.com/acme/demo/tree/main/sub",
    undefined,
    async () => api,
    async (_owner, _repo, _branch, path) => {
      rawPaths.push(path);
      return raw.get(path) ?? "";
    }
  );
  assert.deepEqual(
    [...opened.project.files.keys()].sort(),
    ["README.md", "main.thm", "spec.sig"]
  );
  assert.deepEqual(rawPaths.sort(), [
    "sub/README.md",
    "sub/main.thm",
    "sub/spec.sig",
  ]);
});

test("commit creates one tree and updates the branch", async () => {
  const api = new FakeApi();
  const project = projectFixture();
  project.files.get("main.thm")!.text = 'Specification "spec".\n% edited\n';
  project.files.get("spec.sig")!.text = "sig spec.\n% edited\n";
  const workspace = workspaceFixture(api, project, "token");
  const result = await workspace.commit("Update development");
  assert.deepEqual(result, { status: "committed", revision: "commit-new" });
  assert.deepEqual(api.treeEntries, [
    {
      path: "sub/main.thm",
      mode: "100644",
      type: "blob",
      sha: "blob-1",
    },
    {
      path: "sub/spec.sig",
      mode: "100644",
      type: "blob",
      sha: "blob-2",
    },
  ]);
  assert.equal(api.commitMessage, "Update development");
  assert.deepEqual(api.commitParents, ["commit-base"]);
  assert.deepEqual(api.calls, [
    'blob:Specification "spec".\n% edited\n',
    "blob:sig spec.\n% edited\n",
    "tree",
    "commit",
    "update-ref",
  ]);
  assert.equal(workspace.baseRevision, "commit-new");
});

test("commit reports a moved branch as a conflict", async () => {
  const api = new FakeApi();
  api.refSha = "commit-moved";
  const project = projectFixture();
  project.files.get("main.thm")!.text = "changed";
  const workspace = workspaceFixture(api, project, "token");
  const result = await workspace.commit("Update");
  assert.equal(result.status, "conflict");
  assert.deepEqual(api.calls, []);
});

test("commit reports a non-fast-forward update as a conflict", async () => {
  const api = new FakeApi();
  api.updateError = { status: 422 };
  const project = projectFixture();
  project.files.get("main.thm")!.text = "changed";
  const workspace = workspaceFixture(api, project, "token");
  const result = await workspace.commit("Update");
  assert.equal(result.status, "conflict");
});

test("commit requires a token and actual changes", async () => {
  const api = new FakeApi();
  const project = projectFixture();
  project.files.get("main.thm")!.text = "changed";
  const noToken = workspaceFixture(api, project, undefined);
  await assert.rejects(
    () => noToken.commit("Update"),
    (error: unknown) =>
      error instanceof GitHubWorkspaceError &&
      error.code === "permission-denied"
  );
  const unchanged = workspaceFixture(api, projectFixture(), "token");
  await assert.rejects(
    () => unchanged.commit("Update"),
    (error: unknown) =>
      error instanceof GitHubWorkspaceError && error.code === "io"
  );
});
