// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import type { Project } from "./project";
import { openMemoryFolder } from "./workspace-memory";
import {
  MemoryWorkspace,
  WorkspaceError,
  WorkspaceSession,
  readOnlyWorkspace,
  virtualWorkspace,
  workspaceErrorOf,
  workspaceMessage,
  type Workspace,
} from "./workspace";

function projectFixture(): Project {
  return {
    files: new Map([
      ["main.thm", { text: "Specification \"empty\".\n", kind: "abella" }],
      ["notes.md", { text: "# Notes\n", kind: "text" }],
    ]),
    root: "main.thm",
    active: "main.thm",
  };
}

function writableWorkspace(project: Project): MemoryWorkspace {
  return new MemoryWorkspace("directory", "Folder", project, {
    write: true,
    remove: false,
    structural: false,
    refresh: false,
    commit: false,
    autoSave: false,
  });
}

test("memory workspace lists, reads, writes, and removes", async () => {
  const project = projectFixture();
  const workspace = virtualWorkspace(project);
  assert.deepEqual(
    (await workspace.list()).map((entry) => entry.path).sort(),
    ["main.thm", "notes.md"]
  );
  assert.equal(await workspace.read("notes.md"), "# Notes\n");
  await workspace.write("notes.md", "# Changed\n");
  assert.equal(await workspace.read("notes.md"), "# Changed\n");
  await workspace.write("new.txt", "new\n");
  assert.equal(await workspace.read("new.txt"), "new\n");
  await workspace.remove?.("notes.md");
  await assert.rejects(
    () => workspace.read("notes.md"),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "not-found"
  );
});

test("read-only memory workspaces reject writes and removals", async () => {
  const project = projectFixture();
  const workspace = readOnlyWorkspace("memory", "Notes", project);
  await assert.rejects(
    () => workspace.write("main.thm", "x"),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "unsupported"
  );
  await assert.rejects(
    () => workspace.remove?.("main.thm") ?? Promise.resolve(),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "unsupported"
  );
  assert.equal(workspace.capabilities.write, false);
});

test("autosave workspaces keep dirty markers out of the sidebar", () => {
  const project = projectFixture();
  const persisted: string[] = [];
  const session = new WorkspaceSession(project, virtualWorkspace(project), {
    persist: (_project, workspace) => persisted.push(workspace.name),
  });
  session.markDirty("main.thm");
  assert.equal(session.hasDirty(), false);
  session.persistNow();
  assert.deepEqual(persisted, ["Virtual project"]);
  session.close();
});

test("explicit-save sessions track and clear dirty files", async () => {
  const project = projectFixture();
  const session = new WorkspaceSession(project, writableWorkspace(project), {
    persist: () => undefined,
  });
  session.markDirty("main.thm");
  session.markDirty("notes.md");
  assert.deepEqual(session.dirtyPaths().sort(), ["main.thm", "notes.md"]);
  await session.save("main.thm", "Specification \"empty\".\n% saved\n");
  assert.equal(session.isDirty("main.thm"), false);
  assert.equal(session.isDirty("notes.md"), true);
  assert.match(project.files.get("main.thm")?.text ?? "", /% saved/);
  session.close();
});

test("save-all reports success, cancellation, and failures", async () => {
  const project = projectFixture();
  const workspace: Workspace = {
    kind: "directory",
    name: "Folder",
    capabilities: {
      write: true,
      remove: false,
      structural: false,
      refresh: false,
      commit: false,
      autoSave: false,
    },
    async list() {
      return [];
    },
    async read() {
      return "";
    },
    async write(path: string) {
      if (path === "cancel.thm") {
        throw new WorkspaceError("cancelled", "cancelled");
      }
      if (path === "fail.thm") {
        throw new WorkspaceError("io", "disk full");
      }
    },
  };
  const session = new WorkspaceSession(project, workspace);
  session.markDirty("main.thm");
  session.markDirty("cancel.thm");
  session.markDirty("fail.thm");
  const report = await session.saveAll(
    session.dirtyPaths(),
    (path) => `text for ${path}`
  );
  assert.equal(report.saved, 1);
  assert.equal(report.cancelled, 1);
  assert.equal(report.failures.length, 1);
  assert.equal(report.failures[0].path, "fail.thm");
  assert.equal(session.isDirty("main.thm"), false);
  assert.equal(session.isDirty("cancel.thm"), true);
  assert.equal(session.isDirty("fail.thm"), true);
  session.close();
});

test("workspace errors keep their codes and messages", () => {
  const error = new WorkspaceError("permission-denied", "nope");
  assert.equal(workspaceMessage(error), "nope");
  assert.equal(workspaceErrorOf(error).code, "permission-denied");
  assert.equal(workspaceErrorOf(new Error("io")).code, "io");
  assert.equal(workspaceErrorOf("text").code, "io");
});

function folderFile(path: string, text: string): File {
  const file = new File([text], path.split("/").pop() ?? "file.txt");
  Object.defineProperty(file, "webkitRelativePath", { value: path });
  return file;
}

test("memory folder strips its root and skips ignored paths", async () => {
  const opened = await openMemoryFolder([
    folderFile("project/main.thm", "Specification \"empty\".\n"),
    folderFile("project/notes.md", "# Notes\n"),
    folderFile("project/.git/config", "ignored"),
    folderFile("project/node_modules/pkg/index.js", "ignored"),
  ]);
  assert.deepEqual(
    [...opened.project.files.keys()].sort(),
    ["main.thm", "notes.md"]
  );
  assert.equal(opened.project.root, "main.thm");
  assert.equal(opened.workspace.name, "project");
  assert.equal(opened.workspace.capabilities.write, false);
  assert.equal(opened.workspace.capabilities.structural, false);
});

test("memory folder requires a theorem", async () => {
  await assert.rejects(
    () =>
      openMemoryFolder([
        folderFile("project/spec.sig", "sig spec.\n"),
        folderFile("project/README.md", "# Readme\n"),
      ]),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "not-found"
  );
});
