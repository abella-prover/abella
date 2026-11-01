// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  isAllowedProjectUrl,
  loadSiteProject,
  projectParam,
  resolveProjectUrl,
  type Fetcher,
} from "./workspace-site";
import { WorkspaceError } from "./workspace";

const PAGE = new URL("https://abella-prover.org/web/");
const MANIFEST = "/examples/demo/demo.project.json";

function responseRoutes(
  routes: Record<string, string | number>
): Fetcher {
  return async (url) => {
    const path = new URL(url).pathname;
    const route = routes[path];
    if (route === undefined) {
      return new Response("missing", { status: 404 });
    }
    if (typeof route === "number") {
      return new Response("", { status: route });
    }
    return new Response(route);
  };
}

function manifest(files: string[], entry?: string): string {
  return JSON.stringify({ version: 2, entry, files });
}

test("site projects load their manifest and files", async () => {
  const fetcher = responseRoutes({
    [MANIFEST]: manifest(
      ["demo.thm", "demo.sig", "demo.mod", "notes.md"],
      "demo.thm"
    ),
    "/examples/demo/demo.thm": 'Specification "demo".\n',
    "/examples/demo/demo.sig": "sig demo.\n",
    "/examples/demo/demo.mod": "module demo.\n",
    "/examples/demo/notes.md": "# Notes\n",
  });
  const loaded = await loadSiteProject(MANIFEST, { page: PAGE, fetcher });
  assert.equal(loaded.project.entry, "demo.thm");
  assert.equal(loaded.project.active, "demo.thm");
  assert.deepEqual([...loaded.project.files.keys()].sort(), [
    "demo.mod",
    "demo.sig",
    "demo.thm",
    "notes.md",
  ]);
  assert.equal(loaded.workspace.kind, "site");
  assert.equal(loaded.workspace.name, "demo.thm");
  assert.equal(loaded.workspace.capabilities.write, false);
  assert.equal(loaded.workspace.capabilities.structural, false);
  await assert.rejects(
    () => loaded.workspace.write("demo.thm", "x"),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "unsupported"
  );
});

test("site files are resolved relative to the manifest URL", async () => {
  const fetcher = responseRoutes({
    "/examples/demo/demo.project.json": manifest(
      ["sub/helper.thm", "demo.thm"],
      "demo.thm"
    ),
    "/examples/demo/sub/helper.thm": 'Specification "helper".\n',
    "/examples/demo/demo.thm": 'Specification "demo".\n',
  });
  const loaded = await loadSiteProject(MANIFEST, { page: PAGE, fetcher });
  assert.ok(loaded.project.files.has("sub/helper.thm"));
});

test("project parameters are read and trimmed", () => {
  assert.equal(
    projectParam("?project=%2Fexamples%2Fdemo.project.json"),
    "/examples/demo.project.json"
  );
  assert.equal(projectParam("?project=%20%20"), undefined);
  assert.equal(projectParam("?other=1"), undefined);
});

test("only same-origin or allow-listed project URLs are allowed", () => {
  assert.ok(isAllowedProjectUrl(new URL("/x.json", PAGE), PAGE));
  assert.equal(
    isAllowedProjectUrl(new URL("https://example.com/x.json"), PAGE),
    false
  );
  assert.ok(
    isAllowedProjectUrl(
      new URL("https://docs.example.com/x.json"),
      PAGE,
      ["docs.example.com"]
    )
  );
  assert.equal(
    isAllowedProjectUrl(
      new URL("http://docs.example.com/x.json"),
      PAGE,
      ["docs.example.com"]
    ),
    false
  );
});

test("cross-origin, credentialed, and non-http URLs are rejected", () => {
  assert.throws(
    () => resolveProjectUrl("https://example.com/x.json", PAGE),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "permission-denied"
  );
  assert.throws(
    () => resolveProjectUrl("//example.com/x.json", PAGE),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "permission-denied"
  );
  assert.throws(
    () => resolveProjectUrl("https://user:pass@abella-prover.org/x", PAGE),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "permission-denied"
  );
  assert.throws(
    () => resolveProjectUrl("javascript:alert(1)", PAGE),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "unsupported"
  );
});

test("a same-origin manifest cannot list cross-origin files", async () => {
  const fetcher = responseRoutes({
    [MANIFEST]: manifest(
      ["demo.thm", "https://example.com/evil.thm"],
      "demo.thm"
    ),
    "/examples/demo/demo.thm": 'Specification "demo".\n',
  });
  await assert.rejects(
    () => loadSiteProject(MANIFEST, { page: PAGE, fetcher }),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "permission-denied"
  );
});

test("missing manifests report not-found", async () => {
  await assert.rejects(
    () => loadSiteProject("/missing.project.json", {
      page: PAGE,
      fetcher: responseRoutes({}),
    }),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "not-found"
  );
});

test("unsupported manifest versions are rejected", async () => {
  const fetcher = responseRoutes({
    [MANIFEST]: JSON.stringify({ version: 1, files: ["demo.thm"] }),
  });
  await assert.rejects(
    () => loadSiteProject(MANIFEST, { page: PAGE, fetcher }),
    (error: unknown) =>
      error instanceof WorkspaceError &&
      error.code === "unsupported" &&
      /incompatible version/.test(error.message)
  );
});

test("an invalid entry leaves the project without a theorem", async () => {
  const fetcher = responseRoutes({
    [MANIFEST]: manifest(["notes.md", "demo.thm"], "notes.md"),
    "/examples/demo/notes.md": "# Notes\n",
    "/examples/demo/demo.thm": 'Specification "demo".\n',
  });
  const loaded = await loadSiteProject(MANIFEST, { page: PAGE, fetcher });
  assert.equal(loaded.project.entry, undefined);
  assert.equal(loaded.project.active, undefined);
});

test("unsupported listed files are skipped", async () => {
  const fetcher = responseRoutes({
    [MANIFEST]: manifest(["demo.thm", "logo.png"], "demo.thm"),
    "/examples/demo/demo.thm": 'Specification "demo".\n',
  });
  const loaded = await loadSiteProject(MANIFEST, { page: PAGE, fetcher });
  assert.deepEqual([...loaded.project.files.keys()], ["demo.thm"]);
});

test("file text is normalized and stripped of a byte-order mark", async () => {
  const fetcher = responseRoutes({
    [MANIFEST]: manifest(["demo.thm"], "demo.thm"),
    "/examples/demo/demo.thm": "\uFEFFa\r\nb\r\n",
  });
  const loaded = await loadSiteProject(MANIFEST, { page: PAGE, fetcher });
  assert.equal(loaded.project.files.get("demo.thm")?.text, "a\nb\n");
});
