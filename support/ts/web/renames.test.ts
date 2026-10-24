// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { classify, type Project } from "./project";
import { planRename, type RenamePlan } from "./renames";

function makeProject(
  files: Record<string, string>,
  root = "main.thm"
): Project {
  return {
    files: new Map(
      Object.entries(files).map(([path, text]) => [
        path,
        { text, kind: classify(path) },
      ])
    ),
    root,
    active: root,
  };
}

function planOrThrow(project: Project, from: string, to: string): RenamePlan {
  const result = planRename(project, from, to);
  if (!result.ok) throw new Error(result.message);
  return result.plan;
}

test("renaming a sig renames its mod and updates references", () => {
  const project = makeProject({
    "foo.sig": "sig foo.\n\nkind tm type.\n",
    "foo.mod": "module foo.\n\np.\n",
    "main.thm": 'Specification "foo".\nTheorem t : true.\n',
    "other.thm": 'Specification "foo".\n',
  });

  const plan = planOrThrow(project, "foo.sig", "bar.sig");
  assert.deepEqual(plan.renames, [
    { from: "foo.sig", to: "bar.sig" },
    { from: "foo.mod", to: "bar.mod" },
  ]);
  assert.equal(plan.files.has("foo.sig"), false);
  assert.equal(plan.files.has("foo.mod"), false);
  assert.equal(plan.files.get("bar.sig")?.text, "sig bar.\n\nkind tm type.\n");
  assert.equal(plan.files.get("bar.mod")?.text, "module bar.\n\np.\n");
  assert.equal(
    plan.files.get("main.thm")?.text,
    'Specification "bar".\nTheorem t : true.\n'
  );
  assert.equal(
    plan.files.get("other.thm")?.text,
    'Specification "bar".\n'
  );
});

test("renaming a mod renames its sig", () => {
  const project = makeProject({
    "foo.sig": "sig foo.\n",
    "foo.mod": "module foo.\n",
    "main.thm": 'Specification "foo".\n',
  });

  const plan = planOrThrow(project, "foo.mod", "bar.mod");
  assert.deepEqual(plan.renames, [
    { from: "foo.mod", to: "bar.mod" },
    { from: "foo.sig", to: "bar.sig" },
  ]);
  assert.equal(plan.files.get("bar.sig")?.text, "sig bar.\n");
  assert.equal(plan.files.get("bar.mod")?.text, "module bar.\n");
  assert.equal(plan.files.get("main.thm")?.text, 'Specification "bar".\n');
});

test("renaming a mod without a sig still updates the spec", () => {
  const project = makeProject({
    "foo.mod": "module foo.\n",
    "main.thm": 'Specification "foo".\n',
  });
  const plan = planOrThrow(project, "foo.mod", "bar.mod");
  assert.deepEqual(plan.renames, [{ from: "foo.mod", to: "bar.mod" }]);
  assert.equal(plan.files.get("bar.mod")?.text, "module bar.\n");
  assert.equal(plan.files.get("main.thm")?.text, 'Specification "bar".\n');
});

test("renaming a thm updates imports and the root path", () => {
  const project = makeProject(
    {
      "foo.thm": "Import \"other\".\n",
      "other.thm": "Import \"foo\".\n",
    },
    "foo.thm"
  );
  const plan = planOrThrow(project, "foo.thm", "bar.thm");
  assert.deepEqual(plan.renames, [{ from: "foo.thm", to: "bar.thm" }]);
  assert.equal(plan.root, "bar.thm");
  assert.equal(plan.active, "bar.thm");
  assert.equal(plan.files.get("bar.thm")?.text, "Import \"other\".\n");
  assert.equal(plan.files.get("other.thm")?.text, "Import \"bar\".\n");
});

test("renaming a thm across directories keeps its module name", () => {
  const project = makeProject({
    "foo.thm": 'Import "foo".\n',
    "main.thm": 'Import "foo".\n',
  });
  const plan = planOrThrow(project, "foo.thm", "sub/foo.thm");
  assert.equal(plan.files.get("sub/foo.thm")?.text, 'Import "foo".\n');
  assert.equal(plan.files.get("main.thm")?.text, 'Import "foo".\n');
});

test("companion target collisions abort the rename", () => {
  const project = makeProject({
    "foo.sig": "sig foo.\n",
    "foo.mod": "module foo.\n",
    "bar.mod": "module bar.\n",
    "main.thm": 'Specification "foo".\n',
  });
  const result = planRename(project, "foo.sig", "bar.sig");
  assert.equal(result.ok, false);
  if (!result.ok) assert.match(result.message, /bar\.mod already exists/);
});

test("primary target collisions abort the rename", () => {
  const project = makeProject({
    "foo.thm": "",
    "bar.thm": "",
    "main.thm": "",
  });
  const result = planRename(project, "foo.thm", "bar.thm");
  assert.equal(result.ok, false);
  if (!result.ok) assert.match(result.message, /already exists/);
});

test("renaming updates markdown links relative to each file", () => {
  const project = makeProject({
    "foo.thm": "",
    "foo.sig": "sig foo.\n",
    "README.md":
      "[proof](./foo.thm#top) and [spec](foo.sig)\n" +
      "[reference]: foo.thm \"Proof\"\n",
    "docs/note.md": "[proof](../foo.thm)\n",
  });
  let plan = planOrThrow(project, "foo.thm", "bar.thm");
  assert.equal(
    plan.files.get("README.md")?.text,
    "[proof](bar.thm#top) and [spec](foo.sig)\n" +
      "[reference]: bar.thm \"Proof\"\n"
  );
  assert.equal(
    plan.files.get("docs/note.md")?.text,
    "[proof](../bar.thm)\n"
  );

  plan = planOrThrow(project, "foo.sig", "bar.sig");
  assert.equal(
    plan.files.get("README.md")?.text,
    "[proof](./foo.thm#top) and [spec](bar.sig)\n" +
      "[reference]: foo.thm \"Proof\"\n"
  );
});

test("renaming a non-Abella file leaves Abella text alone", () => {
  const project = makeProject({
    "notes.txt": "hello\n",
    "main.thm": 'Specification "foo".\n',
  });
  const plan = planOrThrow(project, "notes.txt", "notes2.txt");
  assert.equal(plan.files.get("notes2.txt")?.text, "hello\n");
  assert.equal(
    plan.files.get("main.thm")?.text,
    'Specification "foo".\n'
  );
});

test("the original project is not mutated", () => {
  const project = makeProject({
    "foo.sig": "sig foo.\n",
    "foo.mod": "module foo.\n",
    "main.thm": 'Specification "foo".\n',
  });
  planOrThrow(project, "foo.sig", "bar.sig");
  assert.equal(project.files.has("foo.sig"), true);
  assert.equal(project.files.get("foo.sig")?.text, "sig foo.\n");
  assert.equal(
    project.files.get("main.thm")?.text,
    'Specification "foo".\n'
  );
});
