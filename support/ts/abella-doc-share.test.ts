// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { strFromU8, unzipSync } from "fflate";
import {
  MAX_ZIP_BYTES,
  buildProjectZip,
  parseShareData,
  readSources,
  shareTarget,
  uploadProject,
  type ShareData,
} from "./abella-doc-share";

const BASE = "https://docs.example/demo/";

const DATA: ShareData = {
  entry: "demo.thm",
  files: ["demo.thm", "demo.sig", "demo.mod"],
  web: "https://abella-prover.org/web/",
  share: "https://zips.abella-prover.org/",
};

function fakeFetch(
  routes: Record<string, string>
): typeof fetch {
  return (async (input: RequestInfo | URL) => {
    const path = new URL(String(input)).pathname;
    const body = routes[path];
    if (body === undefined) {
      return new Response("missing", { status: 404 });
    }
    return new Response(body);
  }) as typeof fetch;
}

test("share data parses and validates the embedded project", () => {
  const text = JSON.stringify(DATA);
  assert.deepEqual(parseShareData(text), DATA);
  assert.throws(
    () => parseShareData(JSON.stringify({ ...DATA, files: [] })),
    /entry is missing/
  );
  assert.throws(
    () => parseShareData(JSON.stringify({ ...DATA, share: "" })),
    /incomplete/
  );
  assert.throws(() => parseShareData("not json"), /not JSON/);
});

test("sources are fetched relative to the page", async () => {
  const { sources, totalBytes } = await readSources(
    DATA,
    fakeFetch({
      "/demo/demo.thm": 'Specification "demo".\n',
      "/demo/demo.sig": "sig demo.\n",
      "/demo/demo.mod": "module demo.\n",
    }),
    BASE
  );
  assert.equal(sources.get("demo.thm"), 'Specification "demo".\n');
  assert.equal(sources.get("demo.sig"), "sig demo.\n");
  assert.equal(
    totalBytes,
    new TextEncoder().encode(
      'Specification "demo".\nsig demo.\nmodule demo.\n'
    ).byteLength
  );
});

test("a missing source names the file", async () => {
  await assert.rejects(
    () =>
      readSources(
        DATA,
        fakeFetch({ "/demo/demo.thm": "Specification \"demo\".\n" }),
        BASE
      ),
    /demo\.sig \(HTTP 404\)/
  );
});

test("the project zip contains the manifest and every source", () => {
  const sources = new Map([
    ["demo.thm", 'Specification "demo".\n'],
    ["demo.sig", "sig demo.\n"],
    ["demo.mod", "module demo.\n"],
  ]);
  const bytes = buildProjectZip(DATA, sources);
  const entries = unzipSync(bytes);
  assert.deepEqual(
    Object.keys(entries).sort(),
    ["demo.mod", "demo.sig", "demo.thm", "project.json"]
  );
  assert.deepEqual(JSON.parse(strFromU8(entries["project.json"])), {
    version: 2,
    entry: "demo.thm",
    files: ["demo.mod", "demo.sig", "demo.thm"],
  });
  assert.equal(strFromU8(entries["demo.thm"]), sources.get("demo.thm"));
});

test("upload posts a zip and returns the download URL", async () => {
  let seen: RequestInit | undefined;
  const fetchFn = (async (
    input: RequestInfo | URL,
    init?: RequestInit
  ) => {
    assert.equal(String(input), "https://zips.example/zips");
    seen = init;
    return new Response(
      JSON.stringify({ url: "https://zips.example/zips/1/abc" }),
      { status: 201 }
    );
  }) as typeof fetch;

  const url = await uploadProject(
    "https://zips.example",
    new Uint8Array([0x50, 0x4b, 0x03, 0x04]),
    fetchFn,
    BASE
  );
  assert.equal(url, "https://zips.example/zips/1/abc");
  assert.equal(seen?.method, "POST");
  assert.equal(
    (seen?.headers as Record<string, string>)["Content-Type"],
    "application/zip"
  );
});

test("upload surfaces the Worker's error message", async () => {
  const fetchFn = (async () =>
    new Response(JSON.stringify({ message: "The share service is busy." }), {
      status: 503,
    })) as typeof fetch;
  await assert.rejects(
    () => uploadProject("https://zips.example", new Uint8Array([1]), fetchFn),
    /share service is busy/
  );
});

test("the Abella Web target carries the encoded zip URL", () => {
  const url = "https://zips.example/zips/1/abc";
  const target = shareTarget(DATA.web, url, BASE);
  assert.equal(
    target,
    `https://abella-prover.org/web/?zip=${encodeURIComponent(url)}`
  );
});

test("the 8 MiB cap matches the Worker", () => {
  assert.equal(MAX_ZIP_BYTES, 8 * 1024 * 1024);
});
