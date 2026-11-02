// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import { strToU8, zipSync } from "fflate";
import {
  MAX_SHARE_BYTES,
  loadSharedProject,
  resolveShareUrl,
  zipParam,
  type Fetcher,
} from "./share";
import { WorkspaceError } from "./workspace";

const ORIGINS = ["https://zips.example"];
const LINK = "https://zips.example/zips/1/abc";

function projectZip(): ArrayBuffer {
  const bytes = zipSync({
    "project.json": strToU8(
      JSON.stringify({
        version: 2,
        entry: "main.thm",
        files: ["main.thm"],
      })
    ),
    "main.thm": strToU8('Specification "x".\n'),
  });
  const copy = new Uint8Array(bytes.byteLength);
  copy.set(bytes);
  return copy.buffer;
}

function status(code: number, headers: Record<string, string> = {}): Response {
  return new Response("", { status: code, headers });
}

test("zipParam reads a non-empty zip query", () => {
  assert.equal(zipParam("?zip=abc"), "abc");
  assert.equal(zipParam("?zip=%20%20"), undefined);
  assert.equal(zipParam("?other=1"), undefined);
});

test("share URLs are origin- and scheme-checked", () => {
  assert.equal(resolveShareUrl(LINK, ORIGINS).origin, ORIGINS[0]);

  assert.throws(
    () => resolveShareUrl("https://evil.example/zips/1/abc", ORIGINS),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "permission-denied"
  );
  assert.throws(
    () => resolveShareUrl("/zips/1/abc", ORIGINS),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "unsupported"
  );
  assert.throws(
    () =>
      resolveShareUrl("https://user:pass@zips.example/zips/1/abc", ORIGINS),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "permission-denied"
  );
});

test("a 404 is retried until KV propagates the write", async () => {
  let calls = 0;
  const waits: number[] = [];
  const events: number[] = [];
  const fetcher: Fetcher = async () => {
    calls += 1;
    return calls < 3
      ? status(404)
      : new Response(projectZip());
  };
  const imported = await loadSharedProject(LINK, {
    fetcher,
    origins: ORIGINS,
    retryDelays: [1, 2],
    sleep: async (ms) => {
      waits.push(ms);
    },
    onWaiting: (attempt) => {
      events.push(attempt);
    },
  });
  assert.equal(calls, 3);
  assert.deepEqual(waits, [1, 2]);
  assert.deepEqual(events, [1, 2]);
  assert.equal(imported.project.entry, "main.thm");
});

test("a persistent 404 stops after the retry list", async () => {
  let calls = 0;
  const fetcher: Fetcher = async () => {
    calls += 1;
    return status(404);
  };
  await assert.rejects(
    () =>
      loadSharedProject(LINK, {
        fetcher,
        origins: ORIGINS,
        retryDelays: [1, 2],
        sleep: async () => {},
      }),
    /not available/
  );
  assert.equal(calls, 3);
});

test("410 and 503 are terminal with distinct messages", async () => {
  let calls = 0;
  const fetcher: Fetcher = async () => {
    calls += 1;
    return status(410);
  };
  await assert.rejects(
    () =>
      loadSharedProject(LINK, {
        fetcher,
        origins: ORIGINS,
        retryDelays: [1],
        sleep: async () => {},
      }),
    /has expired/
  );
  assert.equal(calls, 1);

  await assert.rejects(
    () =>
      loadSharedProject(LINK, {
        fetcher: async () => status(503),
        origins: ORIGINS,
        retryDelays: [1],
        sleep: async () => {},
      }),
    /busy/
  );
});

test("an oversized archive is rejected before import", async () => {
  await assert.rejects(
    () =>
      loadSharedProject(LINK, {
        fetcher: async () =>
          new Response(projectZip(), {
            headers: {
              "content-length": String(MAX_SHARE_BYTES + 1),
            },
          }),
        origins: ORIGINS,
      }),
    /larger than/
  );
});

test("other HTTP failures are unavailable", async () => {
  await assert.rejects(
    () =>
      loadSharedProject(LINK, {
        fetcher: async () => status(500),
        origins: ORIGINS,
      }),
    (error: unknown) =>
      error instanceof WorkspaceError && error.code === "unavailable"
  );
});
