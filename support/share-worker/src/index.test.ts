// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  handleRequest,
  MAX_ZIP_BYTES,
  TTL_SECONDS,
  type Env,
} from "./handler";

const ZIP = new Uint8Array([
  0x50, 0x4b, 0x03, 0x04, 0x14, 0x00, 0x00, 0x00,
]);

const NOW = 1_700_000_000_000;
const ID = "a".repeat(32);

interface Entry {
  value: ArrayBuffer;
  ttl?: number;
}

function fakeEnv(failPut = false, failGet = false): {
  env: Env;
  store: Map<string, Entry>;
} {
  const store = new Map<string, Entry>();
  const env = {
    ZIPS: {
      async put(
        key: string,
        value: ArrayBuffer,
        options?: { expirationTtl?: number }
      ) {
        if (failPut) throw new Error("KV PUT failed: daily limit");
        store.set(key, { value, ttl: options?.expirationTtl });
      },
      async get(key: string, _type?: string) {
        if (failGet) throw new Error("KV GET failed: daily limit");
        return store.get(key)?.value ?? null;
      },
      async delete(key: string) {
        store.delete(key);
      },
      async list() {
        return { keys: [], list_complete: true, cursor: "" };
      },
    },
  } as unknown as Env;
  return { env, store };
}

function upload(
  body: BodyInit = ZIP,
  headers: Record<string, string> = {
    "content-type": "application/zip",
  }
): Request {
  return new Request("https://zips.example/zips", {
    method: "POST",
    headers,
    body,
  });
}

function options(now = NOW) {
  return { now: () => now, newId: () => ID };
}

test("a valid zip is stored under its expiry and id", async () => {
  const { env, store } = fakeEnv();
  const response = await handleRequest(upload(), env, options());

  assert.equal(response.status, 201);
  const body = (await response.json()) as {
    url: string;
    expiresAt: number;
    retryAfterSeconds: number;
  };
  const expiresAt = NOW + TTL_SECONDS * 1000;
  assert.equal(body.expiresAt, expiresAt);
  assert.equal(body.url, `https://zips.example/zips/${expiresAt}/${ID}`);
  assert.equal(body.retryAfterSeconds, 60);
  assert.equal(
    response.headers.get("access-control-allow-origin"),
    "*"
  );

  const stored = store.get(`zips/${expiresAt}/${ID}`);
  assert.ok(stored);
  assert.equal(stored.ttl, TTL_SECONDS);
});

test("upload rejects the wrong media type and a non-zip body", async () => {
  const { env } = fakeEnv();

  const wrongType = await handleRequest(
    upload(ZIP, { "content-type": "text/plain" }),
    env,
    options()
  );
  assert.equal(wrongType.status, 415);

  const notZip = await handleRequest(
    upload(new Uint8Array([0x50, 0x4b, 0x03, 0x05])),
    env,
    options()
  );
  assert.equal(notZip.status, 415);
});

test("upload rejects empty and oversized archives", async () => {
  const { env } = fakeEnv();

  const empty = await handleRequest(upload(new Uint8Array()), env, options());
  assert.equal(empty.status, 400);

  const oversized = await handleRequest(upload(ZIP), env, {
    ...options(),
    maxBytes: 4,
  });
  assert.equal(oversized.status, 413);
});

test("upload maps a KV write limit to 503", async () => {
  const { env } = fakeEnv(true);
  const response = await handleRequest(upload(), env, options());
  assert.equal(response.status, 503);
  assert.equal(response.headers.get("retry-after"), "60");
});

test("download returns the stored zip with attachment headers", async () => {
  const { env } = fakeEnv();
  await handleRequest(upload(), env, options());
  const expiresAt = NOW + TTL_SECONDS * 1000;

  const response = await handleRequest(
    new Request(`https://zips.example/zips/${expiresAt}/${ID}`),
    env,
    options()
  );
  assert.equal(response.status, 200);
  assert.equal(response.headers.get("content-type"), "application/zip");
  assert.equal(
    response.headers.get("content-disposition"),
    'attachment; filename="abella-web.zip"'
  );
  assert.equal(response.headers.get("cache-control"), "no-store");
  assert.deepEqual(new Uint8Array(await response.arrayBuffer()), ZIP);
});

test("download returns 404 before KV propagation and 410 after expiry", async () => {
  const { env } = fakeEnv();
  const expiresAt = NOW + TTL_SECONDS * 1000;

  const missing = await handleRequest(
    new Request(`https://zips.example/zips/${expiresAt}/${ID}`),
    env,
    options()
  );
  assert.equal(missing.status, 404);

  await handleRequest(upload(), env, options());
  const expired = await handleRequest(
    new Request(`https://zips.example/zips/${expiresAt}/${ID}`),
    env,
    options(expiresAt + 1)
  );
  assert.equal(expired.status, 410);
});

test("download maps a KV read limit to 503", async () => {
  const { env } = fakeEnv(false, true);
  const expiresAt = NOW + TTL_SECONDS * 1000;
  const response = await handleRequest(
    new Request(`https://zips.example/zips/${expiresAt}/${ID}`),
    env,
    options()
  );
  assert.equal(response.status, 503);
});

test("preflight and health are available, unknown routes are 404", async () => {
  const { env } = fakeEnv();

  const preflight = await handleRequest(
    new Request("https://zips.example/zips", { method: "OPTIONS" }),
    env
  );
  assert.equal(preflight.status, 204);
  assert.equal(
    preflight.headers.get("access-control-allow-methods"),
    "GET, POST, OPTIONS"
  );

  const health = await handleRequest(
    new Request("https://zips.example/health"),
    env
  );
  assert.equal(health.status, 200);

  const unknown = await handleRequest(
    new Request("https://zips.example/nope"),
    env
  );
  assert.equal(unknown.status, 404);
});

test("the default size cap is the documented 8 MiB", () => {
  assert.equal(MAX_ZIP_BYTES, 8 * 1024 * 1024);
  assert.equal(TTL_SECONDS, 600);
});
