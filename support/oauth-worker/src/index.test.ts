// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { afterEach, test } from "node:test";
import assert from "node:assert/strict";
import worker, { type Env } from "./index";

const ALLOWED_ORIGIN = "https://abella-prover.org";
const CLIENT_ID = "client-id";
const CLIENT_SECRET = "client-secret";
const REDIRECT_URI = `${ALLOWED_ORIGIN}/web/github-callback.html`;
const GITHUB_TOKEN_URL = "https://github.com/login/oauth/access_token";

const realFetch = globalThis.fetch;
let fetchCalls: { url: string; init: RequestInit | undefined }[] = [];

afterEach(() => {
  globalThis.fetch = realFetch;
  fetchCalls = [];
});

function testEnv(overrides: Partial<Env> = {}): Env {
  return {
    GITHUB_CLIENT_ID: CLIENT_ID,
    GITHUB_CLIENT_SECRET: CLIENT_SECRET,
    ALLOWED_ORIGIN,
    REDIRECT_URI,
    ...overrides,
  };
}

function makeRequest(
  path: string,
  init: RequestInit = {},
  origin: string | null = ALLOWED_ORIGIN
): Request {
  const headers = new Headers(init.headers);
  if (origin === null) headers.delete("Origin");
  else headers.set("Origin", origin);
  return new Request(`https://oauth.abella-prover.org${path}`, {
    ...init,
    headers,
  });
}

function jsonRequest(
  body: unknown,
  init: RequestInit = {},
  origin: string | null = ALLOWED_ORIGIN
): Request {
  return makeRequest(
    "/github/token",
    {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify(body),
      ...init,
    },
    origin
  );
}

async function postToken(
  body: unknown,
  env: Env = testEnv(),
  init: RequestInit = {}
): Promise<Response> {
  return worker.fetch(jsonRequest(body, init), env);
}

function mockFetch(
  handler: (
    url: string,
    init: RequestInit | undefined
  ) => Response | Promise<Response>
): void {
  fetchCalls = [];
  globalThis.fetch = (async (
    input: Parameters<typeof fetch>[0],
    init?: Parameters<typeof fetch>[1]
  ) => {
    const url = input instanceof Request ? input.url : input.toString();
    fetchCalls.push({ url, init });
    return handler(url, init);
  }) as typeof fetch;
}

function assertCommonHeaders(response: Response): void {
  assert.equal(response.headers.get("Cache-Control"), "no-store");
  assert.equal(response.headers.get("X-Content-Type-Options"), "nosniff");
}

function githubResponse(body: unknown, status = 200): Response {
  return new Response(JSON.stringify(body), {
    status,
    headers: { "Content-Type": "application/json" },
  });
}

test("config succeeds for the exact allowed origin", async () => {
  const response = await worker.fetch(
    makeRequest("/github/config"),
    testEnv()
  );
  assert.equal(response.status, 200);
  assert.deepEqual(await response.json(), {
    clientId: CLIENT_ID,
    redirectUri: REDIRECT_URI,
  });
  assertCommonHeaders(response);
  assert.equal(
    response.headers.get("Access-Control-Allow-Origin"),
    ALLOWED_ORIGIN
  );
  assert.equal(response.headers.get("Vary"), "Origin");
});

test("config does not expose the client secret", async () => {
  const response = await worker.fetch(
    makeRequest("/github/config"),
    testEnv()
  );
  const text = await response.text();
  assert.equal(text.includes(CLIENT_SECRET), false);
  assert.equal(text.includes("secret"), false);
});

test("config rejects another origin", async () => {
  const response = await worker.fetch(
    makeRequest("/github/config", {}, "https://evil.example"),
    testEnv()
  );
  assert.equal(response.status, 403);
  assert.deepEqual(await response.json(), {
    error: "forbidden",
    message: "Origin is not allowed.",
  });
  assert.equal(
    response.headers.get("Access-Control-Allow-Origin"),
    null
  );
  assertCommonHeaders(response);
});

test("config rejects a missing origin", async () => {
  const response = await worker.fetch(
    makeRequest("/github/config", {}, null),
    testEnv()
  );
  assert.equal(response.status, 403);
  assert.equal(
    response.headers.get("Access-Control-Allow-Origin"),
    null
  );
});

test("config returns 503 when the worker is not configured", async () => {
  const response = await worker.fetch(
    makeRequest("/github/config"),
    testEnv({ REDIRECT_URI: undefined })
  );
  assert.equal(response.status, 503);
  const text = await response.text();
  assert.equal(text.includes(CLIENT_SECRET), false);
  assert.equal(text.includes("unavailable"), true);
  assert.equal(
    response.headers.get("Access-Control-Allow-Origin"),
    ALLOWED_ORIGIN
  );
});

test("preflight succeeds for the allowed origin", async () => {
  for (const path of ["/github/config", "/github/token"]) {
    const response = await worker.fetch(
      makeRequest(path, { method: "OPTIONS" }),
      testEnv()
    );
    assert.equal(response.status, 204);
    assertCommonHeaders(response);
    assert.equal(
      response.headers.get("Access-Control-Allow-Origin"),
      ALLOWED_ORIGIN
    );
    assert.equal(
      response.headers.get("Access-Control-Allow-Methods"),
      "POST, GET, OPTIONS"
    );
    assert.equal(
      response.headers.get("Access-Control-Allow-Headers"),
      "Content-Type"
    );
    assert.equal(
      response.headers.get("Access-Control-Max-Age"),
      "600"
    );
  }
});

test("preflight rejects a disallowed origin", async () => {
  const response = await worker.fetch(
    makeRequest(
      "/github/token",
      { method: "OPTIONS" },
      "https://evil.example"
    ),
    testEnv()
  );
  assert.equal(response.status, 403);
  assert.equal(
    response.headers.get("Access-Control-Allow-Origin"),
    null
  );
});

test("preflight rejects a missing origin", async () => {
  const response = await worker.fetch(
    makeRequest("/github/token", { method: "OPTIONS" }, null),
    testEnv()
  );
  assert.equal(response.status, 403);
});

test("rejects methods that are not allowed", async () => {
  const configPost = await worker.fetch(
    makeRequest("/github/config", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: "{}",
    }),
    testEnv()
  );
  assert.equal(configPost.status, 405);
  assert.equal(configPost.headers.get("Allow"), "GET, OPTIONS");

  const tokenGet = await worker.fetch(
    makeRequest("/github/token"),
    testEnv()
  );
  assert.equal(tokenGet.status, 405);
  assert.equal(tokenGet.headers.get("Allow"), "POST, OPTIONS");

  const tokenPut = await worker.fetch(
    makeRequest("/github/token", { method: "PUT" }),
    testEnv()
  );
  assert.equal(tokenPut.status, 405);
});

test("unknown routes return 404", async () => {
  const response = await worker.fetch(
    makeRequest("/health"),
    testEnv()
  );
  assert.equal(response.status, 404);
  assert.deepEqual(await response.json(), {
    error: "not_found",
    message: "Not found.",
  });
});

test("rejects a body that is not JSON", async () => {
  const response = await postToken(
    { code: "x", codeVerifier: "y" },
    testEnv(),
    { body: "{" }
  );
  assert.equal(response.status, 400);
  assert.deepEqual(await response.json(), {
    error: "invalid_json",
    message: "Request body is not valid JSON.",
  });
});

test("rejects a missing JSON content type", async () => {
  const response = await postToken(
    { code: "x", codeVerifier: "y" },
    testEnv(),
    { headers: {} }
  );
  assert.equal(response.status, 400);
  assert.deepEqual(await response.json(), {
    error: "invalid_request",
    message: "Expected a JSON request body.",
  });
});

test("rejects missing or invalid fields", async () => {
  const bodies: unknown[] = [
    null,
    [],
    {},
    { code: "x" },
    { codeVerifier: "y" },
    { code: "", codeVerifier: "y" },
    { code: "x", codeVerifier: "" },
    { code: 1, codeVerifier: "y" },
    { code: "x", codeVerifier: 2 },
  ];
  for (const body of bodies) {
    const response = await postToken(body);
    assert.equal(response.status, 400, JSON.stringify(body));
  }
  const longCode = await postToken({
    code: "a".repeat(513),
    codeVerifier: "y",
  });
  assert.equal(longCode.status, 400);
  const longVerifier = await postToken({
    code: "x",
    codeVerifier: "a".repeat(129),
  });
  assert.equal(longVerifier.status, 400);
});

test("rejects an oversized body", async () => {
  const response = await postToken({
    code: "x",
    codeVerifier: "y",
    padding: "a".repeat(5000),
  });
  assert.equal(response.status, 413);
  assert.deepEqual(await response.json(), {
    error: "payload_too_large",
    message: "Request body is too large.",
  });
});

test("rejects an oversized declared content length", async () => {
  const response = await postToken(
    { code: "x", codeVerifier: "y" },
    testEnv(),
    {
      headers: {
        "Content-Type": "application/json",
        "Content-Length": "5000",
      },
    }
  );
  assert.equal(response.status, 413);
});

test("exchanges a code with the expected form fields", async () => {
  mockFetch(() =>
    githubResponse({
      access_token: "gho_token",
      scope: "public_repo",
      token_type: "bearer",
      refresh_token: "refresh-token",
      expires_in: 3600,
    })
  );
  const response = await postToken({
    code: "code-123",
    codeVerifier: "verifier-123",
  });
  assert.equal(response.status, 200);
  assert.deepEqual(await response.json(), {
    token: "gho_token",
    scope: "public_repo",
  });
  assertCommonHeaders(response);
  assert.equal(
    response.headers.get("Access-Control-Allow-Origin"),
    ALLOWED_ORIGIN
  );
  assert.equal(fetchCalls.length, 1);
  assert.equal(fetchCalls[0]!.url, GITHUB_TOKEN_URL);
  const init = fetchCalls[0]!.init!;
  assert.equal(init.method, "POST");
  assert.equal(init.redirect, "manual");
  assert.ok(init.signal instanceof AbortSignal);
  const headers = new Headers(init.headers);
  assert.equal(headers.get("Accept"), "application/json");
  assert.equal(
    headers.get("Content-Type"),
    "application/x-www-form-urlencoded"
  );
  assert.equal(typeof init.body, "string");
  const form = new URLSearchParams(init.body as string);
  assert.equal(form.get("client_id"), CLIENT_ID);
  assert.equal(form.get("client_secret"), CLIENT_SECRET);
  assert.equal(form.get("code"), "code-123");
  assert.equal(form.get("redirect_uri"), REDIRECT_URI);
  assert.equal(form.get("code_verifier"), "verifier-123");
});

test("ignores a client-supplied redirect URI", async () => {
  mockFetch(() =>
    githubResponse({ access_token: "gho_token", scope: "public_repo" })
  );
  const response = await postToken({
    code: "code-123",
    codeVerifier: "verifier-123",
    redirect_uri: "https://evil.example/callback",
  });
  assert.equal(response.status, 200);
  const form = new URLSearchParams(
    fetchCalls[0]!.init!.body as string
  );
  assert.equal(form.get("redirect_uri"), REDIRECT_URI);
});

test("defaults a missing scope to an empty string", async () => {
  mockFetch(() => githubResponse({ access_token: "gho_token" }));
  const response = await postToken({
    code: "code-123",
    codeVerifier: "verifier-123",
  });
  assert.equal(response.status, 200);
  assert.deepEqual(await response.json(), {
    token: "gho_token",
    scope: "",
  });
});

test("maps a GitHub 200 error to a safe 400", async () => {
  mockFetch(() =>
    githubResponse({
      error: "bad_verification_code",
      error_description: "The code passed is incorrect or expired.",
    })
  );
  const response = await postToken({
    code: "leaky-code",
    codeVerifier: "leaky-verifier",
  });
  assert.equal(response.status, 400);
  const text = await response.text();
  assert.equal(text.includes("leaky-code"), false);
  assert.equal(text.includes("leaky-verifier"), false);
  assert.equal(text.includes(CLIENT_SECRET), false);
  assert.equal(text.includes("bad_verification_code"), false);
  assert.deepEqual(JSON.parse(text), {
    error: "invalid_code",
    message: "GitHub rejected the code.",
  });
  assertCommonHeaders(response);
  assert.equal(
    response.headers.get("Access-Control-Allow-Origin"),
    ALLOWED_ORIGIN
  );
});

test("maps access_denied to a 400", async () => {
  mockFetch(() => githubResponse({ error: "access_denied" }));
  const response = await postToken({
    code: "code",
    codeVerifier: "verifier",
  });
  assert.equal(response.status, 400);
  assert.deepEqual(await response.json(), {
    error: "access_denied",
    message: "GitHub denied the authorization request.",
  });
});

test("does not follow an upstream redirect", async () => {
  mockFetch(
    () =>
      new Response(null, {
        status: 302,
        headers: { Location: "https://evil.example/token" },
      })
  );
  const response = await postToken({
    code: "code",
    codeVerifier: "verifier",
  });
  assert.equal(response.status, 502);
  assert.equal(fetchCalls.length, 1);
});

test("maps a GitHub 5xx to 502", async () => {
  mockFetch(() =>
    new Response("upstream down", { status: 503 })
  );
  const response = await postToken({
    code: "code",
    codeVerifier: "verifier",
  });
  assert.equal(response.status, 502);
  assertCommonHeaders(response);
});

test("maps a network failure to 502", async () => {
  mockFetch(() => {
    throw new TypeError("fetch failed");
  });
  const response = await postToken({
    code: "code",
    codeVerifier: "verifier",
  });
  assert.equal(response.status, 502);
  assert.deepEqual(await response.json(), {
    error: "upstream_unavailable",
    message: "GitHub could not be reached.",
  });
});

test("maps a timeout to 504", async () => {
  mockFetch(() => {
    const error = new Error("The operation was aborted.");
    error.name = "TimeoutError";
    throw error;
  });
  const response = await postToken({
    code: "code",
    codeVerifier: "verifier",
  });
  assert.equal(response.status, 504);
  assert.deepEqual(await response.json(), {
    error: "upstream_timeout",
    message: "GitHub did not respond in time.",
  });
});

test("maps invalid upstream JSON to 502", async () => {
  mockFetch(() => new Response("not json", { status: 200 }));
  const response = await postToken({
    code: "code",
    codeVerifier: "verifier",
  });
  assert.equal(response.status, 502);
  assert.deepEqual(await response.json(), {
    error: "upstream_error",
    message: "GitHub returned an invalid response.",
  });
});

test("maps a missing access token to 502", async () => {
  mockFetch(() => githubResponse({ scope: "public_repo" }));
  const response = await postToken({
    code: "code",
    codeVerifier: "verifier",
  });
  assert.equal(response.status, 502);
  assert.deepEqual(await response.json(), {
    error: "upstream_error",
    message: "GitHub returned an invalid token response.",
  });
});

test("rejects a token exchange from another origin", async () => {
  mockFetch(() =>
    githubResponse({ access_token: "gho_token", scope: "public_repo" })
  );
  const response = await worker.fetch(
    jsonRequest(
      { code: "code", codeVerifier: "verifier" },
      {},
      "https://evil.example"
    ),
    testEnv()
  );
  assert.equal(response.status, 403);
  assert.equal(fetchCalls.length, 0);
  assert.equal(
    response.headers.get("Access-Control-Allow-Origin"),
    null
  );
});
