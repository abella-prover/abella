// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { afterEach, test } from "node:test";
import assert from "node:assert/strict";
import {
  createOAuthRequest,
  exchangeGitHubCode,
  fetchGitHubOAuthConfig,
  validateGitHubToken,
  type GitHubOAuthConfig,
} from "./github-oauth";
import {
  isOAuthCallback,
  OAUTH_CALLBACK_TYPE,
  parseOAuthCallback,
} from "./oauth-callback";
import { GITHUB_OAUTH_WORKER } from "./github-oauth-config";
import { WorkspaceError } from "./workspace";

const CONFIG: GitHubOAuthConfig = {
  clientId: "client-id",
  redirectUri: "https://abella-prover.org/web/github-callback.html",
};

const realFetch = globalThis.fetch;
let calls: { url: string; init: RequestInit | undefined }[] = [];

afterEach(() => {
  globalThis.fetch = realFetch;
  calls = [];
});

function jsonResponse(body: unknown, status = 200): Response {
  return new Response(JSON.stringify(body), {
    status,
    headers: { "Content-Type": "application/json" },
  });
}

function mockFetch(
  handler: (
    url: string,
    init: RequestInit | undefined
  ) => Response | Promise<Response>
): void {
  calls = [];
  globalThis.fetch = (async (
    input: Parameters<typeof fetch>[0],
    init?: Parameters<typeof fetch>[1]
  ) => {
    const url = input instanceof Request ? input.url : input.toString();
    calls.push({ url, init });
    return handler(url, init);
  }) as typeof fetch;
}

async function rejectsWith(
  operation: Promise<unknown>,
  code: string
): Promise<WorkspaceError> {
  try {
    await operation;
  } catch (error) {
    assert.ok(error instanceof WorkspaceError);
    assert.equal(error.code, code);
    return error;
  }
  assert.fail("expected the operation to reject");
}

function testBase64url(bytes: Uint8Array): string {
  let binary = "";
  for (const byte of bytes) {
    binary += String.fromCharCode(byte);
  }
  return btoa(binary)
    .replace(/\+/g, "-")
    .replace(/\//g, "_")
    .replace(/=+$/, "");
}

async function expectedChallenge(verifier: string): Promise<string> {
  const digest = await crypto.subtle.digest(
    "SHA-256",
    new TextEncoder().encode(verifier)
  );
  return testBase64url(new Uint8Array(digest));
}

test("OAuth state and verifier are base64url random values", async () => {
  const request = await createOAuthRequest(CONFIG, "public_repo");
  assert.equal(request.state.length, 43);
  assert.equal(request.verifier.length, 43);
  assert.match(request.state, /^[A-Za-z0-9_-]{43}$/);
  assert.match(request.verifier, /^[A-Za-z0-9._~-]{43}$/);
  for (const value of [request.state, request.verifier]) {
    assert.equal(value.includes("+"), false);
    assert.equal(value.includes("/"), false);
    assert.equal(value.includes("="), false);
  }
});

test("OAuth requests use fresh state and verifier values", async () => {
  const first = await createOAuthRequest(CONFIG, "public_repo");
  const second = await createOAuthRequest(CONFIG, "public_repo");
  assert.notEqual(first.state, second.state);
  assert.notEqual(first.verifier, second.verifier);
});

test("OAuth URL carries the PKCE challenge and no secret", async () => {
  const request = await createOAuthRequest(CONFIG, "public_repo");
  const url = new URL(request.url);
  assert.equal(
    `${url.origin}${url.pathname}`,
    "https://github.com/login/oauth/authorize"
  );
  assert.equal(url.searchParams.get("client_id"), CONFIG.clientId);
  assert.equal(
    url.searchParams.get("redirect_uri"),
    CONFIG.redirectUri
  );
  assert.equal(url.searchParams.get("scope"), "public_repo");
  assert.equal(url.searchParams.get("state"), request.state);
  assert.equal(
    url.searchParams.get("code_challenge"),
    await expectedChallenge(request.verifier)
  );
  assert.equal(
    url.searchParams.get("code_challenge_method"),
    "S256"
  );
  assert.equal(url.searchParams.has("client_secret"), false);
});

test("OAuth requests can ask for private repositories", async () => {
  const request = await createOAuthRequest(CONFIG, "repo");
  const url = new URL(request.url);
  assert.equal(url.searchParams.get("scope"), "repo");
});

test("OAuth requests reject incomplete configuration", async () => {
  await rejectsWith(
    createOAuthRequest(
      { clientId: "", redirectUri: CONFIG.redirectUri },
      "public_repo"
    ),
    "io"
  );
});

test("parseOAuthCallback reads code, state, and unknown fields", () => {
  const callback = parseOAuthCallback(
    "?code=abc&state=xyz&iss=https%3A%2F%2Fgithub.com%2Flogin%2Foauth"
  );
  assert.equal(callback.type, OAUTH_CALLBACK_TYPE);
  assert.equal(callback.code, "abc");
  assert.equal(callback.state, "xyz");
  assert.equal(callback.error, undefined);
  assert.equal(callback.errorDescription, undefined);
});

test("parseOAuthCallback reads an access_denied response", () => {
  const callback = parseOAuthCallback(
    "?error=access_denied&error_description=The+user+denied"
  );
  assert.equal(callback.error, "access_denied");
  assert.equal(callback.errorDescription, "The user denied");
  assert.equal(callback.code, undefined);
});

test("parseOAuthCallback tolerates missing and empty fields", () => {
  for (const search of [
    "",
    "?state=xyz",
    "?code=&state=",
    "not-a-query",
  ]) {
    const callback = parseOAuthCallback(search);
    assert.equal(callback.code, undefined);
    assert.equal(callback.error, undefined);
    assert.equal(callback.errorDescription, undefined);
  }
});

test("isOAuthCallback accepts the callback shape", () => {
  const callback = parseOAuthCallback("?code=abc&state=xyz");
  assert.equal(isOAuthCallback(callback), true);
  assert.equal(isOAuthCallback({ ...callback, extra: 1 }), true);
  assert.equal(isOAuthCallback({ type: OAUTH_CALLBACK_TYPE }), true);
});

test("isOAuthCallback rejects other payloads", () => {
  assert.equal(isOAuthCallback(null), false);
  assert.equal(isOAuthCallback([]), false);
  assert.equal(isOAuthCallback("abella-github-oauth"), false);
  assert.equal(isOAuthCallback({ type: "other" }), false);
  assert.equal(
    isOAuthCallback({ type: OAUTH_CALLBACK_TYPE, code: 1 }),
    false
  );
  assert.equal(
    isOAuthCallback({
      type: OAUTH_CALLBACK_TYPE,
      errorDescription: 1,
    }),
    false
  );
});

test("the Worker URL defaults to the production origin", () => {
  assert.equal(
    GITHUB_OAUTH_WORKER,
    "https://oauth.abella-prover.org"
  );
});

test("fetchGitHubOAuthConfig reads the worker configuration", async () => {
  mockFetch(() =>
    jsonResponse({
      clientId: CONFIG.clientId,
      redirectUri: CONFIG.redirectUri,
    })
  );
  const config = await fetchGitHubOAuthConfig("https://oauth.example/");
  assert.deepEqual(config, CONFIG);
  assert.equal(calls.length, 1);
  assert.equal(calls[0]!.url, "https://oauth.example/github/config");
  const init = calls[0]!.init!;
  assert.equal(init.method, "GET");
  assert.equal(init.credentials, "omit");
  assert.equal(init.cache, "no-store");
  assert.equal(
    new Headers(init.headers).get("Accept"),
    "application/json"
  );
});

test("fetchGitHubOAuthConfig rejects an unavailable worker", async () => {
  mockFetch(() =>
    jsonResponse(
      { error: "unavailable", message: "Not configured." },
      503
    )
  );
  const error = await rejectsWith(
    fetchGitHubOAuthConfig("https://oauth.example"),
    "unavailable"
  );
  assert.equal(error.message.includes("unavailable"), true);
});

test("fetchGitHubOAuthConfig rejects an invalid configuration", async () => {
  mockFetch(() =>
    jsonResponse({ clientId: "client-id", redirectUri: "not a url" })
  );
  await rejectsWith(
    fetchGitHubOAuthConfig("https://oauth.example"),
    "io"
  );
});

test("fetchGitHubOAuthConfig maps a network failure", async () => {
  mockFetch(() => {
    throw new TypeError("fetch failed");
  });
  await rejectsWith(
    fetchGitHubOAuthConfig("https://oauth.example"),
    "unavailable"
  );
});

test("exchangeGitHubCode posts the code and verifier", async () => {
  mockFetch(() =>
    jsonResponse({ token: "gho_test", scope: "public_repo" })
  );
  const token = await exchangeGitHubCode(
    "https://oauth.example",
    "code-123",
    "verifier-123"
  );
  assert.deepEqual(token, {
    token: "gho_test",
    scope: "public_repo",
  });
  assert.equal(calls.length, 1);
  assert.equal(calls[0]!.url, "https://oauth.example/github/token");
  const init = calls[0]!.init!;
  assert.equal(init.method, "POST");
  assert.equal(init.credentials, "omit");
  assert.equal(init.cache, "no-store");
  const headers = new Headers(init.headers);
  assert.equal(headers.get("Accept"), "application/json");
  assert.equal(headers.get("Content-Type"), "application/json");
  const body = JSON.parse(init.body as string) as Record<string, unknown>;
  assert.equal(body.redirect_uri, undefined);
  assert.deepEqual(body, {
    code: "code-123",
    codeVerifier: "verifier-123",
  });
});

test("exchangeGitHubCode defaults a missing scope", async () => {
  mockFetch(() => jsonResponse({ token: "gho_test" }));
  const token = await exchangeGitHubCode(
    "https://oauth.example",
    "code",
    "verifier"
  );
  assert.deepEqual(token, { token: "gho_test", scope: "" });
});

test("exchangeGitHubCode maps worker errors", async () => {
  const cases: [string, string][] = [
    ["access_denied", "cancelled"],
    ["invalid_code", "permission-denied"],
    ["configuration_error", "io"],
    ["forbidden", "io"],
    ["invalid_request", "io"],
    ["invalid_json", "io"],
    ["payload_too_large", "io"],
    ["method_not_allowed", "io"],
    ["upstream_unavailable", "unavailable"],
    ["upstream_timeout", "unavailable"],
    ["unexpected", "unavailable"],
  ];
  for (const [error, code] of cases) {
    mockFetch(() => jsonResponse({ error, message: "safe" }, 400));
    await rejectsWith(
      exchangeGitHubCode("https://oauth.example", "code", "verifier"),
      code
    );
  }
});

test("exchangeGitHubCode maps a network failure", async () => {
  mockFetch(() => {
    throw new TypeError("fetch failed");
  });
  await rejectsWith(
    exchangeGitHubCode("https://oauth.example", "code", "verifier"),
    "unavailable"
  );
});

test("exchangeGitHubCode rejects an invalid success body", async () => {
  mockFetch(() => jsonResponse({ scope: "public_repo" }));
  await rejectsWith(
    exchangeGitHubCode("https://oauth.example", "code", "verifier"),
    "io"
  );
});

test("exchangeGitHubCode does not echo the code or verifier", async () => {
  mockFetch(() =>
    jsonResponse({ error: "invalid_code", message: "safe" }, 400)
  );
  const error = await rejectsWith(
    exchangeGitHubCode(
      "https://oauth.example",
      "secret-code",
      "secret-verifier"
    ),
    "permission-denied"
  );
  assert.equal(error.message.includes("secret-code"), false);
  assert.equal(error.message.includes("secret-verifier"), false);
});

test("validateGitHubToken reads the account login", async () => {
  mockFetch(() => jsonResponse({ login: "octocat" }));
  const user = await validateGitHubToken("gho_test");
  assert.deepEqual(user, { login: "octocat" });
  assert.equal(calls.length, 1);
  assert.equal(calls[0]!.url, "https://api.github.com/user");
  const init = calls[0]!.init!;
  assert.equal(init.method, "GET");
  assert.equal(init.credentials, "omit");
  assert.equal(init.cache, "no-store");
  const headers = new Headers(init.headers);
  assert.equal(headers.get("Authorization"), "Bearer gho_test");
  assert.equal(
    headers.get("Accept"),
    "application/vnd.github+json"
  );
  assert.equal(
    headers.get("X-GitHub-Api-Version"),
    "2022-11-28"
  );
});

test("validateGitHubToken rejects an empty token", async () => {
  await rejectsWith(validateGitHubToken(""), "permission-denied");
  assert.equal(calls.length, 0);
});

test("validateGitHubToken maps a 401 to permission denied", async () => {
  mockFetch(() => jsonResponse({ message: "Bad credentials" }, 401));
  const error = await rejectsWith(
    validateGitHubToken("gho_test"),
    "permission-denied"
  );
  assert.equal(error.status, 401);
});

test("validateGitHubToken maps a 403 to unavailable", async () => {
  mockFetch(() => jsonResponse({ message: "Forbidden" }, 403));
  await rejectsWith(validateGitHubToken("gho_test"), "unavailable");
});

test("validateGitHubToken maps a server failure", async () => {
  mockFetch(() => jsonResponse({ message: "Server error" }, 500));
  await rejectsWith(validateGitHubToken("gho_test"), "unavailable");
});

test("validateGitHubToken maps a network failure", async () => {
  mockFetch(() => {
    throw new TypeError("fetch failed");
  });
  await rejectsWith(validateGitHubToken("gho_test"), "unavailable");
});

test("validateGitHubToken rejects an invalid user response", async () => {
  mockFetch(() => jsonResponse({ login: "" }));
  await rejectsWith(validateGitHubToken("gho_test"), "io");
});
