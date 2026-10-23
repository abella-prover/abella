// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Side-effect-free GitHub OAuth client.  It deliberately has no Octokit
// imports; the token is handed to the existing GitHub workspace later.

import { WorkspaceError } from "./workspace";

const AUTHORIZE_URL = "https://github.com/login/oauth/authorize";
const USER_URL = "https://api.github.com/user";

export type GitHubOAuthScope = "public_repo" | "repo";

export interface GitHubOAuthConfig {
  clientId: string;
  redirectUri: string;
}

export interface GitHubOAuthRequest {
  state: string;
  verifier: string;
  url: string;
}

export interface GitHubToken {
  token: string;
  scope: string;
}

export interface GitHubUser {
  login: string;
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function base64url(bytes: Uint8Array): string {
  let binary = "";
  for (const byte of bytes) {
    binary += String.fromCharCode(byte);
  }
  return btoa(binary)
    .replace(/\+/g, "-")
    .replace(/\//g, "_")
    .replace(/=+$/, "");
}

function randomBase64url(): string {
  return base64url(crypto.getRandomValues(new Uint8Array(32)));
}

async function sha256Base64url(value: string): Promise<string> {
  const digest = await crypto.subtle.digest(
    "SHA-256",
    new TextEncoder().encode(value)
  );
  return base64url(new Uint8Array(digest));
}

function workerEndpoint(workerUrl: string, path: string): string {
  return `${workerUrl.replace(/\/+$/, "")}${path}`;
}

async function readJson(response: Response): Promise<unknown> {
  try {
    return await response.json();
  } catch {
    return undefined;
  }
}

function isHttpUrl(value: string): boolean {
  try {
    const url = new URL(value);
    return url.protocol === "https:" || url.protocol === "http:";
  } catch {
    return false;
  }
}

export async function fetchGitHubOAuthConfig(
  workerUrl: string
): Promise<GitHubOAuthConfig> {
  let response: Response;
  try {
    response = await fetch(workerEndpoint(workerUrl, "/github/config"), {
      method: "GET",
      credentials: "omit",
      cache: "no-store",
      headers: { Accept: "application/json" },
    });
  } catch {
    throw new WorkspaceError(
      "unavailable",
      "Could not reach the GitHub sign-in service."
    );
  }
  if (!response.ok) {
    throw new WorkspaceError(
      "unavailable",
      "GitHub sign-in is unavailable right now."
    );
  }
  const body = await readJson(response);
  if (
    !isRecord(body) ||
    typeof body.clientId !== "string" ||
    body.clientId.length === 0 ||
    typeof body.redirectUri !== "string" ||
    !isHttpUrl(body.redirectUri)
  ) {
    throw new WorkspaceError(
      "io",
      "The GitHub sign-in service returned an invalid configuration."
    );
  }
  return { clientId: body.clientId, redirectUri: body.redirectUri };
}

export async function createOAuthRequest(
  config: GitHubOAuthConfig,
  scope: GitHubOAuthScope
): Promise<GitHubOAuthRequest> {
  if (!config.clientId || !config.redirectUri) {
    throw new WorkspaceError(
      "io",
      "The GitHub sign-in configuration is incomplete."
    );
  }
  const state = randomBase64url();
  const verifier = randomBase64url();
  const challenge = await sha256Base64url(verifier);
  const url = new URL(AUTHORIZE_URL);
  url.searchParams.set("client_id", config.clientId);
  url.searchParams.set("redirect_uri", config.redirectUri);
  url.searchParams.set("scope", scope);
  url.searchParams.set("state", state);
  url.searchParams.set("code_challenge", challenge);
  url.searchParams.set("code_challenge_method", "S256");
  return { state, verifier, url: url.toString() };
}

export async function exchangeGitHubCode(
  workerUrl: string,
  code: string,
  verifier: string
): Promise<GitHubToken> {
  if (!code || !verifier) {
    throw new WorkspaceError(
      "io",
      "The GitHub sign-in request is incomplete."
    );
  }
  let response: Response;
  try {
    response = await fetch(workerEndpoint(workerUrl, "/github/token"), {
      method: "POST",
      credentials: "omit",
      cache: "no-store",
      headers: {
        Accept: "application/json",
        "Content-Type": "application/json",
      },
      body: JSON.stringify({ code, codeVerifier: verifier }),
    });
  } catch {
    throw new WorkspaceError(
      "unavailable",
      "Could not reach the GitHub sign-in service."
    );
  }
  const body = await readJson(response);
  if (response.ok) {
    if (
      !isRecord(body) ||
      typeof body.token !== "string" ||
      body.token.length === 0
    ) {
      throw new WorkspaceError(
        "io",
        "The GitHub sign-in service returned an invalid response."
      );
    }
    const scope = typeof body.scope === "string" ? body.scope : "";
    return { token: body.token, scope };
  }
  const error =
    isRecord(body) && typeof body.error === "string" ? body.error : "";
  switch (error) {
    case "access_denied":
      throw new WorkspaceError("cancelled", "GitHub sign-in was cancelled.");
    case "invalid_code":
      throw new WorkspaceError(
        "permission-denied",
        "GitHub sign-in expired. Try again."
      );
    case "configuration_error":
      throw new WorkspaceError("io", "GitHub sign-in is misconfigured.");
    case "forbidden":
      throw new WorkspaceError(
        "io",
        "GitHub sign-in is not allowed from this site."
      );
    case "invalid_request":
    case "invalid_json":
    case "payload_too_large":
    case "method_not_allowed":
      throw new WorkspaceError("io", "GitHub sign-in was rejected.");
    default:
      throw new WorkspaceError(
        "unavailable",
        "GitHub sign-in is unavailable right now."
      );
  }
}

export async function validateGitHubToken(
  token: string
): Promise<GitHubUser> {
  if (!token) {
    throw new WorkspaceError("permission-denied", "GitHub is not connected.");
  }
  let response: Response;
  try {
    response = await fetch(USER_URL, {
      method: "GET",
      credentials: "omit",
      cache: "no-store",
      headers: {
        Authorization: `Bearer ${token}`,
        Accept: "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
      },
    });
  } catch {
    throw new WorkspaceError("unavailable", "Could not reach GitHub.");
  }
  if (response.status === 401) {
    throw new WorkspaceError(
      "permission-denied",
      "GitHub did not accept the token. Reconnect GitHub."
    );
  }
  if (!response.ok) {
    throw new WorkspaceError(
      "unavailable",
      "GitHub could not validate the token."
    );
  }
  const body = await readJson(response);
  if (
    !isRecord(body) ||
    typeof body.login !== "string" ||
    body.login.length === 0
  ) {
    throw new WorkspaceError("io", "GitHub returned an invalid user response.");
  }
  return { login: body.login };
}
