// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Minimal token-exchange endpoint for Abella Web's GitHub OAuth flow.
// The Worker holds the OAuth client secret, never stores data, and never
// logs codes, verifiers, tokens, or secrets.

const GITHUB_TOKEN_URL = "https://github.com/login/oauth/access_token";
const CONFIG_PATH = "/github/config";
const TOKEN_PATH = "/github/token";
const MAX_BODY_BYTES = 4096;
const MAX_CODE_LENGTH = 512;
const MAX_VERIFIER_LENGTH = 128;
const UPSTREAM_TIMEOUT_MS = 10_000;

export interface Env {
  GITHUB_CLIENT_ID?: string;
  GITHUB_CLIENT_SECRET?: string;
  ALLOWED_ORIGIN?: string;
  REDIRECT_URI?: string;
}

interface ConfiguredEnv {
  clientId: string;
  clientSecret: string;
  allowedOrigin: string;
  redirectUri: string;
}

interface TokenRequest {
  code: string;
  codeVerifier: string;
}

interface OAuthErrorMapping {
  error: string;
  message: string;
}

const OAUTH_ERRORS: Record<string, OAuthErrorMapping> = {
  access_denied: {
    error: "access_denied",
    message: "GitHub denied the authorization request.",
  },
  bad_verification_code: {
    error: "invalid_code",
    message: "GitHub rejected the code.",
  },
  incorrect_client_credentials: {
    error: "configuration_error",
    message: "The OAuth client is misconfigured.",
  },
  invalid_request: {
    error: "invalid_request",
    message: "GitHub rejected the token request.",
  },
  redirect_uri_mismatch: {
    error: "configuration_error",
    message: "The OAuth redirect URI is misconfigured.",
  },
  unsupported_grant_type: {
    error: "invalid_request",
    message: "GitHub rejected the token request.",
  },
};

function configured(env: Env): ConfiguredEnv | undefined {
  const clientId = env.GITHUB_CLIENT_ID;
  const clientSecret = env.GITHUB_CLIENT_SECRET;
  const allowedOrigin = env.ALLOWED_ORIGIN;
  const redirectUri = env.REDIRECT_URI;
  if (!clientId || !clientSecret || !allowedOrigin || !redirectUri) {
    return undefined;
  }
  return { clientId, clientSecret, allowedOrigin, redirectUri };
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function isTimeout(error: unknown): boolean {
  if (typeof error !== "object" || error === null) return false;
  const name = (error as { name?: unknown }).name;
  return name === "TimeoutError" || name === "AbortError";
}

function baseHeaders(): Headers {
  const headers = new Headers();
  headers.set("Cache-Control", "no-store");
  headers.set("X-Content-Type-Options", "nosniff");
  return headers;
}

function withCors(
  headers: Headers,
  request: Request,
  allowedOrigin?: string
): Headers {
  const origin = request.headers.get("Origin");
  headers.set("Vary", "Origin");
  if (allowedOrigin !== undefined && origin === allowedOrigin) {
    headers.set("Access-Control-Allow-Origin", allowedOrigin);
    headers.set("Access-Control-Allow-Methods", "POST, GET, OPTIONS");
    headers.set("Access-Control-Allow-Headers", "Content-Type");
    headers.set("Access-Control-Max-Age", "600");
  }
  return headers;
}

function jsonResponse(
  body: unknown,
  status: number,
  request: Request,
  allowedOrigin?: string,
  extra?: Record<string, string>
): Response {
  const headers = withCors(baseHeaders(), request, allowedOrigin);
  headers.set("Content-Type", "application/json; charset=utf-8");
  for (const [name, value] of Object.entries(extra ?? {})) {
    headers.set(name, value);
  }
  return new Response(JSON.stringify(body), { status, headers });
}

function errorResponse(
  error: string,
  message: string,
  status: number,
  request: Request,
  allowedOrigin?: string,
  extra?: Record<string, string>
): Response {
  return jsonResponse(
    { error, message },
    status,
    request,
    allowedOrigin,
    extra
  );
}

function methodNotAllowed(
  allow: string,
  request: Request,
  allowedOrigin: string
): Response {
  return errorResponse(
    "method_not_allowed",
    "Method not allowed.",
    405,
    request,
    allowedOrigin,
    { Allow: allow }
  );
}

function preflightResponse(
  request: Request,
  allowedOrigin: string
): Response {
  const headers = withCors(baseHeaders(), request, allowedOrigin);
  return new Response(null, { status: 204, headers });
}

function originAllowed(request: Request, allowedOrigin: string): boolean {
  return request.headers.get("Origin") === allowedOrigin;
}

function parseTokenRequest(value: unknown): TokenRequest | undefined {
  if (!isRecord(value)) return undefined;
  const code = value.code;
  const codeVerifier = value.codeVerifier;
  if (typeof code !== "string" || typeof codeVerifier !== "string") {
    return undefined;
  }
  if (code.length === 0 || code.length > MAX_CODE_LENGTH) return undefined;
  if (
    codeVerifier.length === 0 ||
    codeVerifier.length > MAX_VERIFIER_LENGTH
  ) {
    return undefined;
  }
  return { code, codeVerifier };
}

async function readTokenRequest(
  request: Request,
  allowedOrigin: string
): Promise<TokenRequest | Response> {
  const mediaType = request.headers
    .get("Content-Type")
    ?.split(";")[0]
    ?.trim()
    .toLowerCase();
  if (mediaType !== "application/json") {
    return errorResponse(
      "invalid_request",
      "Expected a JSON request body.",
      400,
      request,
      allowedOrigin
    );
  }
  const contentLength = request.headers.get("Content-Length");
  if (contentLength !== null) {
    const length = Number(contentLength);
    if (!Number.isSafeInteger(length) || length < 0) {
      return errorResponse(
        "invalid_request",
        "Invalid request body.",
        400,
        request,
        allowedOrigin
      );
    }
    if (length > MAX_BODY_BYTES) {
      return errorResponse(
        "payload_too_large",
        "Request body is too large.",
        413,
        request,
        allowedOrigin
      );
    }
  }
  let body: string;
  try {
    body = await request.text();
  } catch {
    return errorResponse(
      "invalid_request",
      "Could not read the request body.",
      400,
      request,
      allowedOrigin
    );
  }
  if (new TextEncoder().encode(body).byteLength > MAX_BODY_BYTES) {
    return errorResponse(
      "payload_too_large",
      "Request body is too large.",
      413,
      request,
      allowedOrigin
    );
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(body);
  } catch {
    return errorResponse(
      "invalid_json",
      "Request body is not valid JSON.",
      400,
      request,
      allowedOrigin
    );
  }
  const tokenRequest = parseTokenRequest(parsed);
  if (tokenRequest === undefined) {
    return errorResponse(
      "invalid_request",
      "The code and code verifier are required.",
      400,
      request,
      allowedOrigin
    );
  }
  return tokenRequest;
}

function oauthErrorResponse(
  code: string,
  request: Request,
  allowedOrigin: string
): Response {
  const mapping = OAUTH_ERRORS[code] ?? {
    error: "exchange_failed",
    message: "GitHub rejected the token exchange.",
  };
  return errorResponse(
    mapping.error,
    mapping.message,
    400,
    request,
    allowedOrigin
  );
}

async function exchangeWithGitHub(
  tokenRequest: TokenRequest,
  config: ConfiguredEnv,
  request: Request
): Promise<Response> {
  const form = new URLSearchParams({
    client_id: config.clientId,
    client_secret: config.clientSecret,
    code: tokenRequest.code,
    redirect_uri: config.redirectUri,
    code_verifier: tokenRequest.codeVerifier,
  });
  let upstream: Response;
  try {
    upstream = await fetch(GITHUB_TOKEN_URL, {
      method: "POST",
      headers: {
        Accept: "application/json",
        "Content-Type": "application/x-www-form-urlencoded",
      },
      body: form.toString(),
      redirect: "manual",
      signal: AbortSignal.timeout(UPSTREAM_TIMEOUT_MS),
    });
  } catch (error) {
    if (isTimeout(error)) {
      return errorResponse(
        "upstream_timeout",
        "GitHub did not respond in time.",
        504,
        request,
        config.allowedOrigin
      );
    }
    return errorResponse(
      "upstream_unavailable",
      "GitHub could not be reached.",
      502,
      request,
      config.allowedOrigin
    );
  }
  if (
    (upstream.status >= 300 && upstream.status < 400) ||
    upstream.status === 429 ||
    upstream.status >= 500
  ) {
    return errorResponse(
      "upstream_error",
      "GitHub could not complete the token exchange.",
      502,
      request,
      config.allowedOrigin
    );
  }
  let payload: unknown;
  try {
    payload = await upstream.json();
  } catch {
    return errorResponse(
      "upstream_error",
      "GitHub returned an invalid response.",
      502,
      request,
      config.allowedOrigin
    );
  }
  if (!isRecord(payload)) {
    return errorResponse(
      "upstream_error",
      "GitHub returned an invalid response.",
      502,
      request,
      config.allowedOrigin
    );
  }
  const errorCode = payload.error;
  if (typeof errorCode === "string") {
    return oauthErrorResponse(errorCode, request, config.allowedOrigin);
  }
  if (!upstream.ok) {
    return errorResponse(
      "upstream_error",
      "GitHub rejected the token exchange.",
      502,
      request,
      config.allowedOrigin
    );
  }
  const token = payload.access_token;
  if (typeof token !== "string" || token.length === 0) {
    return errorResponse(
      "upstream_error",
      "GitHub returned an invalid token response.",
      502,
      request,
      config.allowedOrigin
    );
  }
  const scope = typeof payload.scope === "string" ? payload.scope : "";
  return jsonResponse(
    { token, scope },
    200,
    request,
    config.allowedOrigin
  );
}

async function exchangeToken(
  request: Request,
  config: ConfiguredEnv
): Promise<Response> {
  const tokenRequest = await readTokenRequest(
    request,
    config.allowedOrigin
  );
  if (tokenRequest instanceof Response) return tokenRequest;
  return exchangeWithGitHub(tokenRequest, config, request);
}

export default {
  async fetch(request: Request, env: Env): Promise<Response> {
    const path = new URL(request.url).pathname;
    const allowedOrigin = env.ALLOWED_ORIGIN;
    if (path !== CONFIG_PATH && path !== TOKEN_PATH) {
      return errorResponse(
        "not_found",
        "Not found.",
        404,
        request,
        allowedOrigin
      );
    }
    const config = configured(env);
    if (config === undefined) {
      return errorResponse(
        "unavailable",
        "The OAuth service is not configured.",
        503,
        request,
        allowedOrigin
      );
    }
    if (request.method === "OPTIONS") {
      if (!originAllowed(request, config.allowedOrigin)) {
        return errorResponse(
          "forbidden",
          "Origin is not allowed.",
          403,
          request,
          config.allowedOrigin
        );
      }
      return preflightResponse(request, config.allowedOrigin);
    }
    if (!originAllowed(request, config.allowedOrigin)) {
      return errorResponse(
        "forbidden",
        "Origin is not allowed.",
        403,
        request,
        config.allowedOrigin
      );
    }
    if (path === CONFIG_PATH) {
      if (request.method !== "GET") {
        return methodNotAllowed(
          "GET, OPTIONS",
          request,
          config.allowedOrigin
        );
      }
      return jsonResponse(
        { clientId: config.clientId, redirectUri: config.redirectUri },
        200,
        request,
        config.allowedOrigin
      );
    }
    if (request.method !== "POST") {
      return methodNotAllowed(
        "POST, OPTIONS",
        request,
        config.allowedOrigin
      );
    }
    return exchangeToken(request, config);
  },
} satisfies ExportedHandler<Env>;
