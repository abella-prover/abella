// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Shared callback payload for the static GitHub callback page and the
// main tab.  This module deliberately has no imports so that the
// callback bundle stays tiny.

export const OAUTH_CALLBACK_TYPE = "abella-github-oauth";

export interface OAuthCallback {
  type: typeof OAUTH_CALLBACK_TYPE;
  code?: string;
  state?: string;
  error?: string;
  errorDescription?: string;
}

function searchParam(
  params: URLSearchParams,
  name: string
): string | undefined {
  const value = params.get(name);
  return value ? value : undefined;
}

export function parseOAuthCallback(search: string): OAuthCallback {
  const params = new URLSearchParams(search);
  return {
    type: OAUTH_CALLBACK_TYPE,
    code: searchParam(params, "code"),
    state: searchParam(params, "state"),
    error: searchParam(params, "error"),
    errorDescription: searchParam(params, "error_description"),
  };
}

export function isOAuthCallback(value: unknown): value is OAuthCallback {
  if (typeof value !== "object" || value === null || Array.isArray(value)) {
    return false;
  }
  const record = value as Record<string, unknown>;
  if (record.type !== OAUTH_CALLBACK_TYPE) return false;
  for (const field of ["code", "state", "error", "errorDescription"]) {
    const item = record[field];
    if (item !== undefined && typeof item !== "string") return false;
  }
  return true;
}
