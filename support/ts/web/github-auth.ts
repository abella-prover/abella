// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// The GitHub token is deliberately session-scoped: it survives a reload in
// the same tab, is not shared with other tabs, and is cleared when the tab
// closes or the user disconnects.  Scope and account metadata live in a
// separate session key so the UI can explain the current connection.

const TOKEN_KEY = "abella.web.v1.github.token";
const META_KEY = "abella.web.v1.github.meta";

export interface GitHubTokenMeta {
  scope?: string;
  login?: string;
}

export function loadGitHubToken(): string | undefined {
  if (typeof sessionStorage === "undefined") return undefined;
  try {
    const token = sessionStorage.getItem(TOKEN_KEY);
    return token ? token : undefined;
  } catch {
    return undefined;
  }
}

export function saveGitHubToken(token: string): void {
  if (typeof sessionStorage === "undefined") return;
  try {
    sessionStorage.setItem(TOKEN_KEY, token);
  } catch {
    // Session storage is optional.
  }
}

export function loadGitHubTokenMeta(): GitHubTokenMeta {
  if (typeof sessionStorage === "undefined") return {};
  try {
    const raw = sessionStorage.getItem(META_KEY);
    if (!raw) return {};
    const parsed: unknown = JSON.parse(raw);
    if (typeof parsed !== "object" || parsed === null) return {};
    const record = parsed as Record<string, unknown>;
    const scope = record.scope;
    const login = record.login;
    return {
      scope: typeof scope === "string" ? scope : undefined,
      login: typeof login === "string" ? login : undefined,
    };
  } catch {
    return {};
  }
}

export function saveGitHubTokenMeta(meta: GitHubTokenMeta): void {
  if (typeof sessionStorage === "undefined") return;
  try {
    sessionStorage.setItem(META_KEY, JSON.stringify(meta));
  } catch {
    // Session storage is optional.
  }
}

export function clearGitHubToken(): void {
  if (typeof sessionStorage === "undefined") return;
  try {
    sessionStorage.removeItem(TOKEN_KEY);
    sessionStorage.removeItem(META_KEY);
  } catch {
    // Session storage is optional.
  }
}
