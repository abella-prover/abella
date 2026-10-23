// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// The GitHub token is deliberately session-scoped: it survives a reload in
// the same tab, is not shared with other tabs, and is cleared when the tab
// closes or the user disconnects.

const TOKEN_KEY = "abella.web.v1.github.token";

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

export function clearGitHubToken(): void {
  if (typeof sessionStorage === "undefined") return;
  try {
    sessionStorage.removeItem(TOKEN_KEY);
  } catch {
    // Session storage is optional.
  }
}
