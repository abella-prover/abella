// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  clearGitHubToken,
  loadGitHubToken,
  saveGitHubToken,
} from "./github-auth";

test("GitHub tokens are session-scoped", () => {
  const store = new Map<string, string>();
  const fake = {
    getItem(key: string) {
      return store.get(key) ?? null;
    },
    setItem(key: string, value: string) {
      store.set(key, value);
    },
    removeItem(key: string) {
      store.delete(key);
    },
  };
  Object.defineProperty(globalThis, "sessionStorage", {
    configurable: true,
    value: fake,
  });
  try {
    assert.equal(loadGitHubToken(), undefined);
    saveGitHubToken("token-1");
    assert.equal(store.get("abella.web.v1.github.token"), "token-1");
    assert.equal(loadGitHubToken(), "token-1");
    clearGitHubToken();
    assert.equal(loadGitHubToken(), undefined);
    assert.equal(store.has("abella.web.v1.github.token"), false);
  } finally {
    delete (globalThis as { sessionStorage?: unknown }).sessionStorage;
  }
});
