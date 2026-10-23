// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { test } from "node:test";
import assert from "node:assert/strict";
import {
  clearGitHubToken,
  loadGitHubToken,
  loadGitHubTokenMeta,
  saveGitHubToken,
  saveGitHubTokenMeta,
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
    assert.deepEqual(loadGitHubTokenMeta(), {});
    saveGitHubToken("token-1");
    saveGitHubTokenMeta({ scope: "repo", login: "octocat" });
    assert.equal(store.get("abella.web.v1.github.token"), "token-1");
    assert.equal(loadGitHubToken(), "token-1");
    assert.deepEqual(loadGitHubTokenMeta(), {
      scope: "repo",
      login: "octocat",
    });
    clearGitHubToken();
    assert.equal(loadGitHubToken(), undefined);
    assert.deepEqual(loadGitHubTokenMeta(), {});
    assert.equal(store.has("abella.web.v1.github.token"), false);
    assert.equal(store.has("abella.web.v1.github.meta"), false);
  } finally {
    delete (globalThis as { sessionStorage?: unknown }).sessionStorage;
  }
});

test("invalid GitHub metadata is ignored", () => {
  const store = new Map<string, string>([
    ["abella.web.v1.github.meta", "{not json"],
  ]);
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
    assert.deepEqual(loadGitHubTokenMeta(), {});
    store.set(
      "abella.web.v1.github.meta",
      JSON.stringify({ scope: 1, login: "octocat" })
    );
    const meta = loadGitHubTokenMeta();
    assert.equal(meta.scope, undefined);
    assert.equal(meta.login, "octocat");
  } finally {
    delete (globalThis as { sessionStorage?: unknown }).sessionStorage;
  }
});
