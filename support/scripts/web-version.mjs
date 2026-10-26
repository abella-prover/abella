// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Cloudflare caches generated assets by URL for 30 days, so a published
// change needs a fresh WEB_ASSET_VERSION.  The constant is compiled into
// the JavaScript, while the checked-in HTML pages carry a literal copy,
// so both must move together.

import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const versionFile = "support/ts/web/version.ts";
const htmlFiles = [
  "web/index.html",
  "web/privacy.html",
  "web/github-callback.html",
];

const versionPattern = /WEB_ASSET_VERSION = "([^"]+)"/;
const referencePattern = /\?v=[0-9A-Za-z._-]+/g;

function read(path) {
  return readFileSync(join(repoRoot, path), "utf8");
}

function write(path, text) {
  writeFileSync(join(repoRoot, path), text);
}

function references(text) {
  return text.match(referencePattern) ?? [];
}

function currentVersion() {
  const match = versionPattern.exec(read(versionFile));
  if (!match) throw new Error(`${versionFile} has no WEB_ASSET_VERSION`);
  return match[1];
}

function today() {
  const now = new Date();
  const month = String(now.getMonth() + 1).padStart(2, "0");
  const day = String(now.getDate()).padStart(2, "0");
  return `${now.getFullYear()}${month}${day}`;
}

function nextVersion(current) {
  const stamp = today();
  const match = /^(\d{8})-(\d+)$/.exec(current);
  if (!match) return `${stamp}-1`;
  const [, date, count] = match;
  // Never move backwards if the committed date is ahead of the clock.
  if (date >= stamp) return `${date}-${Number(count) + 1}`;
  return `${stamp}-1`;
}

function missingReferences() {
  return htmlFiles.filter((path) => references(read(path)).length === 0);
}

function bump() {
  const current = currentVersion();
  const next = nextVersion(current);

  const missing = missingReferences();
  if (missing.length > 0) {
    console.error("Expected a ?v= reference in:");
    for (const path of missing) console.error(`  ${path}`);
    process.exitCode = 1;
    return;
  }

  write(
    versionFile,
    read(versionFile).replace(
      versionPattern,
      () => `WEB_ASSET_VERSION = "${next}"`
    )
  );
  const changed = [versionFile];
  for (const path of htmlFiles) {
    const before = read(path);
    const after = before.replace(referencePattern, `?v=${next}`);
    if (after !== before) {
      write(path, after);
      changed.push(path);
    }
  }

  console.log(`Bumped web asset version ${current} -> ${next}`);
  for (const path of changed) console.log(`  ${path}`);
}

function check() {
  const version = currentVersion();
  const missing = [];
  const stale = [];
  for (const path of htmlFiles) {
    const found = references(read(path));
    if (found.length === 0) {
      missing.push(path);
      continue;
    }
    for (const reference of found) {
      if (reference !== `?v=${version}`) {
        stale.push(`${path}: ${reference}, expected ?v=${version}`);
      }
    }
  }

  if (missing.length > 0 || stale.length > 0) {
    console.error("Web asset versions are inconsistent:");
    for (const problem of new Set(stale)) console.error(`  ${problem}`);
    for (const path of missing) console.error(`  ${path}: no ?v= reference`);
    if (stale.length > 0) {
      console.error("Run 'make web-version-bump' to align them.");
    }
    if (missing.length > 0) {
      console.error("Restore the missing ?v= references by hand.");
    }
    process.exitCode = 1;
    return;
  }
  console.log(`Web asset version ${version} is consistent.`);
}

const mode = process.argv[2];
if (mode === "--bump") {
  bump();
} else if (mode === "--check") {
  check();
} else {
  console.error("usage: web-version.mjs --bump | --check");
  process.exitCode = 2;
}
