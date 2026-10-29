// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Build the Abella Web assets and stamp content hashes into the entry
// pages.  Cloudflare caches assets by URL for 30 days and does not
// revalidate when the origin changes, so every changed asset needs a new
// ?v= value.

import { createHash } from "node:crypto";
import {
  existsSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { build } from "esbuild";
import { copyWebFonts } from "./copy-web-fonts.mjs";

const repoRoot = fileURLToPath(new URL("../../", import.meta.url));
const supportRoot = join(repoRoot, "support");
const webRoot = join(repoRoot, "web");

const launcherPath = join(webRoot, "abella_js/abella_js.bc.wasm.js");
const workerPath = join(webRoot, "abella_js/worker.js");
const mainPath = join(webRoot, "abella_web.js");
const cssPath = join(webRoot, "abella_web.css");
const callbackPath = join(webRoot, "github_callback.js");
const fontPath = join(webRoot, "fonts/FiraCode-VF.woff2");

const dev = process.argv.includes("--dev");
const checkOnly = process.argv.includes("--check");

const pages = [
  {
    path: join(webRoot, "index.html"),
    assets: ["abella_web.css", "abella_web.js"],
  },
  {
    path: join(webRoot, "privacy.html"),
    assets: ["abella_web.css"],
  },
  {
    path: join(webRoot, "github-callback.html"),
    assets: ["github_callback.js"],
  },
];

const REFERENCE_PATTERN =
  /\b(src|href)="((?:\.\/)?[^"?]+)(?:\?([^"]*))?"/g;

function fail(message) {
  throw new Error(message);
}

function shortHash(data) {
  return createHash("sha256").update(data).digest("hex").slice(0, 16);
}

function fileHash(path) {
  if (!existsSync(path)) fail(`missing ${path}; run make web first`);
  return shortHash(readFileSync(path));
}

function stampFont(css, fontHash) {
  const pattern = /fonts\/FiraCode-VF\.woff2(?:\?v=[0-9A-Za-z._-]+)?/g;
  return css.replace(pattern, `fonts/FiraCode-VF.woff2?v=${fontHash}`);
}

function references(text) {
  const found = new Map();
  for (const match of text.matchAll(REFERENCE_PATTERN)) {
    const path = match[2].replace(/^\.\//, "");
    const query = new URLSearchParams(match[3] ?? "");
    found.set(path, query.get("v") ?? "");
  }
  return found;
}

function stampPage(text, assets) {
  return text.replace(
    REFERENCE_PATTERN,
    (match, attribute, rawPath) => {
      const path = rawPath.replace(/^\.\//, "");
      const hash = assets.get(path);
      return hash ? `${attribute}="${rawPath}?v=${hash}"` : match;
    }
  );
}

function assetHashes() {
  return {
    font: fileHash(fontPath),
    css: fileHash(cssPath),
    callback: fileHash(callbackPath),
    launcher: fileHash(launcherPath),
    worker: fileHash(workerPath),
    main: fileHash(mainPath),
  };
}

function check() {
  const hashes = assetHashes();
  const assets = new Map([
    ["abella_web.css", hashes.css],
    ["abella_web.js", hashes.main],
    ["github_callback.js", hashes.callback],
  ]);
  const problems = [];

  for (const page of pages) {
    const found = references(readFileSync(page.path, "utf8"));
    for (const asset of page.assets) {
      if (!found.has(asset)) {
        problems.push(`${page.path}: no reference to ${asset}`);
      } else if (found.get(asset) !== assets.get(asset)) {
        problems.push(
          `${page.path}: ${asset} has ?v=${found.get(asset)}, ` +
            `expected ?v=${assets.get(asset)}`
        );
      }
    }
  }

  const main = readFileSync(mainPath, "utf8");
  if (!main.includes(`worker.js?v=${hashes.worker}`)) {
    problems.push(`${mainPath}: worker reference is not current`);
  }
  const worker = readFileSync(workerPath, "utf8");
  if (!worker.includes(`abella_js.bc.wasm.js?v=${hashes.launcher}`)) {
    problems.push(`${workerPath}: wasm launcher reference is not current`);
  }
  const css = readFileSync(cssPath, "utf8");
  if (!css.includes(`fonts/FiraCode-VF.woff2?v=${hashes.font}`)) {
    problems.push(`${cssPath}: font reference is not current`);
  }

  if (problems.length > 0) {
    for (const problem of problems) console.error(`  ${problem}`);
    fail("web asset stamps are inconsistent; run make web");
  }
  console.log("Web asset stamps are consistent.");
}

async function buildAssets() {
  if (!existsSync(launcherPath)) {
    fail("missing web/abella_js/abella_js.bc.wasm.js; run make web first");
  }

  copyWebFonts();
  const fontHash = fileHash(fontPath);

  await build({
    absWorkingDir: supportRoot,
    entryPoints: [join(supportRoot, "ts/web/github-callback.ts")],
    bundle: true,
    format: "iife",
    minify: true,
    outfile: callbackPath,
  });
  const callbackHash = fileHash(callbackPath);

  await build({
    absWorkingDir: supportRoot,
    entryPoints: [join(supportRoot, "css/web.css")],
    minify: true,
    outfile: cssPath,
  });
  writeFileSync(cssPath, stampFont(readFileSync(cssPath, "utf8"), fontHash));
  const cssHash = fileHash(cssPath);

  const launcherHash = fileHash(launcherPath);

  await build({
    absWorkingDir: supportRoot,
    entryPoints: [join(supportRoot, "ts/web/worker.ts")],
    bundle: true,
    format: "iife",
    minify: true,
    outfile: workerPath,
    define: {
      __WASM_LAUNCHER_HASH__: JSON.stringify(launcherHash),
    },
  });
  const workerHash = fileHash(workerPath);

  rmSync(join(webRoot, "chunks"), { recursive: true, force: true });

  await build({
    absWorkingDir: supportRoot,
    entryPoints: [join(supportRoot, "ts/web/main.ts")],
    bundle: true,
    format: "esm",
    minify: true,
    splitting: true,
    outdir: webRoot,
    entryNames: "abella_web",
    chunkNames: "chunks/[name]-[hash]",
    define: {
      __WORKER_HASH__: JSON.stringify(workerHash),
      ...(dev
        ? {
            __GITHUB_OAUTH_WORKER__: JSON.stringify(
              "http://127.0.0.1:8787"
            ),
          }
        : {}),
    },
  });
  const mainHash = fileHash(mainPath);

  const assets = new Map([
    ["abella_web.css", cssHash],
    ["abella_web.js", mainHash],
    ["github_callback.js", callbackHash],
  ]);

  for (const page of pages) {
    const before = readFileSync(page.path, "utf8");
    const after = stampPage(before, assets);
    for (const asset of page.assets) {
      if (!after.includes(`${asset}?v=${assets.get(asset)}`)) {
        fail(`${page.path}: could not stamp ${asset}`);
      }
    }
    if (after !== before) {
      writeFileSync(page.path, after);
      console.log(`stamped ${page.path}`);
    }
  }

  console.log("Web asset hashes");
  for (const [name, hash] of [
    ["abella_web.js", mainHash],
    ["abella_web.css", cssHash],
    ["github_callback.js", callbackHash],
    ["worker.js", workerHash],
    ["wasm launcher", launcherHash],
    ["font", fontHash],
  ]) {
    console.log(`  ${name.padEnd(18)} ${hash}`);
  }
}

try {
  if (checkOnly) {
    check();
  } else {
    await buildAssets();
  }
} catch (error) {
  console.error(error instanceof Error ? error.message : String(error));
  process.exitCode = 1;
}
