// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Enforce coarse size budgets for the deployed Abella Web assets.  The
// Markdown language support is split into a lazy chunk, so the main
// entry point stays small; the sum of chunks is checked separately.

import { existsSync, readFileSync, readdirSync, statSync } from "node:fs";
import { dirname, join, relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { gzipSync } from "node:zlib";

const webRoot = fileURLToPath(new URL("../../web/", import.meta.url));

const KiB = 1024;

const budgets = {
  "initial JS": { gzip: 180 * KiB },
  "lazy chunks": { gzip: 120 * KiB },
  "abella_web.css": { gzip: 16 * KiB },
  "examples/bundle.json": { gzip: 32 * KiB },
  "wasm assets": { raw: 1024 * KiB },
};

function measure(path) {
  const data = readFileSync(path);
  return { raw: data.length, gzip: gzipSync(data).length };
}

function safeMeasure(path) {
  if (!existsSync(path)) return undefined;
  return measure(path);
}

function sumMeasure(paths) {
  let raw = 0;
  let gzip = 0;
  for (const path of paths) {
    const size = measure(path);
    raw += size.raw;
    gzip += size.gzip;
  }
  return { raw, gzip };
}

function staticImports(path) {
  const source = readFileSync(path, "utf8");
  const found = new Set();
  for (const match of source.matchAll(/from\s*"\.\/([^"]+\.js)"/g)) {
    found.add(match[1]);
  }
  for (const match of source.matchAll(/\bimport\s*"\.\/([^"]+\.js)"/g)) {
    found.add(match[1]);
  }
  return [...found];
}

function collectChunks() {
  const entry = join(webRoot, "abella_web.js");
  const chunksDir = join(webRoot, "chunks");
  const all = existsSync(chunksDir)
    ? readdirSync(chunksDir)
        .filter((name) => name.endsWith(".js"))
        .map((name) => join(chunksDir, name))
    : [];
  const eager = new Set([entry]);
  const queue = [entry];
  while (queue.length > 0) {
    const path = queue.pop();
    for (const imported of staticImports(path)) {
      const next = resolve(dirname(path), imported);
      if (!eager.has(next)) {
        eager.add(next);
        queue.push(next);
      }
    }
  }
  return {
    eager: [...eager],
    lazy: all.filter((path) => !eager.has(path)),
  };
}

function format(bytes) {
  return `${(bytes / KiB).toFixed(1)} KiB`;
}

const rows = [];
let failed = false;

function check(name, path, kind, actual) {
  const limit = budgets[name][kind];
  const ok = actual <= limit;
  if (!ok) failed = true;
  rows.push({
    name,
    path: path ? relative(webRoot, path) : "",
    kind,
    budget: format(limit),
    actual: format(actual),
    ok,
  });
}

const chunks = collectChunks();
if (!existsSync(join(webRoot, "abella_web.js"))) {
  console.error("Missing web/abella_web.js; run npm run web:build first.");
  process.exit(1);
}
const initial = sumMeasure(chunks.eager);
check("initial JS", join(webRoot, "abella_web.js"), "gzip", initial.gzip);
const lazy = sumMeasure(chunks.lazy);
check("lazy chunks", join(webRoot, "chunks"), "gzip", lazy.gzip);

const css = safeMeasure(join(webRoot, "abella_web.css"));
if (!css) {
  console.error("Missing web/abella_web.css; run npm run web:build first.");
  process.exit(1);
}
check("abella_web.css", join(webRoot, "abella_web.css"), "gzip", css.gzip);

const examples = safeMeasure(join(webRoot, "examples/bundle.json"));
if (!examples) {
  console.error(
    "Missing web/examples/bundle.json; run make web-bundle first."
  );
  process.exit(1);
}
check(
  "examples/bundle.json",
  join(webRoot, "examples/bundle.json"),
  "gzip",
  examples.gzip
);

let wasmRaw = 0;
const wasmLauncher = join(webRoot, "abella_js/abella_js.bc.wasm.js");
if (existsSync(wasmLauncher)) wasmRaw += statSync(wasmLauncher).size;
const wasmAssets = join(webRoot, "abella_js/abella_js.bc.wasm.assets");
if (existsSync(wasmAssets)) {
  for (const name of readdirSync(wasmAssets)) {
    if (name.endsWith(".wasm")) {
      wasmRaw += statSync(join(wasmAssets, name)).size;
    }
  }
}
if (wasmRaw === 0) {
  console.error(
    "Missing web/abella_js wasm launcher/assets; run make web first."
  );
  process.exit(1);
}
check("wasm assets", wasmAssets, "raw", wasmRaw);

console.log("Abella Web size check");
for (const row of rows) {
  const status = row.ok ? "ok" : "OVER";
  const suffix = row.path ? ` (${row.path})` : "";
  console.log(
    `  ${status.padEnd(4)} ${row.name.padEnd(20)} ` +
      `${row.kind} ${row.actual.padStart(9)} / ${row.budget}${suffix}`
  );
}

if (failed) {
  console.error("Web asset size budget exceeded.");
  process.exit(1);
}
