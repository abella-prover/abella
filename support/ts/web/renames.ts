// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { classify, type Project, type ProjectTextFile } from "./project";

export interface FileRename {
  from: string;
  to: string;
}

export interface RenamePlan {
  files: Map<string, ProjectTextFile>;
  root: string;
  active: string;
  renames: FileRename[];
  changed: Map<string, string>;
}

export type RenameResult =
  | { ok: true; plan: RenamePlan }
  | { ok: false; message: string };

function dirname(path: string): string {
  const slash = path.lastIndexOf("/");
  return slash < 0 ? "" : path.slice(0, slash);
}

function basename(path: string): string {
  const slash = path.lastIndexOf("/");
  return slash < 0 ? path : path.slice(slash + 1);
}

function extension(path: string): string {
  const name = basename(path);
  const dot = name.lastIndexOf(".");
  return dot <= 0 ? "" : name.slice(dot).toLowerCase();
}

function stem(path: string): string {
  const name = basename(path);
  const dot = name.lastIndexOf(".");
  return dot <= 0 ? name : name.slice(0, dot);
}

function join(dir: string, name: string): string {
  return dir ? `${dir}/${name}` : name;
}

function escapeRegExp(text: string): string {
  return text.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function replaceDeclaration(
  text: string,
  keyword: string,
  oldName: string,
  newName: string
): string {
  const pattern = new RegExp(
    `^(\\s*${keyword}\\s+)${escapeRegExp(oldName)}(\\s*\\.)`,
    "gm"
  );
  return text.replace(
    pattern,
    (_match, before: string, after: string) => `${before}${newName}${after}`
  );
}

function replaceQuotedCommand(
  text: string,
  command: string,
  oldName: string,
  newName: string
): string {
  const pattern = new RegExp(
    `(\\b${command}\\s+")${escapeRegExp(oldName)}(")`,
    "g"
  );
  return text.replace(
    pattern,
    (_match, before: string, after: string) => `${before}${newName}${after}`
  );
}

function splitTarget(target: string): { path: string; suffix: string } {
  const hash = target.indexOf("#");
  const query = target.indexOf("?");
  let cut = target.length;
  if (hash >= 0) cut = Math.min(cut, hash);
  if (query >= 0) cut = Math.min(cut, query);
  return { path: target.slice(0, cut), suffix: target.slice(cut) };
}

function normalizePath(path: string): string | undefined {
  const parts: string[] = [];
  for (const part of path.split("/")) {
    if (part === "" || part === ".") continue;
    if (part === "..") {
      if (parts.length === 0) return undefined;
      parts.pop();
    } else {
      parts.push(part);
    }
  }
  return parts.length > 0 ? parts.join("/") : undefined;
}

function resolveProjectPath(
  mdPath: string,
  target: string
): string | undefined {
  if (!target || target.startsWith("#")) return undefined;
  if (/^[a-z][a-z0-9+.-]*:/i.test(target)) return undefined;
  if (target.startsWith("//")) return undefined;
  const base = target.startsWith("/")
    ? target.slice(1)
    : join(dirname(mdPath), target);
  return normalizePath(base);
}

function relativePath(fromDir: string, toPath: string): string {
  const fromParts = fromDir ? fromDir.split("/") : [];
  const toParts = toPath.split("/");
  let common = 0;
  while (
    common < fromParts.length &&
    common < toParts.length &&
    fromParts[common] === toParts[common]
  ) {
    common++;
  }
  const parts = [
    ...Array<string>(fromParts.length - common).fill(".."),
    ...toParts.slice(common),
  ];
  return parts.join("/");
}

function rewriteTarget(
  target: string,
  mdPath: string,
  renames: Map<string, string>
): string {
  const { path, suffix } = splitTarget(target);
  const resolved = resolveProjectPath(mdPath, path);
  if (!resolved) return target;
  const next = renames.get(resolved);
  if (!next) return target;
  return `${relativePath(dirname(mdPath), next)}${suffix}`;
}

function rewriteMarkdownLinks(
  text: string,
  mdPath: string,
  renames: Map<string, string>
): string {
  const inline =
    /(!?\[[^\]]*\]\(\s*)(<[^>\n]*>|[^)\s]+)(\s*(?:"[^"]*"|'[^']*'|\([^)]*\))?\s*\))/g;
  let next = text.replace(
    inline,
    (_match, prefix: string, destination: string, suffix: string) => {
      const wrapped =
        destination.startsWith("<") && destination.endsWith(">");
      const target = wrapped ? destination.slice(1, -1) : destination;
      const rewritten = rewriteTarget(target, mdPath, renames);
      return `${prefix}${wrapped ? `<${rewritten}>` : rewritten}${suffix}`;
    }
  );
  const reference = /^(\s*\[[^\]]+\]:\s*)(<[^>\n]*>|\S+)(.*)$/gm;
  next = next.replace(
    reference,
    (_match, prefix: string, destination: string, suffix: string) => {
      const wrapped =
        destination.startsWith("<") && destination.endsWith(">");
      const target = wrapped ? destination.slice(1, -1) : destination;
      const rewritten = rewriteTarget(target, mdPath, renames);
      return `${prefix}${wrapped ? `<${rewritten}>` : rewritten}${suffix}`;
    }
  );
  return next;
}

export function planRename(
  project: Project,
  from: string,
  to: string
): RenameResult {
  const source = project.files.get(from);
  if (!source) {
    return { ok: false, message: `File not found: ${from}` };
  }
  if (to === from) {
    return { ok: false, message: "The file name is unchanged." };
  }
  if (project.files.has(to)) {
    return { ok: false, message: `A file named ${to} already exists.` };
  }

  const fromExt = extension(from);
  const toExt = extension(to);
  const renames: FileRename[] = [{ from, to }];
  if (fromExt === toExt && (fromExt === ".sig" || fromExt === ".mod")) {
    const companionExt = fromExt === ".sig" ? ".mod" : ".sig";
    const companionFrom = join(
      dirname(from),
      `${stem(from)}${companionExt}`
    );
    if (project.files.has(companionFrom)) {
      const companionTo = join(
        dirname(to),
        `${stem(to)}${companionExt}`
      );
      if (project.files.has(companionTo)) {
        return {
          ok: false,
          message:
            `Renaming ${from} would also rename ${companionFrom} to ` +
            `${companionTo}, but ${companionTo} already exists.`,
        };
      }
      renames.push({ from: companionFrom, to: companionTo });
    }
  }

  const targets = new Set<string>();
  for (const rename of renames) {
    if (targets.has(rename.to)) {
      return {
        ok: false,
        message: `Two files would be renamed to ${rename.to}.`,
      };
    }
    targets.add(rename.to);
  }

  const files = new Map<string, ProjectTextFile>(
    [...project.files].map(([path, file]) => [path, { ...file }])
  );
  for (const rename of renames) {
    const file = files.get(rename.from);
    if (!file) {
      return { ok: false, message: `File not found: ${rename.from}` };
    }
    files.delete(rename.from);
    files.set(rename.to, {
      text: file.text,
      kind: classify(rename.to),
    });
  }

  const changed = new Map<string, string>();
  const oldName = stem(from);
  const newName = stem(to);
  if (oldName !== newName) {
    if (
      fromExt === toExt &&
      (fromExt === ".sig" || fromExt === ".mod")
    ) {
      for (const rename of renames) {
        const file = files.get(rename.to);
        if (!file) continue;
        const keyword = extension(rename.to) === ".sig" ? "sig" : "module";
        const text = replaceDeclaration(
          file.text,
          keyword,
          oldName,
          newName
        );
        if (text !== file.text) {
          file.text = text;
          changed.set(rename.to, text);
        }
      }
      for (const [path, file] of files) {
        if (!path.toLowerCase().endsWith(".thm")) continue;
        const text = replaceQuotedCommand(
          file.text,
          "Specification",
          oldName,
          newName
        );
        if (text !== file.text) {
          file.text = text;
          changed.set(path, text);
        }
      }
    } else if (fromExt === ".thm" && toExt === ".thm") {
      for (const [path, file] of files) {
        if (!path.toLowerCase().endsWith(".thm")) continue;
        const text = replaceQuotedCommand(
          file.text,
          "Import",
          oldName,
          newName
        );
        if (text !== file.text) {
          file.text = text;
          changed.set(path, text);
        }
      }
    }
  }

  const destinations = new Map(
    renames.map((rename) => [rename.from, rename.to] as const)
  );
  for (const [path, file] of files) {
    if (!/\.(md|markdown)$/i.test(path)) continue;
    const text = rewriteMarkdownLinks(file.text, path, destinations);
    if (text !== file.text) {
      file.text = text;
      changed.set(path, text);
    }
  }

  let root = project.root;
  let active = project.active;
  for (const rename of renames) {
    if (root === rename.from) root = rename.to;
    if (active === rename.from) active = rename.to;
  }

  return {
    ok: true,
    plan: { files, root, active, renames, changed },
  };
}
