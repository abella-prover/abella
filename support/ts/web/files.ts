// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { WorkspaceEntry } from "./workspace";

export function normalizeNewPath(
  input: string | null
): string | undefined {
  if (input === null) return undefined;
  const path = input.trim().replace(/\\/g, "/").replace(/^\.\//, "");
  if (
    path === "" ||
    path.startsWith("/") ||
    path
      .split("/")
      .some((part) => part === "" || part === "." || part === "..")
  ) {
    return undefined;
  }
  return path;
}

export interface TreeNode {
  path: string;
  name: string;
  kind: "file" | "directory";
  openable: boolean;
  reason?: WorkspaceEntry["reason"];
  children: TreeNode[];
}

export interface TreeEdit {
  path?: string;
  folder?: string;
  value: string;
}

export interface TreeOptions {
  entries: WorkspaceEntry[];
  active?: string;
  entry?: string;
  selected?: string;
  expanded: ReadonlySet<string>;
  dirty: ReadonlySet<string>;
  rename?: TreeEdit;
  create?: TreeEdit;
  focusSelected?: boolean;
  focusInput?: boolean;
}

export interface TreeHandlers {
  onOpen(path: string): void;
  onToggle(path: string): void;
  onSelect(path: string): void;
  onContextMenu(path: string, anchor: HTMLElement): void;
  onCommitRename(from: string, value: string): void;
  onCommitCreate(folder: string, value: string): void;
  onCancelEdit(): void;
}

function basename(path: string): string {
  const slash = path.lastIndexOf("/");
  return slash < 0 ? path : path.slice(slash + 1);
}

function sortNodes(nodes: TreeNode[]): void {
  nodes.sort((a, b) => {
    if (a.kind !== b.kind) return a.kind === "directory" ? -1 : 1;
    const byName = a.name.localeCompare(b.name, undefined, {
      numeric: true,
      sensitivity: "base",
    });
    return byName !== 0 ? byName : a.path.localeCompare(b.path);
  });
  for (const node of nodes) sortNodes(node.children);
}

function compactDirectories(nodes: TreeNode[]): void {
  for (const node of nodes) {
    while (
      node.kind === "directory" &&
      node.children.length === 1 &&
      node.children[0].kind === "directory"
    ) {
      const child = node.children[0];
      node.path = child.path;
      node.name = `${node.name}/${child.name}`;
      node.openable = child.openable;
      node.reason = child.reason;
      node.children = child.children;
    }
    compactDirectories(node.children);
  }
}

export function buildTree(entries: WorkspaceEntry[]): TreeNode[] {
  const nodes = new Map<string, TreeNode>();
  const roots: TreeNode[] = [];

  const ensureDirectory = (path: string): TreeNode => {
    const existing = nodes.get(path);
    if (existing) return existing;
    const node: TreeNode = {
      path,
      name: basename(path),
      kind: "directory",
      openable: true,
      children: [],
    };
    nodes.set(path, node);
    const slash = path.lastIndexOf("/");
    if (slash < 0) roots.push(node);
    else ensureDirectory(path.slice(0, slash)).children.push(node);
    return node;
  };

  const ensureNode = (entry: WorkspaceEntry): TreeNode => {
    const existing = nodes.get(entry.path);
    if (existing) {
      existing.kind = entry.kind;
      existing.openable = entry.openable;
      existing.reason = entry.reason;
      return existing;
    }
    const node: TreeNode = {
      path: entry.path,
      name: basename(entry.path),
      kind: entry.kind,
      openable: entry.openable,
      reason: entry.reason,
      children: [],
    };
    nodes.set(entry.path, node);
    return node;
  };

  for (const entry of entries) {
    const node = ensureNode(entry);
    const slash = entry.path.lastIndexOf("/");
    if (slash < 0) {
      if (!roots.includes(node)) roots.push(node);
    } else {
      const parent = ensureDirectory(entry.path.slice(0, slash));
      if (!parent.children.includes(node)) parent.children.push(node);
    }
  }
  sortNodes(roots);
  compactDirectories(roots);
  return roots;
}

export function allDirectories(entries: WorkspaceEntry[]): Set<string> {
  const directories = new Set<string>();
  for (const entry of entries) {
    if (entry.kind === "directory") directories.add(entry.path);
    const parts = entry.path.split("/");
    parts.pop();
    for (let depth = 1; depth <= parts.length; depth++) {
      directories.add(parts.slice(0, depth).join("/"));
    }
  }
  return directories;
}

function reasonText(entry: {
  path: string;
  reason?: WorkspaceEntry["reason"];
}) {
  switch (entry.reason) {
    case "too-large":
      return "File is too large to open.";
    case "unreadable":
      return "File could not be read.";
    default: {
      const name = basename(entry.path);
      const dot = name.lastIndexOf(".");
      const extension = dot > 0 ? name.slice(dot) : "";
      return extension
        ? `Abella Web does not open ${extension} files.`
        : "Abella Web does not open this file type.";
    }
  }
}

function editInput(
  value: string,
  placeholder: string,
  onCommit: (value: string) => void,
  onCancel: () => void
): HTMLInputElement {
  const input = document.createElement("input");
  input.type = "text";
  input.className = "tree-edit";
  input.value = value;
  input.placeholder = placeholder;
  input.autocomplete = "off";
  input.spellcheck = false;
  let done = false;
  const commit = (): void => {
    if (done) return;
    done = true;
    onCommit(input.value);
  };
  const cancel = (): void => {
    if (done) return;
    done = true;
    onCancel();
  };
  input.addEventListener("keydown", (event) => {
    event.stopPropagation();
    if (event.key === "Enter") {
      event.preventDefault();
      commit();
    } else if (event.key === "Escape") {
      event.preventDefault();
      cancel();
    }
  });
  input.addEventListener("blur", cancel);
  queueMicrotask(() => {
    input.focus();
    input.select();
  });
  return input;
}

interface RenderContext {
  options: TreeOptions;
  handlers: TreeHandlers;
  selected: string | undefined;
  focusSelected: boolean;
  focusInput: boolean;
}

function interactive(node: TreeNode): boolean {
  return node.kind === "directory" || node.openable;
}

function firstInteractive(nodes: TreeNode[]): string | undefined {
  for (const node of nodes) {
    if (interactive(node)) return node.path;
    const child = firstInteractive(node.children);
    if (child) return child;
  }
  return undefined;
}

function renderNode(
  node: TreeNode,
  depth: number,
  group: HTMLElement,
  context: RenderContext
): void {
  const { options, handlers } = context;
  const row = document.createElement("div");
  row.className = "tree-row";
  row.dataset.path = node.path;
  row.dataset.kind = node.kind;
  row.dataset.depth = String(depth);
  row.setAttribute("role", "treeitem");
  row.setAttribute("aria-level", String(depth + 1));
  row.style.paddingLeft = `${0.5 + depth * 0.85}rem`;
  const isInert = node.kind === "file" && !node.openable;
  row.classList.toggle("inert", isInert);
  if (isInert) {
    row.setAttribute("aria-disabled", "true");
    row.title = reasonText(node);
  } else {
    row.title = node.path;
    row.tabIndex = node.path === context.selected ? 0 : -1;
  }
  row.classList.toggle("active", node.path === options.active);
  if (node.path === options.active) {
    row.setAttribute("aria-selected", "true");
  }
  if (node.kind === "directory") {
    row.setAttribute(
      "aria-expanded",
      String(options.expanded.has(node.path))
    );
  }
  row.classList.toggle("expanded", options.expanded.has(node.path));

  const chevron = document.createElement("span");
  chevron.className = "tree-chevron";
  chevron.setAttribute("aria-hidden", "true");
  if (node.kind === "directory") {
    chevron.textContent = options.expanded.has(node.path) ? "▾" : "▸";
  }
  row.append(chevron);

  const icon = document.createElement("span");
  icon.className = "tree-icon";
  icon.setAttribute("aria-hidden", "true");
  icon.textContent = node.kind === "directory" ? "▣" : "▤";
  row.append(icon);

  const editing =
    options.rename && options.rename.path === node.path
      ? options.rename
      : undefined;
  if (editing) {
    row.classList.add("editing");
    row.append(
      editInput(
        editing.value,
        node.path,
        (value) => handlers.onCommitRename(node.path, value),
        handlers.onCancelEdit
      )
    );
  } else {
    const label = document.createElement("span");
    label.className = "tree-label";
    label.textContent = node.name;
    row.append(label);
  }

  if (node.kind === "file" && node.path === options.entry && !editing) {
    const entry = document.createElement("span");
    entry.className = "tree-entry";
    entry.setAttribute("role", "img");
    entry.setAttribute("aria-label", "Prover file");
    entry.title = "Prover file";
    entry.textContent = "*";
    row.append(entry);
  }

  if (
    node.kind === "file" &&
    options.dirty.has(node.path) &&
    !editing
  ) {
    const dirty = document.createElement("span");
    dirty.className = "tree-dirty";
    dirty.setAttribute("aria-hidden", "true");
    dirty.textContent = "●";
    row.append(dirty);
  }

  if (!isInert) {
    const menu = document.createElement("button");
    menu.type = "button";
    menu.className = "tree-row-menu";
    menu.tabIndex = -1;
    menu.setAttribute("aria-label", `Actions for ${node.path}`);
    menu.title = "File actions";
    menu.textContent = "⋯";
    menu.addEventListener("click", (event) => {
      event.stopPropagation();
      handlers.onSelect(node.path);
      handlers.onContextMenu(node.path, menu);
    });
    menu.addEventListener("pointerdown", (event) => event.stopPropagation());
    row.append(menu);
  }

  if (!isInert) {
    row.addEventListener("click", (event) => {
      if (event.target instanceof HTMLElement) {
        if (event.target.closest(".tree-row-menu")) return;
        if (event.target.closest(".tree-edit")) return;
      }
      handlers.onSelect(node.path);
      if (node.kind === "directory") handlers.onToggle(node.path);
      else handlers.onOpen(node.path);
    });
    row.addEventListener("focus", () => handlers.onSelect(node.path));
    row.addEventListener("contextmenu", (event) => {
      event.preventDefault();
      handlers.onSelect(node.path);
      handlers.onContextMenu(node.path, row);
    });
  } else {
    row.addEventListener("contextmenu", (event) => event.preventDefault());
  }

  group.append(row);

  if (node.kind === "directory") {
    const childGroup = document.createElement("div");
    childGroup.className = "tree-group";
    childGroup.setAttribute("role", "group");
    if (!options.expanded.has(node.path)) {
      childGroup.hidden = true;
    } else {
      if (options.create && options.create.folder === node.path) {
        appendCreateRow(node.path, depth + 1, childGroup, context);
      }
      for (const child of node.children) {
        renderNode(child, depth + 1, childGroup, context);
      }
    }
    group.append(childGroup);
  }

  if (
    context.focusSelected &&
    node.path === context.selected &&
    !isInert
  ) {
    queueMicrotask(() => row.focus());
  }
}

function appendCreateRow(
  folder: string,
  depth: number,
  group: HTMLElement,
  context: RenderContext
): void {
  const edit = context.options.create;
  if (!edit) return;
  const row = document.createElement("div");
  row.className = "tree-row creating";
  row.setAttribute("role", "treeitem");
  row.setAttribute("aria-level", String(depth + 1));
  row.style.paddingLeft = `${0.5 + depth * 0.85}rem`;
  const chevron = document.createElement("span");
  chevron.className = "tree-chevron";
  row.append(chevron);
  const input = editInput(
    edit.value,
    folder ? `name inside ${folder}` : "file name",
    (value) => context.handlers.onCommitCreate(folder, value),
    context.handlers.onCancelEdit
  );
  row.append(input);
  group.append(row);
  if (context.focusInput) queueMicrotask(() => input.focus());
}

export function renderFiles(
  container: HTMLElement,
  options: TreeOptions,
  handlers: TreeHandlers
): TreeNode[] {
  container.replaceChildren();
  const tree = buildTree(options.entries);
  const selected =
    options.selected !== undefined &&
    tree.some((node) => containsPath(node, options.selected!))
      ? options.selected
      : options.active ?? firstInteractive(tree);
  const context: RenderContext = {
    options,
    handlers,
    selected,
    focusSelected: options.focusSelected ?? false,
    focusInput: options.focusInput ?? false,
  };

  if (options.create && (options.create.folder ?? "") === "") {
    appendCreateRow("", 0, container, context);
  }
  for (const node of tree) {
    renderNode(node, 0, container, context);
  }
  return tree;
}

function containsPath(node: TreeNode, path: string): boolean {
  if (node.path === path) return true;
  return node.children.some((child) => containsPath(child, path));
}

export function visibleRows(container: HTMLElement): HTMLElement[] {
  return [...container.querySelectorAll<HTMLElement>(".tree-row")].filter(
    (row) =>
      row.dataset.kind !== undefined &&
      row.tabIndex >= 0 &&
      !row.hidden &&
      row.offsetParent !== null
  );
}
