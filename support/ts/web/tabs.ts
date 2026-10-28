// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Tab-strip model.  The editor owns one EditorState per path; this module
// owns the order and the active tab.

export interface TabClose {
  tabs: string[];
  active?: string;
}

export function addTab(tabs: readonly string[], path: string): string[] {
  return tabs.includes(path) ? [...tabs] : [...tabs, path];
}

export function closeTabAt(
  tabs: readonly string[],
  path: string,
  active: string | undefined
): TabClose {
  const index = tabs.indexOf(path);
  if (index < 0) return { tabs: [...tabs], active };
  const next = [...tabs];
  next.splice(index, 1);
  if (active !== path) return { tabs: next, active };
  return { tabs: next, active: next[index] ?? next[index - 1] };
}

export function remapTabs(
  tabs: readonly string[],
  renames: ReadonlyMap<string, string>
): string[] {
  return tabs.map((path) => renames.get(path) ?? path);
}

export interface TabState {
  tabs: string[];
  active?: string;
}

/**
 * Drop tabs whose files no longer exist, keep the active tab when it is
 * still open, and otherwise fall back to a neighbour or the first tab.
 * The editor's active path is reconciled separately by the caller.
 */
export function reconcileTabState(
  tabs: readonly string[],
  exists: (path: string) => boolean,
  active: string | undefined,
  fallback?: string
): TabState {
  const valid = [...new Set(tabs.filter((path) => exists(path)))];
  let nextActive =
    active !== undefined && exists(active)
      ? active
      : fallback !== undefined && exists(fallback)
        ? fallback
        : valid[0];
  if (nextActive !== undefined && !valid.includes(nextActive)) {
    valid.push(nextActive);
  }
  return { tabs: valid, active: nextActive };
}

function suffixOf(path: string, depth: number): string {
  const parts = path.split("/");
  return parts.slice(Math.max(0, parts.length - depth)).join("/");
}

/**
 * Basenames unless another tab shares one; then extend with the shortest
 * unique parent-directory suffix.
 */
export function tabLabels(tabs: readonly string[]): Map<string, string> {
  const labels = new Map<string, string>();
  for (const path of tabs) {
    const depth = path.split("/").length;
    let suffixDepth = 1;
    while (
      suffixDepth < depth &&
      tabs.some(
        (other) =>
          other !== path &&
          suffixOf(other, suffixDepth) === suffixOf(path, suffixDepth)
      )
    ) {
      suffixDepth++;
    }
    labels.set(path, suffixOf(path, suffixDepth));
  }
  return labels;
}
