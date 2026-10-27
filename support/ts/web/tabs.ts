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
