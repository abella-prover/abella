// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

export interface ExampleEntry {
  id: string;
  group: string;
  name: string;
  root: string;
  sig: string | null;
  mod: string | null;
}

export interface Bundle {
  version: number;
  examples: ExampleEntry[];
  files: Record<string, string>;
}

export async function loadBundle(): Promise<Bundle | undefined> {
  try {
    const response = await fetch("examples/bundle.json", { cache: "no-store" });
    if (!response.ok) return undefined;
    const bundle = (await response.json()) as Bundle;
    if (!bundle.examples || !bundle.files) return undefined;
    return bundle;
  } catch {
    return undefined;
  }
}

export function fillExampleSelect(
  select: HTMLSelectElement,
  bundle: Bundle
): void {
  select.replaceChildren();
  select.disabled = false;
  const placeholder = document.createElement("option");
  placeholder.value = "";
  placeholder.textContent = "Load an example…";
  select.append(placeholder);

  const groups = new Map<string, ExampleEntry[]>();
  for (const example of bundle.examples) {
    const list = groups.get(example.group) ?? [];
    list.push(example);
    groups.set(example.group, list);
  }
  for (const [group, examples] of groups) {
    const optgroup = document.createElement("optgroup");
    optgroup.label = group;
    for (const example of examples) {
      const option = document.createElement("option");
      option.value = example.id;
      option.textContent = example.name;
      optgroup.append(option);
    }
    select.append(optgroup);
  }
}
