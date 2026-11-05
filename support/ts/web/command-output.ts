// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { ChangeSet } from "@codemirror/state";
import type { OutputEntry, OutputLocation } from "./session";

export interface CommandOutput {
  from: number;
  to: number;
  position: number;
  entries: readonly OutputEntry[];
}

export class CommandOutputStore {
  private outputs = new Map<number, CommandOutput>();

  set(location: OutputLocation, entries: readonly OutputEntry[]): void {
    if (entries.length === 0) {
      this.outputs.delete(location.from);
      return;
    }
    this.outputs.set(location.from, {
      from: location.from,
      to: location.to,
      position: location.position,
      entries: [...entries],
    });
  }

  get(from: number): CommandOutput | undefined {
    return this.outputs.get(from);
  }

  values(): readonly CommandOutput[] {
    return [...this.outputs.values()].sort((a, b) => a.from - b.from);
  }

  prune(tip: number): boolean {
    let changed = false;
    for (const [from, output] of this.outputs) {
      if (output.position <= tip) continue;
      this.outputs.delete(from);
      changed = true;
    }
    return changed;
  }

  remap(changes: ChangeSet): boolean {
    let changed = false;
    const next = new Map<number, CommandOutput>();
    for (const output of this.outputs.values()) {
      let touched = false;
      changes.iterChangedRanges((fromA, toA) => {
        if (fromA < output.to && output.from < toA) touched = true;
        else if (
          fromA === toA &&
          fromA > output.from &&
          fromA < output.to
        ) {
          touched = true;
        }
      });
      if (touched) {
        changed = true;
        continue;
      }
      const from = changes.mapPos(output.from, 1);
      const to = changes.mapPos(output.to, -1);
      const position = changes.mapPos(output.position, -1);
      if (
        from !== output.from ||
        to !== output.to ||
        position !== output.position
      ) {
        changed = true;
      }
      next.set(from, {
        from,
        to,
        position,
        entries: output.entries,
      });
    }
    this.outputs = next;
    return changed;
  }

  clear(): void {
    this.outputs.clear();
  }
}
