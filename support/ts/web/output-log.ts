// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { OutputEntry } from "./session";

export interface OutputRecord {
  entry: OutputEntry;
  position?: number;
  seq: number;
}

export class OutputLog {
  private records: OutputRecord[] = [];
  private nextSequence = 0;

  get count(): number {
    return this.records.length;
  }

  get ordered(): readonly OutputRecord[] {
    return [...this.records].sort((a, b) => {
      if (a.position !== undefined && b.position !== undefined) {
        return a.position - b.position || a.seq - b.seq;
      }
      if (a.position !== undefined) return -1;
      if (b.position !== undefined) return 1;
      return a.seq - b.seq;
    });
  }

  get hasError(): boolean {
    return this.records.some(
      (record) => record.entry.severity === "error"
    );
  }

  append(entries: readonly OutputEntry[], position?: number): void {
    for (const entry of entries) {
      this.records.push({ entry, position, seq: this.nextSequence++ });
    }
  }

  /** Remove positioned entries generated after `tip`; return their count. */
  prune(tip: number): number {
    const before = this.records.length;
    this.records = this.records.filter(
      (record) => record.position === undefined || record.position <= tip
    );
    return before - this.records.length;
  }

  clear(): void {
    this.records = [];
    this.nextSequence = 0;
  }
}
