// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { OutputEntry, OutputLocation } from "./session";

export interface OutputRecord {
  entry: OutputEntry;
  location?: OutputLocation;
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
      const aPosition = a.location?.position;
      const bPosition = b.location?.position;
      if (aPosition !== undefined && bPosition !== undefined) {
        return aPosition - bPosition || a.seq - b.seq;
      }
      if (aPosition !== undefined) return -1;
      if (bPosition !== undefined) return 1;
      return a.seq - b.seq;
    });
  }

  get hasError(): boolean {
    return this.records.some(
      (record) => record.entry.severity === "error"
    );
  }

  append(entries: readonly OutputEntry[], location?: OutputLocation): void {
    if (location !== undefined) {
      this.records = this.records.filter(
        (record) => record.location?.from !== location.from
      );
    }
    for (const entry of entries) {
      this.records.push({ entry, location, seq: this.nextSequence++ });
    }
  }

  /** Remove positioned entries generated after `tip`; return their count. */
  prune(tip: number): number {
    const before = this.records.length;
    this.records = this.records.filter(
      (record) =>
        record.location === undefined || record.location.position <= tip
    );
    return before - this.records.length;
  }

  clear(): void {
    this.records = [];
    this.nextSequence = 0;
  }
}
