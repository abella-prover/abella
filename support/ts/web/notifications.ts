// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { OutputEntry } from "./session";

export interface NotificationRecord {
  entry: OutputEntry;
  seq: number;
}

export class NotificationLog {
  private records: NotificationRecord[] = [];
  private nextSequence = 0;
  private unreadCount = 0;

  get entries(): readonly NotificationRecord[] {
    return this.records;
  }

  get count(): number {
    return this.records.length;
  }

  get unread(): number {
    return this.unreadCount;
  }

  get hasError(): boolean {
    return this.records.some(
      (record) => record.entry.severity === "error"
    );
  }

  add(entries: readonly OutputEntry[]): void {
    for (const entry of entries) {
      this.records.push({ entry, seq: this.nextSequence++ });
      this.unreadCount++;
    }
  }

  markRead(): void {
    this.unreadCount = 0;
  }

  clear(): void {
    this.records = [];
    this.nextSequence = 0;
    this.unreadCount = 0;
  }
}
