// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { ProjectFile, RunResult, SourcePos } from "./types";
import { WEB_ASSET_VERSION } from "./version";

export interface Driver {
  init(files: ProjectFile[], root: string): Promise<RunResult>;
  reset(files: ProjectFile[], root: string): Promise<RunResult>;
  process(command: string, start: SourcePos): Promise<RunResult>;
  back(count: number): Promise<RunResult>;
  terminate(): void;
  restart?(): void;
  onProgress?: (module: string) => void;
}

interface Pending {
  resolve: (value: RunResult) => void;
  reject: (reason: Error) => void;
}

const WORKER_PATH = `abella_js/worker.js?v=${WEB_ASSET_VERSION}`;

export class WorkerDriver implements Driver {
  private worker!: Worker;
  private ready!: Promise<void>;
  private rejectReady?: (error: Error) => void;
  private pending = new Map<number, Pending>();
  private nextId = 0;
  onProgress?: (module: string) => void;

  constructor(onProgress?: (module: string) => void) {
    this.onProgress = onProgress;
    this.spawn();
  }

  private spawn(): void {
    this.worker = new Worker(WORKER_PATH);
    this.ready = new Promise((resolve, reject) => {
      this.rejectReady = reject;
      const onReady = (event: MessageEvent) => {
        if (event.data?.type === "ready") {
          this.worker.removeEventListener("message", onReady);
          this.worker.removeEventListener("error", onError);
          this.rejectReady = undefined;
          resolve();
        }
      };
      const onError = (event: ErrorEvent) => {
        this.worker.removeEventListener("message", onReady);
        this.worker.removeEventListener("error", onError);
        this.rejectReady = undefined;
        reject(new Error(event.message || "Could not start the prover worker"));
      };
      this.worker.addEventListener("message", onReady);
      this.worker.addEventListener("error", onError);
    });
    // A restart can reject this before any caller awaits it.
    this.ready.catch(() => undefined);
    this.worker.addEventListener("message", (event) => this.receive(event));
    this.worker.addEventListener("error", (event) => {
      const error = new Error(event.message || "Prover worker error");
      this.rejectPending(error);
    });
  }

  private rejectPending(error: Error): void {
    for (const pending of this.pending.values()) pending.reject(error);
    this.pending.clear();
  }

  private receive(event: MessageEvent): void {
    const message = event.data;
    if (message?.type === "progress") {
      this.onProgress?.(String(message.module ?? ""));
      return;
    }
    if (message?.type === "ready") return;
    const pending = this.pending.get(message?.id);
    if (!pending) return;
    this.pending.delete(message.id);
    if (message.ok) {
      pending.resolve(message.result as RunResult);
    } else {
      pending.reject(new Error(String(message.error ?? "Unknown worker error")));
    }
  }

  private async call(
    type: string,
    payload: Record<string, unknown>
  ): Promise<RunResult> {
    await this.ready;
    const id = this.nextId++;
    return new Promise<RunResult>((resolve, reject) => {
      this.pending.set(id, { resolve, reject });
      this.worker.postMessage({ id, type, ...payload });
    });
  }

  init(files: ProjectFile[], root: string): Promise<RunResult> {
    return this.call("init", { files, root });
  }

  reset(files: ProjectFile[], root: string): Promise<RunResult> {
    return this.call("reset", { files, root });
  }

  process(command: string, start: SourcePos): Promise<RunResult> {
    return this.call("process", { command, start });
  }

  back(count: number): Promise<RunResult> {
    return this.call("back", { count });
  }

  terminate(): void {
    this.worker.terminate();
    this.rejectPending(new Error("Prover worker terminated"));
  }

  restart(): void {
    this.rejectReady?.(new Error("Prover worker restarted"));
    this.rejectReady = undefined;
    this.worker.terminate();
    this.rejectPending(new Error("Prover worker restarted"));
    this.spawn();
  }
}
