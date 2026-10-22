// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type {
  Engine,
  ProjectFile,
  RunResult,
  SourcePos,
} from "./types";

export interface Driver {
  init(files: ProjectFile[], root: string): Promise<RunResult>;
  reset(files: ProjectFile[], root: string): Promise<RunResult>;
  process(command: string, start: SourcePos): Promise<RunResult>;
  back(count: number): Promise<RunResult>;
  terminate(): void;
  onProgress?: (module: string) => void;
}

interface Pending {
  resolve: (value: RunResult) => void;
  reject: (reason: Error) => void;
}

export function workerPath(engine: Engine): string {
  return engine === "wasm" ? "abella_js/worker.js" : "abella_worker.js";
}

export async function loadEngine(): Promise<Engine> {
  try {
    const response = await fetch("engine.json", { cache: "no-store" });
    if (!response.ok) return "wasm";
    const data = (await response.json()) as { engine?: string };
    return data.engine === "js" ? "js" : "wasm";
  } catch {
    return "wasm";
  }
}

export class WorkerDriver implements Driver {
  private worker: Worker;
  private ready: Promise<void>;
  private pending = new Map<number, Pending>();
  private nextId = 0;
  onProgress?: (module: string) => void;

  constructor(engine: Engine, onProgress?: (module: string) => void) {
    this.worker = new Worker(workerPath(engine));
    this.onProgress = onProgress;
    this.ready = new Promise((resolve, reject) => {
      const onReady = (event: MessageEvent) => {
        if (event.data?.type === "ready") {
          this.worker.removeEventListener("message", onReady);
          this.worker.removeEventListener("error", onError);
          resolve();
        }
      };
      const onError = (event: ErrorEvent) => {
        this.worker.removeEventListener("message", onReady);
        this.worker.removeEventListener("error", onError);
        reject(new Error(event.message || "Could not start the prover worker"));
      };
      this.worker.addEventListener("message", onReady);
      this.worker.addEventListener("error", onError);
    });
    this.worker.addEventListener("message", (event) => this.receive(event));
    this.worker.addEventListener("error", (event) => {
      const error = new Error(event.message || "Prover worker error");
      for (const pending of this.pending.values()) pending.reject(error);
      this.pending.clear();
    });
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
    for (const pending of this.pending.values()) {
      pending.reject(new Error("Prover worker terminated"));
    }
    this.pending.clear();
  }
}
