// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Web Worker entry for the Abella Web prover engine.
//
// esbuild replaces __ENGINE__ at build time and emits this file either as
// web/abella_js/worker.js (wasm) or web/abella_worker.js (js).  The wasm
// launcher resolves its .wasm assets relative to this worker's URL, which is
// why the wasm build lives inside web/abella_js/.

declare const __ENGINE__: "js" | "wasm";
declare function importScripts(...urls: string[]): void;
declare const Abellajs: import("./types").Abellajs;

if (__ENGINE__ === "wasm") {
  importScripts("abella_js.bc.wasm.js");
} else {
  importScripts("abella_js.js");
}

const scope = self as unknown as {
  postMessage(message: unknown): void;
  onmessage: ((event: MessageEvent) => void) | null;
};

function announceWhenReady(): void {
  if (typeof Abellajs !== "undefined") {
    Abellajs.setOnImport((module) => {
      scope.postMessage({ type: "progress", stage: "compiling", module });
    });
    scope.postMessage({ type: "ready", engine: __ENGINE__ });
  } else {
    setTimeout(announceWhenReady, 10);
  }
}

announceWhenReady();

scope.onmessage = async (event: MessageEvent) => {
  const message = event.data as {
    id: number;
    type: "init" | "reset" | "process" | "back";
    files?: Parameters<typeof Abellajs.init>[0];
    root?: string;
    command?: string;
    start?: Parameters<typeof Abellajs.process>[1];
    count?: number;
  };
  try {
    let result;
    switch (message.type) {
      case "init":
        result = Abellajs.init(message.files ?? [], message.root ?? "");
        break;
      case "reset":
        result = Abellajs.reset(message.files ?? [], message.root ?? "");
        break;
      case "process":
        result = Abellajs.process(
          message.command ?? "",
          message.start ?? { offset: 0, line: 1, bol: 0 }
        );
        break;
      case "back":
        result = Abellajs.back(message.count ?? 0);
        break;
    }
    scope.postMessage({ type: "result", id: message.id, ok: true, result });
  } catch (error) {
    scope.postMessage({
      type: "result",
      id: message.id,
      ok: false,
      error: String(error),
    });
  }
};
