// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Shared types for the Abella Web frontend and worker protocol.

export interface ProjectFile {
  path: string;
  contents: string;
  binary?: boolean;
}

export interface SourcePos {
  offset: number;
  line: number;
  bol: number;
}

export interface RunResult {
  status: "ok" | "error";
  messages: RawMessage[];
}

export type ProofState = {
  name: string;
  vars: [string, string | null][];
  hyps: [string, string][];
  goal: string;
  more: number;
};

export type RawMessage =
  | {
      type: "top_command";
      id: number;
      command: string;
      range?: number[] | null;
    }
  | {
      type: "proof_command";
      id: number;
      thm_id: number;
      theorem: string;
      command: string;
      start_state: ProofState;
      end_state?: ProofState;
      range?: number[] | null;
    }
  | {
      type: "system_message";
      id: number;
      severity: "info" | "error";
      message: string;
    }
  | { type: "link"; id: number; source: number[] | null; url: string };

export interface Abellajs {
  init(files: ProjectFile[], root: string): RunResult;
  reset(files: ProjectFile[], root: string): RunResult;
  process(command: string, start: SourcePos): RunResult;
  back(count: number): RunResult;
  thc(path: string): string | null;
  setOnImport(callback: (name: string) => void): void;
}

export type Engine = "wasm" | "js";
