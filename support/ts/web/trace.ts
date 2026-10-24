// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { OutputEntry } from "./session";
import type { ProofState } from "./types";

function row(className: string, ...children: (Node | string)[]): HTMLElement {
  const element = document.createElement("div");
  element.className = className;
  for (const child of children) {
    element.append(
      typeof child === "string" ? document.createTextNode(child) : child
    );
  }
  return element;
}

function code(text: string): HTMLElement {
  const element = document.createElement("code");
  element.textContent = text;
  return element;
}

export function renderSequent(state: ProofState): HTMLElement {
  const box = document.createElement("div");
  box.className = "sequent";
  if (state.name) {
    box.append(row("sequent-name", `Subgoal ${state.name}`));
  }
  const variables = (state.vars ?? [])
    .filter(([, type]) => !type)
    .map(([name]) => name);
  if (variables.length > 0) {
    box.append(row("sequent-row", code(`Variables: ${variables.join(" ")}`)));
  }
  for (const [name, term] of state.hyps ?? []) {
    const line = row("sequent-row", code(""));
    const codeEl = line.firstChild as HTMLElement;
    const hyp = document.createElement("span");
    hyp.className = "sequent-hyp";
    hyp.textContent = name;
    codeEl.append(hyp, document.createTextNode(`: ${term}`));
    box.append(line);
  }
  box.append(row("sequent-line"));
  const goal = row("sequent-row", code(""));
  (goal.firstChild as HTMLElement).append(
    document.createTextNode(`\u00a0${state.goal}`)
  );
  box.append(goal);
  if (state.more > 0) {
    box.append(
      row(
        "sequent-more",
        `(+ ${state.more} more subgoal${state.more > 1 ? "s" : ""})`
      )
    );
  }
  return box;
}

export interface OutputLine {
  entry: OutputEntry;
  from?: number;
}

export function appendOutput(
  container: HTMLElement,
  lines: readonly OutputLine[],
  onSelect?: (from: number) => void
): void {
  for (const { entry, from } of lines) {
    const line = document.createElement("div");
    line.className = "output-entry";
    line.dataset.severity = entry.severity;
    line.textContent = entry.message;
    if (from !== undefined && onSelect) {
      line.classList.add("output-jump");
      line.tabIndex = 0;
      line.setAttribute("role", "button");
      line.title = "Jump to the command that produced this output";
      const jump = (): void => {
        const selection = window.getSelection();
        if (
          selection &&
          !selection.isCollapsed &&
          selection.anchorNode &&
          line.contains(selection.anchorNode)
        ) {
          return;
        }
        onSelect(from);
      };
      line.addEventListener("click", jump);
      line.addEventListener("keydown", (event) => {
        if (event.key !== "Enter" && event.key !== " ") return;
        event.preventDefault();
        onSelect(from);
      });
    }
    container.append(line);
  }
  container.scrollTop = container.scrollHeight;
}
