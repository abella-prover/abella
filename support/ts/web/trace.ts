// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import type { ProofState, RawMessage } from "./types";

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

export function appendMessages(
  container: HTMLElement,
  messages: RawMessage[]
): void {
  for (const message of messages) {
    if (message.type !== "system_message") continue;
    const line = document.createElement("div");
    line.className = "message";
    line.dataset.severity = message.severity;
    line.textContent = message.message;
    container.append(line);
  }
  container.scrollTop = container.scrollHeight;
}

export function errorMessages(messages: RawMessage[]): string[] {
  return messages
    .filter(
      (message): message is Extract<RawMessage, { type: "system_message" }> =>
        message.type === "system_message" && message.severity === "error"
    )
    .map((message) => message.message);
}
