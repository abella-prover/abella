// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { sortPaths, type Project } from "./project";

function fileButton(
  project: Project,
  path: string,
  active: string,
  onSelect: (path: string) => void
): HTMLElement {
  const button = document.createElement("button");
  button.type = "button";
  button.className = "file";
  button.dataset.path = path;
  if (path === active) button.classList.add("active");
  if (path === project.root) button.classList.add("root");
  const name = document.createElement("span");
  name.className = "file-name";
  name.textContent = path;
  button.append(name);
  if (path === project.root) {
    const marker = document.createElement("span");
    marker.className = "file-root";
    marker.title = "Root reasoning file";
    marker.textContent = "*";
    button.append(marker);
  }
  button.addEventListener("click", () => onSelect(path));
  return button;
}

export function renderFiles(
  container: HTMLElement,
  project: Project,
  active: string,
  onSelect: (path: string) => void
): void {
  container.replaceChildren();
  const abella = sortPaths(
    [...project.files.keys()].filter(
      (path) => project.files.get(path)!.kind === "abella"
    )
  );
  const text = sortPaths(
    [...project.files.keys()].filter(
      (path) => project.files.get(path)!.kind === "text"
    )
  );

  const addGroup = (title: string, paths: string[]) => {
    if (paths.length === 0) return;
    const heading = document.createElement("div");
    heading.className = "file-group";
    heading.textContent = title;
    container.append(heading);
    for (const path of paths) {
      container.append(fileButton(project, path, active, onSelect));
    }
  };

  addGroup("Abella", abella);
  addGroup("Other files", text);
}
