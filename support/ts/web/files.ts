// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

import { sortPaths, type Project } from "./project";

function directoryOf(path: string): string {
  const slash = path.lastIndexOf("/");
  return slash < 0 ? "" : path.slice(0, slash);
}

function basenameOf(path: string): string {
  const slash = path.lastIndexOf("/");
  return slash < 0 ? path : path.slice(slash + 1);
}

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
  button.title = path;
  button.setAttribute("aria-label", path);
  if (path === active) {
    button.classList.add("active");
    button.setAttribute("aria-current", "true");
  }
  if (path === project.root) button.classList.add("root");
  const name = document.createElement("span");
  name.className = "file-name";
  name.textContent = basenameOf(path);
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

  const byKind = (kind: string) =>
    sortPaths(
      [...project.files.keys()].filter(
        (path) => project.files.get(path)!.kind === kind
      )
    );

  const addGroup = (title: string, paths: string[]) => {
    if (paths.length === 0) return;
    const heading = document.createElement("div");
    heading.className = "file-group";
    heading.textContent = title;
    container.append(heading);

    const directories = new Map<string, string[]>();
    for (const path of paths) {
      const directory = directoryOf(path);
      const list = directories.get(directory) ?? [];
      list.push(path);
      directories.set(directory, list);
    }

    for (const directory of [...directories.keys()].sort((a, b) =>
      a.localeCompare(b)
    )) {
      const dirHeading = document.createElement("div");
      dirHeading.className = "file-dir";
      dirHeading.textContent = directory || "Project";
      dirHeading.title = directory || "Project";
      container.append(dirHeading);
      const inDirectory = directories.get(directory)!;
      inDirectory.sort((a, b) => basenameOf(a).localeCompare(basenameOf(b)));
      for (const path of inDirectory) {
        container.append(fileButton(project, path, active, onSelect));
      }
    }
  };

  addGroup("Abella", byKind("abella"));
  addGroup("Other files", byKind("text"));
}
