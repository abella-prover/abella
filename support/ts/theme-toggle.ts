// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

export type Theme = "light" | "dark";

export interface ThemeToggle {
  element: HTMLLabelElement;
  setTheme(theme: Theme, persist: boolean): void;
}

const sunMoonIcons = `
    <svg class="theme-icon theme-icon-sun" viewBox="0 0 16 16"
         fill="none" stroke="currentColor" stroke-width="1.5"
         stroke-linecap="round" aria-hidden="true">
      <circle cx="8" cy="8" r="2.75"/>
      <path d="M8 1.5v1.25M8 13.25v1.25M1.5 8h1.25M13.25 8h1.25M3.4 3.4l.9.9M11.7 11.7l.9.9M12.6 3.4l-.9.9M4.3 11.7l-.9.9"/>
    </svg>
    <svg class="theme-icon theme-icon-moon" viewBox="0 0 16 16"
         fill="currentColor" aria-hidden="true">
      <path d="M13.5 9.7A5.7 5.7 0 0 1 6.3 2.5 5.7 5.7 0 1 0 13.5 9.7Z"/>
    </svg>`;

export function loadTheme(themeKey: string): Theme {
  try {
    const saved = localStorage.getItem(themeKey);
    if (saved === "dark" || saved === "light") return saved;
  } catch {
    // Storage can be unavailable in private browsing.
  }
  return window.matchMedia("(prefers-color-scheme: dark)").matches
    ? "dark"
    : "light";
}

export function createThemeToggle(themeKey: string): ThemeToggle {
  const label = document.createElement("label");
  label.classList.add("theme-toggle");
  const input = document.createElement("input");
  input.type = "checkbox";
  input.classList.add("theme-switch");
  input.setAttribute("role", "switch");
  input.setAttribute("aria-label", "Dark mode");
  const track = document.createElement("span");
  track.classList.add("theme-toggle-track");
  const knob = document.createElement("span");
  knob.classList.add("theme-toggle-knob");
  knob.innerHTML = sunMoonIcons;
  track.append(knob);
  label.append(input, track);

  const refresh = () => {
    const dark = document.documentElement.dataset.theme === "dark";
    input.checked = dark;
    label.title = dark ? "Switch to light mode" : "Switch to dark mode";
  };

  const setTheme = (theme: Theme, persist: boolean) => {
    document.documentElement.dataset.theme = theme;
    if (persist) {
      try {
        localStorage.setItem(themeKey, theme);
      } catch {
        // Storage can be unavailable in private browsing.
      }
    }
    refresh();
  };

  input.addEventListener("change", () => {
    setTheme(input.checked ? "dark" : "light", true);
  });

  refresh();
  return { element: label, setTheme };
}
