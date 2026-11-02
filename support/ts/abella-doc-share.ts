// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Browser-side packaging for the doc page's "Edit this" button.  The
// page reads its own sources, builds the version 2 zip, uploads it to
// the share Worker, and opens Abella Web with a short-lived ?zip= URL.

import { strToU8, zipSync } from "fflate";

export interface ShareData {
  entry: string;
  files: string[];
  web: string;
  share: string;
}

export interface ShareOptions {
  fetch?: typeof fetch;
  open?: (url: string) => void;
  baseUrl?: string;
}

export const MAX_ZIP_BYTES = 8 * 1024 * 1024;

function isStringArray(value: unknown): value is string[] {
  return (
    Array.isArray(value) && value.every((item) => typeof item === "string")
  );
}

export function parseShareData(text: string): ShareData {
  let data: unknown;
  try {
    data = JSON.parse(text);
  } catch {
    throw new Error("The project data embedded in this page is not JSON.");
  }
  if (typeof data !== "object" || data === null || Array.isArray(data)) {
    throw new Error("The project data embedded in this page is invalid.");
  }
  const record = data as Record<string, unknown>;
  const { entry, files, web, share } = record;
  if (
    typeof entry !== "string" ||
    entry === "" ||
    !isStringArray(files) ||
    typeof web !== "string" ||
    web === "" ||
    typeof share !== "string" ||
    share === ""
  ) {
    throw new Error("The project data embedded in this page is incomplete.");
  }
  if (!files.includes(entry)) {
    throw new Error("The project entry is missing from the embedded file list.");
  }
  return { entry, files, web, share };
}

function withBase(raw: string, baseUrl?: string): URL {
  try {
    return new URL(raw, baseUrl);
  } catch {
    throw new Error(`The project uses an invalid URL: ${raw}`);
  }
}

function documentBase(): string | undefined {
  return typeof document === "undefined" ? undefined : document.baseURI;
}

export async function readSources(
  data: ShareData,
  fetchFn: typeof fetch = fetch,
  baseUrl = documentBase()
): Promise<{ sources: Map<string, string>; totalBytes: number }> {
  const encoder = new TextEncoder();
  const sources = new Map<string, string>();
  let totalBytes = 0;
  await Promise.all(
    data.files.map(async (path) => {
      const url = withBase(path, baseUrl);
      let response: Response;
      try {
        response = await fetchFn(url.toString(), {
          cache: "no-store",
          credentials: "same-origin",
        });
      } catch {
        throw new Error(`Could not read ${path}.`);
      }
      if (!response.ok) {
        throw new Error(
          `Could not read ${path} (HTTP ${response.status}). ` +
            "Serve the Abella sources next to the generated page."
        );
      }
      const text = await response.text();
      totalBytes += encoder.encode(text).byteLength;
      sources.set(path, text);
    })
  );
  return { sources, totalBytes };
}

export function buildProjectZip(
  data: ShareData,
  sources: Map<string, string>
): Uint8Array {
  const files = [...new Set(data.files)].sort();
  if (files.includes("project.json")) {
    throw new Error("A source file may not be named project.json.");
  }
  const archive: Record<string, Uint8Array> = {
    "project.json": strToU8(
      JSON.stringify({ version: 2, entry: data.entry, files }, null, 2)
    ),
  };
  for (const path of files) {
    const text = sources.get(path);
    if (text === undefined) {
      throw new Error(`Could not read ${path}.`);
    }
    archive[path] = strToU8(text);
  }
  return zipSync(archive, { level: 6 });
}

export async function uploadProject(
  share: string,
  bytes: Uint8Array,
  fetchFn: typeof fetch = fetch,
  baseUrl = documentBase()
): Promise<string> {
  const endpoint = new URL(
    "zips",
    withBase(share.endsWith("/") ? share : `${share}/`, baseUrl)
  );
  const payload = new Uint8Array(bytes.byteLength);
  payload.set(bytes);
  let response: Response;
  try {
    response = await fetchFn(endpoint.toString(), {
      method: "POST",
      headers: { "Content-Type": "application/zip" },
      body: new Blob([payload.buffer], { type: "application/zip" }),
      cache: "no-store",
      credentials: "omit",
    });
  } catch {
    throw new Error("Could not reach the share service.");
  }
  if (!response.ok) {
    let message = "";
    try {
      const body = (await response.json()) as { message?: unknown };
      if (typeof body.message === "string") message = body.message;
    } catch {
      // The error body is optional.
    }
    throw new Error(
      message ||
        `The share service rejected the upload (HTTP ${response.status}).`
    );
  }
  let body: unknown;
  try {
    body = await response.json();
  } catch {
    throw new Error("The share service returned an unreadable response.");
  }
  const url = (body as { url?: unknown }).url;
  if (typeof url !== "string" || url === "") {
    throw new Error("The share service did not return a download URL.");
  }
  return url;
}

export function shareTarget(
  web: string,
  url: string,
  baseUrl = documentBase()
): string {
  const target = withBase(web, baseUrl);
  target.searchParams.set("zip", url);
  return target.toString();
}

function formatBytes(bytes: number): string {
  if (bytes < 1024) return `${bytes} B`;
  if (bytes < 1024 * 1024) return `${(bytes / 1024).toFixed(1)} KiB`;
  return `${(bytes / (1024 * 1024)).toFixed(1)} MiB`;
}

export interface UploadConfirmation {
  files: number;
  bytes: number;
}

interface ConfirmationResult {
  confirmed: boolean;
  tab: Window | null;
}

function confirmUpload(
  details: UploadConfirmation
): Promise<ConfirmationResult> {
  return new Promise((resolve) => {
    const dialog = document.createElement("dialog");
    dialog.className = "edit-dialog";
    dialog.setAttribute("aria-labelledby", "abella-upload-title");

    const title = document.createElement("h2");
    title.id = "abella-upload-title";
    title.textContent = "Upload this project?";

    const text = document.createElement("p");
    text.append(
      `Upload ${details.files} file${details.files === 1 ? "" : "s"} ` +
        `(${formatBytes(details.bytes)}) to Abella Web? ` +
        "The link expires in 10 minutes."
    );

    const actions = document.createElement("div");
    actions.className = "edit-dialog-actions";
    const cancel = document.createElement("button");
    cancel.type = "button";
    cancel.textContent = "Cancel";
    const upload = document.createElement("button");
    upload.type = "button";
    upload.className = "edit-dialog-upload";
    upload.textContent = "Upload";
    actions.append(cancel, upload);

    dialog.append(title, text, actions);
    document.body.append(dialog);

    let settled = false;
    const finish = (confirmed: boolean, tab: Window | null): void => {
      if (settled) return;
      settled = true;
      if (dialog.open) dialog.close();
      dialog.remove();
      resolve({ confirmed, tab });
    };

    cancel.addEventListener("click", () => finish(false, null));
    upload.addEventListener("click", () => {
      // Open the tab in this click handler.  Opening it after an await
      // would let popup blockers drop it.
      finish(true, window.open("", "_blank"));
    });
    dialog.addEventListener("cancel", (event) => {
      event.preventDefault();
      finish(false, null);
    });
    dialog.addEventListener("click", (event) => {
      if (event.target === dialog) finish(false, null);
    });

    dialog.showModal();
    upload.focus();
  });
}

export function installProjectShare(options: ShareOptions = {}): void {
  const dataElement = document.getElementById("abella-project");
  const button = document.querySelector<HTMLButtonElement>(
    "button[data-abella-share]"
  );
  if (!dataElement || !button) return;

  let data: ShareData;
  try {
    data = parseShareData(dataElement.textContent ?? "");
  } catch {
    return;
  }

  const status = document.createElement("p");
  status.className = "edit-status";
  status.setAttribute("role", "status");
  (document.getElementById("logobox") ?? button).after(status);
  const setStatus = (text: string, error = false): void => {
    status.textContent = text;
    status.dataset.state = error ? "error" : "";
  };

  button.addEventListener("click", async () => {
    if (button.disabled) return;
    if (window.location.protocol === "file:") {
      setStatus(
        "Serve the documentation over HTTP to use Edit this. " +
          "A file:// page cannot read its source files.",
        true
      );
      return;
    }

    const fetchFn = options.fetch ?? fetch;
    const openFn =
      options.open ?? ((url: string) => (window.location.href = url));
    const baseUrl = options.baseUrl ?? document.baseURI;
    let tab: Window | null = null;

    button.disabled = true;
    setStatus("Reading sources…");
    try {
      const { sources, totalBytes } = await readSources(
        data,
        fetchFn,
        baseUrl
      );
      const bytes = buildProjectZip(data, sources);
      if (bytes.byteLength > MAX_ZIP_BYTES) {
        throw new Error(
          `The project is ${formatBytes(bytes.byteLength)}; ` +
            `the share limit is ${formatBytes(MAX_ZIP_BYTES)}.`
        );
      }

      setStatus("Waiting for confirmation…");
      const confirmation = await confirmUpload({
        files: data.files.length,
        bytes: totalBytes,
      });
      if (!confirmation.confirmed) {
        setStatus("Upload cancelled.");
        return;
      }
      tab = confirmation.tab;

      setStatus("Uploading…");
      const url = await uploadProject(data.share, bytes, fetchFn, baseUrl);
      const target = shareTarget(data.web, url, baseUrl);
      setStatus("Opening Abella Web…");
      if (tab) {
        tab.location.href = target;
        setStatus("");
      } else {
        openFn(target);
      }
    } catch (error) {
      tab?.close();
      setStatus(
        error instanceof Error ? error.message : String(error),
        true
      );
    } finally {
      button.disabled = false;
    }
  });
}
