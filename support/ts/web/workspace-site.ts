// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Read-only workspace backed by a static project manifest and its source
// files.  The manifest is the version 2 document that abella_doc writes
// next to each theorem page; every listed path is resolved relative to
// the manifest URL.

import {
  classify,
  explicitEntry,
  normalizeNewlines,
  parseProjectManifest,
  type Project,
  type ProjectTextFile,
} from "./project";
import {
  MAX_FILE_BYTES,
  MAX_FILES,
  MAX_MANIFEST_BYTES,
  isCandidateFile,
} from "./workspace-directory";
import {
  WorkspaceError,
  readOnlyWorkspace,
  type Workspace,
} from "./workspace";

export const PROJECT_PARAM = "project";
export const SITE_FETCH_CONCURRENCY = 6;

/**
 * Extra origins, as hostnames, that may serve project manifests in
 * addition to the page's own origin.  Empty by default: the doc-site
 * feature is entirely same-origin.
 */
export const SITE_PROJECT_ALLOWLIST: readonly string[] = [];

export type Fetcher = (url: string, init?: RequestInit) => Promise<Response>;

export interface SiteProject {
  project: Project;
  workspace: Workspace;
  manifestUrl: URL;
}

export interface LoadSiteOptions {
  page?: URL;
  allowlist?: readonly string[];
  fetcher?: Fetcher;
  concurrency?: number;
}

export function projectParam(search: string): string | undefined {
  const value = new URLSearchParams(search).get(PROJECT_PARAM)?.trim();
  return value ? value : undefined;
}

export function isAllowedProjectUrl(
  url: URL,
  page: URL,
  allowlist: readonly string[] = SITE_PROJECT_ALLOWLIST
): boolean {
  if (url.origin === page.origin) return true;
  return (
    url.protocol === "https:" &&
    allowlist.some((host) => host.toLowerCase() === url.hostname.toLowerCase())
  );
}

export function resolveProjectUrl(
  raw: string,
  page: URL,
  allowlist: readonly string[] = SITE_PROJECT_ALLOWLIST
): URL {
  let url: URL;
  try {
    url = new URL(raw, page);
  } catch {
    throw new WorkspaceError(
      "unsupported",
      "The project address is not a valid URL."
    );
  }
  if (url.protocol !== "http:" && url.protocol !== "https:") {
    throw new WorkspaceError(
      "unsupported",
      "Project links must use http or https."
    );
  }
  if (url.username || url.password) {
    throw new WorkspaceError(
      "permission-denied",
      "Project links must not include credentials."
    );
  }
  if (!isAllowedProjectUrl(url, page, allowlist)) {
    throw new WorkspaceError(
      "permission-denied",
      "Abella Web only opens projects from this site."
    );
  }
  return url;
}

function errorText(error: unknown): string {
  return error instanceof Error && error.message
    ? error.message
    : String(error);
}

function stripBom(text: string): string {
  return text.charCodeAt(0) === 0xfeff ? text.slice(1) : text;
}

async function fetchText(
  fetcher: Fetcher,
  url: URL,
  limit: number,
  label: string
): Promise<string> {
  let response: Response;
  try {
    response = await fetcher(url.toString(), { cache: "no-cache" });
  } catch (error) {
    throw new WorkspaceError(
      "unavailable",
      `Could not load ${label}: ${errorText(error)}`
    );
  }
  if (!response.ok) {
    const code = response.status === 404 ? "not-found" : "unavailable";
    throw new WorkspaceError(
      code,
      `Could not load ${label} (HTTP ${response.status}).`,
      response.status
    );
  }
  const length = Number(response.headers.get("content-length"));
  if (Number.isFinite(length) && length > limit) {
    throw new WorkspaceError("unsupported", `${label} is too large.`);
  }
  let text: string;
  try {
    text = await response.text();
  } catch {
    throw new WorkspaceError("io", `Could not read ${label}.`);
  }
  if (text.length > limit) {
    throw new WorkspaceError("unsupported", `${label} is too large.`);
  }
  return stripBom(text);
}

function siteName(manifestUrl: URL, entry: string | undefined): string {
  if (entry) return entry;
  const name = manifestUrl.pathname.split("/").pop() ?? "";
  return name.replace(/\.project\.json$/i, "") || "Site project";
}

async function fetchProjectFiles(
  manifest: { files: string[] },
  manifestUrl: URL,
  page: URL,
  allowlist: readonly string[],
  fetcher: Fetcher,
  concurrency: number
): Promise<Map<string, ProjectTextFile>> {
  const paths = [...new Set(manifest.files)]
    .filter(isCandidateFile)
    .sort((left, right) => left.localeCompare(right));
  if (paths.length > MAX_FILES) {
    throw new WorkspaceError(
      "unsupported",
      `The project lists more than ${MAX_FILES} files.`
    );
  }

  const files = new Map<string, ProjectTextFile>();
  let cursor = 0;
  let fatal: unknown;
  const worker = async (): Promise<void> => {
    while (fatal === undefined && cursor < paths.length) {
      const path = paths[cursor++];
      const url = new URL(path, manifestUrl);
      if (!isAllowedProjectUrl(url, page, allowlist)) {
        fatal = new WorkspaceError(
          "permission-denied",
          `The project manifest lists a file outside this site: ${path}.`
        );
        return;
      }
      try {
        const text = await fetchText(fetcher, url, MAX_FILE_BYTES, path);
        files.set(path, {
          text: normalizeNewlines(text),
          kind: classify(path),
        });
      } catch (error) {
        fatal = error;
      }
    }
  };
  const workers = Math.max(
    1,
    Math.min(concurrency, Math.max(1, paths.length))
  );
  await Promise.all(Array.from({ length: workers }, worker));
  if (fatal !== undefined) {
    throw fatal instanceof WorkspaceError
      ? fatal
      : new WorkspaceError("io", errorText(fatal));
  }
  return files;
}

export async function loadSiteProject(
  rawUrl: string,
  options: LoadSiteOptions = {}
): Promise<SiteProject> {
  const page = options.page ?? new URL(globalThis.location.href);
  const allowlist = options.allowlist ?? SITE_PROJECT_ALLOWLIST;
  const fetcher = options.fetcher ?? fetch;
  const concurrency = options.concurrency ?? SITE_FETCH_CONCURRENCY;
  const manifestUrl = resolveProjectUrl(rawUrl, page, allowlist);
  const text = await fetchText(
    fetcher,
    manifestUrl,
    MAX_MANIFEST_BYTES,
    "the project manifest"
  );
  let manifest;
  try {
    manifest = parseProjectManifest(text);
  } catch (error) {
    throw new WorkspaceError("unsupported", errorText(error));
  }
  const files = await fetchProjectFiles(
    manifest,
    manifestUrl,
    page,
    allowlist,
    fetcher,
    concurrency
  );
  const entry = explicitEntry(files, manifest.entry);
  const project: Project = { files, entry, active: entry };
  return {
    project,
    workspace: readOnlyWorkspace(
      "site",
      siteName(manifestUrl, entry),
      project
    ),
    manifestUrl,
  };
}
