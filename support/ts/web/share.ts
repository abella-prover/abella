// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// `?zip=` loading for the ephemeral project handoff.  KV writes can take
// up to 60 seconds to propagate, so a 404 is retried with backoff while
// the UI shows that it is waiting.  410 and 503 are terminal.

import { importProjectBytes, type ImportedProject } from "./archive";
import { SHARE_WORKER_ORIGINS } from "./share-config";
import { WorkspaceError } from "./workspace";

export const ZIP_PARAM = "zip";
export const MAX_SHARE_BYTES = 16 * 1024 * 1024;
export const SHARE_RETRY_BUDGET_MS = 60_000;
export const SHARE_RETRY_DELAYS_MS = [1000, 2000, 4000, 8000, 15000, 30000];

export type Fetcher = (url: string, init?: RequestInit) => Promise<Response>;

export interface LoadShareOptions {
  fetcher?: Fetcher;
  origins?: readonly string[];
  retryDelays?: readonly number[];
  sleep?: (ms: number) => Promise<void>;
  onWaiting?: (attempt: number, waitMs: number) => void;
  now?: () => number;
}

export function zipParam(search: string): string | undefined {
  const value = new URLSearchParams(search).get(ZIP_PARAM)?.trim();
  return value ? value : undefined;
}

export function resolveShareUrl(
  raw: string,
  origins: readonly string[] = SHARE_WORKER_ORIGINS
): URL {
  let url: URL;
  try {
    url = new URL(raw);
  } catch {
    throw new WorkspaceError(
      "unsupported",
      "The shared project link is not a valid URL."
    );
  }
  if (url.protocol !== "http:" && url.protocol !== "https:") {
    throw new WorkspaceError(
      "unsupported",
      "Shared project links must use http or https."
    );
  }
  if (url.username || url.password) {
    throw new WorkspaceError(
      "permission-denied",
      "Shared project links must not include credentials."
    );
  }
  if (!origins.includes(url.origin)) {
    throw new WorkspaceError(
      "permission-denied",
      "This link is not from a trusted share service."
    );
  }
  return url;
}

function errorText(error: unknown): string {
  return error instanceof Error && error.message
    ? error.message
    : String(error);
}

function defaultSleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function fetchOnce(
  fetcher: Fetcher,
  url: URL
): Promise<Response> {
  try {
    return await fetcher(url.toString(), {
      cache: "no-store",
      redirect: "error",
    });
  } catch (error) {
    throw new WorkspaceError(
      "unavailable",
      `Could not load the shared project: ${errorText(error)}`
    );
  }
}

function tooLarge(): WorkspaceError {
  return new WorkspaceError(
    "unsupported",
    `The shared project archive is larger than ${MAX_SHARE_BYTES} bytes.`
  );
}

export async function loadSharedProject(
  rawUrl: string,
  options: LoadShareOptions = {}
): Promise<ImportedProject> {
  const url = resolveShareUrl(rawUrl, options.origins);
  const fetcher = options.fetcher ?? fetch;
  const delays = options.retryDelays ?? SHARE_RETRY_DELAYS_MS;
  const sleep = options.sleep ?? defaultSleep;
  const now = options.now ?? Date.now;
  const deadline = now() + SHARE_RETRY_BUDGET_MS;

  for (let attempt = 0; ; attempt += 1) {
    const response = await fetchOnce(fetcher, url);

    if (response.status === 404) {
      const delay = delays[attempt];
      if (delay === undefined) {
        throw new WorkspaceError(
          "not-found",
          "The shared project is not available. The link may have expired."
        );
      }
      const remaining = deadline - now();
      if (remaining <= 0) {
        throw new WorkspaceError(
          "not-found",
          "The shared project did not become available in time. " +
            "Try the Edit this button again."
        );
      }
      const wait = Math.min(delay, remaining);
      options.onWaiting?.(attempt + 1, wait);
      await sleep(wait);
      continue;
    }

    if (response.status === 410) {
      throw new WorkspaceError(
        "not-found",
        "This shared project link has expired. " +
          "Click Edit this on the documentation page again."
      );
    }
    if (response.status === 503) {
      throw new WorkspaceError(
        "unavailable",
        "The share service is busy. Try again later."
      );
    }
    if (!response.ok) {
      throw new WorkspaceError(
        "unavailable",
        `Could not load the shared project (HTTP ${response.status}).`,
        response.status
      );
    }

    const length = Number(response.headers.get("content-length"));
    if (Number.isFinite(length) && length > MAX_SHARE_BYTES) {
      throw tooLarge();
    }
    let bytes: Uint8Array;
    try {
      bytes = new Uint8Array(await response.arrayBuffer());
    } catch {
      throw new WorkspaceError(
        "io",
        "Could not read the shared project archive."
      );
    }
    if (bytes.byteLength > MAX_SHARE_BYTES) {
      throw tooLarge();
    }
    return importProjectBytes(bytes);
  }
}
