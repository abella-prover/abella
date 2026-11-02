// Copyright (C) 2026 Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

// Ephemeral zip handoff Worker backed by Workers KV.  The doc page
// uploads a zip and Abella Web downloads it from the returned URL.  A
// 600-second KV expiration is the real lifetime; the expiry embedded in
// the key is checked again on read.

export interface Env {
  ZIPS: KVNamespace;
}

export interface HandlerOptions {
  now?: () => number;
  newId?: () => string;
  ttlSeconds?: number;
  maxBytes?: number;
}

export const TTL_SECONDS = 600;
export const MAX_ZIP_BYTES = 8 * 1024 * 1024;

const ZIP_MAGIC = [0x50, 0x4b, 0x03, 0x04];
const ID_PATTERN = /^[0-9a-f]{32}$/;

const CORS_HEADERS: Record<string, string> = {
  "Access-Control-Allow-Origin": "*",
  "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
  "Access-Control-Allow-Headers": "Content-Type",
  "Access-Control-Max-Age": "86400",
  "X-Content-Type-Options": "nosniff",
};

function json(
  status: number,
  body: unknown,
  extra: Record<string, string> = {}
): Response {
  return new Response(JSON.stringify(body), {
    status,
    headers: {
      ...CORS_HEADERS,
      "Content-Type": "application/json; charset=utf-8",
      "Cache-Control": "no-store",
      ...extra,
    },
  });
}

function makeId(): string {
  const bytes = new Uint8Array(16);
  crypto.getRandomValues(bytes);
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, "0")).join(
    ""
  );
}

function isZip(bytes: Uint8Array): boolean {
  return ZIP_MAGIC.every((byte, index) => bytes[index] === byte);
}

function parseKey(
  pathname: string
): { expiresAt: number; id: string } | undefined {
  const parts = pathname.split("/");
  if (parts.length !== 4 || parts[0] !== "" || parts[1] !== "zips") {
    return undefined;
  }
  const rawExpires = parts[2];
  const id = parts[3];
  if (!/^\d+$/.test(rawExpires) || !ID_PATTERN.test(id)) return undefined;
  const expiresAt = Number(rawExpires);
  if (!Number.isSafeInteger(expiresAt)) return undefined;
  return { expiresAt, id };
}

async function readZip(
  request: Request,
  env: Env,
  options: HandlerOptions
): Promise<Response> {
  const maxBytes = options.maxBytes ?? MAX_ZIP_BYTES;
  const contentType = (request.headers.get("content-type") ?? "")
    .toLowerCase();
  if (!contentType.startsWith("application/zip")) {
    return json(415, {
      error: "unsupported_media_type",
      message: "Upload a zip archive.",
    });
  }

  const declared = Number(request.headers.get("content-length"));
  if (Number.isFinite(declared) && declared > maxBytes) {
    return json(413, {
      error: "too_large",
      message: `Archives are limited to ${maxBytes} bytes.`,
    });
  }

  let body: ArrayBuffer;
  try {
    body = await request.arrayBuffer();
  } catch {
    return json(400, {
      error: "invalid_body",
      message: "Could not read the archive.",
    });
  }

  if (body.byteLength === 0) {
    return json(400, {
      error: "invalid_body",
      message: "The archive is empty.",
    });
  }
  if (body.byteLength > maxBytes) {
    return json(413, {
      error: "too_large",
      message: `Archives are limited to ${maxBytes} bytes.`,
    });
  }
  if (!isZip(new Uint8Array(body))) {
    return json(415, {
      error: "invalid_zip",
      message: "The body is not a zip archive.",
    });
  }

  const newId = options.newId ?? makeId;
  const id = newId();
  if (!ID_PATTERN.test(id)) {
    return json(500, {
      error: "internal",
      message: "Could not allocate an id.",
    });
  }

  const ttlSeconds = options.ttlSeconds ?? TTL_SECONDS;
  const now = options.now ?? Date.now;
  const expiresAt = now() + ttlSeconds * 1000;
  const key = `zips/${expiresAt}/${id}`;

  try {
    await env.ZIPS.put(key, body, { expirationTtl: ttlSeconds });
  } catch (error) {
    console.error(`share-worker: KV put failed: ${String(error)}`);
    return json(
      503,
      {
        error: "busy",
        message:
          "The share service is temporarily unavailable. Try again later.",
      },
      { "Retry-After": "60" }
    );
  }

  return json(201, {
    url: `${new URL(request.url).origin}/zips/${expiresAt}/${id}`,
    expiresAt,
    retryAfterSeconds: 60,
  });
}

async function sendZip(
  request: Request,
  env: Env,
  options: HandlerOptions
): Promise<Response> {
  const key = parseKey(new URL(request.url).pathname);
  if (!key) {
    return json(404, {
      error: "not_found",
      message: "No such route.",
    });
  }

  const now = options.now ?? Date.now;
  if (now() > key.expiresAt) {
    return json(410, {
      error: "expired",
      message: "This project link has expired.",
    });
  }

  let value: ArrayBuffer | null;
  try {
    value = await env.ZIPS.get(`zips/${key.expiresAt}/${key.id}`, "arrayBuffer");
  } catch (error) {
    console.error(`share-worker: KV get failed: ${String(error)}`);
    return json(
      503,
      {
        error: "busy",
        message:
          "The share service is temporarily unavailable. Try again later.",
      },
      { "Retry-After": "60" }
    );
  }

  if (value === null) {
    return json(404, {
      error: "not_found",
      message: "This project link is not available yet.",
    });
  }

  return new Response(value, {
    status: 200,
    headers: {
      ...CORS_HEADERS,
      "Content-Type": "application/zip",
      "Content-Disposition": 'attachment; filename="abella-web.zip"',
      "Cache-Control": "no-store",
    },
  });
}

export async function handleRequest(
  request: Request,
  env: Env,
  options: HandlerOptions = {}
): Promise<Response> {
  if (request.method === "OPTIONS") {
    return new Response(null, { status: 204, headers: CORS_HEADERS });
  }

  const pathname = new URL(request.url).pathname;
  if (request.method === "POST" && pathname === "/zips") {
    return readZip(request, env, options);
  }
  if (request.method === "GET" && pathname === "/health") {
    return json(200, { ok: true });
  }
  if (request.method === "GET") {
    return sendZip(request, env, options);
  }

  return json(
    405,
    {
      error: "method_not_allowed",
      message: "Method not allowed.",
    },
    { Allow: "GET, POST, OPTIONS" }
  );
}
