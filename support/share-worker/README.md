# Abella Web ZIP Worker

Ephemeral zip handoff Worker for the **Edit this** button on
`abella_doc` pages. It is backed only by Workers KV: no R2, no Durable
Object, no payment method. The Workers Free plan's hard KV cutoffs are
the cost guarantee.

The doc page builds the zip in the browser, uploads it here, and opens
`https://abella-prover.org/web/?zip=<url>`. Abella Web downloads and
imports it.

## Routes

All routes send `Access-Control-Allow-Origin: *`, no credentials, and
`X-Content-Type-Options: nosniff`. JSON and zip responses are
`Cache-Control: no-store`.

### `POST /zips`

```http
POST /zips
Content-Type: application/zip

<zip bytes>
```

- maximum 8 MiB;
- the body must start with the zip local-file-header magic
  `PK\x03\x04`;
- the key is `zips/<expiresAt>/<id>` with a random 128-bit `id`;
- `expirationTtl` is 600 seconds, the minimum the plan uses.

```json
{
  "url": "https://zips.abella-prover.org/zips/1767225600000/<id>",
  "expiresAt": 1767225600000,
  "retryAfterSeconds": 60
}
```

Errors: `400` empty/unreadable, `413` too large, `415` wrong type or
not a zip, `503` KV write limit (with `Retry-After: 60`).

### `GET /zips/<expiresAt>/<id>`

- `410` when the expiry in the key has passed;
- `404` when KV has not propagated the write yet or the value is gone;
- `200` with the zip, `Content-Disposition: attachment`, and
  `Cache-Control: no-store`;
- `503` when the KV read limit is hit.

`404` is deliberately ambiguous: KV writes can take up to 60 seconds to
propagate, and Abella Web retries `404` with backoff.

### `OPTIONS`

Returns `204` with the CORS preflight headers. `GET /health` returns
`{ "ok": true }`.

## Configuration

`wrangler.jsonc` binds the `ZIPS` namespace:

| Environment | Worker name | KV namespace |
| --- | --- | --- |
| default (dev) | `abella-web-zips-dev` | `abella-web-zips-dev` |
| production | `abella-web-zips` | `production-ZIPS` |

Local `wrangler dev` uses Wrangler's local KV simulation, so the dev
namespace is only used if a dev Worker is deployed.

```sh
npm ci
npm run dev        # http://127.0.0.1:8788
npm run check
npm test
npm run deploy     # wrangler deploy --env production
```

The production route is `zips.abella-prover.org`. The site CSP must
include it in `connect-src`; doc pages with their own CSP need the same
entry.

## Cost safety

- KV free tier: 1,000 writes/day, 100,000 reads/day, 1 GB storage.
- Exceeding a limit returns an error, not a bill.
- The 600-second TTL means steady-state storage is tiny; the write
  limit is the real ceiling.
- The per-IP Cloudflare rate-limit rule keeps one client from
  exhausting the day's writes.
- Do not enable R2 or attach a payment method.

## Privacy

The Worker does not log request bodies or file names. The download URL
is an unguessable capability valid until its expiry. The doc page asks
for confirmation before uploading sources.
