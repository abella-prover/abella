# Abella Web OAuth Worker

Token-exchange Worker for the GitHub OAuth flow in Abella Web. It is a
separate npm package; `make web` does not install or build it.

The Worker is deliberately small: two routes, no storage, no sessions,
and no token persistence. It is the only component that knows the OAuth
client secret.

## Routes

Every route requires an exact `Origin` match against `ALLOWED_ORIGIN`.
Responses carry `Cache-Control: no-store` and
`X-Content-Type-Options: nosniff`. CORS is never a wildcard and never
allows credentials.

### `GET /github/config`

Returns the public configuration needed to start a flow:

```http
GET /github/config
Origin: https://abella-prover.org
```

```json
{
  "clientId": "Iv1.0123456789abcdef",
  "redirectUri": "https://abella-prover.org/web/github-callback.html"
}
```

The response never contains the client secret. If any required variable
is missing, the route returns `503` and the frontend keeps the OAuth
button hidden.

### `POST /github/token`

Exchanges an authorization code with PKCE:

```http
POST /github/token
Origin: https://abella-prover.org
Content-Type: application/json

{"code":"...","codeVerifier":"..."}
```

Success returns only `token` and `scope`:

```json
{"token":"gho_...","scope":"public_repo"}
```

Errors use the same shape:

```json
{"error":"invalid_code","message":"GitHub rejected the code."}
```

Status mapping:

- `400`: invalid request, malformed JSON, missing fields, or a code that
  GitHub rejects;
- `403`: missing or mismatched origin;
- `405`: method not allowed;
- `413`: body larger than 4 KiB;
- `502`: GitHub failure, redirect, or network failure;
- `503`: Worker misconfigured;
- `504`: upstream timeout.

The Worker derives `redirect_uri` from `REDIRECT_URI`; it ignores any
client-supplied redirect URI. It sends `client_id`, `client_secret`,
`code`, `redirect_uri`, and `code_verifier` to GitHub's token endpoint,
uses a 10-second timeout, and does not follow redirects. GitHub's HTTP
200 error responses map to safe messages; `refresh_token`, `token_type`,
and any other fields are dropped.

## Local development

Use the loopback origin `http://127.0.0.1:8000`, not `localhost`. The
development OAuth App, the Worker environment, and the frontend build
must all agree on that exact origin.

### Development OAuth App

Register a separate GitHub OAuth App for local work. Do not use the
production app or the production client secret on a development machine.

- Application name: `Abella Web (dev)`
- Homepage URL: `http://127.0.0.1:8000/`
- Authorization callback URL:
  `http://127.0.0.1:8000/github-callback.html`
- Leave "Expire access tokens" disabled.

The callback URL must match exactly and must not rely on wildcard
matching.

### Local secret

Install dependencies, then copy the example secret file:

```sh
npm install
cp .dev.vars.example .dev.vars
```

Put the development client secret in `.dev.vars`:

```text
GITHUB_CLIENT_SECRET=...
```

`.dev.vars` is gitignored. Wrangler loads it with
`wrangler dev --env dev`. Never commit it and never put the secret in
`wrangler.jsonc`, the frontend, or this README.

The public development settings live under `env.dev.vars` in
`wrangler.jsonc`:

```text
GITHUB_CLIENT_ID=<development client id>
ALLOWED_ORIGIN=http://127.0.0.1:8000
REDIRECT_URI=http://127.0.0.1:8000/github-callback.html
```

### Run it

```sh
npm run dev
```

The Worker listens on `http://127.0.0.1:8787`. Serve the generated
`web/` tree from the repository root:

```sh
cd web
python3 -m http.server 8000 --bind 127.0.0.1
```

Then open `http://127.0.0.1:8000/`. The callback page is
`http://127.0.0.1:8000/github-callback.html`.

Check the routes without a browser:

```sh
curl -i -H 'Origin: http://127.0.0.1:8000' \
  http://127.0.0.1:8787/github/config
```

A probe exchange with a fake code should return `400 invalid_code`, not
a network error, if GitHub is reachable and the client credentials are
correct:

```sh
curl -i -X POST \
  -H 'Origin: http://127.0.0.1:8000' \
  -H 'Content-Type: application/json' \
  -d '{"code":"probe","codeVerifier":"probe"}' \
  http://127.0.0.1:8787/github/token
```

If you serve the repository root instead of `web/`, the callback path
becomes `/web/github-callback.html`; update the OAuth App, the Worker
`REDIRECT_URI`, and the frontend build to match.

## Configuration

`wrangler.jsonc` defines a `dev` and a `production` environment.

| Variable | Kind | Notes |
| --- | --- | --- |
| `GITHUB_CLIENT_ID` | plain var | Public OAuth App client ID |
| `GITHUB_CLIENT_SECRET` | secret | Set with `wrangler secret put` |
| `ALLOWED_ORIGIN` | plain var | Exact site origin |
| `REDIRECT_URI` | plain var | Exact registered callback URL |

The production environment currently omits `GITHUB_CLIENT_ID` until the
production OAuth App exists. Until it is set, `GET /github/config`
returns `503` and the frontend falls back to personal access tokens.

## Deployment

1. Create the production OAuth App with homepage
   `https://abella-prover.org/web/` and callback
   `https://abella-prover.org/web/github-callback.html`.
2. Record its client ID in `env.production.vars` in `wrangler.jsonc`.
3. Set the client secret:
   ```sh
   npx wrangler secret put GITHUB_CLIENT_SECRET --env production
   ```
4. Run the checks and deploy:
   ```sh
   npm run check
   npm test
   npm run deploy
   ```
5. Attach the chosen hostname, preferably `oauth.abella-prover.org`,
   with a Cloudflare custom domain or DNS record.
6. Add that exact origin to the site's `connect-src` CSP and build the
   frontend against it.

`make publish-web` never deploys this Worker. Deployment is an
independent operation with its own environment and secret.

## Rate limiting

Configure a Cloudflare rate-limit rule in the dashboard:

- route: `POST /github/token`;
- limit: 30 requests per minute per IP;
- action: block for 60 seconds.

The Worker does not keep a distributed counter. PKCE makes stolen codes
hard to use; the rate limit is for abuse and cost control.

## Secret rotation

1. Generate a new client secret in the GitHub OAuth App.
2. Run `wrangler secret put GITHUB_CLIENT_SECRET --env production`.
3. Verify a new sign-in works.
4. Invalidate the old secret in GitHub if the UI offers that step.
5. If the secret was exposed, review Worker analytics for unusual
   traffic and ask affected users to revoke the app in GitHub settings.

The Worker does not log request bodies, codes, verifiers, tokens, or
`Authorization` headers.

## Security properties

- The client secret exists only as a Cloudflare secret.
- PKCE S256 is required end to end; the verifier stays in the main tab.
- The redirect URI is fixed by the Worker configuration.
- CORS allows only the exact site origin, with `Vary: Origin`.
- Request bodies are capped at 4 KiB; codes and verifiers have length
  limits.
- Upstream exchanges use a 10-second timeout and manual redirects.
- GitHub error responses are mapped to fixed, safe messages.
- The Worker stores nothing and returns only `token` and `scope`.

## Rollback

Remove `GITHUB_CLIENT_ID` from the deployed configuration, or disable the
route, and `GET /github/config` returns `503`. The frontend then hides
the OAuth button and leaves the PAT path available without a static-site
redeploy.

## Testing

From this directory:

```sh
npm run check
npm test
```

From the repository root:

```sh
make oauth-worker-check
```

The tests mock `fetch`; they never contact GitHub and never use real
OAuth secrets.
