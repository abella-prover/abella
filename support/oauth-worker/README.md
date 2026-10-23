# Abella Web OAuth Worker

Token-exchange Worker for the GitHub OAuth flow in Abella Web. It is a
separate npm package; `make web` does not install or build it.

## Local development

Use the loopback origin `http://127.0.0.1:8000`, not `localhost`. The
development OAuth App, the Worker environment, and the frontend build must
all agree on that exact origin.

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

Store the development client secret in `.dev.vars` in this directory:

```text
GITHUB_CLIENT_SECRET=...
```

`.dev.vars` is gitignored. Never commit it and never put the secret in
`wrangler.jsonc`, the frontend, or this README. The public client ID, the
allowed origin, and the redirect URI are plain configuration and can be
committed.

### Static server

Serve the generated `web/` tree as the document root:

```sh
cd web
python3 -m http.server 8000 --bind 127.0.0.1
```

Open `http://127.0.0.1:8000/`. The callback page is
`http://127.0.0.1:8000/github-callback.html`, and the development Worker
listens on `http://127.0.0.1:8787`.

The public development settings live under `env.dev.vars` in
`wrangler.jsonc`:

```text
GITHUB_CLIENT_ID=<development client id>
ALLOWED_ORIGIN=http://127.0.0.1:8000
REDIRECT_URI=http://127.0.0.1:8000/github-callback.html
```

Only `GITHUB_CLIENT_SECRET` belongs in `.dev.vars`.

If you serve the repository root instead of `web/`, the callback path
becomes `/web/github-callback.html`; update the OAuth App, the Worker
`REDIRECT_URI`, and the frontend build to match.

### Loopback checks

- Confirm GitHub's token endpoint is reachable from the development
  machine; a probe without valid credentials still receives a JSON
  response from GitHub rather than a network failure.
- `python3 -m http.server 8000 --bind 127.0.0.1` serves `web/` and
  `github-callback.html` with HTTP 200.
- Loopback is a secure context, so `crypto.subtle.digest("SHA-256", ...)`
  works without HTTPS.
