Abella Web
==========

Abella Web is the static browser interface in `web/`. Build it with:

```sh
make web                 # wasm backend (default)
make web ENGINE=js       # diagnostic/fallback js_of_ocaml backend
make publish-web         # build and rsync web/ to the site
```

`make web` needs Node 22+, Dune 3.20+, and, for the default wasm
backend, `wasm_of_ocaml-compiler` 6.4.x plus system Binaryen 119+.
The selected compiler is not needed for `make all` or the native tests.

The frontend reads the backend from `web/engine.json`. Test the
TypeScript and unit tests, and check the bundle budgets, with:

```sh
cd support
npm run check
npm run web:test
npm run web:size
```

The size check includes the small `github_callback.js` bundle.

Serve `web/` from a static server for local testing. For a wasm
deployment, serve `.wasm` files as `application/wasm` and include
`'wasm-unsafe-eval'` in the CSP `script-src`. The wasm browser floor is
Chrome/Edge 119+, Firefox 122+, and Safari 18.2+.

The GitHub backend calls `https://api.github.com` and
`https://raw.githubusercontent.com`; a deployed CSP must allow both
origins in `connect-src`.

`make publish-web` expects SSH access to the publishing account and
copies the whole generated `web/` tree, including lazy JavaScript
chunks. Generated assets are gitignored.

GitHub authentication
---------------------

Public GitHub repositories load without a token. A personal access
token (PAT) can be entered in the GitHub dialog for private access and
commits. A fine-grained PAT is the least-privilege option.

`Sign in with GitHub` uses an OAuth popup and a small Cloudflare Worker
to exchange the authorization code. The Worker holds the client secret;
the static site never sees it. The token is kept in `sessionStorage`
for the tab, never in `localStorage`, a URL, a log, or an error message.
The PAT path remains available when the Worker is missing or
misconfigured.

The Worker lives in `support/oauth-worker/`. Its README covers the
route contract, deployment, rate limiting, secret rotation, and
security properties. This section covers the site-side setup.

The OAuth Worker URL is compiled into the frontend:

- production default: `https://oauth.abella-prover.org`;
- local development: `http://127.0.0.1:8787`, selected by
  `npm run web:build:dev`.

`support/ts/web/github-oauth-config.ts` holds the production default.
The development build defines `__GITHUB_OAUTH_WORKER__`. Do not add a
query-parameter or `localStorage` override: a malicious Worker would
receive authorization codes.

Local OAuth development
-----------------------

Use the loopback origin `http://127.0.0.1:8000`, not `localhost`.
Register a separate development GitHub OAuth App with:

- homepage URL: `http://127.0.0.1:8000/`
- callback URL: `http://127.0.0.1:8000/github-callback.html`

Put its client secret in `support/oauth-worker/.dev.vars`; the public
client ID, allowed origin, and redirect URI are in the `dev` environment
of `support/oauth-worker/wrangler.jsonc`. Never commit `.dev.vars`.

Run the pieces in three terminals:

```sh
# Worker
cd support/oauth-worker && npm run dev

# static site from web/
cd web && python3 -m http.server 8000 --bind 127.0.0.1

# frontend built against the local Worker
cd support && npm run web:build:dev
```

Open `http://127.0.0.1:8000/`. The callback page is served from the
same tree; `web/github_callback.js` is generated and ignored by git.
The callback page carries `Referrer-Policy: no-referrer` through its
meta tag in local development.

Production OAuth deployment
---------------------------

1. Create the production GitHub OAuth App with homepage
   `https://abella-prover.org/web/` and callback
   `https://abella-prover.org/web/github-callback.html`.
2. Add its public client ID to `env.production.vars` in
   `support/oauth-worker/wrangler.jsonc`.
3. Set the secret:
   ```sh
   cd support/oauth-worker
   npx wrangler secret put GITHUB_CLIENT_SECRET --env production
   ```
4. Deploy the Worker:
   ```sh
   cd support/oauth-worker
   npm run deploy
   ```
5. Attach the Worker hostname, preferably
   `oauth.abella-prover.org`, and configure the Cloudflare rate-limit
   rule documented in the Worker README.
6. Build with the production default and publish the static site:
   ```sh
   make web
   make publish-web
   ```

`make publish-web` never deploys the Worker. Worker deployment is an
independent operation with its own environment and secret.

The Worker's `GET /github/config` is the feature flag: if it is missing,
returns 503, or is rejected by CORS, the site hides the OAuth action and
keeps the PAT path. This is also the rollback: disable the Worker route
or remove its client ID and the static site falls back without a
redeploy.

CSP, COOP, and callback headers
------------------------------

Allow the Worker origin and both GitHub origins in `connect-src`:

```text
connect-src 'self' https://api.github.com
  https://raw.githubusercontent.com https://oauth.abella-prover.org;
```

If the Worker uses its `workers.dev` fallback URL instead of the custom
domain, use that exact URL in both the CSP and the frontend build.

Do not set `Cross-Origin-Opener-Policy: same-origin` on `/web/` if the
OAuth popup is to work. `same-origin-allow-popups` is acceptable.
Verify the actual deployment headers on the real origin.

Serve `web/github-callback.html` with `Cache-Control: no-store`,
`Referrer-Policy: no-referrer`, `X-Frame-Options: DENY`, and
`frame-ancestors 'none'` where per-file headers are available. The
callback needs no extra `script-src` permission because it loads only a
same-origin script.

Security notes
--------------

- The OAuth client secret exists only as a Cloudflare Worker secret.
- PKCE S256 protects the authorization code; the verifier stays in the
  main tab.
- The Worker uses an exact origin allowlist, a fixed redirect URI, a
  4 KiB body limit, a 10-second upstream timeout, manual redirects, and
  safe fixed error messages.
- The frontend stores the token and its scope/account metadata only in
  `sessionStorage`. Disconnect clears both.
- The OAuth action requests `public_repo` by default. `repo` is an
  explicit opt-in and grants account-wide private repository access;
  use a fine-grained PAT for per-repository least privilege.
- The dialog provides a link to GitHub's authorized-app settings for
  reviewing or revoking access.
- Rotate the Worker secret as described in
  `support/oauth-worker/README.md` if it is ever exposed.
