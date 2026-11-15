# Abella Web deployment

Deploys the built `web/` tree as Cloudflare Workers Static Assets on
`web.abella-prover.org`. This is an assets-only Worker, independent of
the OAuth (`support/oauth-worker`) and ZIP (`support/share-worker`)
Workers.

Normally deployed through the repository root:

```sh
make publish-web
```

That rebuilds `web/`, verifies the stamped asset references, removes
`web/.test/` and `*.map` files, and runs `wrangler deploy` from this
directory. `make publish-web-dry-run` validates without uploading.

Response headers come from `support/web/_headers`, copied to
`web/_headers` by `make web`. The `[[routes]]` entry in
`wrangler.toml` attaches `web.abella-prover.org` as a Worker Custom
Domain; confirm that the route and DNS record appear after deployment.
