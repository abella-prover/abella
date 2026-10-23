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

Serve `web/` from a static server for local testing. For a wasm
deployment, serve `.wasm` files as `application/wasm` and include
`'wasm-unsafe-eval'` in the CSP `script-src`. The wasm browser floor is
Chrome/Edge 119+, Firefox 122+, and Safari 18.2+.

`make publish-web` expects SSH access to the publishing account and
copies the whole generated `web/` tree, including lazy JavaScript
chunks. Generated assets are gitignored.
