# See LICENSE for licensing details.

DUNE := dune

.PHONY: all
all: support/.stamp
	$(DUNE) build bin/abella.exe bin/abella_doc.exe bin/abella_dep.exe

.PHONY: all-release
all-release: # support/.stamp
	$(DUNE) build --release bin/abella.exe bin/abella_doc.exe \
	  bin/abella_dep.exe

.PHONY: web
web: support/ts/keywords.generated.ts
	rm -f web/abella_worker.js web/abella_js.js web/engine.json
	mkdir -p web/examples web/abella_js
	$(DUNE) exec bin/abella_bundle.exe -- \
	  -m support/web-examples.json -o web/examples/bundle.json
	$(DUNE) build --profile release src/js/abella_js.bc.wasm.js
	rm -rf web/abella_js/abella_js.bc.wasm.assets
	rm -f web/abella_js/abella_js.bc.wasm.js
	cp _build/default/src/js/abella_js.bc.wasm.js web/abella_js/
	cp -r _build/default/src/js/abella_js.bc.wasm.assets web/abella_js/
	( cd support && npm install --no-save && npm run web:build )

.PHONY: web-bundle
web-bundle:
	mkdir -p web/examples
	$(DUNE) exec bin/abella_bundle.exe -- \
	  -m support/web-examples.json -o web/examples/bundle.json

WEB_DEV_SESSION ?= abella-web-dev
WEB_DEV_PORT ?= 8000

.PHONY: web-dev-local
web-dev-local:
	WEB_DEV_SESSION=$(WEB_DEV_SESSION) WEB_DEV_PORT=$(WEB_DEV_PORT) \
	  support/scripts/web-dev-local.sh

# Only the dev build compiles the loopback OAuth Worker URL, and `make
# web` bakes in the production one, so the order matters.
.PHONY: web-dev
web-dev: web
	( cd support && npm run web:build:dev )

.PHONY: publish-web
publish-web:
	$(MAKE) --no-print-directory web
	( cd support && npm run web:check )
	rsync -aviz --delete \
	  --exclude '.test/' \
	  --exclude '*.map' \
	  web/ abellaweb@origin.abella-prover.org:abella-prover.org/web/

.PHONY: oauth-worker-check
oauth-worker-check:
	( cd support/oauth-worker && npm ci && npm run check && npm test )

.PHONY: oauth-worker-deploy
oauth-worker-deploy:
	( cd support/oauth-worker && npm ci && npm run deploy )

support/ts/keywords.generated.ts: src/lexer.mll bin/abella_keywords.ml
	$(DUNE) exec bin/abella_keywords.exe -- -o $@

support/.stamp: $(wildcard support/ts/*.ts) support/package.json \
                support/package-lock.json \
                support/ts/keywords.generated.ts
	( cd support && \
	  npm install --no-save && \
	  npm run build && \
	  touch .stamp )

.PHONY: clean
clean:
	$(DUNE) clean
	$(RM) abella

.PHONY: test
test:
	$(DUNE) runtest --release

.PHONY: publish-doc
publish-doc: examples/make.stamp
	rsync -aviz \
	  --exclude '*.thc' \
	  --exclude '*.out' \
	  --exclude '*.json' \
	  --exclude '*.stamp' \
	  --exclude '.gitignore' \
	  examples abellaweb@origin.abella-prover.org:abella-prover.org/

examples/make.stamp: $(wildcard examples/**/*.{sig,mod,thm})
examples/make.stamp: $(wildcard _build/default/bin/abella*.exe)
examples/make.stamp: $(wildcard $(patsubst %.thm,%.thc,$(wildcard examples/**/*.thm)))
examples/make.stamp:
	git clean -fxd examples
	$(DUNE) exec bin/abella_doc.exe -- -r examples
	touch examples/make.stamp
