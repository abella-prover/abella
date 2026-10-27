# See LICENSE for licensing details.

DUNE := dune

ifneq ($(strip $(ENGINE)),)
$(error ENGINE is no longer supported; Abella Web builds wasm only)
endif

# run with `make BYTECODE=true` to produce bytecode
EXTN := $(if $(strip $(BYTECODE)),bc,exe)
BINS := $(patsubst %,%.$(EXTN),src/abella src/abella_doc src/abella_dep)

.PHONY: all
all: support/.stamp
	$(DUNE) build $(BINS)

.PHONY: all-release
all-release: # support/.stamp
	$(DUNE) build --release $(BINS)

.PHONY: web
web:
	rm -f web/abella_worker.js web/abella_js.js web/engine.json
	mkdir -p web/examples web/abella_js
	$(DUNE) exec src/abella_bundle.exe -- \
	  -m support/web-examples.json -o web/examples/bundle.json
	( cd support && npm install --no-save && npm run web:build )
	$(DUNE) build --profile release src/js/abella_js.bc.wasm.js
	rm -rf web/abella_js/abella_js.bc.wasm.assets
	rm -f web/abella_js/abella_js.bc.wasm.js
	cp _build/default/src/js/abella_js.bc.wasm.js web/abella_js/
	cp -r _build/default/src/js/abella_js.bc.wasm.assets web/abella_js/

.PHONY: web-bundle
web-bundle:
	mkdir -p web/examples
	$(DUNE) exec src/abella_bundle.exe -- \
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

WEB_VERSION_FILE := support/ts/web/version.ts
WEB_ASSET_INPUTS := $(wildcard support/ts/web/*.ts) \
                    $(wildcard support/css/*.css) \
                    src/js/abella_js.ml

.PHONY: web-version-bump
web-version-bump:
	node support/scripts/web-version.mjs --bump

.PHONY: web-version-check
web-version-check:
	@node support/scripts/web-version.mjs --check || exit 1
	@last=$$(git log -1 --format=%H -- $(WEB_VERSION_FILE)); \
	if [ -n "$$last" ] && git diff --quiet $$last -- $(WEB_VERSION_FILE); then \
	  changed=$$(git diff --name-only $$last -- $(WEB_ASSET_INPUTS) || true); \
	  if [ -n "$$changed" ]; then \
	    echo "Web assets changed since the last version bump:"; \
	    echo "$$changed" | sed 's/^/  /'; \
	    echo "Run 'make web-version-bump'."; \
	    exit 1; \
	  fi; \
	fi

# The check must run before the build, which bakes the version into the
# JavaScript, so the two steps are sequenced by hand.
.PHONY: publish-web
publish-web:
	$(MAKE) --no-print-directory web-version-check
	$(MAKE) --no-print-directory web
	rsync -aviz \
	  --exclude '.test/' \
	  --exclude '*.map' \
	  web/ abellaweb@origin.abella-prover.org:abella-prover.org/web/

.PHONY: oauth-worker-check
oauth-worker-check:
	( cd support/oauth-worker && npm ci && npm run check && npm test )

.PHONY: oauth-worker-deploy
oauth-worker-deploy:
	( cd support/oauth-worker && npm ci && npm run deploy )

support/.stamp: $(wildcard support/ts/*.ts) support/package.json \
                support/package-lock.json
	( cd support && \
	  npm install --no-save && \
	  npm run build && \
	  touch .stamp )

.PHONY: clean
clean:
	$(DUNE) clean
	$(RM) abella $(BINS)

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
examples/make.stamp: $(wildcard _build/default/src/abella*.$(EXTN))
examples/make.stamp: $(wildcard $(patsubst %.thm,%.thc,$(wildcard examples/**/*.thm)))
examples/make.stamp:
	git clean -fxd examples
	$(DUNE) exec src/abella_doc.$(EXTN) -- -r examples
	touch examples/make.stamp

.PHONY: makefile_debug
makefile_debug:
	@echo "BYTECODE='$(BYTECODE)'"
	@echo "EXTN='$(EXTN)'"
	@echo "BINS='$(BINS)'"
