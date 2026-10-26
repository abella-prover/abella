# See LICENSE for licensing details.

DUNE := dune

# run with `make BYTECODE=true` to produce bytecode
EXTN := $(if $(strip $(BYTECODE)),bc,exe)
BINS := $(patsubst %,%.$(EXTN),src/abella src/abella_doc src/abella_dep)

.PHONY: all
all: support/.stamp
	$(DUNE) build $(BINS)

.PHONY: all-release
all-release: # support/.stamp
	$(DUNE) build --release $(BINS)

ENGINE ?= wasm

# Cloudflare proxies the public apex; SSH publishing must use a DNS-only
# origin record.  Override with WEB_ORIGIN=173.236.255.153 if needed.
WEB_ORIGIN ?= origin.abella-prover.org

.PHONY: web
web:
	mkdir -p web/examples web/abella_js
	$(DUNE) exec src/abella_bundle.exe -- \
	  -m support/web-examples.json -o web/examples/bundle.json
	( cd support && npm install --no-save && npm run web:build )
ifeq ($(ENGINE),js)
	$(DUNE) build --profile release src/js/abella_js.bc.js
	rm -f web/abella_js.js
	cp _build/default/src/js/abella_js.bc.js web/abella_js.js
	rm -rf web/abella_js
	echo '{"engine":"js"}' > web/engine.json
else
	$(DUNE) build --profile release src/js/abella_js.bc.wasm.js
	rm -f web/abella_js.js
	rm -rf web/abella_js/abella_js.bc.wasm.assets
	rm -f web/abella_js/abella_js.bc.wasm.js
	cp _build/default/src/js/abella_js.bc.wasm.js web/abella_js/
	cp -r _build/default/src/js/abella_js.bc.wasm.assets web/abella_js/
	echo '{"engine":"wasm"}' > web/engine.json
endif

.PHONY: web-bundle
web-bundle:
	mkdir -p web/examples
	$(DUNE) exec src/abella_bundle.exe -- \
	  -m support/web-examples.json -o web/examples/bundle.json

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
	rsync -aviz -e "ssh -o HostName=$(WEB_ORIGIN)" \
	  --exclude '.test/' \
	  --exclude '*.map' \
	  web/ abellaweb@abella-prover.org:abella-prover.org/web/

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
