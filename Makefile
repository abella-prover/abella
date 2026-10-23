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

.PHONY: publish-web
publish-web: web
	rsync -aviz \
	  --exclude '.test/' \
	  --exclude '*.map' \
	  web/ abellaweb@abella-prover.org:abella-prover.org/web/

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
