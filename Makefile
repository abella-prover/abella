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
	  examples abellaweb@abella-prover.org:abella-prover.org/

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
