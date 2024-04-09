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

support/.stamp: $(wildcard support/ts/*.ts support/css/*.css)
	( cd support && \
	  npm install --no-save && \
	  npm run build && \
	  touch .stamp )

AIN := abella.install

.PHONY: $(AIN)
$(AIN):
	$(RM) $(AIN)
	echo 'bin: [' >> $(AIN)
	echo '"_build/default/src/abella.$(EXTN)" {"abella"}' >> $(AIN)
	echo '"_build/default/src/abella_doc.$(EXTN)" {"abella_doc"}' >> $(AIN)
	echo '"_build/default/src/abella_dep.$(EXTN)" {"abella_dep"}' >> $(AIN)
	echo ']' >> $(AIN)
	echo 'man: [' >> $(AIN)
	for pr in _build/default/src/*.$(EXTN) ; do \
	  $$pr --help=groff > $${pr%%.$(EXTN)}.1 ; \
	  echo '"'$${pr%%.$(EXTN)}.1'"' >> $(AIN) ; \
	done
	echo ']' >> $(AIN)
	echo 'share: [' >> $(AIN)
	for f in emacs/* `find examples -type f | grep -E '(sig|mod|thm)$$'` ; do \
	    echo '"'$$f'"' '{"'$$f'"}' >> $(AIN) ; \
	done
	echo ']' >> $(AIN)

.PHONY: clean
clean:
	$(DUNE) clean
	$(RM) abella $(BINS) $(AIN)

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
