# See LICENSE for licensing details.

BINS := src/abella.bc src/abella_doc.bc src/abella_dep.bc

.PHONY: all all-release
all: src/abella_doc_dist.ml
	dune build $(BINS)

all-release:
	dune build --release $(BINS)

src/abella_doc_dist.ml: $(wildcard support/**/*.ts support/**/*.css)
	( cd support && \
	  npm install --no-save && \
	  npm run build )
	ocaml-crunch -m plain -o src/abella_doc_dist.ml support/dist

AIN := abella.install

.PHONY: $(AIN)
$(AIN):
	rm -f $(AIN)
	echo 'bin: [' >> $(AIN)
	echo '"_build/default/src/abella.bc" {"abella"}' >> $(AIN)
	echo '"_build/default/src/abella_doc.bc" {"abella_doc"}' >> $(AIN)
	echo '"_build/default/src/abella_dep.bc" {"abella_dep"}' >> $(AIN)
	echo ']' >> $(AIN)
	echo 'man: [' >> $(AIN)
	for pr in _build/default/src/*.bc ; do \
	  $$pr --help=groff > $${pr%%.bc}.1 ; \
	  echo '"'$${pr%%.bc}.1'"' >> $(AIN) ; \
	done
	echo ']' >> $(AIN)
	echo 'share: [' >> $(AIN)
	for f in emacs/* `find examples -type f | grep -E '(sig|mod|thm)$$'` ; do \
	    echo '"'$$f'"' '{"'$$f'"}' >> $(AIN) ; \
	done
	echo ']' >> $(AIN)

.PHONY: clean
clean:
	dune clean
	$(RM) abella $(BINS) abella.install

.PHONY: test
test:
	dune runtest --release

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
examples/make.stamp: $(wildcard _build/default/src/abella*.bc)
examples/make.stamp: $(wildcard $(patsubst %.thm,%.thc,$(wildcard examples/**/*.thm)))
examples/make.stamp:
	git clean -fxd examples
	dune exec src/abella_doc.bc -- -r examples
	touch examples/make.stamp
