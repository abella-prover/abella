# See LICENSE for licensing details.

BINS := src/abella.exe src/abella_doc.exe src/abella_dep.exe

.PHONY: all all-release
all:
	dune build $(BINS)

all-release:
	dune build --release $(BINS)

AIN := abella.install

.PHONY: $(AIN)
$(AIN):
	rm -f $(AIN)
	echo 'bin: [' >> $(AIN)
	echo '"_build/default/src/abella.exe" {"abella"}' >> $(AIN)
	echo '"_build/default/src/abella_doc.exe" {"abella_doc"}' >> $(AIN)
	echo '"_build/default/src/abella_dep.exe" {"abella_dep"}' >> $(AIN)
	echo ']' >> $(AIN)
	echo 'man: [' >> $(AIN)
	for pr in _build/default/src/*.exe ; do \
	  $$pr --help=groff > $${pr%%.exe}.1 ; \
	  echo '"'$${pr%%.exe}.1'"' >> $(AIN) ; \
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
examples/make.stamp: $(wildcard _build/default/src/abella*.exe)
examples/make.stamp: $(wildcard $(patsubst %.thm,%.thc,$(wildcard examples/**/*.thm)))
examples/make.stamp:
	git clean -fxd examples
	dune exec src/abella_doc.exe -- -r examples
	touch examples/make.stamp
