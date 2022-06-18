# See LICENSE for licensing details.

BINS := src/abella.exe src/abella_doc.exe

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
