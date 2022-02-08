# See LICENSE for licensing details.

.PHONY: all all-release
all:
	dune build src/abella.exe

all-release:
	dune build --release src/abella.exe

AIN := abella.install

.PHONY: $(AIN)
$(AIN):
	echo 'bin: ["_build/default/src/abella.exe" {"abella"}]' > $(AIN)
	echo 'share: [' >> $(AIN)
	for f in emacs/* `find examples -type f | grep -E '(sig|mod|thm)$$'` ; do \
	    echo '"'$$f'"' '{"'$$f'"}' >> $(AIN) ; \
	done
	echo ']' >> $(AIN)


.PHONY: clean
clean:
	dune clean
	$(RM) abella abella.exe abella.install

# .PHONY: test
# test: all
# 	$(OCB) -no-links test/test.native
# 	_build/test/test.native
