# See LICENSE for licensing details.

OCB = ocamlbuild -classic-display

.PHONY: all
all:
	$(OCB) -no-links src/abella.native
	if file _build/src/abella.native | grep Windows >/dev/null 2>&1 ; then \
	  cp _build/src/abella.native abella.exe ; \
	else \
	  cp -a _build/src/abella.native abella ; \
	fi

.PHONY: all-windows
all-windows:
	OCAMLFIND_TOOLCHAIN=windows $(MAKE) all

AIN := abella.install

.PHONY: $(AIN)
$(AIN):
	echo 'bin: ["_build/src/abella.native" {"abella"}]' > $(AIN)
	echo 'share: [' >> $(AIN)
	for f in emacs/* `find examples -type f | grep -E '(sig|mod|thm)$$'` ; do \
	    echo '"'$$f'"' '{"'$$f'"}' >> $(AIN) ; \
	done
	echo ']' >> $(AIN)

.PHONY: clean
clean:
	$(OCB) -clean
	$(RM) src/version.ml
	$(RM) abella abella.exe

.PHONY: byte
byte:
	$(OCB) src/abella.byte

.PHONY: gitclean
gitclean:
	git clean -xfd -e examples

.PHONY: top
top: all
	$(OCB) src/abella.cma
	ocaml

.PHONY: test
test: all
	$(OCB) -no-links test/test.native
	_build/test/test.native
