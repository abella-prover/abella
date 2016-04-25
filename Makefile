# See COPYING for licensing details.

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

.PHONY: clean
clean:
	$(OCB) -clean
	$(RM) src/version.ml
	$(RM) abella abella.exe
	$(RM) tester tester.exe

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
	$(OCB) -no-links -Is src,test,test/ext -lib unix test/test.native
	if file _build/test/test.native | grep Windows >/dev/null 2>&1 ; then \
	  cp _build/test/test.native tester.exe ; \
	else \
	  cp -a _build/test/test.native tester ; \
	fi
