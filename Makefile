# See COPYING for licensing details.

OCB = ocamlbuild -classic-display

.PHONY: all
all: src/abella.native src/copy_exe.native
	_build/src/copy_exe.native _build/src/abella.native abella

.PHONY: clean
clean:
	$(OCB) -clean
	$(RM) src/version.ml
	$(RM) abella abella.exe

.PHONY: byte
byte: src/abella.byte

.PHONY: gitclean
gitclean:
	git clean -xfd -e examples

.PHONY: top
top: all src/abella.cma
	ocaml

%.native:
	$(OCB) -no-links $@

%.byte:
	$(OCB) -no-links $@

%.cma:
	$(OCB) -no-links $@
