# See COPYING for licensing details.

OCB = ocamlbuild -classic-display

.PHONY: all
all:
	$(OCB) -no-links src/abella.native
	$(OCB) -no-links src/copy_exe.native
	_build/src/copy_exe.native _build/src/abella.native abella

.PHONY: clean
clean:
	$(OCB) -clean
	$(RM) src/version.ml
	$(RM) abella abella.exe

.PHONY: gitclean
gitclean:
	git clean -xfd -e examples

.PHONY: top
top: all
	$(OCB) src/abella.cma
	ocaml
