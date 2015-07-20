# See COPYING for licensing details.

OCB = ocamlbuild -classic-display

.PHONY: all
all:
	$(OCB) -no-links src/abella.native
	$(OCB) -no-links src/copy_exe.native
	cp -a _build/src/abella.native _build/src/abella.native.target
	_build/src/copy_exe.native _build/src/abella.native.target abella

.PHONY: abella.js
abella.js:
	$(OCB) -use-ocamlfind src/abella.byte
	js_of_ocaml +weak.js abella.byte

.PHONY: clean
clean:
	$(OCB) -clean
	$(RM) src/version.ml
	$(RM) abella abella.exe abella.js abella.byte abella.native

.PHONY: gitclean
gitclean:
	git clean -xfd -e examples

.PHONY: top
top: all
	$(OCB) src/abella.cma
	ocaml
