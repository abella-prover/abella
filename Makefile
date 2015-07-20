# See COPYING for licensing details.

OCB = ocamlbuild -classic-display -use-ocamlfind

.PHONY: all
all:
	$(OCB) -no-links src/abella.native
	$(OCB) -no-links src/copy_exe.native
	cp -a _build/src/abella.native _build/src/abella.native.target
	_build/src/copy_exe.native _build/src/abella.native.target abella

.PHONY: abella_js.js
abella_js.js:
	$(OCB) -use-ocamlfind src/js/abella_js.byte
	js_of_ocaml +weak.js abella_js.byte
	mv abella_js.js try/

.PHONY: clean
clean:
	$(OCB) -clean
	$(RM) src/version.ml
	$(RM) abella abella.exe abella.native abella_js.js abella_js.byte

.PHONY: gitclean
gitclean:
	git clean -xfd -e examples

.PHONY: top
top: all
	$(OCB) src/abella.cma
	ocaml
