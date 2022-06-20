examples.tar.gz:
	if test ! -f ../abella ; then \
	  cd .. && dune build && ln -sf _build/default/src/abella.exe abella ; \
	fi
#	git clean -fxd .
	omake -j1 upload-html

.PHONY: rebuild
rebuild:
	../_build/default/src/abella_doc.exe logic/cut.thm
	npm run build
	rsync -avz css abellaweb@abella-prover.org:abella-prover.org/examples/
