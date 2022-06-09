examples.tar.gz:
	if test ! -f ../abella ; then \
	  cd .. && dune build && ln -sf _build/default/src/abella.exe abella ; \
	fi
#	git clean -fxd .
	omake -j1 upload-html
