ifndef $(VERSION)
VERSION := $(shell if test -e OMakefile ; then grep -E '^VERSION =' OMakefile | cut -d' ' -f3; else echo 1.4.0-dev0 ; fi)
endif

OCB = ocamlbuild -use-ocamlfind -classic-display -no-links

.PHONY: all
all: src/version.ml src/abella.ml src/abella.cma src/abella.native

%.native:
	$(OCB) $@

%.cma:
	$(OCB) $@

src/version.ml:
	if test ! -e $@ ; then \
	  echo 'let version = "$(VERSION)";;' > $@ ; \
	fi

.PHONY: clean
clean:
	$(OCB) -clean
	$(RM) src/version.ml

.PHONY: top
top: all
	ocaml
