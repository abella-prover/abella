ifndef $(VERSION)
VERSION := 2.0.0
endif

OCB = ocamlbuild -classic-display

.PHONY: all
all: src/version.ml src/abella.ml src/abella.cma src/abella.native

%.native:
	$(OCB) $@

%.cma:
	$(OCB) $@

src/version.ml:
	if test ! -e $@ ; then \
	  echo 'let version = "$(VERSION)"' > $@ ; \
	fi

# src/abella.ml: src/main.ml
# 	cp -a $< $@

.PHONY: clean
clean:
	$(OCB) -clean

.PHONY: top
top: all
	ocaml
