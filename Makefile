ifndef $(VERSION)
VERSION := 1.4.0b1
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
