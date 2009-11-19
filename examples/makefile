# Generic Abella makefile
#  1. Ensure abella is in your PATH
#  2. Change 'example' below to the name of your root development
#  3. Run 'make'


.PHONY: all
all: example.out


# Everything after this point is generic and should be duplicated
# in user's makefiles

.PHONY: *.out
%.out :
	abella $*.thm

%.thc :
	abella $*.thm -c $*.thc

-include depend
depend: *.thm *.sig *.mod
	abella -M *.thm > depend-stage
	mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.thc depend
