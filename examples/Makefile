# Modify the path to the Abella executables as needed
ABELLA= ..

.PHONY: all
all: eval.out


# Everything after this point is generic and should be duplicated
# in user's makefiles

.PHONY: *.out
%.out :
	$(ABELLA)/abella $*.thm

%.thc :
	$(ABELLA)/abella $*.thm -c $*.thc

-include depend
depend: *.thm *.sig *.mod
	$(ABELLA)/abella -M *.thm > depend-stage
	mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.thc depend
