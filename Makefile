default: src/Makefile
	make -C src lpp

src/Makefile: src/Makefile.in configure
	./configure
configure: configure.ac
	autoconf

.PHONY: test
test: src/Makefile
	@echo Testing the core LLambda library
	make -C src test
	@echo Testing lpp on examples
	make -C src lpp

.PHONY: clean
clean:
	make -C src clean
