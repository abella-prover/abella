ELS = $(shell ls *.el)

EMACSFLAGS = -L /home/kaustuv/.elisp/ProofGeneral/generic

ELCS = ${ELS:%.el=%.elc}

.PHONY: all
all: .stamp-compile

.stamp-compile: ${ELS}
	emacs ${EMACSFLAGS} -batch -f batch-byte-compile ${ELS}
	@touch .stamp-compile

.PHONY: clean
clean:
	${RM} *.elc .stamp-compile
