# A simple wrapper around coq_makefile
ALLV := $(shell grep \.v Make)

include Makefile.inc
Makefile.inc : Make
	coq_makefile -f Make -o Makefile.inc

.depend: Makefile.inc

realclean: archclean
	rm -f Makefile.inc .depend *.vo *.html ynot.tgz

doc: $(ALLV)
	coqdoc -toc $(ALLV)

.PHONY: tarball
tarball:
	tar czvf ynot.tgz GNUmakefile Makefile.inc .depend Make $(ALLV)
