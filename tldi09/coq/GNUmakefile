# A simple wrapper around coq_makefile
ALLV := $(shell grep \.v Make)

include Makefile.inc
Makefile.inc : Make
	coq_makefile -f Make -o Makefile.inc

.depend: Makefile.inc

.PHONY: tarball
tarball:
	tar czvf ynot.tgz GNUmakefile Makefile.inc .depend Make README $(ALLV)
