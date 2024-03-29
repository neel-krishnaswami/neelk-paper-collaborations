##############################################################################
##                 The Calculus of Inductive Constructions                  ##
##                                                                          ##
##                                Projet Coq                                ##
##                                                                          ##
##                     INRIA                        ENS-CNRS                ##
##              Rocquencourt                        Lyon                    ##
##                                                                          ##
##                                  Coq V7                                  ##
##                                                                          ##
##                                                                          ##
##############################################################################

# WARNING
#
# This Makefile has been automagically generated by coq_makefile
# Edit at your own risks !
#
# END OF WARNING

#
# This Makefile was generated by the command line :
# coq_makefile -f Make -o Makefile.inc 
#

##########################
#                        #
# Variables definitions. #
#                        #
##########################

CAMLP4LIB=`camlp5 -where 2> /dev/null || camlp4 -where`
CAMLP4=`basename $CAMLP4LIB`
COQSRC=-I $(COQTOP)/kernel -I $(COQTOP)/lib \
  -I $(COQTOP)/library -I $(COQTOP)/parsing \
  -I $(COQTOP)/pretyping -I $(COQTOP)/interp \
  -I $(COQTOP)/proofs -I $(COQTOP)/syntax -I $(COQTOP)/tactics \
  -I $(COQTOP)/toplevel -I $(COQTOP)/contrib/correctness \
  -I $(COQTOP)/contrib/extraction -I $(COQTOP)/contrib/field \
  -I $(COQTOP)/contrib/fourier -I $(COQTOP)/contrib/graphs \
  -I $(COQTOP)/contrib/interface -I $(COQTOP)/contrib/jprover \
  -I $(COQTOP)/contrib/omega -I $(COQTOP)/contrib/romega \
  -I $(COQTOP)/contrib/ring -I $(COQTOP)/contrib/xml \
  -I $(CAMLP4LIB)
ZFLAGS=$(OCAMLLIBS) $(COQSRC)
OPT=
COQFLAGS=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQC=$(COQBIN)coqc
GALLINA=gallina
COQDOC=$(COQBIN)coqdoc
CAMLC=ocamlc -c
CAMLOPTC=ocamlopt -c
CAMLLINK=ocamlc
CAMLOPTLINK=ocamlopt
COQDEP=$(COQBIN)coqdep -c
GRAMMARS=grammar.cma
CAMLP4EXTEND=pa_extend.cmo pa_macro.cmo q_MLast.cmo
PP=-pp "$(CAMLP4)o -I . -I $(COQTOP)/parsing $(CAMLP4EXTEND) $(GRAMMARS) -impl"
COQC=$(COQBIN)coqc
COQLIBS=$(COQLIBS)
COQFLAGS=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)

#########################
#                       #
# Libraries definition. #
#                       #
#########################

OCAMLLIBS=-I .\
  -I stdlib
COQLIBS=-I .\
  -I stdlib

###################################
#                                 #
# Definition of the "all" target. #
#                                 #
###################################

VFILES=stdlib/Permut.v\
  stdlib/Multiset.v\
  stdlib/Permutation.v\
  stdlib/Sorting.v\
  stdlib/SetoidList.v\
  ETactics.v\
  UsefulMisc.v\
  Assumptions.v\
  BasicTactics.v\
  MemModel.v\
  HeapProp.v\
  Exn.v\
  ST.v\
  DisjointUnion.v\
  Separation.v\
  STsep.v\
  Precise.v\
  Tactics.v\
  Table.v\
  MiscLemmas.v\
  Flyweight.v\
  IteratorsSpec.v\
  Iterators.v\
  IteratorsExamples.v\
  Subject.v
VOFILES=$(VFILES:.v=.vo)
VIFILES=$(VFILES:.v=.vi)
GFILES=$(VFILES:.v=.g)
HTMLFILES=$(VFILES:.v=.html)
GHTMLFILES=$(VFILES:.v=.g.html)

all: stdlib/Permut.vo\
  stdlib/Multiset.vo\
  stdlib/Permutation.vo\
  stdlib/Sorting.vo\
  stdlib/SetoidList.vo\
  ETactics.vo\
  UsefulMisc.vo\
  Assumptions.vo\
  BasicTactics.vo\
  MemModel.vo\
  HeapProp.vo\
  Exn.vo\
  ST.vo\
  DisjointUnion.vo\
  Separation.vo\
  STsep.vo\
  Precise.vo\
  Tactics.vo\
  Table.vo\
  MiscLemmas.vo\
  Flyweight.vo\
  IteratorsSpec.vo\
  Iterators.vo\
  IteratorsExamples.vo\
  Subject.vo

spec: $(VIFILES)

gallina: $(GFILES)

html: $(HTMLFILES)

gallinahtml: $(GHTMLFILES)

all.ps: $(VFILES)
	$(COQDOC) -ps -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.ps: $(VFILES)
	$(COQDOC) -ps -g -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`



####################
#                  #
# Special targets. #
#                  #
####################

.PHONY: all opt byte archclean clean install depend html

.SUFFIXES: .v .vo .vi .g .html .tex .g.tex .g.html

.v.vo:
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

.v.vi:
	$(COQC) -i $(COQDEBUG) $(COQFLAGS) $*

.v.g:
	$(GALLINA) $<

.v.tex:
	$(COQDOC) -latex $< -o $@

.v.html:
	$(COQDOC) -html $< -o $@

.v.g.tex:
	$(COQDOC) -latex -g $< -o $@

.v.g.html:
	$(COQDOC) -html -g $< -o $@

byte:
	$(MAKE) all "OPT="

opt:
	$(MAKE) all "OPT=-opt"

include .depend

.depend depend:
	rm -f .depend
	$(COQDEP) -i $(COQLIBS) $(VFILES) *.ml *.mli >.depend
	$(COQDEP) $(COQLIBS) -suffix .html $(VFILES) >>.depend

install:
	mkdir -p `$(COQC) -where`/user-contrib
	cp -f $(VOFILES) `$(COQC) -where`/user-contrib

Makefile.inc: Make
	mv -f Makefile.inc Makefile.inc.bak
	$(COQBIN)coq_makefile -f Make -o Makefile.inc


clean:
	rm -f *.cmo *.cmi *.cmx *.o $(VOFILES) $(VIFILES) $(GFILES) *~
	rm -f all.ps all-gal.ps $(HTMLFILES) $(GHTMLFILES)

archclean:
	rm -f *.cmx *.o

html:

# WARNING
#
# This Makefile has been automagically generated by coq_makefile
# Edit at your own risks !
#
# END OF WARNING

