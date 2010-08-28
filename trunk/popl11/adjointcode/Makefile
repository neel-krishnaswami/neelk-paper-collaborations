PREPROCESSOR = -pp camlp4of
GTKLIB = -I +lablgtk2 lablgtk.cma gtkInit.cmo
CAMLP4LIB = -I +camlp4 dynlink.cma camlp4lib.cma
OCAMLC = ocamlc 


toplevel: pa_metric.cma debug.cma
	ocamlmktop -o frpcaml.exe $(GTKLIB) $(CAMLP4LIB) camlp4of.cma rewrite.cma frp.cma pa_metric.cma debug.cma 

pa_metric.cma: rewrite.cma frp.cma pa_metric.cmo grammar.cmo
	$(OCAMLC) -a -o pa_metric.cma rewrite.cma frp.cma grammar.cmo pa_metric.cmo

# If you don't want to  use the syntax extension, then just build frp.cma and #load that in your toplevel

frp.cma: dataflow.cmo dsl.cmo
	$(OCAMLC) $(GTKLIB) -a -o frp.cma dataflow.cmo dsl.cmo

dataflow.cmo: dataflow.mli dataflow.mli
	$(OCAMLC) dataflow.mli dataflow.ml

dsl.cmo: dataflow.cmo dsl.mli dsl.ml
	$(OCAMLC) $(GTKLIB) dataflow.cmo dsl.mli dsl.ml

debug.cma: debug.cmo
	$(OCAMLC) -a -o debug.cma debug.cmo

debug.cmo: rewrite.cma frp.cma pa_metric.cmo grammar.cmo
	$(OCAMLC) $(GTKLIB) $(CAMLP4LIB) $(PREPROCESSOR) rewrite.cma frp.cma grammar.cmo debug.mli debug.ml 

grammar.cmo: grammar.ml grammar.mli term.cmo
	$(OCAMLC) $(CAMLP4LIB) $(PREPROCESSOR) rewrite.cma frp.cma grammar.mli grammar.ml 

pa_metric.cmo: rewrite.cma frp.cma grammar.cmo pa_metric.ml
	$(OCAMLC) $(GTKLIB) $(CAMLP4LIB) $(PREPROCESSOR) -o pa_metric.cmo rewrite.cma frp.cma grammar.cmo -c pa_metric.ml

term.cmo: term.mli term.ml
	$(OCAMLC) $(CAMLP4LIB) term.mli term.ml

combinators.cmo: combinators.mli combinators.ml
	$(OCAMLC) $(CAMLP4LIB) $(PREPROCESSOR) combinators.mli combinators.ml

elaborator.cmo: term.cmo combinators.cmo elaborator.ml elaborator.ml
	$(OCAMLC) $(GTKLIB) $(CAMLP4LIB) combinators.cmo term.cmo elaborator.mli elaborator.ml

rewrite.cma: term.cmo combinators.cmo elaborator.cmo
	$(OCAMLC) -a -o rewrite.cma term.cmo combinators.cmo elaborator.cmo


clean:
	rm *.cm* frpcaml.exe