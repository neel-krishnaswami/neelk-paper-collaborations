val parsetype : string -> Term.tp
val parsexpr : string -> Term.exp
val display : string -> unit
val displays : string -> unit
val display_ast : Camlp4.PreCast.Syntax.Ast.expr -> unit
val test_scheck : (Term.var * string) list -> string -> string -> unit
val test_ssynth : (Term.var * string) list -> string -> Term.tp
val test_scheck_shrink :
  (Term.var * string) list ->
  (Term.var * string) list -> string -> string -> unit
val test_ssynth_shrink :
  (Term.var * string) list ->
  (Term.var * string) list -> string -> Term.tp
val test_ucheck :
  (Term.var * string) list ->
  (Term.var * string) list -> string -> string -> unit
val test_usynth :
  (Term.var * string) list ->
  (Term.var * string) list -> string -> Term.tp
val test_ucheck_shrink :
  (Term.var * string) list ->
  (Term.var * string) list ->
  (Term.var * string) list -> string -> string -> unit
val test_usynth_shrink :
  (Term.var * string) list ->
  (Term.var * string) list ->
  (Term.var * string) list -> string -> Term.tp

