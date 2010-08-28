module Monad :
  sig
    type 'a t = Error of Camlp4.PreCast.Loc.t * string | Ok of 'a
    val return : 'a -> 'a t
    val ( >>= ) : 'a t -> ('a -> 'b t) -> 'b t
    val error_loc : Camlp4.PreCast.Loc.t -> string -> 'a t
    val error : string -> 'a t
    val error_at : Camlp4.PreCast.Loc.t -> 'a t -> 'a t
  end

val lookup : (string * 'a) list -> string -> (Combinators.ast * 'a) Monad.t

val synch_ok : Term.tp -> unit Monad.t

val ultra_ok : Term.tp -> unit Monad.t

val scheck : 
  (Term.var * Term.tp) list -> Term.exp -> Term.tp -> Combinators.ast Monad.t

val ssynth :
  (Term.var * Term.tp) list -> Term.exp -> (Combinators.ast * Term.tp) Monad.t

val scheck_shrink :
  (Term.var * Term.tp) list ->
  (Term.var * Term.tp) list ->
  Term.exp -> Term.tp -> Combinators.ast Monad.t

val ssynth_shrink :
  (Term.var * Term.tp) list ->
  (Term.var * Term.tp) list ->
  Term.exp -> (Combinators.ast * Term.tp) Monad.t

val ucheck :
  (Term.var * Term.tp) list ->
  (Term.var * Term.tp) list ->
  Term.exp -> Term.tp -> Combinators.ast Monad.t

val usynth :
  (Term.var * Term.tp) list ->
  (Term.var * Term.tp) list ->
  Term.exp -> (Combinators.ast * Term.tp) Monad.t

val ucheck_shrink :
  (Term.var * Term.tp) list ->
  (Term.var * Term.tp) list ->
  (Term.var * Term.tp) list ->
  Term.exp -> Term.tp -> Combinators.ast Monad.t

val usynth_shrink :
  (Term.var * Term.tp) list ->
  (Term.var * Term.tp) list ->
  (Term.var * Term.tp) list ->
  Term.exp -> (Combinators.ast * Term.tp) Monad.t

val elaborate :
  Term.exp -> Camlp4.PreCast.Ast.loc -> Camlp4.PreCast.Ast.expr

val elaborates :
  Term.exp -> Camlp4.PreCast.Ast.loc -> Camlp4.PreCast.Ast.expr

