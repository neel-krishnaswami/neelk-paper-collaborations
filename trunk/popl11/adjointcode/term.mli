type tp = InT of Camlp4.PreCast.Ast.Loc.t * tp'
and tp' =
  | One
  | Times of tp * tp
  | Arrow of tp * tp
  | Shrink of tp * tp
  | Stream of tp
  | Discrete (* We don't check ML types -- let Ocaml do 
		that! *)
  | G of tp 
  | I
  | Tensor of tp * tp
  | Lolli of tp * tp
  | Window 
  | F of tp

val tp_equal : tp -> tp -> bool
 
type var = string

type exp = In of Camlp4.PreCast.Ast.Loc.t * exp'
and exp' = 
  | Var of var
  | Let of var * exp * exp
  | App of exp * exp
  | Lam of var * exp
  | Unit
  | LetUnit of exp * exp 
  | Pair of exp * exp
  | LetPair of var * var * exp * exp 
  | Value of exp
  | Annot of exp * tp
  | Embed of Camlp4.PreCast.Ast.expr
  | Const of Camlp4.PreCast.Ast.expr
  | Start of exp
  | Cons of exp
  | Fix of exp 
  | MakeF of exp
  | LetF of var * exp * exp
  | MakeG of exp
  | UnG of exp 
  | Bracket of exp  (* For use in the contractive world *)


 val loc_exp : exp -> Camlp4.PreCast.Ast.Loc.t
 val loc_tp : tp -> Camlp4.PreCast.Ast.Loc.t
 val mk_fun : Camlp4.PreCast.Ast.Loc.t -> var list -> exp -> exp
 
