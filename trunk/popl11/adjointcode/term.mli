 type tp = InT of Camlp4.PreCast.Ast.Loc.t * tp'
 and tp' =
     Arrow of tp * tp
   | Shrink of tp * tp
   | One
   | Times of tp * tp
   | Val of tp
   | Lolli of tp * tp
   | I
   | Tensor of tp * tp
   | Omega of tp
   | Gui of tp 
   | Discrete
   | Lollishrink of tp * tp

 val tp_equal : tp -> tp -> bool
 
type var = string

type exp = In of Camlp4.PreCast.Ast.Loc.t * exp'
and exp' =
     Var of var
   | Let of var * exp * exp
   | App of exp * exp
   | Lam of var * exp
   | Unit
   | Pair of exp * exp
   | Fst of exp
   | Snd of exp
   | Value of exp
   | Annot of exp * tp
   | EmbedF of Camlp4.PreCast.Ast.expr
   | Embed of Camlp4.PreCast.Ast.expr
   | Inject of Camlp4.PreCast.Ast.expr
   | Map of exp
   | Start of exp
   | Stream of exp
   | Cons of exp
   | Fix of exp
   | LetOmega of var * exp * exp
   | Bracket of exp
   | LetGui of var * exp * exp
   | Return of exp 

 val loc_exp : exp -> Camlp4.PreCast.Ast.Loc.t
 val loc_tp : tp -> Camlp4.PreCast.Ast.Loc.t
 val mk_fun : Camlp4.PreCast.Ast.Loc.t -> var list -> exp -> exp
 
