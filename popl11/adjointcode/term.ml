open Camlp4.PreCast (* I ought to be parametric in the 
		       location type ... *)

(* We have one big syntactic category for types, for 
   which we check well-formedness in a post-pass *)

type tp = InT of Ast.Loc.t * tp'
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


(* Equality of types needs to ignore source locations. *)

let rec tp_equal (InT(_, tp1)) (InT(_, tp2)) =
  match tp1, tp2 with
  | One, One
  | I, I
  | Discrete, Discrete
  | Window, Window 
      -> true
  | Stream tp1', Stream tp2' 
  | F tp1', F tp2' 
  | G tp1', G tp2' 
      -> tp_equal tp1' tp2'                   
  | Times (tp1', tp1''), Times (tp2', tp2'')
  | Tensor(tp1', tp1''), Tensor(tp2', tp2'')
  | Lolli (tp1', tp1''), Lolli (tp2', tp2'')
  | Arrow (tp1', tp1''), Arrow (tp2', tp2'')
  | Shrink(tp1', tp1''), Shrink(tp2', tp2'') 
      -> tp_equal tp1' tp2' && tp_equal tp1'' tp2''
  | _ -> false
    
(* Similarly, expressions come in one undifferentiated 
   mass -- we use typing to sort it all out *)

type var = string

type exp = In of Ast.Loc.t * exp'
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
  | Embed of Ast.expr
  | Const of Ast.expr
  | Start of exp
  | Cons of exp
  | Fix of exp 
  | MakeF of exp
  | LetF of var * exp * exp
  | MakeG of exp
  | UnG of exp 
  | Bracket of exp  (* For use in the contractive world *)

let loc_exp (In(loc, _)) = loc
let loc_tp (InT(loc, _)) = loc
			       
let rec mk_fun loc vs body =
  match vs with
  | [] -> assert false
  | [x] -> In(loc, Lam(x, body))
  | x :: xs -> In(loc, Lam(x, mk_fun loc xs body))
