open Camlp4.PreCast (* I ought to be parametric in the location type ... *)

(* We have one big syntactic category for types, for which we check 
   well-formedness in a post-pass *)

type tp = InT of Ast.Loc.t * tp'
and tp' =
  | Arrow of tp * tp
  | Shrink of tp * tp
  | One
  | Times of tp * tp
  | Val of tp
  | Lolli of tp * tp
  | I
  | Tensor of tp * tp
  | Omega of tp
  | Gui of tp 
  | Discrete (* We don't check ML types -- let Ocaml do that! *)
  | Lollishrink of tp * tp 

(* Equality of types needs to ignore source locations. *)

let rec tp_equal (InT(_, tp1)) (InT(_, tp2)) =
  match tp1, tp2 with
  | One, One | I, I | Discrete, Discrete -> true
  | Omega tp1', Omega tp2' | Val tp1', Val tp2' | Gui tp1', Gui tp2' -> tp_equal tp1' tp2'                   
  | Times (tp1', tp1''), Times (tp2', tp2'')
  | Tensor(tp1', tp1''), Tensor(tp2', tp2'')
  | Lolli (tp1', tp1''), Lolli (tp2', tp2'')
  | Lollishrink(tp1', tp1''), Lollishrink (tp2', tp2'')
  | Arrow (tp1', tp1''), Arrow (tp2', tp2'')
  | Shrink(tp1', tp1''), Shrink(tp2', tp2'') ->
	tp_equal tp1' tp2' && tp_equal tp1'' tp2''
  | _ -> false
    
(* Similarly, expressions come in one undifferentiated mass -- we use
   typing to sort it all out *)

type var = string

type exp = In of Ast.Loc.t * exp'
and exp' = 
  | Var of var
  | Let of var * exp * exp
  | App of exp * exp
  | Lam of var * exp
  | Unit
  | Pair of exp * exp
  | Fst of exp
  | Snd of exp
  | Value of exp
  | Annot of exp * tp
  | EmbedF of Ast.expr 
  | Embed of Ast.expr
  | Inject of Ast.expr  
  | Map of exp
  | Start of exp
  | Stream of exp
  | Cons of exp
  | Fix of exp 
  | LetOmega of var * exp * exp
  | Bracket of exp  (* For use in the contractive world *)
  | LetGui of var * exp * exp
  | Return of exp 

let loc_exp (In(loc, _)) = loc
let loc_tp (InT(loc, _)) = loc
			       
let rec mk_fun loc vs body =
  match vs with
  | [] -> assert false
  | [x] -> In(loc, Lam(x, body))
  | x :: xs -> In(loc, Lam(x, mk_fun loc xs body))
