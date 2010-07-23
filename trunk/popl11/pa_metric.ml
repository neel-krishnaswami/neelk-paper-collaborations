open Camlp4.PreCast


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
  | Discrete (* We don't check ML types -- let Ocaml do that! *)
(* | Lollishrink of tp * tp *)

(* Equality of types needs to ignore source locations. *)

let rec tp_equal (InT(_, tp1)) (InT(_, tp2)) =
  match tp1, tp2 with
  | One, One | I, I | Discrete, Discrete -> true
  | Omega tp1', Omega tp2' | Val tp1', Val tp2' -> tp_equal tp1' tp2'			
  | Times(tp1', tp1''), Times(tp2', tp2'')
  | Tensor(tp1', tp1''), Tensor(tp2', tp2'')
  | Lolli(tp1', tp1''), Lolli(tp2', tp2'')
  | Arrow(tp1', tp1''), Arrow(tp2', tp2'')
  | Shrink(tp1', tp1''), Shrink(tp2', tp2'') ->
      tp_equal tp1' tp2' && tp_equal tp2' tp2''
  | _ -> false
      
(* Similarly, expressions come in one undifferentiated mass -- we use
typing to sort it all out *)

type var = string;;

type exp = In of Ast.Loc.t * exp'
and exp' = 
  | Var of var
  | Let of var * exp * exp
  | App of exp * exp
  | Lam of var * exp
  | SLam of var * exp
  | Unit
  | Pair of exp * exp
  | Fst of exp
  | Snd of exp
  | Value of exp
  | Annot of exp * tp
  | EmbedF of Ast.expr 
  | Embed of Ast.expr
  | Start of exp
  | Stream of exp
  | Cons of exp
  | Fix of exp 
  | LetOmega of var * exp * exp
  | Bracket of exp  (* For use in the contractive world *)

let loc_exp (In(loc, _)) = loc
let loc_tp (InT(loc, _)) = loc

(* Now, we'll implement a type-directed elaborator *)

(* First, we need constructors for the syntactic operations in the metric signature. The generic
   constructors are parameterized by *three* modules. The first two are the "current category"
   and the "other category". The third is the parent module within which the two current categories
   and the adjunction operators reside. 
*)

let id0 id m m' p _loc = <:expr< ($uid:p$ . $uid:m$ . $lid:id$) >>;;
let id1 id f m m' p _loc = <:expr< $uid:p$ . $uid:m$ . $lid:id$ $(f m m' p _loc)$>>;;
let id2 id f1 f2 m m' p _loc =  <:expr< ($uid:p$ . $uid:m$ . $lid:id$ $(f1 m m' p _loc)$ $(f2 m m' p _loc)$) >>;;

let id0' id m m' p _loc = <:expr< ($uid:p$ . $lid:id$) >>;;
let id1' id f m m' p _loc = <:expr< $uid:p$ . $lid:id$ $(f m m' p _loc)$>>;;
let id2' id f1 f2 m m' p _loc =  <:expr< ($uid:p$ . $lid:id$ $(f1 m m' p _loc)$ $(f2 m m' p _loc)$) >>;;


let id = id0 "id"
let compose = id2 "compose"
let one = id0 "one"
let pair = id2 "pair"
let pi1 = id0 "fst"
let pi2 = id0 "snd"
let curry = id1 "curry"
let eval = id0 "eval"
let cons = id0 "cons"

let flip f m m' = f m' m 

let oned  = id0' "oned"
let prod  = id0' "prod"
let prod' = id0' "prod'"

let varepsilon = id0' "varepsilon"
let eta = id0' "eta"

let value e = id1' "value" (flip e)
let omega e = id1' "omega" (flip e)

let discrete e = id1 "discrete" (fun _ _ _ _ -> e)
let fix = id0' "fix"
let cons = id0' "cons"

let sweak = id0 "sweak"
let spair = id0 "spair"
let scurry = id0 "scurry"
let seval = id0 "seval"
let swap = id0 "swap"
let scomposel = id1 "scomposel"
let scomposer = id1 "scomposer"
let eval' = id0 "eval'"

let times f g = pair (compose pi1 f) (compose pi2 g) 
let assocr = pair (compose pi1 pi1) (pair (compose pi1 pi2) pi2)
let assocl = pair (pair pi1 (compose pi2 pi1)) (compose pi2 pi2)

let uncurry = curry(compose (pair (compose (pair pi1 (compose pi2 pi1))
				           eval)
                                  (compose pi2 pi2))
		            eval)

(* The contractive gadgets are kept in curried form, so applications
   of contractive functions need to curry the argument to the depth of 
   the contraction environment. *)

let rec curryenv env tm =
  match env with
  | []  -> assert false
  | [_] -> curry tm
  | _ :: env' -> compose (curryenv env' (curry tm)) uncurry

(* Now, we write a small bidirectional elaborator for this language *)

(* Introduce an error monad *)

type 'a t = Error of Loc.t * string | Ok of 'a
let return x = Ok x
let (>>=) m f =
  match m with
  | Error (loc, msg) -> Error(loc, msg)
  | Ok v -> f v
let error_loc loc msg = Error (loc, msg)
let error msg = error_loc Loc.ghost msg

let error_at loc = function
  | Error(_, msg) -> Error(loc, msg)
  | Ok v -> Ok v

(* To look up variables we need to construct the n-th projection *)

let rec lookup' f env x = 
  match env with
  | [] -> error (f x)
  | (y,tp) :: env when x = y -> return (pi2, tp)
  | (y,_) :: env -> (lookup' f env x) >>= (fun (e, tp) ->
		    return (compose pi1 e, tp))

let lookup env x =
  lookup' (fun x -> Printf.sprintf "Unbound variable: '%s'" x) env x

let lookup_shrink env x = 
  lookup' (fun x -> Printf.sprintf "Variable not bound in nonexpansive context: '%s'" x) env x

(* Checking well-formedness of types *)

(* The functions to check well-formedness. *)

let rec synch_ok (InT(_loc, body)) =
  match body with 
  | One             -> return ()
  | Times(tp, tp')
  | Arrow(tp, tp') 
  | Shrink(tp, tp') -> synch_ok tp >>= (fun () -> synch_ok tp')
  | Val tp -> ultra_ok tp
  | _ -> error_loc _loc "synch_ok: ill-formed type" 
and ultra_ok (InT(_loc, body)) =
  match body with
  | I -> return ()
  | Tensor(tp, tp')
  | Lolli(tp, tp') -> ultra_ok tp >>= (fun () -> ultra_ok tp')
  | Omega tp -> synch_ok tp
  | Discrete -> return ()
  | _ -> error_loc _loc "ultra_ok: ill-formed type" 
      
(* Basically, what follows implements a simple bidirectional 
   typechecking algorithm, and along the way spits out a (well-typed)
   ML syntax tree. The typechecking lets reuse the same syntax for 
   both sides of the adjunction, which is quite handy -- 

*)

let rec scheck env (In(_loc, s)) (InT(tploc, tp))  =
  match (s, tp) with
  | Unit, One -> return one
  | Pair(s1, s2), Times(tps1, tps2) ->
      scheck env s1 tps1 >>= (fun e1 -> 
      scheck env s2 tps2 >>= (fun e2 ->
      return (pair e1 e2)))
  | Lam(x, s2), Arrow(tps1, tps2) ->
      scheck ((x,tps1) :: env) s2 tps2 >>= (fun e2 ->
      return (curry e2))
  | Let(x, s1, s2), _ -> 
      ssynth env s1 >>= (fun (e1, tps1) ->
      scheck ((x,tps1) :: env) s2 (InT(tploc, tp)) >>= (fun e2 ->
      return (compose (pair id e1) e2)))
  | SLam(x, s2), Shrink(tps1, tps2) ->
      scheck_shrink env [x,tps1] s2 tps2
  | Value u1, Val tpu1 ->
      ucheck env [] u1 tpu1 >>= (fun e1 ->
      return (compose eta (value (compose (pair id one) e1))))
  | _ -> ssynth env (In(_loc, s)) >>= (fun (e, tp') -> 
	 if tp_equal (InT(tploc, tp)) tp' then return e else error_loc _loc "scheck: type mismatch")

and ssynth env (In(_loc, s)) =
  match s with
  | Var x -> error_at _loc (lookup env x)
  | App(s1, s2) ->
      ssynth env s1 >>= (fun (e1, InT(_, tps)) ->
	match tps with
	| Arrow(tps2, tps1) ->
	    scheck env s2 tps2 >>= (fun e2 -> return (compose (pair e1 e2) eval, tps1))
	| Shrink(tps2, tps1) ->
	    scheck env s2 tps2 >>= (fun e2 -> return (compose (pair e1 e2) eval', tps1))
	| _ -> error_loc _loc "Expected function type")
  | Fst s ->
      ssynth env s >>= (fun (e, InT(_, tps)) ->
	match tps with
	| Times(tps1, tps2) -> return (compose e pi1, tps1)
	| _ -> error_loc _loc "Expected product type")
  | Snd s -> 
      ssynth env s >>= (fun (e, InT(_, tps)) ->
	match tps with
	| Times(tps1, tps2) -> return (compose e pi2, tps2)
	| _ -> error_loc _loc "Expected product type")
  | Annot(s, tps) ->
      synch_ok tps >>= (fun () -> 
      scheck env s tps >>= (fun e -> return (e, tps)))
  | Let(x, s1, s2) -> 
      ssynth env s1 >>= (fun (e1, tps1) ->
      ssynth ((x,tps1) :: env) s2 >>= (fun (e2, tps2) ->
      return (compose (pair id e1) e2, tps2)))
  | Value u1 ->
      usynth env [] u1 >>= (fun (e1, tpu1) ->
      return (compose eta (value (compose (pair id one) e1)),
	      InT(loc_tp tpu1, Val tpu1)))
  | _ -> error_loc _loc "ssynths: Cannot synthesize type"


and scheck_shrink env env' (In(_loc, s)) (InT(tploc, tps)) =
  match (s, tps) with
  | Bracket(s1), _ ->
      scheck env s1 (InT(tploc, tps)) >>= (fun e1 ->
      return (compose e1 sweak))
  | SLam(x, s2), Shrink(tps1, tps2) ->
      scheck_shrink env ((x,tps1) :: env') s2 tps2 >>= (fun e -> 
      return (compose e scurry))
  | Pair(s1, s2), Times(tps1, tps2) -> 
      scheck_shrink env env' s1 tps1 >>= (fun e1 -> 
      scheck_shrink env env' s2 tps2 >>= (fun e2 ->
      return (compose (pair e1 e2) spair)))
  | Unit, One -> return (compose one sweak)
  | Lam(x, s2), Arrow(tps1, tps2) ->
      scheck_shrink ((x,tps1) :: env) env' s2 tps2 >>= (fun e2 ->
      return (compose (curry e2) swap))
  | _ -> ssynth_shrink env env' (In(_loc, s)) >>= (fun (e, tps') -> 
         if tp_equal (InT(tploc, tps)) tps' then
	   return e
	 else
	   error_loc _loc "scheck_shrink: type mismatch")

and ssynth_shrink env env' (In(_loc, s)) =
  match s with
  | Var x -> error_at _loc (lookup_shrink env x >>= (fun (e, tps) -> 
			    return (compose e sweak, tps)))
  | App(s1, s2) ->
      ssynth_shrink env env' s1 >>= (fun (e1, InT(_, tps)) -> 
      match tps with
      | Shrink(tps2, tps1) ->
	  scheck (env' @ env) s2 tps2 >>= (fun e2 ->
            return ((compose (pair e1 (curryenv env' e2)) seval), tps1))
      | Arrow(tps2, tps1) ->
	  scheck_shrink env env' s2 tps2 >>= (fun e2 -> 
  	  let e = compose (compose (pair e1 e2) spair) (scomposer eval) in
	  return (e, tps1))
      | _ -> error_loc _loc "ssynth_shrink: expecting arrow type")
  | Fst s ->
      ssynth_shrink env env' s >>= (fun (e, InT(_, tps)) ->
	match tps with
	| Times(tps1, tps2) -> return (compose e (scomposer pi1), tps1)
	| _ -> error_loc _loc "Expected product type")
  | Snd s -> 
      ssynth_shrink env env' s >>= (fun (e, InT(_, tps)) ->
	match tps with
	| Times(tps1, tps2) -> return (compose e (scomposer pi2), tps2)
	| _ -> error "Expected product type")
  | Annot(s, tps) ->
      synch_ok tps >>= (fun () -> 
      scheck_shrink env env' s tps >>= (fun e -> return (e, tps)))
  | _ -> error_loc _loc "ssynth_shrink: Cannot synthesize type"	

and ucheck senv uenv (In(_loc, u)) (InT(tploc, tpu)) =
  match u, tpu with
  | Fix u', Omega(tps) ->
      ucheck senv uenv u' (InT(tploc, Omega(InT(tploc, Shrink(tps, tps))))) >>= (fun e ->
      return (compose e fix))
  | Lam(x, u2), Lolli(tpu1, tpu2) ->
      ucheck senv ((x, tpu1) :: uenv) u2 tpu2 >>= (fun e2 ->
      return (curry (compose assocr e2)))
  | Pair(u1, u2), Tensor(tpu1, tpu2) ->
      ucheck senv uenv u1 tpu1 >>= (fun e1 -> 
      ucheck senv uenv u2 tpu2 >>= (fun e2 -> 
      return (pair e1 e2)))
  | Unit, I ->
      return one
  | Let(x, s1, s2), _ -> 
      usynth senv uenv s1 >>= (fun (e1, tpu1) ->
      ucheck senv ((x,tpu1) :: uenv) s2 (InT(tploc, tpu)) >>= (fun e2 ->
      return (compose (pair id e1) (compose assocr e2))))
  | Stream s, Omega tps ->
      scheck senv s tps >>= (fun e -> 
      return (compose pi1 (omega e)))
  | LetOmega(x, u1, u2), _ ->
      usynth senv uenv u1 >>= (fun (e1, (InT(_, tpu1))) -> 
      match tpu1 with
      | Omega tps ->
	  ucheck ((x,tps) :: senv) uenv u2 (InT(tploc, tpu)) >>= (fun e2 ->
          let swizzle = pair (pair (compose pi2 pi1) pi1) (compose pi2 pi2) in
	  let e = compose (pair e1 id) (compose swizzle (compose (times prod' id) e2)) in
	  return e)
      | _ -> error_loc _loc "ucheck: expected omega-type")
  | Cons u, Omega(InT(_, Arrow(InT(_, Arrow(InT(_, Val(tpx)), tpa)),
			       InT(_, Shrink(InT(_, Val(tpx')), tpa'))))) ->
      if not (tp_equal tpa tpa') then
	error_loc _loc "ucheck: cons result types don't match"
      else if not (tp_equal tpx tpx') then
	error_loc _loc "ucheck: cons argument stream types don't match"
      else
	ucheck senv uenv u tpx >>= (fun e ->
	return (compose e cons))
  | _ -> usynth senv uenv (In(_loc, u)) >>= (fun (e, tpu') ->
	 if tp_equal (InT(tploc, tpu)) tpu' then return e else error_loc _loc "ucheck: type mismatch")

and usynth senv uenv (In(_loc, u)) =
  match u with 
  | Fix u' ->
      usynth senv uenv u' >>= (fun (e, (InT(_, tpu))) ->
      match tpu with
      | Omega(InT(loc, Shrink(tps, tps'))) when tp_equal tps tps' ->
	  return (compose e fix, InT(loc, Omega(tps)))
      | _ -> error_loc _loc "usynth: fixed point expected contractive map")
  | Var x -> error_at _loc 
               ((lookup uenv x) >>= (fun (e, tpu) ->
	        return (compose pi2 e, tpu)))
  | EmbedF e ->
      return (curry (compose pi2 (discrete e)),
	      InT(_loc, Lolli(InT(_loc, Discrete), InT(_loc, Discrete))))
  | Embed e ->
      return (compose one (compose oned (discrete <:expr< fun () -> $e$>>)),
	      InT(_loc, Discrete))
  | App(u1, u2) ->
      usynth senv uenv u1 >>= (fun (e1, InT(_, tpu1)) -> 
      match tpu1 with
      | Lolli(tpu2, tpu1) ->
	  ucheck senv uenv u2 tpu2 >>= (fun e2 ->
          return (compose (pair e1 e2) eval, tpu1))
      | _ -> error_loc _loc "usynth: expected lolli type")
  | Fst u ->
      usynth senv uenv u >>= (fun (e, InT(_, tpu)) ->
      match tpu with
      | Tensor(tpu1, tpu2) -> return (compose e pi1, tpu1)
      | _ -> error_loc _loc "usynth: expected tensor type")
  | Snd u -> 
      usynth senv uenv u >>= (fun (e, InT(_, tpu)) ->
      match tpu with
      | Tensor(tpu1, tpu2) -> return (compose e pi2, tpu2)
      | _ -> error_loc _loc "usynth: expected tensor type")
  | Start s ->
      ssynth senv s >>= (fun (e, InT(_, tps)) ->
      match tps with
      | Val tpu -> 
	  return (compose pi1 (compose (omega e) varepsilon), tpu)
      | _ -> error_loc _loc "usynth: Expected Val type")
  | Annot(u, tpu) ->
      ultra_ok tpu >>= (fun () -> 
      ucheck senv uenv u tpu >>= (fun e -> return (e, tpu)))
  | Let(x, s1, s2)-> 
      usynth senv uenv s1 >>= (fun (e1, tpu1) ->
      usynth senv ((x,tpu1) :: uenv) s2 >>= (fun (e2, tpu) ->
      return (compose (pair id e1) (compose assocr e2), tpu)))
  | Stream s ->
      ssynth senv s >>= (fun (e, tps) -> 
      return (compose pi1 (omega e), InT(loc_tp tps, Omega tps)))
  | LetOmega(x, u1, u2) ->
      usynth senv uenv u1 >>= (fun (e1, InT(_, tpu1)) -> 
      match tpu1 with
      | Omega tps ->
	  usynth ((x,tps) :: senv) uenv u2 >>= (fun (e2, tpu) ->
          let swizzle = pair (pair (compose pi2 pi1) pi1) (compose pi2 pi2) in
	  let e = compose (pair e1 id) (compose swizzle (compose (times prod' id) e2)) in
	  return (e, tpu))
      | _ -> error_loc _loc "usynth: expected omega-type")
  | _ -> error_loc _loc "usynth: Can't synthesize type" 

(* The elaborate functions try and *)

let elaborate u _loc =
  match usynth [] [] u with
  | Ok(e, tp) -> e "U" "C" "Dsl" _loc
  | Error(loc, msg) -> Loc.raise loc (Failure msg)

let elaborates s _loc =
  match ssynth [] s with
  | Ok(e, tp) -> e "C" "U" "Dsl" _loc
  | Error(loc, msg) -> Loc.raise loc (Failure msg)

(* The parser. *)
  
let rec mk_fun loc vs body =
  match vs with
  | [] -> assert false
  | [x] -> In(loc, Lam(x, body))
  | x :: xs -> In(loc, Lam(x, mk_fun loc xs body));;

let rec mk_sfun loc vs body =
  match vs with
  | [] -> assert false 
  | [x] -> In(loc, SLam(x, body))
  | x :: xs -> In(loc, SLam(x, mk_sfun loc xs body));;


let mtype : tp Gram.Entry.t = Gram.Entry.mk "mtype";;
let mtype_base : tp Gram.Entry.t = Gram.Entry.mk "mtype_base";;


let arith : int Gram.Entry.t = Gram.Entry.mk "arith";;

let mexpr : exp Gram.Entry.t = Gram.Entry.mk "mexpr";;

let parsetype s = Gram.parse_string mtype Ast.Loc.ghost s
let parsexpr s = Gram.parse_string mexpr Ast.Loc.ghost s

let display s =
  let _loc = Loc.ghost in 
  Printers.OCaml.print_implem <:str_item<let _ = $elaborate (parsexpr s) _loc$>>

let displays s =
  let _loc = Loc.ghost in 
  Printers.OCaml.print_implem <:str_item<let _ = $elaborates (parsexpr s) _loc$>>

let display_ast t = 
  let _loc = Loc.ghost in 
  Printers.OCaml.print_implem <:str_item<let _ = $t$>>

open Syntax

(* The payoff for piling all the syntactic categories into one big soup 
   comes here -- it makes parsing very simple, and lets us generate better
   error messages (since we can use semantic info to identify problems). 
*)
	      
EXTEND Gram
  GLOBAL: arith expr mtype mexpr ;

  mtype:
    [ RIGHTA
      [ tp1 = mtype; "->"; tp2 = mtype            -> InT(_loc, Arrow(tp1, tp2))
      | tp1 = mtype; "~>"; tp2 = mtype            -> InT(_loc, Shrink(tp1, tp2)) 
      | tp1 = mtype; "-"; LIDENT "o"; tp2 = mtype -> InT(_loc, Lolli(tp1, tp2)) ]
    | [ tp1 = mtype; "&"; tp2 = mtype  		  -> InT(_loc, Times(tp1, tp2))
      | tp1 = mtype; "*"; tp2 = mtype  		  -> InT(_loc, Tensor(tp1, tp2))]
    | [ UIDENT "I"                     		  -> InT(_loc, I)
      | LIDENT "one"                              -> InT(_loc, One)
      | UIDENT "V"; "("; tp = mtype; ")" 	  -> InT(_loc, Val(tp))
      | UIDENT "S"; "("; tp = mtype; ")" 	  -> InT(_loc, Omega(tp))
      | UIDENT "D"; "("; tp = ctyp; ")"  	  -> InT(_loc, Discrete)
      | "("; tp = mtype; ")"             	  -> tp ]
    ];

  mexpr: [ "binders"
           [ "fun"; vs = LIST1 [v = LIDENT -> v]; fn = ["->" -> mk_fun | "~>" -> mk_sfun]; body = mexpr ->
 	       fn _loc vs body
	   | "let"; LIDENT "omega"; "("; v = LIDENT; ")"; "="; e = mexpr; "in"; e' = mexpr -> 
               In(_loc, LetOmega(v, e, e'))
	   | "let"; LIDENT "omega"; "("; v = LIDENT; ":"; tp = mtype; ")"; "="; e = mexpr; "in"; e' = mexpr -> 
               In(_loc, LetOmega(v, In(Loc.merge (loc_exp e) (loc_tp tp), Annot(e, InT(loc_tp tp, Omega tp))), e'))
	   | "let"; v = LIDENT; "="; e = mexpr; "in"; e' = mexpr -> In(_loc, Let(v, e, e'))
 	   | "let"; v = LIDENT; ":"; tp = mtype; "="; e = mexpr; "in"; e' = mexpr ->
	       In(_loc, Let(v, In(Loc.merge (loc_exp e) (loc_tp tp), Annot(e, tp)), e'))
	   ] 
         | "annotation"
   	   [ e = mexpr; ":";  t = mtype -> In(_loc, Annot(e, t)) ]
 	 | "application"
 	   [ LIDENT "value"; e = mexpr -> In(_loc, Value(e))
 	   | LIDENT "fst"; e = mexpr -> In(_loc, Fst(e))
	   | LIDENT "snd"; e = mexpr -> In(_loc, Snd(e))
	   | LIDENT "start"; e = mexpr -> In(_loc, Start(e))
	   | LIDENT "omega"; e = mexpr -> In(_loc, Stream(e))
	   | LIDENT "fix"; e = mexpr -> In(_loc, Fix(e))
	   | LIDENT "cons"; e = mexpr -> In(_loc, Cons(e))
	   | LIDENT "discrete"; e = expr -> In(_loc, EmbedF(e))
           | LIDENT "const"; e = expr -> In(_loc, Embed(e))
 	   |  m = mexpr; m' = mexpr -> In(_loc, App(m, m'))  ]
 	 | "atomic"
	   [ v = LIDENT -> In(_loc, Var v)
 	   |  "("; ")" -> In(_loc, Unit)
 	   |  "("; e = mexpr; ")" -> e
	   |  "("; e = mexpr; ","; e' = mexpr -> In(_loc, Pair(e, e'))
           |  "["; e = mexpr; "]" -> In(_loc, Bracket(e))
	   ]
	 ];

  expr: LEVEL "top"
    [ [ "do"; UIDENT "U"; "("; m = mexpr; ")" -> elaborate m _loc
      | "do"; UIDENT "S"; "("; m = mexpr; ")" -> elaborates m _loc
      ] 
    ];
END


