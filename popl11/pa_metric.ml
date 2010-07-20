open Camlp4.PreCast

type tp =
  | Arrow of tp * tp
  | Shrink of tp * tp
  | One
  | Prod of tp * tp
  | Stream of tp
  | Gui of tp
  | Discrete of unit;;

type var = string;;

type exp =
  | Var of var
  | Fun of var * exp
  | App of exp * exp
  | Annot of tp * exp
  | Let of var * exp * exp
  | Return of exp
  | Letv of var * exp * exp
  | Cons of exp * exp
  | Unit
  | Pair of exp * exp
  | Fst of exp 
  | Snd of exp
  | Value of Ast.expr
  | ValApp of Ast.expr * exp
  | Fix of exp
  | SFun of var * shrinkexp

and shrinkexp =
  | SLift of exp
  | SSFun of var * exp
  | SFun of var * exp
  | SApp of shrinkexp * exp
  | SLet of shrinkexp * shrinkexp
  | SPair of shrinkexp * shrinkexp
  | SFst of shrinkexp
  | SSnd of shrinkexp
  | SUnit
  | SCons of exp * exp 
  | SAnnot of tp * shrinkexp

let rec ofold v none some =
  match v with
  | Some x -> some x
  | None -> none;;

let rec omap v f = ofold v None (fun x -> Some (f x));;

(* Simple bidirectional typechecker for this language *)

let rec check env e tp = 
  (match (e, tp) with
  | Fun(v, e'), Arrow(tp1, tp2)  -> check ((v, tp1) :: env) e' tp2
  | Pair(e1, e2), Prod(tp1, tp2) -> check env e1 tp1 && check env e2 tp2
  | Unit, One                    -> true
  | Let(x, t, e'), tp' -> ofold (synth env t) false (fun tp -> check ((x,tp) :: env) e' tp')
  | Letv(x, t, e'), (Gui(_) as tp') ->
      ofold (synth env t) false (function
				   | Gui(tp) -> check ((x,tp) :: env) e' tp'
				   | _ -> false)
  | Cons(e, e'), Stream(tp) -> check env e tp && check env e' (Stream tp)
  | Return e, Gui(tp) -> check env e tp
  | Value e, Discrete () -> true (* We do not replicate the Ocaml typechecker! *)
  | SFun(x, s), Shrink(tp1, tp2) -> check_shrink env [(x, tp1)] s tp2
  | _ -> (Some tp) = synth env e)

and synth env = function
  | Var x -> (try Some(List.assoc x env) with Not_found -> None)
  | Annot(tp, e) -> if check env e tp then Some tp else None
  | App(t, e) -> ofold (synth env t)
                       None
                       (function
			  | Arrow(tp1, tp2) when check env e tp1 -> Some(tp2)
			  | _ -> None)
  | Fst t -> ofold (synth env t) None (function
				 | Prod(tp1, tp2) -> Some tp1
				 | _ -> None)
  | Snd t -> ofold (synth env t) None (function
				 | Prod(tp1, tp2) -> Some tp2
				 | _ -> None)
  | ValApp(c, e') -> ofold (synth env e')
                        None
			(function
			   | Discrete () -> Some (Discrete ())
			   | _ -> None)
  | _ -> None

and check_shrink env senv s tp =
  (match (s, tp) with
  | SLift e -> check_shrink env e tp
  | SSFun(x, s'), Shrink(tp1, tp2) -> check_shrink env ((x, tp1) :: senv) s' tp2
  | SUnit, One -> true
  | SPair(s1, s2), Prod(tp1, tp2) ->
      let c = check_shrink env senv in c s1 tp && c s2 tp2
  | SLet(x, s, s') -> 
      ofold (synth_shrink env senv s) false
	(fun tp -> check_shrink ((x,tp) :: env) senv s')
  | SCons(e', e), Stream(tp') -> 
      let c = check (env @ senv) in c e' tp' && c e tp 
  | _, tp -> ofold (synth_shrink env senv s) false (fun tp' -> tp = tp'))
	
and synth_shrink env senv s =
  match s with
  | SFst s' ->
      ofold (synth_shrink env senv s') None
	(function Prod(tp1, tp2) -> Some tp1
	   | _ -> None)
  | SSnd s' -> 
      ofold (synth_shrink env senv s') None
	(function Prod(tp1, tp2) -> Some tp2
	   | _ -> None)
  | SApp(s', e) ->
      ofold (synth_shrink env senv s') None
	(function Shrink(tp1, tp2) when check (env @ senv) e tp1 -> Some tp2
	   | _ -> None)
  | SLift e -> synth env e
  | SAnnot(tp, s') when check_shrink env senv s' tp -> Some tp
  | _ -> None
          

(* Syntactic constructors for the operations in the metric signature *)

let id0 id m _loc = <:expr< ($uid:m$ . $lid:id$) >>;;
let id1 id f m _loc = <:expr< $uid:m$ . $lid:id$ $(f m _loc)$>>;;
let id2 id f1 f2 m _loc =  <:expr< ($uid:m$ . $lid:id$ $(f1 m _loc)$ $(f2 m _loc)$) >>;;

let id = id0 "id"
let compose = id2 "compose"
let one = id0 "one"
let pair = id2 "pair"
let pi1 = id0 "fst"
let pi2 = id0 "snd"
let curry = id1 "curry"
let apply = id0 "apply"
let cons = id0 "cons"
let return = id0 "return"
let bind = id1 "bind"
let strength = id0 "strength"
let embed f m _loc = <:expr< $uid:m$.embed $f$ >>
let value f m _loc = <:expr< $uid:m$.value $f$ >>

(* The elaborator. Basically it works by implementing the
   interpretation of the monadic metalanguage into CCC's with a strong
   monad.

   Right now this is essentially untyped; it should be integrated with
   the typechecker so that the error messages we generate are at least
   vaguely comprehensible. In particular, we should generate type
   annotations such that the OCaml type checker will report errors
   based on the mismatches in the user's types, rather than the
   gigantic ones based on the combinator expressions we generate.

   After implementing it, I should note this in our POPL paper as an
   implementation technique that other EDSL authors should use.
*)

let rec lookup env x =
  match env with
  | [] -> failwith (Printf.sprintf "Unbound variable '%s'" x)
  | y :: env when x = y -> pi2
  | y :: env -> compose pi1 (lookup env x)

let elaborate =
  let rec loop env = function
    | Var x          -> lookup env x
    | App(e1, e2)    -> compose (pair (loop env e1) (loop env e2)) apply
    | Fun(x, e)      -> curry (loop (x::env) e)
    | Unit           -> one
    | Pair(e1, e2)   -> pair (loop env e1) (loop env e2)
    | Fst e          -> compose pi1 (loop env e)
    | Snd e          -> compose pi2 (loop env e)
    | Cons(e, e')    -> compose (pair (loop env e) (loop env e')) cons
    | Let(x, e, e')  -> compose (pair id (loop env e)) (loop (x::env) e')
    | Return e       -> compose (loop env e) return
    | Annot(_, e)    -> loop env e
    | Letv(x, e, e') -> compose (compose (pair id (loop env e)) strength) (loop (x::env) e')
    | ValApp(c, e')  -> compose (pair (value c) (loop env e')) apply
    | Value c        -> embed c
    | Fix(e)         -> 
  in
  loop []

(* The parser. This does not presently call the typechecker, which should be
   fixed before POPL. *)
  
let rec mk_fun vs body =
  match vs with
  | [] -> assert false
  | [x] -> Fun(x, body)
  | x :: xs -> Fun(x, mk_fun xs body);;

let rec mk_sfun vs body =
  match vs with
  | [] -> body 
  | x :: xs -> SFun(x, mk_fun xs body);;


let mtype = Gram.Entry.mk "mtype";;
let mexpr = Gram.Entry.mk "mtype";;
let mshrink = Gram.Entry.mk "mshrink";;

open Syntax
	      
EXTEND Gram
  GLOBAL: expr mtype mexpr;

  mtype: [ [ LIDENT "unit"  -> One 
           | "("; tp1 = mtype; ","; tp2 = mtype; ")" -> Prod(tp1, tp2)
	   | "("; tp = mtype; ")" -> tp
	   ]
	 
	 | "arrow" RIGHTA
	   [ tp1 = mtype; "->"; tp2 = mtype -> Arrow(tp1, tp2) ]
	 | "simple"
           [ "["; tp = mtype; "]" -> Stream(tp) 
           | LIDENT "gui"; "("; tp = mtype; ")" -> Gui(tp)
	   | LIDENT "value"; "("; tp = ctyp; ")" -> Discrete ()
	   ]
	 ]
	 ;

  mexpr: [ "binders"
           [ "fun"; vs = LIST1 [v = LIDENT -> v]; "->"; body = mexpr ->
	       mk_fun vs body
	   | "fun"; vs = LIST1 [v = LIDENT -> v]; "-o"; body = mshrink ->
	       mk_sfun vs body
	   | "let"; v = LIDENT; "="; e = mexpr; "in"; e' = mexpr -> Let(v, e, e')
	   | "let"; v = LIDENT; ":"; tp = mtype; "="; e = mexpr; "in"; e' = mexpr ->
	       Let(v, Annot(tp, e), e')
	   | "let"; "val"; v = LIDENT; "="; e = mexpr; "in"; e' = mexpr ->
	       Letv(v, e, e')
	   | "let"; "val"; v = LIDENT; ":"; tp = mtype; "="; e = mexpr; "in"; e' = mexpr ->
	       Letv(v, Annot(tp, e), e')
	   ]
	 | "infixes"
	   [  e = mexpr; "::"; e' = mexpr -> Cons(e, e')
	   |  LIDENT "call"; e = expr; e' = mexpr -> ValApp(e, e')
	   ]
	 | "application"
	   [ LIDENT "return"; e = mexpr -> Return(e)
	   | LIDENT "value"; e = expr -> Value(e)
	   | LIDENT "fst"; e = mexpr -> Fst(e)
	   | LIDENT "snd"; e = mexpr -> Snd(e)
	   |  m = mexpr; m' = mexpr -> App(m, m')  ]
	 | "atomic"
	   [ v = LIDENT -> Var v
	   |  "("; ")" -> Unit
	   |  "("; m = mexpr; ")" -> m 
	   |  "("; m = mexpr; ":";  t = mtype; ")" -> Annot(t, m)
	   |  "("; m = mexpr; ","; m' = mexpr -> Pair(m, m')
	   ]
	 ]
         ;

  mshrink: [ "binders"
             [ "fun"; vs = LIST1 [v = LIDENT -> v]; "-o"; body = mexpr ->
		 mk_sfun vs body 
	     | "let"; v = LIDENT; "="; e = mshrink; "in"; e' = mexpr -> SLet(v, e, e')
	     | "let"; v = LIDENT; ":"; tp = mtype; "="; e = mshrink; "in"; e' = mexpr ->
		 SLet(v, SAnnot(tp, e), e')]
	   | "infixes"
	     [

  expr: LEVEL "top"
    [ [ "do"; "("; m = mexpr; ")" -> elaborate m "Metric" _loc ] ]
    ;
END

