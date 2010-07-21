open Camlp4.PreCast


type tps =
  | Arrow of tps * tps
  | Shrink of tps * tps
  | One
  | Times of tps * tps
  | Val of tpu
and tpu =
  | Discrete (* We don't check ML types -- let Ocaml do that! *)
  | Lolli of tpu * tpu
  | I
  | Tensor of tpu * tpu
  | Omega of tps 
(*  | Lollishrink of tpu * tpu *)

(* Expressions come in one undifferentiated mass -- we use typing to sort it all out *)

type var = string;;

type exp =
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
  | AnnotS of exp * tps
  | AnnotU of exp * tpu
  | Const of Ast.expr
  | Start of exp
  | Stream of exp
  | LetOmega of var * exp * exp
  | Bracket of exp  (* For use in the contractive world *)

(* Now, we'll implement a type-directed elaborator *)

(* First, we need constructors for the syntactic operations in the metric signature. The generic
   constructors are parameterized by *three* modules. The first two are the "current category"
   and the "other category". The third is the parent module within which the two current categories
   reside. 
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
let embed f m _loc = <:expr< $uid:m$.embed $f$ >>
let value f m _loc = <:expr< $uid:m$.value $f$ >>

let flip f m m' = f m' m 

let oned  = id0 "oned"
let prod  = id0 "prod"
let prod' = id0 "prod'"

let varepsilon = id0' "varepsilon"
let eta = id0' "eta"

let value e = id1' "value" (flip e)
let omega e = id1' "omega" (flip e)
let discrete e = id1' "discrete" (fun _ _ _ _ -> e)

let sweak = id0 "sweak"
let spair = id0 "spair"
let scurry = id0 "scurry"
let seval = id0 "seval"
let swap = id0 "swap"
let scomposel = id1 "scomposel"
let scomposer = id1 "scomposer"

(* The contractive gadgets are kept in curried form, so applications
   of contractive functions need to curry the argument to the depth of 
   the contraction environment. *)

let rec curryenv env tm =
  match env with
  | [] -> tm
  | _ :: env' -> curry (curryenv env' tm)

(* Now, we write a small bidirectional elaborator for this language *)

(* Introduce an error monad *)

type 'a t = Error of string | Ok of 'a
let return x = Ok x
let (>>=) m f =
  match m with
  | Error msg -> (Error msg)
  | Ok v -> f v
let error msg = Error msg

(* To look up variables we need to construct the n-th projection *)

let rec lookup env x =
  match env with
  | [] -> error (Printf.sprintf "Unbound variable '%s'" x)
  | (y,tp) :: env when x = y -> return (pi2, tp)
  | (y,_) :: env -> (lookup env x) >>= (fun (e, tp) ->
		    return (compose pi1 e, tp))

type result = string -> string -> string -> Ast.loc -> Ast.expr

(* Basically, what follows implements a simple bidirectional 
   typechecking algorithm, and along the way spits out a (well-typed)
   ML syntax tree. The typechecking lets reuse the same syntax for 
   both sides of the adjunction, which is quite handy -- 

*)

let rec scheck env s tp : result t =
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
      scheck ((x,tps1) :: env) s2 tp >>= (fun e2 ->
      return (compose (pair id e1) e2)))
  | SLam(x, s2), Shrink(tps1, tps2) ->
      scheck_shrink env [x,tps1] s2 tps2
  | Value u1, Val tpu1 ->
      ucheck env [] u1 tpu1 >>= (fun e1 ->
      return (compose eta (value e1)))
  | _ -> ssynth env s >>= (fun (e, tp') -> 
	 if tp = tp' then return e else error "type mismatch")

and ssynth env : exp -> (result * tps) t = function
  | Var x -> lookup env x 
  | App(s1, s2) ->
      ssynth env s1 >>= (fun (e1, tps) ->
	match tps with
	| Arrow(tps2, tps1) ->
	    scheck env s2 tps2 >>= (fun e2 -> return (compose (pair e1 e2) eval, tps1))
	| _ -> error "Expected function type")
  | Fst s ->
      ssynth env s >>= (fun (e, tps) ->
	match tps with
	| Times(tps1, tps2) -> return (compose e pi1, tps1)
	| _ -> error "Expected product type")
  | Snd s -> 
      ssynth env s >>= (fun (e, tps) ->
	match tps with
	| Times(tps1, tps2) -> return (compose e pi2, tps2)
	| _ -> error "Expected product type")
  | AnnotS(s, tps) ->
      scheck env s tps >>= (fun e -> return (e, tps))
  | _ -> error "ssynths: Cannot synthesize type"


and scheck_shrink env env' s tps =
  match (s, tps) with
  | Bracket(s1), _ ->
      scheck env s1 tps >>= (fun e1 ->
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
  | _ -> ssynth_shrink env env' s >>= (fun (e, tps') -> 
         if tps = tps' then return e else error "scheck_shrink: type mismatch")

and ssynth_shrink env env' s =
  match s with
  | Var _ -> error "ssynth_shrink: Illegal variable use"
  | App(s1, s2) ->
      ssynth_shrink env env' s1 >>= (fun (e1, tps) -> 
      match tps with
      | Shrink(tps2, tps1) ->
	  scheck (env @ env') s2 tps2 >>= (fun e2 ->
            return ((compose (pair e1 (curryenv env' e2)) seval), tps1))
      | Arrow(tps2, tps1) ->
	  scheck_shrink env env' s2 tps2 >>= (fun e2 -> 
  	  let e = compose (compose (pair e1 e2) spair) (scomposer eval) in
	  return (e, tps1))
      | _ -> error "ssynth_shrink: expecting arrow type")
  | Fst s ->
      ssynth_shrink env env' s >>= (fun (e, tps) ->
	match tps with
	| Times(tps1, tps2) -> return (compose e (scomposer pi1), tps1)
	| _ -> error "Expected product type")
  | Snd s -> 
      ssynth_shrink env env' s >>= (fun (e, tps) ->
	match tps with
	| Times(tps1, tps2) -> return (compose e (scomposer pi2), tps2)
	| _ -> error "Expected product type")
  | AnnotS(s, tps) ->
      scheck_shrink env env' s tps >>= (fun e -> return (e, tps))
  | _ -> error "ssynth_shrink: Cannot synthesize type"	

and ucheck senv uenv u tpu =
  match u, tpu with
  | Lam(x, u2), Lolli(tpu1, tpu2) ->
      ucheck senv ((x, tpu1) :: uenv) u2 tpu2 >>= (fun e2 ->
      return (curry e2))
  | Pair(u1, u2), Tensor(tpu1, tpu2) ->
      ucheck senv uenv u1 tpu1 >>= (fun e1 -> 
      ucheck senv uenv u2 tpu2 >>= (fun e2 -> 
      return (pair e1 e2)))
  | Unit, I ->
      return one
  | Let(x, s1, s2), _ -> 
      usynth senv uenv s1 >>= (fun (e1, tpu1) ->
      ucheck senv ((x,tpu1) :: uenv) s2 tpu >>= (fun e2 ->
      return (compose (pair id e1) e2)))
  | Const e, Discrete ->
      return (compose oned (discrete e))
  | Stream s, Omega tps ->
      scheck senv s tps >>= (fun e -> 
      return (compose pi1 (omega e)))
  | LetOmega(x, u1, u2), _ ->
      usynth senv uenv u1 >>= (fun (e1, tpu1) -> 
      match tpu1 with
      | Omega tps ->
	  ucheck ((x,tps) :: senv) uenv u2 tpu >>= (fun e2 ->
          let swizzle = pair (pair (compose pi2 pi1) pi1) (compose pi2 pi2) in
	  let times f g = pair (compose pi1 f) (compose pi2 g) in 
	  let e = compose (pair e1 id) (compose swizzle (compose (times prod' id) e2)) in
	  return e)
      | _ -> error "ucheck: expected omega-type")
  | _ -> usynth senv uenv u >>= (fun (e, tpu') ->
	 if tpu = tpu' then return e else error "ucheck: type mismatch")

and usynth senv uenv = function
  | Var x -> (lookup uenv x) >>= (fun (e, tpu) ->
	     return (compose pi2 e, tpu))
  | App(u1, u2) ->
      usynth senv uenv u1 >>= (fun (e1, tpu1) -> 
      match tpu1 with
      | Lolli(tpu2, tpu1) ->
	  ucheck senv uenv u2 tpu2 >>= (fun e2 ->
          return (compose (pair e1 e2) eval, tpu1))
      | _ -> error "usynth: expected lolli type")
  | Fst u ->
      usynth senv uenv u >>= (fun (e, tpu) ->
      match tpu with
      | Tensor(tpu1, tpu2) -> return (compose e pi1, tpu1)
      | _ -> error "usynth: expected tensor type")
  | Snd u -> 
      usynth senv uenv u >>= (fun (e, tpu) ->
      match tpu with
      | Tensor(tpu1, tpu2) -> return (compose e pi2, tpu2)
      | _ -> error "usynth: expected tensor type")
  | Start s ->
      ssynth senv s >>= (fun (e, tps) ->
      match tps with
      | Val tpu -> 
	  return (compose pi1 (compose (omega e) varepsilon), tpu)
      | _ -> error "usynth: Expected Val type")
  | AnnotU(u, tpu) ->
      ucheck senv uenv u tpu >>= (fun e -> return (e, tpu))
  | _ -> error "usynth: Can't synthesize type" 



(* The parser. This does not presently call the typechecker, which should be
   fixed before POPL. *)
  
let rec mk_fun vs body =
  match vs with
  | [] -> assert false
  | [x] -> Lam(x, body)
  | x :: xs -> Lam(x, mk_fun xs body);;

let rec mk_sfun vs body =
  match vs with
  | [] -> body 
  | x :: xs -> SLam(x, mk_fun xs body);;


let mtypeu = Gram.Entry.mk "mtypeu";;
let mtypes = Gram.Entry.mk "mtypes";;
let mexpr = Gram.Entry.mk "mexpr";;

open Syntax
	      
EXTEND Gram
  GLOBAL: expr mtype mexpr;

  mtypes: [ [ LIDENT "one"  -> One 
            | "("; tp1 = mtypes; ","; tp2 = mtypes; ")" -> Prod(tp1, tp2)
	    | "("; tp = mtypes; ")" -> tp
	    ]
	  | "arrow" RIGHTA
	   [ tp1 = mtypes; "->"; tp2 = mtypes -> Arrow(tp1, tp2) 
           | tp1 = mtypes; "~>"; tp2 = mtypes -> Shrink(tp1, tp2)
           ]
	  | "simple"
            | LIDENT "value"; "("; tp = mtypeu; ")" -> Val(tp)
	    ]
	  ]
	  ;

  mtypeu: [ [ UIDENT "I"  -> One 
            | tp1 = mtypeu; "#"; tp2 = mtypeu -> Prod(tp1, tp2)
	    | "("; tp = mtypeu; ")" -> tp
	    ]
	  | "arrow" RIGHTA
	   [ tp1 = mtypeu; "-o"; tp2 = mtypeu -> Lolli(tp1, tp2) 
           ]
	  | "simple"
            | LIDENT "omega"; "("; tp = mtypes; ")" -> Omega(tp)
	    | LIDENT "discrete"; "("; tp = ctyp; ")" -> Discrete 
	    ]
	  ]
	  ;

  mexpr: [ "binders"
           [ "fun"; vs = LIST1 [v = LIDENT -> v]; "->"; body = mexpr ->
 	       mk_fun vs body
	   | "fun"; vs = LIST1 [v = LIDENT -> v]; "-o"; body = mshrink ->
 	       mk_sfun vs body
	   | "let"; v = LIDENT; "="; e = mexpr; "in"; e' = mexpr -> Let(v, e, e')
 	   | "let"; v = LIDENT; ":"; tp = mtypes; "="; e = mexpr; "in"; e' = mexpr ->
	       Let(v, AnnotS(tp, e), e')
 	   | "let"; v = LIDENT; ":"; tp = mtypeu; "="; e = mexpr; "in"; e' = mexpr ->
	       Let(v, AnnotU(tp, e), e')
	   | "let"; UIDENT "Omega"; "("; v = LIDENT; ")"; "="; e = mexpr; "in"; e' = mexpr -> 
                LetOmega(v, e, e')

 	   | "let"; "val"; v = LIDENT; "="; e = mexpr; "in"; e' = mexpr ->
	       Letv(v, e, e')
 	   | "let"; "val"; v = LIDENT; ":"; tp = mtype; "="; e = mexpr; "in"; e' = mexpr ->
 	       Letv(v, Annot(tp, e), e')
	   ]
 	 | "infixes"
 	   [  e = mexpr; "::"; e' = mexpr -> Cons(e, e')
	   |  LIDENT "fix"; e = expr -> Fix(e)
	   ]
 	 | "application"
 	   [ LIDENT "value"; e = expr -> Value(e)
 	   | LIDENT "fst"; e = mexpr -> Fst(e)
	   | LIDENT "snd"; e = mexpr -> Snd(e)
	   | LIDENT "start"; e = mexpr -> Start(e)
	   | UIDENT "Omega"; e = mexpr -> Stream(e)
 	   |  m = mexpr; m' = mexpr -> App(m, m')  ]
 	 | "atomic"
	   [ v = LIDENT -> Var v
 	   |  "("; ")" -> Unit
 	   |  "("; e = mexpr; ")" -> e
	   |  "("; e = mexpr; ":";  t = mtypeu; ")" -> AnnotU(t, e)
	   |  "("; e = mexpr; ":";  t = mtypes; ")" -> AnnotS(t, e)
	   |  "("; e = mexpr; ","; e' = mexpr -> Pair(e, e')
           |  "["; e = mexpr; "]" -> Bracket(e)
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
    [ [ "do"; "("; m = mexpr; ")" -> elaborate m "U" "C" "Metric" _loc ] ]
    ;
END


