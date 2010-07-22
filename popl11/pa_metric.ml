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
  | EmbedF of Ast.expr 
  | Embed of Ast.expr
  | Start of exp
  | Stream of exp
  | Cons of exp
  | Fix of exp 
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


let times f g = pair (compose pi1 f) (compose pi2 g) 
let assocr = times (compose pi1 pi1) (times (compose pi1 pi2) pi2)
let assocl = times (times pi1 (compose pi2 pi1)) (compose pi2 pi2)

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

type 'a t = Error of string | Ok of 'a
let return x = Ok x
let (>>=) m f =
  match m with
  | Error msg -> (Error msg)
  | Ok v -> f v
let error msg = Error msg

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
  | Var x -> lookup_shrink env x >>= (fun (e, tps) -> 
             return (compose e sweak, tps))
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
  | Fix u', Omega(tps) ->
      ucheck senv uenv u' (Omega(Shrink(tps, tps))) >>= (fun e ->
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
      ucheck senv ((x,tpu1) :: uenv) s2 tpu >>= (fun e2 ->
      return (compose (pair id e1) (compose assocr e2))))
  | Stream s, Omega tps ->
      scheck senv s tps >>= (fun e -> 
      return (compose pi1 (omega e)))
  | LetOmega(x, u1, u2), _ ->
      usynth senv uenv u1 >>= (fun (e1, tpu1) -> 
      match tpu1 with
      | Omega tps ->
	  ucheck ((x,tps) :: senv) uenv u2 tpu >>= (fun e2 ->
          let swizzle = pair (pair (compose pi2 pi1) pi1) (compose pi2 pi2) in
	  let e = compose (pair e1 id) (compose swizzle (compose (times prod' id) e2)) in
	  return e)
      | _ -> error "ucheck: expected omega-type")
  | _ -> usynth senv uenv u >>= (fun (e, tpu') ->
	 if tpu = tpu' then return e else error "ucheck: type mismatch")

and usynth senv uenv = function
  | Fix u' ->
      usynth senv uenv u' >>= (fun (e, tpu) ->
      match tpu with
      | Omega(Shrink(tps, tps')) when tps = tps' -> return (compose e fix, Omega(tps))
      | _ -> error "usynth: fixedpoint expected contractive map")
  | Cons u ->
      usynth senv uenv u >>= (fun (e, tpu) ->
	return (compose e cons, Omega(Shrink(Val tpu, Val tpu))))
  | Var x -> (lookup uenv x) >>= (fun (e, tpu) ->
	     return (compose pi2 e, tpu))
  | EmbedF e ->
      return (curry (compose pi2 (discrete e)), Lolli(Discrete, Discrete))
  | Embed e ->
      let _loc = Ast.Loc.ghost in 
      return (compose one (compose oned (discrete <:expr< fun () -> $e$>>)), Discrete)
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
  | Let(x, s1, s2)-> 
      usynth senv uenv s1 >>= (fun (e1, tpu1) ->
      usynth senv ((x,tpu1) :: uenv) s2 >>= (fun (e2, tpu) ->
      return (compose (pair id e1) (compose assocr e2), tpu)))
  | Stream s ->
      ssynth senv s >>= (fun (e, tps) -> 
      return (compose pi1 (omega e), Omega tps))
  | LetOmega(x, u1, u2) ->
      usynth senv uenv u1 >>= (fun (e1, tpu1) -> 
      match tpu1 with
      | Omega tps ->
	  usynth ((x,tps) :: senv) uenv u2 >>= (fun (e2, tpu) ->
          let swizzle = pair (pair (compose pi2 pi1) pi1) (compose pi2 pi2) in
	  let e = compose (pair e1 id) (compose swizzle (compose (times prod' id) e2)) in
	  return (e, tpu))
      | _ -> error "usynth: expected omega-type")
  | _ -> error "usynth: Can't synthesize type" 


let elaborate u _loc =
  match usynth [] [] u with
  | Ok(e, tp) -> e "U" "C" "Dsl" _loc
  | Error msg -> failwith msg

let elaborates s _loc =
  match ssynth [] s with
  | Ok(e, tp) -> e "C" "U" "Dsl" _loc
  | Error msg -> failwith msg


(* The parser. This does not presently call the typechecker, which should be
   fixed before POPL. *)
  
let rec mk_fun vs body =
  match vs with
  | [] -> assert false
  | [x] -> Lam(x, body)
  | x :: xs -> Lam(x, mk_fun xs body);;

let rec mk_sfun vs body =
  match vs with
  | [] -> assert false 
  | [x] -> SLam(x, body)
  | x :: xs -> SLam(x, mk_fun xs body);;


let mtypeu : tpu Gram.Entry.t = Gram.Entry.mk "mtypeu";;
let mtypes : tps Gram.Entry.t = Gram.Entry.mk "mtypes";;
let mexpr : exp Gram.Entry.t = Gram.Entry.mk "mexpr";;

let parsetype m s = Gram.parse_string m Ast.Loc.ghost s

let parsexpr s = Gram.parse_string mexpr Ast.Loc.ghost s
let display s =
  let _loc = Loc.ghost in 
  Printers.OCaml.print_implem <:str_item<let _ = $elaborate (parsexpr s) _loc$>>

let displays s =
  let _loc = Loc.ghost in 
  Printers.OCaml.print_implem <:str_item<let _ = $elaborates (parsexpr s) _loc$>>

open Syntax
	      
EXTEND Gram
  GLOBAL: expr mtypes mtypeu mexpr;

  mtypes: [ [  LIDENT "one" -> One 
            | "("; tp1 = mtypes; ","; tp2 = mtypes; ")" -> Times(tp1, tp2)
	    | "("; tp = mtypes; ")" -> tp
	    ]
	  | "arrow" RIGHTA
	   [ tp1 = mtypes; "->"; tp2 = mtypes -> Arrow(tp1, tp2) 
           | tp1 = mtypes; "~>"; tp2 = mtypes -> Shrink(tp1, tp2)
           ]
	  | "simple"
            [ UIDENT "V"; "("; tp = mtypeu; ")" -> Val(tp)
	    ]
	  ];

  mtypeu: [ [ UIDENT "I"  -> I 
            | tp1 = mtypeu; "#"; tp2 = mtypeu -> Tensor(tp1, tp2)
	    | "("; tp = mtypeu; ")" -> tp
	    ]
	  | "arrow" RIGHTA
	   [ tp1 = mtypeu; "-o"; tp2 = mtypeu -> Lolli(tp1, tp2) 
           ]
	  | "simple"
            [ UIDENT "S"; "("; tp = mtypes; ")" -> Omega(tp)
	    | UIDENT "D"; "("; tp = ctyp; ")" -> Discrete 
	    ]
	  ];

  mexpr: [ "binders"
           [ "fun"; vs = LIST1 [v = LIDENT -> v]; fn = ["->" -> mk_fun | "~>" -> mk_sfun]; body = mexpr ->
 	       fn vs body
	   | "let"; LIDENT "omega"; "("; v = LIDENT; ")"; "="; e = mexpr; "in"; e' = mexpr -> 
                LetOmega(v, e, e')
	   | "let"; v = LIDENT; "="; e = mexpr; "in"; e' = mexpr -> Let(v, e, e')
 	   | "let"; v = LIDENT; ":"; tp = mtypes; "="; e = mexpr; "in"; e' = mexpr ->
	       Let(v, AnnotS(e, tp), e')
 	   | "let"; v = LIDENT; ":"; tp = mtypeu; "="; e = mexpr; "in"; e' = mexpr ->
	       Let(v, AnnotU(e, tp), e')
	   ] 
 	 | "application"
 	   [ LIDENT "value"; e = mexpr -> Value(e)
 	   | LIDENT "fst"; e = mexpr -> Fst(e)
	   | LIDENT "snd"; e = mexpr -> Snd(e)
	   | LIDENT "start"; e = mexpr -> Start(e)
	   | LIDENT "omega"; e = mexpr -> Stream(e)
	   | LIDENT "fix"; e = mexpr -> Fix(e)
	   | LIDENT "cons"; e = mexpr -> Cons(e)
	   | LIDENT "discrete"; e = expr -> EmbedF(e)
           | LIDENT "const"; e = expr -> Embed(e)
 	   |  m = mexpr; m' = mexpr -> App(m, m')  ]
 	 | "atomic"
	   [ v = LIDENT -> Var v
 	   |  "("; ")" -> Unit
 	   |  "("; e = mexpr; ")" -> e
	   |  "("; e = mexpr; ":";  t = mtypeu; ")" -> AnnotU(e, t)
	   |  "("; e = mexpr; ":";  t = mtypes; ")" -> AnnotS(e, t)
	   |  "("; e = mexpr; ","; e' = mexpr -> Pair(e, e')
           |  "["; e = mexpr; "]" -> Bracket(e)
	   ]
	 ];

  expr: LEVEL "top"
    [ [ "do"; "("; m = mexpr; ")" -> elaborate m _loc ] ]
    ;
END


