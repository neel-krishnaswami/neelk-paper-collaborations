open Camlp4.PreCast
open Term
open Combinators 

module Monad =
struct 
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
end
open Monad


(* To look up variables we need to construct the n-th projection *)

let rec lookup' f env x = 
  match env with
  | [] -> error (f x)
  | (y,tp) :: env when x = y -> return (pi2, tp)
  | (y,_) :: env -> (lookup' f env x) >>= (fun (e, tp) ->
                  return (compose pi1 e, tp))

let varnames env = String.concat ", " (List.map fst env)

let lookup env x =
  lookup' (fun x -> Printf.sprintf "Unbound variable: '%s' in context [%s]" x (varnames env))
    env
    x

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
  | Lollishrink(tp, tp') -> ultra_ok tp >>= (fun () -> ultra_ok tp')
  | Omega tp -> synch_ok tp
  | Discrete -> return ()
  | Gui tp -> ultra_ok tp 
  | _ -> error_loc _loc "ultra_ok: ill-formed type" 


let rec string_of_type (InT(_, t)) =
  match t with 
  | One -> "one"
  | I   -> "I"
  | Times(t, t') -> Printf.sprintf "(%s & %s)" (string_of_type t) (string_of_type t')
  | Tensor(t, t') -> Printf.sprintf "(%s * %s)" (string_of_type t) (string_of_type t')
  | Arrow(t, t') -> Printf.sprintf "(%s -> %s)" (string_of_type t) (string_of_type t')
  | Shrink(t, t') -> Printf.sprintf "(%s ~> %s)" (string_of_type t) (string_of_type t')
  | Lolli(t, t') -> Printf.sprintf "(%s -o %s)" (string_of_type t) (string_of_type t')
  | Lollishrink(t, t') -> Printf.sprintf "(%s -* %s)" (string_of_type t) (string_of_type t')
  | Gui t -> Printf.sprintf "Gui(%s)" (string_of_type t)
  | Discrete -> "D(_)"
  | Val t -> Printf.sprintf "V(%s)" (string_of_type t)
  | Omega t -> Printf.sprintf "S(%s)" (string_of_type t)

let mismatch loc string (t1 : Term.tp) (t2 : Term.tp)  =
  error_loc loc (Printf.sprintf "%s: expected %s but got %s" string (string_of_type t1) (string_of_type t2))
      
let mismatch1 loc string (t1 : Term.tp) = 
  error_loc loc (Printf.sprintf "%s, but got %s" string (string_of_type t1))

(* Basically, what follows implements a simple bidirectional 
   typechecking algorithm, and along the way spits out a (well-typed)
   ML syntax tree. So typechecking lets reuse the same syntax for 
   both sides of the adjunction, which is quite handy....
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
  | Lam(x, s2), Shrink(tps1, tps2) ->
      scheck_shrink env [x,tps1] s2 tps2 >>= (fun e ->
      return (compose e (scomposel (pair one id))))
  | Value u1, Val tpu1 ->
      ucheck env [] u1 tpu1 >>= (fun e1 ->
      return (compose eta (value (compose (pair id one) e1))))
  | _ -> ssynth env (In(_loc, s)) >>= (fun (e, tp') -> 
         if tp_equal (InT(tploc, tp)) tp' then return e else mismatch _loc "scheck" (InT(tploc, tp)) tp')

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
  | Lam(x, s2), Shrink(tps1, tps2) ->
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
  | Value u, Val(tpu) ->
      ucheck_shrink env env' [] u tpu >>= (fun e ->
      let f = value(compose (pair id one) (compose e (scomposel (pair id one)))) in 
      return (compose eta (compose f contract')))
  | _ -> ssynth_shrink env env' (In(_loc, s)) >>= (fun (e, tps') -> 
         if tp_equal (InT(tploc, tps)) tps' then
           return e
         else
           mismatch _loc "scheck_shrink" (InT(tploc, tps)) tps')

and ssynth_shrink env env' (In(_loc, s)) =
  match s with
  | Var x -> error_at _loc (lookup_shrink env x >>= (fun (e, tps) -> 
                            return (compose e sweak, tps)))
  | App(s1, s2) ->
      ssynth_shrink env env' s1 >>= (fun (e1, InT(_, tps)) -> 
      match tps with
      | Shrink(tps2, tps1) ->
          scheck (env' @ env) s2 tps2 >>= (fun e2 ->
            let e2' = curry (compose (reassoc env') e2) in 
            return ((compose (pair e1 e2') seval), tps1))
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
  | Bracket(s1) ->
      ssynth env s1  >>= (fun (e1, tps) ->
      return (compose e1 sweak, tps))
  | _ -> error_loc _loc "ssynth_shrink: Cannot synthesize type" 

and ucheck senv uenv (In(_loc, u)) (InT(tploc, tpu) as tpu') =
  match u, tpu with
  | Return u1, Gui tpu1 ->
      ucheck senv uenv u1 tpu1 >>= (fun e1 ->
      return(compose e1 guireturn))
  | Return _, _ -> mismatch1 _loc "ucheck: expected Gui type at return" tpu'
  | LetGui(x, u1, u2), Gui _ ->
      usynth senv uenv u1 >>= (fun (e1, (InT(_, tpu1) as tpu1')) ->
      match tpu1 with
      | Gui tpu1' -> ucheck senv ((x,tpu1') :: uenv) u2 tpu' >>= (fun e2 ->
		    return (compose (pair id e1) (compose strength (bind (compose assocr e2)))))
      | _ -> mismatch1 _loc "ucheck: expected Gui type at let argument" tpu1')
  | LetGui(_, _, _), _ -> mismatch1 _loc "ucheck: expected Gui type at let body" tpu'
  | Inject e, Lolli(tpu1, tpu2) ->
      return (compose one (curry (compose pi2 (fun _ _ _ _ -> e))))
  | Fix u', Omega(_) ->
      ucheck senv uenv u' (InT(tploc, Lollishrink(tpu', tpu'))) >>= (fun e ->
      return (compose e fix))
  | Fix _, _ -> mismatch1 _loc "ucheck: expected stream type for fixed point" tpu'
  | Lam(x, u2), Lolli(tpu1, tpu2) ->
      ucheck senv ((x, tpu1) :: uenv) u2 tpu2 >>= (fun e2 ->
      return (curry (compose assocr e2)))
  | Lam(x, u2), Lollishrink(tpu1, tpu2) ->
      ucheck_shrink senv uenv [x, tpu1] u2 tpu2 >>= (fun e2 ->
      return (compose e2 (scomposel (pair one id))))
  | Lam(_, _), _ -> mismatch1 _loc "ucheck: expected arrow type for lambda" tpu'
  | Pair(u1, u2), Tensor(tpu1, tpu2) ->
      ucheck senv uenv u1 tpu1 >>= (fun e1 -> 
      ucheck senv uenv u2 tpu2 >>= (fun e2 -> 
      return (pair e1 e2)))
  | Pair(u1, u2), Discrete ->
      ucheck senv uenv u1 tpu' >>= (fun e1 ->
      ucheck senv uenv u2 tpu' >>= (fun e2 ->
      return (compose (pair e1 e2) paird)))
  | Pair(_, _), _ -> mismatch1 _loc "ucheck: expected product type for pair" tpu'
  | Unit, I ->
      return one
  | Unit, _ -> mismatch1 _loc "ucheck: expected type I for unit" tpu'
  | Let(x, s1, s2), _ -> 
      usynth senv uenv s1 >>= (fun (e1, tpu1) ->
      ucheck senv ((x,tpu1) :: uenv) s2 tpu' >>= (fun e2 ->
      return (compose (pair id e1) (compose assocr e2))))
  | Stream s, Omega tps ->
      scheck senv s tps >>= (fun e -> 
      return (compose pi1 (omega e)))
  | Stream s, _ -> mismatch1 _loc "ucheck: expected stream type for omega-expression" tpu'
  | LetOmega(x, u1, u2), _ ->
      usynth senv uenv u1 >>= (fun (e1, (InT(_, tpu1))) -> 
      match tpu1 with
      | Omega tps ->
          ucheck ((x,tps) :: senv) uenv u2 (InT(tploc, tpu)) >>= (fun e2 ->
          let swizzle = pair (pair (compose pi2 pi1) pi1) (compose pi2 pi2) in
          let e = compose (pair e1 id) (compose swizzle (compose (times prod' id) e2)) in
          return e)
      | _ -> error_loc _loc "ucheck: expected omega-type")
  | Cons u, Lollishrink(InT(_, Omega(InT(_, Val(tpx)))), InT(_, Omega(InT(_, Val(tpx'))))) -> 
      if not (tp_equal tpx tpx') then
        error_loc _loc "ucheck: cons argument stream types don't match"
      else
        ucheck senv uenv u tpx >>= (fun e ->
        return (compose e cons))
  | Cons u, _ -> error_loc _loc "ucheck: cons constructs function type"
  | _ -> usynth senv uenv (In(_loc, u)) >>= (fun (e, tpu'') ->
         if tp_equal tpu' tpu'' then return e
	 else mismatch _loc "ucheck" tpu' tpu'')

and usynth senv uenv (In(_loc, u)) =
  match u with 
  | Return u1 ->
      usynth senv uenv u1 >>= (fun (e1, tpu1) ->
      return(compose e1 guireturn, InT(_loc, Gui(tpu1))))
  | LetGui(x, u1, u2) -> 
      usynth senv uenv u1 >>= (fun (e1, InT(_, tpu1)) ->
      match tpu1 with
      | Gui tpu1' -> usynth senv ((x,tpu1') :: uenv) u2 >>= (fun (e2, tpu2) ->
		     match tpu2 with
		     | InT(_, Gui(_)) -> return (compose (pair id e1) (compose strength (bind (compose assocr e2))),
						 tpu2)
		     | _ -> error_loc _loc "usynth: expected Gui type in body")
      | _ -> error_loc _loc "usynth: expected Gui type in argument")
  | Fix u' ->
      usynth senv uenv u' >>= (fun (e, (InT(loc, tpu))) ->
      match tpu with
      | Lollishrink(InT(_, Omega(tps)), InT(_, Omega(tps'))) when tp_equal tps tps' ->
          return (compose e fix, InT(loc, Omega(tps)))
      | _ -> error_loc _loc "usynth: fixed point expected contractive map")
  | Var x -> error_at _loc 
               ((lookup uenv x) >>= (fun (e, tpu) ->
                return (compose pi2 e, tpu)))
  | EmbedF e ->
      return (curry (compose pi2 (discrete e)),
              InT(_loc, Lolli(InT(_loc, Discrete), InT(_loc, Discrete))))
  | Embed e ->
      return (compose one (compose oned (discrete (unitize e _loc))),
              InT(_loc, Discrete))
  | App(u1, u2) ->
      usynth senv uenv u1 >>= (fun (e1, (InT(_, tpu) as tpu')) -> 
      match tpu with
      | Lolli(tpu2, tpu1) ->
          ucheck senv uenv u2 tpu2 >>= (fun e2 ->
          return (compose (pair e1 e2) eval, tpu1))
      | Lollishrink(tpu2, tpu1) ->
          ucheck senv uenv u2 tpu2 >>= (fun e2 ->
          return (compose (pair e1 e2) eval', tpu1))
      | Discrete ->
	  ucheck senv uenv u2 tpu' >>= (fun e2 ->
	  return (compose (pair (compose e1 apply) e2) eval, tpu'))
      | _ -> error_loc _loc "usynth: expected lolli type")
  | Fst u ->
      usynth senv uenv u >>= (fun (e, (InT(_, tpu) as tpu')) ->
      match tpu with
      | Tensor(tpu1, tpu2) -> return (compose e pi1, tpu1)
      | Discrete -> return (compose e (compose paird' pi1), tpu')
      | _ -> error_loc _loc "usynth: expected tensor type")
  | Snd u -> 
      usynth senv uenv u >>= (fun (e, (InT(_, tpu) as tpu')) ->
      match tpu with
      | Tensor(tpu1, tpu2) -> return (compose e pi2, tpu2)
      | Discrete -> return (compose e (compose paird' pi2), tpu')
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
  | Cons u -> 
      usynth senv uenv u >>= (fun (e, tpx) ->
      let loc = loc_tp tpx in 
      return (compose e cons,
              InT(loc, Lollishrink(InT(loc, Omega(InT(loc, Val(tpx)))),
				   InT(loc, Omega(InT(loc, Val(tpx))))))))
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

and ucheck_shrink senv uenv uenv' (In(_loc, u) as u') (InT(_, tpu) as tpu') =
  match u, tpu with
  | Bracket u1, _ ->
      ucheck senv uenv u1 tpu' >>= (fun e1 -> 
      return (compose pi2 (compose e1 sweak)))
  | Lam(x, u2), Lolli(tpu1, tpu2) ->
      ucheck_shrink senv ((x, tpu1) :: uenv) uenv' u2 tpu2 >>= (fun e2 ->
      return (compose (curry (compose assocr e2)) swap))
  | Lam(x, u2), Lollishrink(tpu1, tpu2) ->
      ucheck_shrink senv uenv ((x, tpu1) :: uenv') u2 tpu2 >>= (fun e2 ->
      return (compose e2 scurry))
  | Lam(x, u2), _ -> error_loc _loc "ucheck_shrink: expected arrow type"
  | Pair(u1, u2), Tensor(tpu1, tpu2) ->
      ucheck_shrink senv uenv uenv' u1 tpu1 >>= (fun e1 ->
      ucheck_shrink senv uenv uenv' u2 tpu2 >>= (fun e2 ->
      return (compose (times e1 e2) spair)))
  | Pair(u1, u2), Discrete ->
      ucheck_shrink senv uenv uenv' u1 tpu' >>= (fun e1 ->
      ucheck_shrink senv uenv uenv' u2 tpu' >>= (fun e2 ->
      return (compose (times e1 e2) (compose spair (scomposer paird)))))
  | Pair(u1, u2), _ ->
      error_loc _loc "ucheck_shrink: expected tensor type"	
  | Unit, One -> 
      return (compose one sweak)
  | Unit, _ ->
      error_loc _loc "ucheck_shrink: expected I type"	
  | Stream s1, Omega tps1 ->
      scheck senv s1 tps1 >>= (fun e1 -> 
      return (compose pi1 (compose (omega e1) sweak)))
  | Stream s1, _ ->
      error_loc _loc "ucheck_shrink: expected stream type"	
  | Cons u1, Lollishrink(InT(_, Omega(InT(_, Val(tpx)))),
			 InT(_, Omega(InT(_, Val(tpx'))))) -> 
      if not (tp_equal tpx tpx') then
        error_loc _loc "ucheck_shrink: cons argument stream types don't match"
      else
	ucheck_shrink senv uenv uenv' u1 tpx >>= (fun e1 -> 
        return (compose e1 (scomposer cons)))
  | Cons u1, _ ->
      error_loc _loc "ucheck_shrink: cons constructs function type"
  | _ -> usynth_shrink senv uenv uenv' u' >>= (fun (e1, tpu'') ->
	 if tp_equal tpu' tpu'' then 
	   return e1
	 else
	   mismatch _loc "ucheck_shrink" tpu' tpu'')

and usynth_shrink senv uenv uenv' (In(_loc, u)) =
  match u with
  | Fix u1 ->
      usynth_shrink senv uenv uenv' u1 >>= (fun (e1, InT(_, tpu1)) -> 
      match tpu1 with 
      | Lollishrink(tpu2, tpu2') when tp_equal tpu2 tpu2' -> 
	  return (compose e1 (scomposer fix), tpu2)
      | _ -> error_loc _loc "usynth_shrink: fixed point expected contractive map")
  | Var x -> error_at _loc
               (lookup uenv x >>= (fun (e, tpu1) -> 
		return (compose pi2 (compose e sweak), tpu1)))
  | EmbedF e ->
      return (compose (curry (compose pi2 (discrete e))) sweak,
              InT(_loc, Lolli(InT(_loc, Discrete), InT(_loc, Discrete))))
  | Embed e ->
      return (compose (compose one (compose oned (discrete (unitize e _loc)))) sweak,
              InT(_loc, Discrete))
  | App(u1, u2) ->
      usynth_shrink senv uenv uenv' u1 >>= (fun (e1, (InT(_, tpu1) as tpu1')) -> 
      match tpu1 with
      | Lolli(tpu2, tpu1) ->
          ucheck_shrink senv uenv uenv' u2 tpu2 >>= (fun e2 ->
          let eval' = compose spair (scomposer eval) in 
          return (compose (pair e1 e2) eval', tpu1))
      | Lollishrink(tpu2, tpu1) ->
          ucheck senv (uenv' @ uenv) u2 tpu2 >>= (fun e2 ->
          let e2' = curry (compose assocr (compose (times id (reassoc uenv')) e2)) in
	  return (compose (pair e1 e2') seval, tpu1))
      | Discrete ->
	  ucheck senv (uenv' @ uenv) u2 tpu1' >>= (fun e2 ->
          let f = pair (compose e1 (scomposer apply)) e2 in
	  return (compose f (compose spair (scomposer eval)), tpu1'))
      | _ -> error_loc _loc "usynth: expected lolli type")
  | Fst u ->
      usynth_shrink senv uenv uenv' u >>= (fun (e, (InT(_, tpu) as tpu')) ->
      match tpu with
      | Tensor(tpu1, tpu2) -> return (compose e (scomposer pi1), tpu1)
      | Discrete -> return (compose e (scomposer (compose paird' pi1)), tpu')
      | _ -> error_loc _loc "usynth: expected tensor type")
  | Snd u -> 
      usynth_shrink senv uenv uenv' u >>= (fun (e, (InT(_, tpu) as tpu')) ->
      match tpu with
      | Tensor(tpu1, tpu2) -> return (compose e (scomposer pi2), tpu2)
      | Discrete -> return (compose e (scomposer (compose paird' pi2)), tpu')
      | _ -> error_loc _loc "usynth: expected tensor type")
  | Cons u1 -> 
      usynth_shrink senv uenv uenv' u1 >>= (fun (e1, tpu1) -> 
      return (compose e1 (scomposer cons),
	      let loc = loc_tp tpu1 in
	      InT(loc, Lollishrink(InT(loc, Omega(InT(loc, Val tpu1))),
				   InT(loc, Omega(InT(loc, Val tpu1)))))))
  | _ -> error_loc _loc "usynth_shrink: can't synthesize type"


(* The elaborate functions try and elaborate terms in the empty context *)

let elaborate u _loc =
  match usynth [] [] u with
  | Ok(e, tp) -> e "U" "C" "Dsl" _loc
  | Error(loc, msg) -> Loc.raise loc (Failure msg)

let elaborates s _loc =
  match ssynth [] s with
  | Ok(e, tp) -> e "C" "U" "Dsl" _loc
  | Error(loc, msg) -> Loc.raise loc (Failure msg)

