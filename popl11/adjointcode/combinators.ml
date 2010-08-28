open Camlp4.PreCast

type ast = string -> string -> string -> Ast.loc -> Ast.expr

let id0 id : ast = fun m m' p _loc ->
  <:expr< ($uid:p$ . $uid:m$ . $lid:id$) >>;;
let id1 id (f : ast) : ast = fun m m' p _loc ->
  <:expr< $uid:p$ . $uid:m$ . $lid:id$ $(f m m' p _loc)$>>;;
let id2 id (f1 : ast) (f2 : ast) : ast = fun m m' p _loc ->
  <:expr< ($uid:p$ . $uid:m$ . $lid:id$ $(f1 m m' p _loc)$ $(f2 m m' p _loc)$) >>;;

let id0' id : ast = fun m m' p _loc ->
  <:expr< ($uid:p$ . $lid:id$) >>;;
let id1' id (f : ast) : ast = fun  m m' p _loc ->
  <:expr< $uid:p$ . $lid:id$ $(f m m' p _loc)$>>;;
let id2' id (f1 : ast) (f2 : ast) : ast = fun  m m' p _loc ->
  <:expr< ($uid:p$ . $lid:id$ $(f1 m m' p _loc)$ $(f2 m m' p _loc)$) >>;;


let id = id0 "id"
let compose = id2 "compose"
let one = id0 "one"
let pair = id2 "pair"
let pi1 = id0 "fst"
let pi2 = id0 "snd"
let curry = id1 "curry"
let eval = id0 "eval"
let cons = id0 "cons"
let head = id0 "head"
let tails = id0 "tails"
let stream = id1 "stream"
let cons = id0 "cons"
let fix = id0 "fix"
let sweak = id0 "sweak"
let spair = id0 "spair"
let scurry = id0 "scurry"
let seval = id0 "seval"
let swap = id0 "swap"
let scomposel = id1 "scomposel"
let scomposer = id1 "scomposer"
let eval' = id0 "eval'"
let tensor = id2 "tensor"
let rho = id0 "rho"
let lambda = id0 "lambda"
let rho' = id0 "rho'"
let lambda' = id0 "lambda'"
let assocl = id0 "assocl"
let assocr = id0 "assocr"
let sym = id0 "sym"

let flip (f : ast) : ast = fun m m' -> f m' m 

let one'  = id0' "one'"
let oned  = id0' "oned"
let prod  = id0' "prod"
let prod' = id0' "prod'"

let paird = id0' "paird"
let paird' = id0' "paird'"
let apply = id0' "apply"

let varepsilon = id0' "varepsilon"
let eta = id0' "eta"

let f e = id1' "f" (flip e)
let g e = id1' "g" (flip e)

let discrete e = id1 "discrete" (fun _ _ _ _ -> e)
let unitize e _loc =  <:expr< fun () -> $e$>>

let times f g = pair (compose pi1 f) (compose pi2 g) 
let passocr =
  pair (compose pi1 pi1) (pair (compose pi1 pi2) pi2)
let passocl =
  pair (pair pi1 (compose pi2 pi1)) (compose pi2 pi2)

let uncurry =
  curry(compose
	  (pair
	     (compose
		(pair pi1 (compose pi2 pi1))
                eval)
             (compose pi2 pi2))
          eval)

(* Reassociating environments, to move contractive 
   hypotheses into and out of the regular context *)

let rec reassoc = function
  | [] -> pi1 
  | _ :: gamma -> compose passocl (times (reassoc gamma) id)
