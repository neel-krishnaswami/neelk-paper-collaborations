module type MONAD =
sig
  (* A (somewhat redundant) signature for monads *)
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val unit : (unit -> 'a) -> 'a t
  val lift : ('a -> 'b t) -> 'a t -> 'b t

  val return : 'a -> 'a t
  val bind   : 'a t -> ('a -> 'b t) -> 'b t
  val join   : 'a t t -> 'a t 
end;;

module type DATAFLOW =
sig
  type 'a cell

  module Expr : sig
    include MONAD

    (* The operation to read a cell *)

    val read : 'a cell -> 'a t
    val newcell : 'a t -> 'a cell t

    (* local() lets you use some  local state in an expression. Obviously 
       this can be catastrophic if used carelessly (eg, if update() is 
       called inside a local) *)

    val local : (unit -> 'a) -> 'a t 
  end

  val newcell : 'a Expr.t -> 'a cell
  val update  : 'a cell -> 'a Expr.t -> unit

  val eval : 'a Expr.t -> 'a
end;;

module type CCC =
sig
  type ('a,'b) hom
  type one
  type ('a,'b) prod
  type ('a,'b) exp

  val id : ('a,'a) hom
  val compose : ('a,'b) hom -> ('b,'c) hom -> ('a,'c) hom

  val one : ('a,one) hom

  val fst : (('a,'b) prod, 'a) hom 
  val snd : (('a,'b) prod, 'b) hom 
  val pair : ('a,'b) hom -> ('a,'c) hom -> ('a, ('b,'c) prod) hom

  val curry : (('a,'b) prod, 'c) hom -> ('a, ('b,'c) exp) hom
  val eval : ((('a,'b) exp, 'a) prod, 'b) hom
end;;

module type COKLEISLI =
sig
  include CCC

  type ('a,'b) shrink
  val sweak     : ('a, ('b,'a) shrink) hom
  val spair     : ((('a,'b) shrink, ('a,'c) shrink) prod, ('a,('b,'c) prod) shrink) hom
  val scurry    : ((('a,'b) prod, 'c) shrink, ('a,('b,'c) shrink) shrink) hom
  val scomposer : ('a,'b) hom -> (('c,'a) shrink, ('c,'b) shrink) hom
  val scomposel : ('a,'b) hom -> (('b,'c) shrink, ('a,'c) shrink) hom
  val seval     : ((('a, ('b,'c) shrink) shrink, ('a,'b) exp) prod, ('a,'c) shrink) hom
  val swap      : (('a, ('b, 'c) shrink) exp, ('b, ('a, 'c) exp) shrink) hom 
  val swap'     : (('a, ('b, 'c) exp) shrink, ('b, ('a, 'c) shrink) exp) hom
  val eval'     : ((('a,'b) shrink, 'a) prod, 'b) hom
end;;

module type ULTRAMETRIC =
sig
  include CCC

  type 'a discrete
  val discrete : ('a -> 'b) -> ('a discrete, 'b discrete) hom

end;;

module type DSL =
sig
  module C : COKLEISLI   
  module U : ULTRAMETRIC 

  type 'a omega
  type 'a value

  (* Functorial actions *)

  val value : ('a,'b) U.hom -> ('a value, 'b value) C.hom
  val omega : ('a,'b) C.hom -> ('a omega, 'b omega) U.hom 

  (* Unit & counit *)

  val eta : ('a, 'a omega value) C.hom
  val varepsilon : ('a value omega, 'a) U.hom

  (* Monoidal structure *)

  val one'  : (U.one, C.one omega) U.hom 
  val prod  : (('a, 'b) C.prod omega, ('a omega, 'b omega) U.prod) U.hom
  val prod' : (('a omega, 'b omega) U.prod, ('a, 'b) C.prod omega) U.hom

  (* Compatibility with ML types *)

  val oned   : (U.one, unit U.discrete) U.hom
  val paird  : (('a U.discrete, 'b U.discrete) U.prod, ('a * 'b) U.discrete) U.hom
  val paird' : (('a * 'b) U.discrete, ('a U.discrete, 'b U.discrete) U.prod) U.hom

  (* Operations *)

  val cons : ('a, (('a value, 'b) C.exp, ('a value, 'b) C.shrink) C.exp omega) U.hom
  val fix : (('a,'a) C.shrink omega, 'a omega) U.hom

  (* Run things *)
  val run : ((C.one omega, U.one) U.prod, 'a U.discrete value omega) U.hom -> (unit -> 'a option)
  val run' : ((C.one omega, U.one) U.prod, 'a U.discrete) U.hom -> 'a
end;;

module Dataflow : DATAFLOW =
struct
  module Int = struct
    type t = int
    let compare = compare
  end
  module IntMap = Map.Make(Int)

  (* Generate unique ids *)

  let gen = ref 0
  let next() =
    let n = !gen in
    let () = gen := !gen + 1 in
      n

  (* The type of cells. *)

  type 'a cell = {
    value : 'a option ref;       (* The memoized value -- None if unready *)
    code  : 'a code ref;         (* The cell's expression *)
    ident : int;                 (* The unique id for the cell *)
    reads : ecell IntMap.t ref;  (* The cells that a ready cell has read *)
    obs   : ecell IntMap.t ref;  (* The cells that this cell is read by *)
  }

  (* Expressions are thunks returning a value and the cells read during the
     execution of the code expression *)

  and 'a code = (unit -> ('a * ecell IntMap.t))

  (* Some annoying gunk to simulate existentials with 
     universal types -- Haskell could do it directly, and OCaml 3.12
     could allow modules as values. *)

  and 'a cell_handler = {handler: 'b. 'b cell -> 'a}
  and ecell = {unpack: 'a. 'a cell_handler -> 'a}
  let pack cell = {unpack = fun h -> h.handler cell}

  (* Operations on existentially quantified cells follow *)

  let ident ecell = ecell.unpack {handler = fun c -> c.ident}
  let reads ecell = ecell.unpack {handler = fun c -> c.reads}
  let observers ecell = ecell.unpack {handler = fun c -> c.obs}

  let attach_observer ecell r =
    let map = observers r in map := IntMap.add (ident ecell) ecell !map

  let detach_observer ecell r = 
    let map = observers r in map := IntMap.remove (ident ecell) !map

  (* Treat IntMaps as sets *)

  let empty = IntMap.empty
  let (++) m1 m2 = IntMap.fold IntMap.add m1 m2
  let singleton ecell = IntMap.add (ident ecell) ecell IntMap.empty
  let setiter f ecells = IntMap.fold (fun _ ecell () -> f ecell) ecells ()

  module Expr = 
  struct 
    type 'a t = 'a code

    let map f m = fun () -> let (v, r) = m() in (f v, r)

    let unit x = fun () -> (x(), empty)
    let lift f m = fun () -> 
      let (v, s) = m() in
      let (v', s') = f v () in
      (v', s ++ s')

    let return v = unit (fun () -> v)
    let bind m f = lift f m
    let join mm = bind mm (fun m -> bind m return)

    (* When we read a cell, we check to see if it is memoized, 
       and return its value if it is. If it's not, then we 
       (1) execute its code, (2) set its value and reads fields,
       and (3) add it to the observer field of everything it read. *)

    let read cell = fun () ->
      let ecell = pack cell in  
      match !(cell.value) with
      | Some v -> (v, singleton ecell)
      | None ->
          begin
            let (v, rds) = !(cell.code)() in
            cell.value := Some v;
            cell.reads := rds;
            setiter (attach_observer ecell) rds;
            (v, singleton ecell)
          end

    let newcell code =
      unit (fun () -> 
	      let id = next() in
	      { value = (ref None);
		code = (ref code);
		ident = id;
		reads = (ref empty);
		obs = (ref empty) })


    let local thunk = fun () -> (thunk(), empty)
  end
    
  let newcell code = 
    let id = next() in
    { value = (ref None);
      code = (ref code);
      ident = id;
      reads = (ref empty);
      obs = (ref empty) }

  (* To invalidate a cell, we set its memoized value to None,
     remove it from the observers lists of everything it reads,
     and then recursively invalidate everything which reads it. *)
    
  let rec invalidate ecell =
    ecell.unpack { handler = fun cell -> 
      match !(cell.value) with
      | None -> ()
      | Some _ ->
          begin
            let rs = !(reads ecell) in
            let os = !(observers ecell) in
            cell.value := None;
            cell.reads := empty;
            cell.obs   := empty;
            setiter (detach_observer (pack cell)) rs;
            setiter invalidate os;
          end
   }

  let update cell code =
    begin
      cell.code := code;
      invalidate (pack cell)
    end

  let eval code = fst(code())
end;;


module Dsl : DSL =
struct 
  (* This module extends the datflow expression monad with some reader state 
     to make everything parametric in the clock and the update list. *)
  module Code =
  struct
    module D = Dataflow.Expr

    type clock = unit Dataflow.cell
    type updates = unit D.t list ref
    type state = clock * updates
    type 'a code = state -> 'a D.t 

    let return x s = D.return x 
    let read cell s = D.read cell
    let (>>=) m f s = D.bind (m s) (fun v -> f v s)
    let newref v s = D.local (fun () -> ref v)
    let get r s = D.local (fun () -> !r)
    let set r v s = D.local (fun () -> r := v)
    let local thunk s = D.local thunk

    let cell code s = D.newcell (code s)
    let clock (clock, _) = D.read clock
    let register cell (_, updates) =
      let poke = D.bind (D.read cell) (fun _ -> D.return ()) in
      updates := poke :: !updates;
      D.return ()

   (* Some utility functions for dealing with optionals *)
    let ozip = function 
      | Some x, Some y -> Some(x,y)
      | _ -> None

    let omap f = function
      | None -> None
      | Some v -> Some(f v)

    let (>>-) m f = m >>= (function None -> return None
			   | Some v -> f v)

    let (>>!) m f = m >>= (function None -> assert false
			   | Some v -> f v)
  end

  module U =
  struct
    open Code

    type one = unit
    type ('a,'b) prod = 'a * 'b
    type ('a,'b) exp = 'a -> 'b code
    type ('a,'b) hom = 'a -> 'b code
    type 'a discrete = 'a 

    let id x = return x
    let compose f g x = (f x) >>= (fun y -> g y)

    let one = fun _ -> return ()
    let fst = fun (a,b) -> return a
    let snd = fun (a,b) -> return b
    let pair f g a = (f a) >>= (fun u ->
                     (g a) >>= (fun v -> 
                     return (u,v)))
    let curry f  = fun a -> return (fun b -> f(a,b))
    let eval (f,x) = f x

    let discrete f x = return (f x)

  end
			  
  module C =
  struct
    open Code
    type 'a stream = 'a option Dataflow.cell

    type one = unit
    type ('a,'b) prod = 'a * 'b
    type ('a,'b) exp = 'a stream -> 'b stream code
    type ('a,'b) shrink = 'a stream -> 'b stream code
    type ('a,'b) hom = 'a stream -> 'b stream code

    (* This should be type-indexed, to get finer dependency tracking. In Haskell,
       we could use the type function mechanism to implement this!  
     *)

    let zip xs ys = (read xs) >>= (fun x' -> 
                    (read ys) >>= (fun y' ->
		      match x', y' with
		      | None, None
		      | Some _, Some _ -> cell ((read xs) >>= fun x' -> 
                                                (read ys) >>= fun y' ->
						return (ozip (x', y')))
		      | None, Some _ ->
			  (newref None) >>= (fun r ->
			  (cell ((read xs) >>= (fun x ->
				 (read ys) >>= (fun newval ->
				 (get r) >>= (fun oldval ->
				 (set r newval) >>= (fun () ->
				 return (ozip(x, oldval)))))))) >>= (fun xys ->
			  (register xys) >>= (fun () ->
			  return xys)))
		      | Some _, None -> 
			  (newref None) >>= (fun r ->
			  (cell ((read ys) >>= (fun y ->
				 (read xs) >>= (fun newval ->
				 (get r) >>= (fun oldval ->
				 (set r newval) >>= (fun () ->
				 return (ozip(oldval, y)))))))) >>= (fun xys ->
			  (register xys) >>= (fun () ->
			  return xys)))))

    let id xs = cell (read xs)
    let compose f g xs = (f xs) >>= (fun ys -> g ys)

    let one xs = cell(return(Some ()))
    let pair f g xs = (f xs) >>= (fun ys ->
		      (g xs) >>= (fun zs ->
			zip ys zs))
    let fst abs = cell ((read abs) >>- (fun (a,b) -> return (Some a)))
    let snd abs = cell ((read abs) >>- (fun (a,b) -> return (Some b)))
    let eval fxs = (fst fxs) >>= (fun fs ->
		   (snd fxs) >>= (fun xs ->
		   cell ((read fs) >>- (fun f -> (f xs) >>= read))))
    let curry f = fun xs -> cell(read xs >>- (fun _ -> 
                                 return (Some(fun ys -> (zip xs ys) >>= f))))

    let sweak xs = cell(return(Some(fun ys -> return xs)))
    let spair fgs = cell((read fgs) >>- (fun (f,g) -> return(Some(pair f g))))
    let scurry fs = cell(return(Some(fun xs -> 
                    cell(return(Some(fun ys ->
		    cell(read fs >>- (fun f -> 
                         zip xs ys >>= (fun xys -> 
                         f xys >>= read)))))))))

		      
    let scomposer f gs = cell(read gs >>- (fun g -> return(Some(compose g f))))
    let scomposel f gs = cell(read gs >>- (fun g -> return(Some(compose f g))))

    let seval fgs = cell(read fgs >>- (fun (f,g) ->
			 return(Some(fun gammas ->
				       (g gammas) >>= (fun bs ->
				       (f gammas) >>= (fun hs ->
					 cell((read hs) >>- (fun h ->
                                              (h bs) >>= (fun cs ->
					      read cs)))))))))

(*			   
    let seval fgs = cell(read fgs >>- (fun (f, g) -> 
                         return(Some(fun xs -> (g xs) >>= (fun ys ->
					       (f xs) >>= (fun hs ->
					       (zip hs ys) >>= (fun hys ->
						 eval hys)))))))
*)

    let swap fs =
      (curry (curry (compose
		       (pair (compose (pair (compose fst fst) snd) eval)
			     (compose fst snd))
		       eval)))
      fs
    let swap' = swap

    let eval' = eval
  end

  type 'a omega = 'a option Dataflow.cell
  type 'a value = 'a

  open Code

  let value uhom = fun xs -> cell((read xs) >>- (fun x -> 
                                  (uhom x) >>= (fun v -> 
				  return(Some v))))
  let omega chom = fun xs -> chom xs

  let eta xs = cell((read xs) >>- (fun _ -> return (Some xs)))
  let varepsilon xs = read xs >>= (function
				     | None -> assert false
				     | Some x -> return x)

  let one' () = cell(return(Some()))
  let prod xys = 
    cell(read xys >>= (function
      | None -> assert false
      | Some(x,y) -> return(Some x))) >>= (fun xs -> 
    cell(read xys >>= (function
      | None -> assert false
      | Some(x,y) -> return(Some y))) >>= (fun ys ->
    return (xs, ys)))

  let prod' (xs,ys) = cell(read xs >>= (fun x' -> 
			   read ys >>= (fun y' ->
			   match x', y' with
			   | Some x, Some y -> return (Some(x,y))
			   | _ -> assert false)))
					

  let oned () = return ()
  let paird (a, b) = return (a, b)
  let paird' (a, b) = return (a, b)

  let cons x =
    cell(return(Some(fun fs ->
    cell((read fs) >>! (fun _ -> 
	 return(Some(fun ys -> 
                        (newref (Some x)) >>= (fun r ->
                        (cell((get r) >>= (fun old ->
                              (read ys) >>= (fun newval ->
                              match old with
                              | None -> return newval
                              | Some _ -> 
                                 (set r newval) >>= (fun () -> 
                                  return old)))))
                        >>= (fun zs ->
                        (register zs) >>= (fun () ->
			(read fs) >>! (fun f -> 
			f zs)))))))))))

  let fix fs = (read fs) >>= (function None -> assert false
		| Some f ->
	       (newref None) >>= (fun r -> 
               (cell(clock >>= (fun () -> get r))) >>= (fun input ->
               (register input) >>= (fun () -> 
	       (f input) >>= (fun pre -> 
               (cell(clock >>= (fun () ->
                     (read input) >>= (fun _ ->
		     (read pre) >>= (fun v ->
		     (set r v) >>= (fun () ->
		     return v)))))) >>= (fun output ->
	       (register output) >>= (fun () -> 
	       return output)))))))

  let run umor =
    let clock = Dataflow.newcell (Dataflow.Expr.return ()) in
    let updates = ref [] in
    let unit = Dataflow.newcell (Dataflow.Expr.return (Some ())) in 
    let output = Dataflow.eval (umor (unit, ()) (clock, updates))  in
    let step () =
      begin
	Dataflow.update clock (Dataflow.Expr.return ());
	let v = Dataflow.eval (Dataflow.Expr.read output) in
	(List.iter Dataflow.eval !updates; v)
(*
	match Dataflow.eval (Dataflow.Expr.read output) with
	| None -> assert false
	| Some v -> (List.iter Dataflow.eval !updates; v)
*)
      end
    in
    step      

  let run' umor = 
    let clock = Dataflow.newcell (Dataflow.Expr.return ()) in
    let updates = ref [] in
    let unit = Dataflow.newcell (Dataflow.Expr.return (Some ())) in 
    Dataflow.eval (umor (unit, ()) (clock, updates))


end;;

(*









  (* TODO...
(* TODO
  type 'a gui 
  val return   : ('a, 'a gui) hom
  val bind     : ('a, 'b gui) hom -> ('a gui, 'b gui) hom
  val strength : (('a, 'b gui) prod, ('a,'b) prod gui) hom
  val button   : (string discrete omega, bool discrete omega gui) hom
  val checkbox : (string discrete omega, bool discrete omega gui) hom
  val label    : (string discrete stream, one gui) hom
  val vstack   : ('a gui, 'a gui) hom 
  val hstack   : ('a gui, 'a gui) hom 
*)

    type 'a gui = (GObj.widget -> unit) -> 'a

    let bind m f attach -> f (m attach) attach
    let strength (a, bgui) attach = return (a, bgui attach)

    let button labels attach =
      (local (fun () -> GButton.button ~packing:attach ())) >>= (fun b ->
      (cell (return (Some false))) >>= (fun bsig ->
      (cell ((read labels) >>= (function
		| Some msg -> local (fun () -> b#set_label msg)
		| None -> return ()))) >>= (fun setlabel ->
      (local (b#connect#pressed
		~callback:(fun () -> Dataflow.update bsig (return (Some true))))) >>= (fun _ -> 
      (local (b#connect#released
		~callback:(fun () -> Dataflow.update bsig (return (Some false))))) >>= (fun _ ->
      (register setlabel) >>= (fun () ->
      return bsig))))))

    let checkbok labels attach =
      (local (fun () -> GButton.check_button ~packing:attach ())) >>= (fun b ->
      (cell(return (Some false))) >>= (fun bsig -> 
      (cell((read labels) >>= (function 
                 Some msg -> local (fun () -> b#set_label msg)
	       | None -> return ()))) >>= (fun setlabel -> 
      (local (b#connect#toggled
		~callback:(fun () ->
			     let b = Dataflow.eval (read bsig) in 
			     Dataflow.update bsig (return (omap not b))))) >>= (fun () -> 
      (register setlabel) >>= (fun () -> 
      return bsig)))))

    let label labels attach  =
      (local (fun () -> GMisc.label ~packing:attach ())) >>= (fun w ->
      (cell((read labels) >>= (function
	      | None -> return ()
	      | Some msg -> Dataflow.Expr.local (fun () -> w#set_text msg)))) >>= (fun setlabel -> 
      (register setlabel) >>= (fun () ->
      return w)))

    let vstack gui attach = 
	(local (fun () -> GPack.vbox ~packing:attach ())) >>= (fun box -> 
	return (gui box#add))

    let hstack gui attach = 
	(local (fun () -> GPack.hbox ~packing:attach ())) >>= (fun box -> 
	return (gui box#add))

    let gfix f =
      fun b clock attach rs -> 
	let r = ref None in
	let xin = newcell ((read clock) >>= (fun () -> (get r))) in
	let ((xout', b'), rs) = f (xin, b) clock attach rs in
	let xout = newcell ((read xout') >>= (fun x ->
                            (set r x) >>= (fun () ->
                            return x))) in
	let r = newcell ((read xout) >>= (fun _ -> return ())) in 
	((xout, b'), r :: rs)

  let return x attach = x

  let guirun f =
    let clock = Dataflow.newcell (Dataflow.Expr.return ()) in
    let w = GWindow.window ~border_width:10 () in
    let _ = w#connect#destroy ~callback:GMain.Main.quit in
    let v = GPack.vbox ~packing:w#add () in 
    let ((), refreshes) = f () clock v#add [] in
    let _ = GMain.Idle.add
            (fun () -> List.iter (fun c -> Dataflow.eval (read c)) refreshes; true) in
    let _ = w#show () in 
    GMain.Main.main ()
  | Let(x, s1, s2), _ -> 
      usynth senv uenv s1 >>= (fun (e1, tpu1) ->
      ucheck senv ((x,tpu1) :: uenv) s2 tpu >>= (fun e2 ->
      return (compose (pair id e1) e2)))
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
*)



module DslTest =
struct
  open Dsl

  let zero () = 0
  let succ n = n + 1

  let ($) = U.compose

  (* The least efficient way to generate a stream of zeros known to man *)
  let zeros = oned $ U.discrete zero $ cons $ fix

  (* More interesting examples than this need the DSL, or your eyes will bleed.... *)
end



module type METRIC =
sig
  type one
  type ('a,'b) prod
  type ('a,'b) exp
  type ('a,'b) shrink
  type 'a value
  type 'a stream (* Corresponds to 'a value stream in the paper; this is an efficiency hack *)
  type 'a gui (* The GUI monad does not have a denotational semantics yet *)

  type ('a,'b) hom
  type ('a,'b) contract

  val id : ('a,'a) hom
  val compose : ('a,'b) hom -> ('b,'c) hom -> ('a,'c) hom 

  val one : ('a, one) hom

  val prod : ('a,'b) hom -> ('c,'d) hom -> (('a,'c) prod, ('b,'d) prod) hom
  val fst  : (('a,'b) prod, 'a) hom 
  val snd  : (('a,'b) prod, 'b) hom
  val pair : ('a,'b) hom -> ('a,'c) hom -> ('a, ('b,'c) prod) hom

  val exp : ('a,'b) hom -> ('c,'d) hom -> (('b,'c) exp, ('a,'d) exp) hom
  val curry : (('a,'b) prod, 'c) hom -> ('a, ('b,'c) exp) hom
  val apply : ((('a,'b) exp, 'a) prod, 'b) hom
 
  val scomposel : ((('a,'b) exp, ('b,'c) shrink) prod, ('a,'c) shrink) hom 
  val scomposer : ((('a,'b) shrink, ('b,'c) exp) prod, ('a,'c) shrink) hom
  val spair     : ((('a,'b) shrink, ('a,'c) shrink) prod, ('a, ('b,'c) prod) shrink) hom
  val sunit     : ('a, ('b, one) shrink) hom
  val sweak     : ('a, 'b) hom -> ('a, ('c, 'b) shrink) hom 
  val sapply    : ('a, ((('b,'c) shrink, 'b) prod, 'c) shrink) hom
  val scurry    : ((('a,'b) prod, 'c) shrink, ('a, ('b, 'c) shrink) shrink) hom 
  val suncurry  : (('a, ('b, 'c) shrink) shrink, (('a,'b) prod, 'c) shrink) hom 
                 
  val value : ('a -> 'b) -> ('a value, 'b value) hom
  val embed : 'a -> ('b, 'a value) hom 
  val cart  : (('a * 'b) value, ('a value, 'b value) prod) hom
  val cart' : (('a value, 'b value) prod, ('a * 'b) value) hom
  val unit  : (one, unit value) hom 

  val stream : ('a -> 'b) -> ('a stream, 'b stream) hom
  val cons   : (('a value, 'a stream) prod, 'a stream) contract
  val dist   : (('a stream, 'b stream) prod, ('a * 'b) stream) hom 
  val dist'  : (('a * 'b) stream, ('a stream, 'b stream) prod) hom 
  val unfold : 'a -> ('a -> 'b * 'a) -> (one, 'b stream) hom

  val cons'   : 'a -> ('a stream, 'a stream) hom

  (* check coerces a hom to a contraction *)

  val check : ('a,'b) hom -> ('a,'b) contract option

  (* fix is written as a "Conway operator" rather than a pure fixed point, 
     because iterated fixed points are more efficient this way. Using Bekic's
     lemma results in code and computation duplication.... *)

  val fix   : (('a stream, 'b) prod, ('a stream, 'b) prod) contract -> ('b, ('a stream, 'b) prod) hom

  val return   : ('a, 'a gui) hom
  val bind     : ('a, 'b gui) hom -> ('a gui, 'b gui) hom
  val strength : (('a, 'b gui) prod, ('a,'b) prod gui) hom
  val button   : (string stream, bool stream gui) hom
  val checkbox : (string stream, bool stream gui) hom
  val label    : (string stream, one gui) hom
  val vstack   : ('a gui, 'a gui) hom 
  val hstack   : ('a gui, 'a gui) hom 
  val gfix     : (('a stream,'b) prod, ('a stream,'b) prod gui) contract -> 
                 ('b, ('a stream,'b) prod gui) hom

  val run : (one, 'a stream) hom -> (unit -> 'a)
  val guirun : (one, one gui) hom -> unit 
end;;



module Metric : METRIC =
struct 
  let read = Dataflow.Expr.read
  let (>>=) = Dataflow.Expr.bind
  let return = Dataflow.Expr.return
  let local = Dataflow.Expr.local
  let newcell = Dataflow.newcell

  type clock = unit Dataflow.cell
  type 'a builder = clock -> 'a 

  type ('a,'b) hom = 'a -> 'b builder
  type ('a,'b) contract = ('a,'b) hom 

  type one = unit
  type ('a,'b) prod = 'a * 'b
  type ('a,'b) exp = ('a,'b) hom
  type ('a,'b) shrink = ('a,'b) hom
  type 'a value = 'a 
  type 'a stream = 'a option Dataflow.cell
  type refreshes = unit Dataflow.cell list 
  type 'a gui = (GObj.widget -> unit) -> refreshes -> 'a * refreshes
    
  let id = fun x clock -> x
  let compose f g =
    fun x clock -> g (f x clock) clock

  (* maps into the unit type are always contractive *)
  let one = fun x clock -> ()

  let prod f g =
    fun (x,y) clock -> (f x clock, g y clock)

  let fst' = Pervasives.fst
  let snd' = Pervasives.snd

  let fst = fun (a, b) clock -> a
  let snd = fun (a, b) clock -> b

  let pair f g =
    fun x clock -> (f x clock, g x clock)

  let exp f h = fun g clock -> compose f (compose g h)
  let curry f = fun x clock -> fun y -> f (x, y)
  let apply = fun (f, x) clock -> f x clock

  let scomposel = fun (f,g) clock -> compose f g 
  let scomposer = fun (f,g) clock -> compose f g 
  let spair = fun (f,g) clock -> pair f g
  let sunit = fun _ clock -> fun _ clock -> ()
  let sweak f = fun a clock -> (fun c clock -> f a clock)
  let sapply = fun _ clock -> fun (f, b) clock -> f b clock
  let scurry f clock = fun a clock b clock -> f (a,b) clock
  let suncurry f clock = fun (a,b) clock -> f a clock b clock

  let value f = fun x clock -> f x
  let embed x = fun _ clock -> x

  let cart    = fun (a,b) clock -> (a,b)
  let cart'   = fun (a,b) clock -> (a,b)
  let unit    = fun () clock -> ()

  let get r = local (fun () -> !r)
  let set r v = local (fun () -> r := v)
  let omap f = function None -> None | Some x -> Some (f x)


  let stream f : ('a stream, 'b stream) hom = 
    fun xs clock ->
      newcell ((read xs) >>= (fun x -> return (omap f x)))
    
  let dist =
     fun (xs, ys) clock ->
       newcell ((read xs) >>= (fun x -> 
                (read ys) >>= (fun y ->
                match (x, y) with
                | (Some x, Some y) -> return (Some(x,y))
                | _                -> return None)))

  let dist' =
     fun xys clock ->
       let xs = newcell ((read xys) >>= (fun xy -> return (omap fst' xy))) in 
       let ys = newcell ((read xys) >>= (fun xy -> return (omap snd' xy))) in 
       (xs, ys)
                
  (* Now that we've dropped the indices, this is unsafe *)

  let check f = Some f 

 (* cons (x, xs) adds x to the front of a stream, replacing up to one 
    null value. (We treat the ref as a 1-place buffer.) *)

  let cons =
    fun (x, xs) clock ->
      let r = ref (Some x) in
      newcell ((get r) >>= (function
                | None -> read xs
                | Some old ->
                    (read xs) >>= (fun x ->
                    (set r x) >>= (fun () ->
                    return (Some old)))))
    
 (* Now, the way the fixed point works is that it passes in a cell
    which will return None on the first time step. Since f is contractive,
    we know the result of applying f will return a value which doesn't
    really look at the input cell on the first time step. Therefore we 
    can pass in something that returns None at time 0.

    The input is clocked, since we are diking out the input signal and 
    can't rely on "asynchronous time" to make things work. 
 *)
    
  let fix f =
    fun b clock ->
      let r = ref None in
      let xin = newcell ((read clock) >>= (fun () -> (get r))) in
      let (xout', b') = f (xin, b) clock in
      let xout =  newcell ((read xout') >>= (fun x ->
                          (set r x) >>= (fun () ->
                          return x))) in
      (xout, b')

 (* unfold creates a stream from a seed and a step function. This is 
    also clocked because we need a source of time to decide when to 
    update the ref cell and advance the state. *)

  let unfold seed f =
    fun () clock ->
      let r = ref seed in
      newcell ((read clock) >>= (fun () -> 
               (get r) >>= (fun s ->
               let (v, s) = f s in
               (set r s) >>= (fun () ->
               return (Some v)))))

  let cons' x = fun xs -> cons (x, xs)

  (* The GUI monad! 'a gui values are functions which take a function to
     attach a widget to a parent as an argument, and then return a list of 
     unit cells which may need to be refreshed at each timestep (to reflect 
     updates to the gui). 

     It might be worth building the idea of eager cells/actions/etc into 
     the underlying dataflow library, rather than building them up the 
     way we're doing here. It would require a rethink/respec of the lower
     level though. 
  *)


  (* ('a, 'b gui) hom == 
     int * ('a -> (clock -> widget -> refreshes -> 'b * refreshes)) *)

  let bind f =
    fun agui clock attach rs ->
      let (a, rs) = agui attach rs in
      let (b, rs) = f a clock attach rs in
      (b, rs)
       
  let strength =
    fun (a, bgui) clock attach rs ->
      let (b, rs) = bgui attach rs in
      ((a,b), rs)

  let button =
    fun labels clock attach rs ->
      let b = GButton.button ~packing:attach () in
      let bsig = Dataflow.newcell (return (Some false)) in
      let setlabel = newcell ((read labels) >>= (function
                     | Some msg -> Dataflow.Expr.local (fun () -> b#set_label msg)
                     | None     -> return ())) in
      let _ = b#connect#pressed
        ~callback:(fun () ->
                     Dataflow.update bsig (return (Some true));
                     Dataflow.update clock (return ())) in 
      let _ = b#connect#released
        ~callback:(fun () ->
                     Dataflow.update bsig (return (Some false));
                     Dataflow.update clock (return ())) in
      (bsig, setlabel :: rs)

  let checkbox =
    fun labels clock attach rs ->
      let b = GButton.check_button ~packing:attach () in
      let bsig = Dataflow.newcell (return (Some false)) in
      let setlabel = newcell ((read labels) >>= (function
                     | Some msg -> Dataflow.Expr.local (fun () -> b#set_label msg)
                     | None     -> return ())) in
      let _ = b#connect#toggled
        ~callback:(fun () ->
                     let b = Dataflow.eval (read bsig) in 
                     Dataflow.update bsig (return (omap not b));
                     Dataflow.update clock (return ())) in 
      (bsig, setlabel :: rs)

  let label =
    fun labels clock attach rs ->
      let w = GMisc.label ~packing:attach () in 
      let settext = newcell ((read labels) >>= (function
                     | Some msg -> Dataflow.Expr.local (fun () -> w#set_text msg)
                     | None     -> return ())) in
      ((), settext :: rs)

  let vstack =
    fun gui clock attach rs ->
      let box = GPack.vbox ~packing:attach () in
      gui box#add rs
       
  let hstack =
    fun gui clock attach rs ->
      let box = GPack.hbox ~packing:attach () in
      gui box#add rs

  let gfix f =
    fun b clock attach rs -> 
      let r = ref None in
      let xin = newcell ((read clock) >>= (fun () -> (get r))) in
      let ((xout', b'), rs) = f (xin, b) clock attach rs in
      let xout = newcell ((read xout') >>= (fun x ->
                          (set r x) >>= (fun () ->
                          return x))) in
      let r = newcell ((read xout) >>= (fun _ -> return ())) in 
      ((xout, b'), r :: rs)


  let return = fun a clock attach rs -> (a, rs)

  let guirun f =
    let clock = newcell (Dataflow.Expr.return ()) in
    let w = GWindow.window ~border_width:10 () in
    let _ = w#connect#destroy ~callback:GMain.Main.quit in
    let v = GPack.vbox ~packing:w#add () in 
    let ((), refreshes) = f () clock v#add [] in
    let _ = GMain.Idle.add
            (fun () -> List.iter (fun c -> Dataflow.eval (read c)) refreshes; true) in
    let _ = w#show () in 
    GMain.Main.main ()

  let run f =
    let clock = newcell (Dataflow.Expr.return ()) in
    let xs = f () clock in 
    fun () ->
      (Dataflow.update clock (Dataflow.Expr.return ());
       match Dataflow.eval (read xs) with
       | Some v -> v
       | None   -> assert false)
end

module GuiTest =
struct
  open Metric
  let ($) = compose
  let lift = bind
  let const x = unfold () (fun () -> (x, ()))
  let bool2str b = if b then "True" else "False"
  let bool2int b = if b then 1 else 0 
  let gui f = lift (f $ return)
  let gstream f = gui (stream f)
  let finish () = one $ return

  let sum (x,y) = x + y


  let contract g =
    match check g with 
    | Some f -> f
    | None -> assert false

  let fix' f = (fix (contract (prod f one))) $ fst
  let gfix' f = (gfix (contract (fst $ f $ gui (pair id one)))) $ gui fst 

  let succ = value (fun n -> n + 1)

  let w0 = (const "Hello") $ label $ bind ((const "World") $ label) $ hstack

  let w0' = (const "Hello") $ label $ bind ((const "World") $ label) $ vstack

  let w2 = (const "Click me") $ button $ gui one

  let w3 = (const "Click me") $ button $ (gstream bool2str) $ (lift label) $ gui one

  let w4 = (gfix' (button $ (gstream bool2str))) $ gui one 

  let w5 = (gfix' (cons' "Not yet clicked" $ button $ (gstream bool2str))) $ gui one 

  let w6 = (gfix' (checkbox $ (gstream bool2str))) $ gui one

end
*)

