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
end

module type SMCC =
sig
  type ('a,'b) hom
  type one
  type ('a,'b) tensor
  type ('a,'b) lolli

  val id : ('a,'a) hom
  val compose : ('a,'b) hom -> ('b,'c) hom -> ('a,'c) hom

  val tensor : ('a,'b) hom -> ('a,'c) hom -> ('a, ('b,'c) tensor) hom
  val rho    : (('a, one) tensor, 'a) hom
  val lambda : ((one, 'a) tensor, 'a) hom
  val assocl : ((('a, 'b) tensor, 'c) tensor, ('a, ('b, 'c) tensor) tensor) hom
  val assocr : (('a, ('b, 'c) tensor) tensor, (('a, 'b) tensor, 'c) tensor) hom
  val sym    : (('a,'b) tensor, ('b, 'a) tensor) hom 

  val curry : (('a,'b) tensor, 'c) hom -> ('a, ('b,'c) lolli) hom
  val eval : ((('a,'b) lolli, 'a) tensor, 'b) hom
end

module type CONTRACTIVE =
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
end

module type ULTRAMETRIC =
sig
  include CONTRACTIVE 

  type ('a,'b) sum
  val inl : ('a, ('a,'b) sum) hom
  val inr : ('b, ('a,'b) sum) hom
  val case : ('a,'b) hom -> ('c,'b) hom -> (('a,'c) sum, 'b) hom 

  type 'a discrete
  val discrete : ('a -> 'b) -> ('a discrete, 'b discrete) hom
  val const : 'a -> ('b, 'a discrete) hom

  type 'a stream
  val head : ('a stream, 'a) hom
  val tails  : ('a stream, 'a stream stream) hom
  val stream :  ('a,'b) hom -> ('a stream, 'b stream) hom 
  val cons  : ('a, ('a stream, 'a stream) shrink) hom 
  val fix   : (('a stream, 'a stream) shrink, 'a stream) hom
end

module type GUI = SMCC

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
  let return' x s = D.return (Some x)

  let read cell s = D.read cell
  let (>>=) m f s = D.bind (m s) (fun v -> f v s)
  let newref v s = D.local (fun () -> ref v)
  let get r s = D.local (fun () -> !r)
  let set r v s = D.local (fun () -> r := v)
  let local thunk s = D.local thunk

  let get_clock (clock, _) = D.return clock

  let cell code s = D.newcell (code s)
  let clock (clock, _) = D.read clock
  let register cell (_, updates) =
    let poke = D.bind (D.read cell) (fun _ -> D.return ()) in
    updates := poke :: !updates;
    D.return ()

  let fix f s =
    D.fix (fun c -> f (fun _ -> c) s)

 (* Some utility functions for dealing with optionals *)
  let ozip = function 
    | Some x, Some y -> Some(x,y)
    | _ -> None

  let omap f = function
    | None -> None
    | Some v -> Some(f v)

  let ofold none some = function
    | None -> none
    | Some v -> some v

  let (>>-) m f = m >>= (function None -> return None
                         | Some v -> f v)

  let (>>!) m f = m >>= (function None -> assert false
                         | Some v -> f v)
end


module U =
struct
  (* The strict implementation of ultrametrics...this is much better, but 
     the proof isn't finished yet. *)
  open Code

  type one = unit
  type ('a,'b) prod = 'a * 'b
  type ('a,'b) sum = Inl of 'a | Inr of 'b 
  type 'a discrete = 'a 

  (* Note that contractives and ordinary functions are *different* types. 
     Shrinking maps are lazy, and ordinary maps are strict, and furthermore,
     shrinking maps never fail! *)
  type ('a,'b) exp = 'a -> 'b option code
  type ('a,'b) hom = 'a -> 'b option code
  type ('a,'b) shrink = 'a option code-> 'b code

  (* The implementation of GTK guis! *)
  type 'a gui = (GObj.widget -> unit) -> 'a option code 

  let id x = return' x
  let compose f g = fun x -> f x >>- g 
  let one = fun _ -> return' ()
  let pair f g = fun at -> f at >>- (fun a ->
                           g at >>- (fun b ->
                           return' (a,b)))
  let fst = fun (a,b) -> return' a
  let snd = fun (a,b) -> return' b 

  (* Double-check case... *)

  let inl = fun v -> return' (Inl v)
  let inr = fun v -> return' (Inr v)

  let case (f : ('a,'b) hom) (g : ('c,'b) hom) = function
    | Inl v -> f v
    | Inr v -> g v

  let curry f = fun a -> return'(fun b -> f(a,b)) 

  let eval (f,x) = f x

  let discrete f = fun x -> return' (f x)

  let const x = fun _ -> return' x
    
  (* The contractive operations must be implemented lazily, since  
     we need to be able to re-evaluate the input in case it is 
     currently undefined. Also, we need to impedance-match options & 
     non-options. 
  *)
  let sweak = fun x -> return' (fun _ -> return x)

  let spair = fun (f,g) -> return' (fun xt -> f xt >>= (fun y ->  
                                              g xt >>= (fun z -> 
                                              return (y,z))))
  let scurry = fun f -> return' (fun at -> 
                                   return (fun bt -> f (at >>- (fun a ->
                                                        bt >>- (fun b ->
                                                        return' (a,b))))))
  let eval' (f,x) = f (return' x) >>= return'

  let seval (shrink, f) = return' (fun xs -> shrink xs >>= (fun g -> 
                                             g (xs >>- f)))
 
  let swap f = return' (fun yst -> return (fun x -> f x >>- (fun g -> 
                                                    g yst >>= return')))

  (* The swap' direction is not trivially implementable, give the 
     representation I have chosen. Luckily, we don't need it! *)

  let swap' f = assert false

  (* Right composition relies on the fact that even noncontrative things
     promise to return Some value when given a proper value. *)

  let scomposer f = fun g -> return' (fun cthunk -> g cthunk >>= (fun a -> 
                                                    f a >>= (fun b' -> 
                                                    match b' with
                                                    | None -> assert false
                                                    | Some b -> return b)))
  let scomposel (f : ('a,'b) hom) = fun (g : ('b,'c) shrink) ->
    return' (fun bthunk -> g (bthunk >>- f))

  (* Stream operations *)
  type 'a stream = 'a option Dataflow.cell

  let stream (f : ('a,'b) hom) : ('a stream, 'b stream) hom =
    fun xs ->  (cell(read xs >>- f)) >>= (fun v -> return (Some v))

  let head xs = read xs 

  let tails : ('a stream, 'a stream stream) hom =
    fun xs -> cell((read xs) >>- (fun _ -> return (Some xs))) >>= return'

  let cons (x : 'a) = 
   return'(fun xst -> 
            newref (Some x) >>= (fun (r : 'a option ref) ->
            newref None >>= (fun (xsr : 'a option Dataflow.cell option ref) ->  
            cell(get xsr >>= fun v ->
                (match v with
                 | Some xs -> return(Some xs)
                 | None -> xst >>= (fun xs' ->
                           set xsr xs' >>= (fun () ->
                           return xs'))) >>= (fun (xs' : 'a option Dataflow.cell option) ->
                 ofold (return None) read xs' >>= (fun (newval : 'a option) -> 
                  get r >>= (fun (oldval : 'a option) ->
                 (match oldval with
                 | None -> return newval
                 | Some _ -> set r newval >>= (fun () ->
                             return oldval)))))) >>= (fun output ->
            register output >>= (fun () ->
            return output)))))
     
  let fix (f : ('a stream, 'a stream) shrink) =
      newref None >>= (fun (r : 'a option ref) ->
      cell(clock >>= (fun () -> get r)) >>= (fun (input : 'a stream) -> 
      register input >>= (fun () -> 
      f (return (Some input)) >>= (fun (pre : 'a stream) -> 
      cell(clock >>= (fun () ->
           read input >>= (fun _ -> 
           read pre >>= (fun v ->
           set r v >>= (fun () ->
           return v))))) >>= (fun output -> 
      register output >>= (fun () -> 
      return' output))))))
end                                      

module L =
struct
  open Code
  (* The implementation types are actually the *same* as for ultrametrics, 
     even though semantically there's a Kleisli embedding thing going on. 

     The difference is that we will perform some additional side-effects in 
     these code expressions, which will create and wire up widgets. This will
     show up in extra calls to local()... *)

  type one = unit
  type ('a,'b) tensor = 'a * 'b
  type ('a,'b) lolli = 'a -> 'b option code
  type ('a,'b) hom = 'a -> 'b option code

  let id x = return' x
  let compose f g = fun x -> f x >>- g 
  let one = fun _ -> return' ()
  let tensor f g = fun at -> f at >>- (fun a ->
                             g at >>- (fun b ->
                             return' (a,b)))

  let rho (x, ()) = return' x
  let lambda ((), x) = return' x
  let assocl ((a,b), c) = return' (a, (b,c))
  let assocr (a, (b,c)) = return' ((a,b), c)
  let sym (a,b) = return' (b, a)

  let curry f = fun a -> return'(fun b -> f(a,b)) 

  let eval (f,x) = f x
end


open Code
type 'a f = 'a 
type 'a g = 'a option code 

(* Functorial actions  *)

let f uhom = uhom
let g (lhom : ('a, 'b) L.hom) : ('a g, 'b g) U.hom =
  fun acode -> acode >>- (fun v -> return'(lhom v))

(* Unit & Counit *)

let eta x = return' (return' x)

let varepsilon acode = acode 


let one = return'
let prod = return'
let one' = return'
let prod' = return'

let oned   = fun v -> return' v
let paird  = fun v -> return' v
let paird' = fun v -> return' v
let apply f = return' (fun x -> return' (f x))


(* GUI stuff *)

type window = GObj.widget

let label justify  =
  fun labels -> 
    local (fun () -> GMisc.label ~justify ()) >>= (fun w ->
    cell((read labels) >>= (function
         | None -> return ()
         | Some msg -> local (fun () -> w#set_text msg))) >>= (fun setlabel -> 
    register setlabel >>= (fun () ->
    return' (w#coerce))))
								     
let button =
  fun () -> 
    local (fun () -> GButton.button ()) >>= (fun (b : GButton.button) ->
    get_clock >>= (fun clock -> 
    cell (return' false) >>= (fun bsig ->
    local (fun () -> b#connect#pressed
             ~callback:(fun () ->
  			Dataflow.update bsig (Dataflow.Expr.return (Some true));
  			Dataflow.update clock (Dataflow.Expr.return ()))) >>= (fun _ -> 
    local (fun () -> b#connect#released
             ~callback:(fun () ->
  			Dataflow.update bsig (Dataflow.Expr.return (Some false));
  			Dataflow.update clock (Dataflow.Expr.return ()))) >>= (fun _ -> 
    let makebutton labels = 
      cell (read labels >>= (function
            | Some msg -> local (fun () -> b#set_label msg)
            | None -> return ())) >>= (fun setlabel ->
      register setlabel >>= (fun () ->
      return' b#coerce))
    in 
    return' (makebutton, bsig))))))

let checkbox = fun () -> 
  local (fun () -> GButton.check_button ()) >>= (fun b ->
  get_clock >>= (fun clock -> 
  cell (return' false) >>= (fun bsig ->
  local (fun () -> b#connect#toggled
           ~callback:(fun () ->
			let b = Dataflow.eval (Dataflow.Expr.read bsig) in 
			Dataflow.update bsig  (Dataflow.Expr.return (omap not b));
		        Dataflow.update clock (Dataflow.Expr.return ()))) >>= (fun _ ->
  let makebox labels = 
    cell (read labels >>= (function
          | Some msg -> local (fun () -> b#set_label msg)
          | None -> return ())) >>= (fun setlabel ->
    register setlabel >>= (fun () ->
    return' b#coerce))
  in 
  return' (makebox, bsig)))))

let stack orientation packing homogeneity expand =
  let expand = match expand with
    | `EXPAND -> true
    | `NOEXPAND -> false
  in
  let pack_style = match packing with
    | `START -> `START
    | `FINISH -> `END
  in
  let homogeneous = match homogeneity with
    | `HOMOGENEOUS -> true
    | `INHOMOGENEOUS -> false
  in
  fun (w1, w2) -> 
    local (fun () -> GPack.box orientation ~homogeneous ()) >>= (fun box ->
    local (fun () -> box#pack  ~expand ~from:pack_style w1) >>= (fun () -> 				   
    local (fun () -> box#pack  ~expand ~from:pack_style w2) >>= (fun () -> 				   
    return' box#coerce)))

let run (uhom : ((L.one g, U.one) U.prod, 'a U.discrete U.stream) U.hom) = 
  let clock = Dataflow.newcell (Dataflow.Expr.return ()) in
  let updates = ref [] in
  let one = return' () in 
  let empty_context = (one, ()) in 
  let output = match Dataflow.eval (uhom empty_context (clock, updates)) with
               | None -> assert false
               | Some output -> output
  in
  let step () =
    begin
      Dataflow.update clock (Dataflow.Expr.return ());
      let v = Dataflow.eval (Dataflow.Expr.read output) in
      (List.iter Dataflow.eval !updates; v)
    end
  in step

let guirun (f : (L.one, window) L.hom) : unit = 
  let clock = Dataflow.newcell (Dataflow.Expr.return ()) in
  let updates = ref []
  in
  let w = GWindow.window ~border_width:10 () in
  let _ = w#connect#destroy ~callback:GMain.Main.quit in
  let () = match Dataflow.eval (f () (clock,updates)) with
    | None -> assert false
    | Some widget -> w#add widget 
  in
  let _ = GMain.Idle.add
	    (fun () -> List.iter Dataflow.eval (!updates); true) in
  let _ = GMain.Timeout.add
	  ~ms:10
	  ~callback:(fun () -> Dataflow.update clock (Dataflow.Expr.return ()); true) in
  let _ = w#show () in 
    GMain.Main.main ()


