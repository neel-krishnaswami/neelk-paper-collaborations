(* Generate unique ids and make maps indexed by same*)

let gen = ref 0
let next() =
  let n = !gen in
  let () = gen := !gen + 1 in
      n

module Int = struct
  type t = int
  let compare = compare
end
module IntMap = Map.Make(Int)

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

  let fix f =
    let rec thunk () = f thunk () in
    thunk
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
