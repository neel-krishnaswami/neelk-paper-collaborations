(* The type of dataflow cells *)
type 'a cell
  
module Expr : sig
  (* A (somewhat redundant) signature for monads *)
  type 'a t
  val map : ('a -> 'b) -> 'a t -> 'b t
  val unit : (unit -> 'a) -> 'a t
  val lift : ('a -> 'b t) -> 'a t -> 'b t

  val return : 'a -> 'a t
  val bind   : 'a t -> ('a -> 'b t) -> 'b t
  val join   : 'a t t -> 'a t 

  (* The interesting operations of the monadic API, to read and
     create cells *)

  val read : 'a cell -> 'a t
  val newcell : 'a t -> 'a cell t

  val fix : ('a t -> 'a t) -> 'a t

  (* local() lets you use some  local state in an expression. Obviously 
     this can be catastrophic if used carelessly (eg, if update() is 
     called inside a local) *)
      
  val local : (unit -> 'a) -> 'a t 
end

(* Evaluation and update --- note they don't live in the Expr monad *)

val eval : 'a Expr.t -> 'a
val update  : 'a cell -> 'a Expr.t -> unit
val newcell : 'a Expr.t -> 'a cell
