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

  val tensor  : ('a,'b) hom -> ('a,'c) hom -> ('a, ('b,'c) tensor) hom
  val rho     : (('a, one) tensor, 'a) hom
  val rho'    : ('a, ('a, one) tensor) hom 
  val lambda  : ((one, 'a) tensor, 'a) hom
  val lambda' : ('a, (one, 'a) tensor) hom
  val assocl  : ((('a, 'b) tensor, 'c) tensor, ('a, ('b, 'c) tensor) tensor) hom
  val assocr  : (('a, ('b, 'c) tensor) tensor, (('a, 'b) tensor, 'c) tensor) hom
  val sym     : (('a,'b) tensor, ('b, 'a) tensor) hom 

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
  val head   : ('a stream, 'a) hom
  val tails  : ('a stream, 'a stream stream) hom
  val stream :  ('a,'b) hom -> ('a stream, 'b stream) hom 
  val cons   : ('a, ('a stream, 'a stream) shrink) hom 
  val fix    : (('a stream, 'a stream) shrink, 'a stream) hom
end

module type GUI = SMCC

module L : GUI   
module U : ULTRAMETRIC 

type 'a f  
type 'a g

(* Functorial actions *)

val f : ('a,'b) U.hom -> ('a f, 'b f) L.hom
val g : ('a,'b) L.hom -> ('a g, 'b g) U.hom

(* Unit & counit *)

val eta : ('a, 'a g f) L.hom
val varepsilon : ('a f g, 'a) U.hom

(* Monoidal structure *)

val one   : (U.one f, L.one) L.hom 
val one'  : (L.one, U.one f) L.hom 
val prod  : (('a, 'b) U.prod f, ('a f, 'b f) L.tensor) L.hom
val prod' : (('a f, 'b f) L.tensor, ('a, 'b) U.prod f) L.hom

(* Compatibility with ML types *)

val oned   : (U.one, unit U.discrete) U.hom
val paird  : (('a U.discrete, 'b U.discrete) U.prod, ('a * 'b) U.discrete) U.hom
val paird' : (('a * 'b) U.discrete, ('a U.discrete, 'b U.discrete) U.prod) U.hom
val apply  : (('a -> 'b) U.discrete, ('a U.discrete, 'b U.discrete) U.exp) U.hom 

(* GUI operations *)

type window
val button   : (L.one, ((string U.discrete U.stream f, window) L.lolli,
			bool U.discrete U.stream f) L.tensor) L.hom
val checkbox : (L.one, ((string U.discrete U.stream f, window) L.lolli,
			bool U.discrete U.stream f) L.tensor) L.hom
val label  : [`LEFT | `RIGHT | `CENTER | `FILL] -> 
              (string U.discrete U.stream, window) L.hom 
val stack : [`HORIZONTAL | `VERTICAL] -> 
            [`FINISH | `START] -> 
	    [`HOMOGENEOUS | `INHOMOGENEOUS] ->
	    [`EXPAND | `NOEXPAND] -> 
	      ((window, window) L.tensor, window) L.hom 

(* Run a program -- will never actually return a None value *)

val run : ((L.one g, U.one) U.prod, 'a U.discrete U.stream) U.hom -> (unit -> 'a option)
val guirun : (L.one, window) L.hom -> unit

