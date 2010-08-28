(* Create the grammar entries -- don't make them in the syntax extension because of 
   linker weirdness... *)
open Camlp4.PreCast
open Term

let mtype : tp Gram.Entry.t = Gram.Entry.mk "mtype"
let mexpr : exp Gram.Entry.t = Gram.Entry.mk "mexpr"
