(* Term formers for changing DSL syntax into ML syntax, with one for each combinator *)

type ast = string -> string -> string ->
    Camlp4.PreCast.Ast.loc -> Camlp4.PreCast.Ast.expr

val id0 : string -> ast
val id1 : string -> ast -> ast
val id2 : string -> ast -> ast -> ast
val id0' : string -> ast
val id1' : string -> ast -> ast
val id2' : string -> ast -> ast -> ast

val id : ast
val compose : ast -> ast -> ast
val one : ast
val pair : ast -> ast -> ast
val pi1 : ast
val pi2 : ast
val curry : ast -> ast
val eval : ast
val fix : ast
val cons : ast
val head : ast
val tails : ast 
val stream : ast -> ast
val sweak : ast
val spair : ast
val scurry : ast
val seval : ast
val swap : ast
val scomposel : ast -> ast
val scomposer : ast -> ast
val eval' : ast
val tensor : ast -> ast -> ast
val rho : ast   
val rho' : ast   
val lambda : ast
val lambda' : ast
val assocl : ast
val assocr : ast 
val sym : ast 

val flip : ast -> ast
val one' : ast
val oned : ast
val prod : ast
val prod' : ast
val paird : ast
val paird' : ast
val apply : ast 

val varepsilon : ast
val eta : ast
val f : ast -> ast
val g : ast -> ast

val discrete : Camlp4.PreCast.Ast.expr -> ast
val unitize  : Camlp4.PreCast.Ast.expr -> Camlp4.PreCast.Ast.loc -> Camlp4.PreCast.Ast.expr

val times : ast -> ast -> ast
val passocr : ast
val passocl : ast
val uncurry : ast

(* Reassociate an environment *)

val reassoc : 'a list -> ast
