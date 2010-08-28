(* Term formers for changing DSL syntax into ML syntax, with one for each combinator *)

type ast = string -> string -> string -> Camlp4.PreCast.Ast.loc -> Camlp4.PreCast.Ast.expr

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

val guireturn : ast
val bind : ast -> ast
val strength : ast

val flip : ast -> ast
val one' : ast
val oned : ast
val prod : ast
val prod' : ast
val paird : ast
val paird' : ast
val apply : ast 
val contract : ast
val contract' : ast
val varepsilon : ast
val eta : ast
val value : ast -> ast
val omega : ast -> ast
val discrete : Camlp4.PreCast.Ast.expr -> ast
val unitize  : Camlp4.PreCast.Ast.expr -> Camlp4.PreCast.Ast.loc -> Camlp4.PreCast.Ast.expr
val fix : ast
val cons : ast
val sweak : ast
val spair : ast
val scurry : ast
val seval : ast
val swap : ast
val scomposel : ast -> ast
val scomposer : ast -> ast
val eval' : ast
val times : ast -> ast -> ast
val assocr : ast
val assocl : ast
val uncurry : ast

(* Reassociate an environment *)

val reassoc : 'a list -> ast
