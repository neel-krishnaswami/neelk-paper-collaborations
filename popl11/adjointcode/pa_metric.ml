open Camlp4.PreCast
  
open Syntax
open Elaborator
open Term
open Grammar  

(* The payoff for piling all the syntactic categories into one big soup 
   comes here -- it makes parsing very simple, and lets us generate somewhat
   better error messages (since we can use semantic info to identify problems). 
*)
            
EXTEND Gram
  GLOBAL: expr mtype mexpr ;

  mtype:
    [ RIGHTA
      [ tp1 = mtype; "->"; tp2 = mtype            -> InT(_loc, Arrow(tp1, tp2))
      | tp1 = mtype; "~>"; tp2 = mtype            -> InT(_loc, Shrink(tp1, tp2)) 
      | tp1 = mtype; "-"; LIDENT "o"; tp2 = mtype -> InT(_loc, Lolli(tp1, tp2)) 
      | tp1 = mtype; "-*"; tp2 = mtype            -> InT(_loc, Lollishrink(tp1, tp2)) ]
    | [ tp1 = mtype; "&"; tp2 = mtype             -> InT(_loc, Times(tp1, tp2))
      | tp1 = mtype; "*"; tp2 = mtype             -> InT(_loc, Tensor(tp1, tp2))]
    | [ UIDENT "I"                                -> InT(_loc, I)
      | LIDENT "one"                              -> InT(_loc, One)
      | UIDENT "V"; "("; tp = mtype; ")"          -> InT(_loc, Val(tp))
      | UIDENT "S"; "("; tp = mtype; ")"          -> InT(_loc, Omega(tp))
      | UIDENT "D"; "("; tp = ctyp; ")"           -> InT(_loc, Discrete)
      | UIDENT "Gui"; "("; tp = mtype; ")"         -> InT(_loc, Gui(tp))
      | "("; tp = mtype; ")"                      -> tp ]
    ];

  mexpr: [ "binders"
           [ "fun"; vs = LIST1 [v = LIDENT -> v]; "->"; body = mexpr ->
               mk_fun _loc vs body
           | "let"; LIDENT "omega"; "("; v = LIDENT; ")"; "="; e = mexpr; "in"; e' = mexpr -> 
               In(_loc, LetOmega(v, e, e'))
           | "let"; LIDENT "omega"; "("; v = LIDENT; ":"; tp = mtype; ")"; "="; e = mexpr; "in"; e' = mexpr -> 
               In(_loc, LetOmega(v, In(Loc.merge (loc_exp e) (loc_tp tp),
				       Annot(e, InT(loc_tp tp, Omega tp))), e'))
           | "let"; LIDENT "gui"; "("; v = LIDENT; ")"; "="; e = mexpr; "in"; e' = mexpr -> 
               In(_loc, LetGui(v, e, e'))
           | "let"; LIDENT "gui"; "("; v = LIDENT; ":"; tp = mtype; ")"; "="; e = mexpr; "in"; e' = mexpr -> 
               In(_loc, LetGui(v, In(Loc.merge (loc_exp e) (loc_tp tp),
				       Annot(e, InT(loc_tp tp, Gui tp))), e'))
           | "let"; v = LIDENT; "="; e = mexpr; "in"; e' = mexpr -> In(_loc, Let(v, e, e'))
           | "let"; v = LIDENT; ":"; tp = mtype; "="; e = mexpr; "in"; e' = mexpr ->
               In(_loc, Let(v, In(Loc.merge (loc_exp e) (loc_tp tp), Annot(e, tp)), e'))
           ] 
         | "annotation"
           [ e = mexpr; ":";  t = mtype -> In(_loc, Annot(e, t)) ]
         | "application"
           [ LIDENT "value"; e = mexpr -> In(_loc, Value(e))
           | LIDENT "fst"; e = mexpr -> In(_loc, Fst(e))
           | LIDENT "snd"; e = mexpr -> In(_loc, Snd(e))
           | LIDENT "start"; e = mexpr -> In(_loc, Start(e))
           | LIDENT "omega"; e = mexpr -> In(_loc, Stream(e))
           | LIDENT "fix"; e = mexpr -> In(_loc, Fix(e))
           | LIDENT "cons"; e = mexpr -> In(_loc, Cons(e))
	   | LIDENT "return"; e = mexpr -> In(_loc, Return(e))
           | LIDENT "discrete"; e = expr -> In(_loc, EmbedF(e))
           | LIDENT "const"; e = expr -> In(_loc, Embed(e))
	   | LIDENT "inject"; e = expr -> In(_loc, Inject(e))
           |  m = mexpr; m' = mexpr -> In(_loc, App(m, m'))  ]
         | "atomic"
           [ v = LIDENT -> In(_loc, Var v)
           |  "("; ")" -> In(_loc, Unit)
           |  "("; e = mexpr; ")" -> e
           |  "("; e = mexpr; ","; e' = mexpr -> In(_loc, Pair(e, e'))
           |  "["; e = mexpr; "]" -> In(_loc, Bracket(e))
           ]
         ];

  expr: LEVEL "top"
    [ [ "do"; UIDENT "U"; "("; m = mexpr; ")" -> elaborate m _loc
      | "do"; UIDENT "S"; "("; m = mexpr; ")" -> elaborates m _loc
      ] 
    ];
END
