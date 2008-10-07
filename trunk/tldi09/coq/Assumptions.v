(* These should be consistent with impredicative Set without Choice.
   With predicative Set, then there are set-theoretic models in which
   these axioms are true. *) 

Require Export Eqdep.
Require Export ProofIrrelevance.

(* This is a bit stronger than eta. *)
Axiom extensional : 
  forall (A: Type)
         (B: A -> Type) 
         (f g: forall x: A, B x),
    (forall x: A, f x = g x) -> f = g.

Axiom em : forall p: Prop, p \/ ~p.
