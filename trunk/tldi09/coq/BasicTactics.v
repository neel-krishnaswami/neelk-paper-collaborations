(* This tactic will fail unless there is a hypothesis with type t in the
 * context. It is only useful in other tactics.
 *)
Ltac exist_hyp t := match goal with
  | H1:t |- _ => idtac
 end.

(* Remove all duplicate hypotheses *)
Ltac cleanup :=
  repeat match goal with
    | H:?X1 |- _ => clear H; exist_hyp X1
  end.

(* useful for destructing a hypothesis that has a mess of existentials in it *)
Ltac destructs h := 
  try repeat (destruct h); auto.

(* Similar to destructs, but uses decompose. *)
Ltac crush h :=
  decompose [and or] h; decompose sum h; decompose [and or] h.

(* This is like crush, except it will crush all crushable things in the
 * context. A crushable thing is a hypothesis whose outer constructor is
 * (/\), (\/), or exists.
 *)
Ltac crushall :=
  match goal with 
  | H:(exists x: _, _) |- _ => destruct H; crushall
  | H:(_ /\ _)         |- _ => destruct H; crushall
  | H:(_ \/ _)         |- _ => destruct H; crushall
  | _ => idtac
  end.

Ltac noexn_tac4 h :=
  elim h;
  clear h;
  let h2 := fresh "H1" in
  intros h2 h. 

(* == Manipulating the Goal == *)

(* simplifies complicated goals with exists, /\ and \/ *)
Ltac destroy :=
  repeat (progress (try constructor; auto)).

(* Try to find obvious existensal eliminations *)
Ltac exists_find :=
  match goal with
  | a:?T, b:?T |- exists x:?T,_ => idtac     (* two choices, do nothing *)
  | a:?T       |- exists x:?T,_ => exists a  (* found a unique choice *)
  |            |- _             => fail      (* nothing to use in context *)
  end.

(* Try to find obvious existensal eliminations for refs
 * Note: vector is not defined here, so we use ?V
 *)
Ltac exists_findv :=
  match goal with
  | a:?T, b:?T |- exists x: ?V ?T 1,_ => idtac
  | a:?T       |- exists x: ?V ?T 1,_ => exists (V a 1)
  |            |- _                   => fail
  end.

Ltac exfind := repeat (exists_find || exists_findv).

(* Greg's super introducers *)

(* this is a tactic that deconstructs a goal by introducing all assumptions,
 * but along the way, deconstructing any assumptions that involve /\, exists,
 * and (noexn _ _ _) \/ P.  It also rewrites when we have (x = e) -> P to
 * P[e/x].
 *) 
Ltac superintro := 
  match goal with
  | [ |- (exists x, _) -> _ ] => 
      let h := fresh "H" in intro h; elim h; clear h
  | [ |- False -> _] => tauto
  | [ |- (False \/ _) -> _] =>
      let h := fresh "H" in intro h; elim h ; [ tauto | clear h ]
  | [ |- (_ \/ False) -> _] =>
      let h := fresh "H" in intro h; elim h ; [ clear h | tauto ]
  | [ |- (_ /\ _) -> _] => 
      let h := fresh "H" in intro h; elim h; clear h
  | [ |- (_ = _) -> _ ] =>
      let h := fresh "H" in intro h; rewrite h
  | [ |- forall x, _ ] => intro
  | _ => idtac
  end. 

(* tactic to deconstruct a combination of existentials and conjunctions in
 * a hypothesis -- works better than destructs. *)
Ltac destructs_in H := 
  match (type of H) with
  | (exists x,_) => 
    elim H ; clear H ; intro ; intro H ; destructs_in H
  | (_ /\ _) => 
    let H2 := fresh "H" in 
        elim H ; clear H ; intros H H2 ; destructs_in H ; destructs_in H2 
  | _ => idtac
  end.


(* repeat superintro until no progress *)
Ltac superintros := repeat (progress superintro).


(* == Big tactics == *)

Ltac destroy_crush_find :=
  intros; destroy; intros; crushall; subst; cleanup; exfind.

(* This one can be used as the default - see mbool *)
Ltac simplifier :=
  repeat (progress destroy_crush_find); auto.

