Require Import MemModel.
Require Import ETactics.
Require Import UsefulMisc.

(* definition of heap predicates *)
Definition hprop := heap -> Prop.

Delimit Scope hprop_scope with hprop. 

(* Definition of lifted logical operations *)
Definition hand (P:hprop) (Q:hprop) : hprop := (fun h => P h /\ Q h).
Definition himp (P:hprop) (Q:hprop) : hprop  := (fun h => P h -> Q h).
Definition hiff (P:hprop) (Q:hprop) : hprop  := hand (himp P Q) (himp Q P).
Definition hor (P:hprop) (Q:hprop) := (fun h => P h \/ Q h).
Definition hxor (P:hprop) (Q:hprop) := (fun h => xor (P h) (Q h)).

Definition hlift (P:Prop) : hprop := (fun h => P).

(* rename boxheap to boxheap *)

(* and lift forall *)

Definition boxh (P:hprop) : Prop := forall h, P h.
Definition exh (A:Type)(P:A->hprop) : hprop := (fun h => (exists x : A, P x h)).

Hint Unfold boxh.

Implicit Arguments exh [A].

(* Print Grammar constr. *)

(* Notations *)
Infix "/#\" := hand (at level 80, right associativity) : hprop_scope.
Infix "\#/" := hor (at level 85, right associativity) : hprop_scope.
Infix "-#>" := himp (at level 87, right associativity) : hprop_scope.
Infix "<-#>" := hiff (at level 88, right associativity) : hprop_scope.

Notation "'boxheap' P" := (boxh P) (at level 89, no associativity) : hprop_scope.

Notation "'existsh' x , p" := (exh (fun x => p))
  (at level 200, x ident, right associativity) : hprop_scope.
Notation "'existsh' x : t , p" := (exh (fun x:t => p))
  (at level 200, x ident, right associativity,
    format "'[' 'existsh' '/ ' x : t , '/ ' p ']'")
  : hprop_scope. 

Open Local Scope hprop_scope.

(* some tactics *)
Ltac unlift := unfold hlift, himp, boxh, exh, hand, hiff, hor, hxor.
Ltac unlift_in H := unfold hlift, himp, boxh, exh, hand, hiff, hor, hxor in H.

Ltac happly H := let H0 := fresh "UNLIFT" in 
  set (H0 := H); clearbody H0; unlift_in H0; apply H0; clear H0.

Ltac happlys H := let H0 := fresh "UNLIFT" in 
  set (H0 := H); clearbody H0; unlift_in H0; applys H0; clear H0.

Ltac heapply H := let H0 := fresh "UNLIFT" in 
  set (H0 := H); clearbody H0; unlift_in H0; eapply H0; clear H0.

Ltac heapplys H := let H0 := fresh "UNLIFT" in 
  set (H0 := H); clearbody H0; unlift_in H0; eapplys H0; clear H0.

Tactic Notation "happly" "*" constr(H) := 
  first [ happly H | heapply H]; auto* .

Tactic Notation "happlys" "*" constr(H) := 
  first [ happlys H | heapplys H]; auto* .


(* reflexivity *)
Lemma hand_refl: forall (P:hprop), boxheap P -#> P /#\ P.
  unfold hand, himp. intros. split; trivial.
Qed.

Lemma hor_refl: forall (P:hprop), boxheap P -#> P \#/ P.
Proof. 
  unlift. intuition.
Qed.

Implicit Arguments hor_refl [P].

Lemma himp_refl: forall (P:hprop), boxheap P -#> P.
  unfold himp. intros. intro. trivial.
Qed.

Lemma hiff_refl: forall (P:hprop), boxheap P <-#> P.
  unfold hiff. intros. split; apply* himp_refl.
Qed.

Lemma hxor_irref : forall (P:hprop), boxheap hxor P P -#> hlift False.
Proof.
  intros. unfold boxh, himp, hxor, hlift. intro. apply* xor_irref.
Qed.

(* symmetry *)
 
Lemma hand_sym: forall (P:hprop) (Q:hprop), boxheap P /#\ Q -#> Q /#\ P.
  unfold himp, boxh. intros. destruct H. split; trivial.
Qed.

Implicit Arguments hand_sym [P Q].

Lemma hor_sym: forall (P:hprop) (Q:hprop), boxheap P \#/ Q -#> Q \#/ P.
  unlift. intuition.
Qed.

Implicit Arguments hor_sym [P Q].

Lemma hiff_sym: forall (P:hprop) (Q:hprop), boxheap (P <-#> Q) -#> (Q <-#> P).
  unfold himp, hiff, boxh. intros. destruct H. split; trivial.
Qed.

Implicit Arguments hiff_sym [P Q].

Lemma hxor_sym : forall (P:hprop) (Q:hprop), boxheap hxor P Q -#> hxor Q P.
Proof.
  unfold hxor, exh, boxh, himp. intros. apply* xor_sym.
Qed.

Implicit Arguments hxor_sym [P Q].

Lemma hxor_hiff : forall (P:hprop) (Q:hprop), boxheap hxor P Q -#> (P <-#> Q) -#> hlift False.
Proof.
  unfold boxh, hxor, hiff, himp, hlift. intros. apply* xor_iff.
Qed.

Implicit Arguments hxor_hiff [P Q].

Lemma lift_all1 (P:Prop) : P -> boxheap hlift P.
Proof.
  unfold boxh, hlift. auto. 
Qed.

Implicit Arguments lift_all1 [P].

Lemma lift_all2 (P:Prop) : boxheap hlift P -> P.
Proof.
  unfold boxh, hlift. intros. apply H. exact empty.
Qed.

Implicit Arguments lift_all2 [P].

(* transitivity *)

