Require Import DisjointUnion.
Require Import List.
Require Import MemModel.
Require Import ST.
Require Import Separation.
Require Import STsep.
Require Import Assumptions.
Require Import Precise.
Require Import Coq.Lists.ListSet.
Require Import Tactics.
Require Import Iterators.
Require Import IteratorsSpec.

Set Implicit Arguments.
Unset Strict Implicit.

Open Local Scope stsep_scope.
Open Local Scope hprop_scope.

Program Definition Test1 :
    STsep emp Ac (fun y i m => exists P1, exists c1 : Ac, Val c1 = y /\
	Icoll c1 (4 :: nil) P1 m) :=
	sdo (c1 <-- Inewcoll;
	     Iadd c1 4;;
	     sret c1).
Next Obligation.
nextvc.
exists empty.
split.
trivial.
exists empty.
split.
remove_empty.
apply splits_refl.
intros.
nextvc.
nextvc.
exists j1.
split.
exists (nil (A:=nat)).
exists x0.
assumption.
exists empty.
split.
remove_empty.
apply splits_refl.
intros.
split.
intros.
destruct H1.
nextvc.
destruct (H2 nil x0 H).
exists x2.
exists x.
split.
trivial.
assumption.
intros.
destruct H1.
inversion H1.
Defined.

Program Definition Test2 :
    STsep emp Ac (fun y i m => exists P2, exists c1 : Ac, Val c1 = y /\
	Icoll c1 (3 :: 4 :: nil) P2 m) :=
	sdo (c1 <-- Test1;
	     Iadd c1 3;;
	     sret c1).
Next Obligation.
nextvc.
exists empty.
split.
trivial.
exists empty.
split.
remove_empty.
apply splits_refl.
intros.
split.
Focus 2.
intros.
destruct H0 as [ y [ z [ H1 H2 ] ] ].
inversion H1.
intros.
nextvc.
destruct H0 as [ P1 [ c1 [ H1 H2 ] ] ].
inversion H1.
rewrite H0 in H2.
clear c1 H1 H0.
   exists j1.
   split.
  exists (4 :: nil).
    exists P1.
    assumption.
 exists empty.
   split.
  remove_empty.
    apply splits_refl.
 intros.
   split.
  intros.
    nextvc.
    destruct H0.
    destruct (H0 (4 :: nil) P1 H2).
    exists x1.
    exists x.
    split.
   trivial.
  assumption.
 intros.
   destruct H0.
   inversion H0.
Defined.


Program Definition Test3 :
    STsep emp (Ac*Ac)%type (fun y i m => exists P1, exists P2, exists c1, exists c2,
	Val (c1,c2) = y /\ ((Icoll c1 (3 :: 4 :: nil) P1) # (Icoll c2 (3 :: nil) P2)) m) :=
	sdo (c1 <-- Test2;
	     c2 <-- Inewcoll;
	     Iadd c2 3;;
	     sret (c1,c2)).
Next Obligation.
simpl in |- *.
intros.
simpl in *.
 subst.
auto with *.
nextvc.
exists empty.
split.
 trivial.
exists empty.
  split.
 remove_empty.
   apply splits_refl.
intros.
  split.
   intros.
   destruct H0 as (P2, (c1, (H1, H2))).
   inversion H1.
   rewrite H3 in H2.
   clear H3 H1 c1.
   nextvc.
   exists empty.
   split.
  trivial.
 exists j1.
   split.
  remove_empty.
    apply splits_refl.
 intros.
   split.
    intros.
    destruct H0 as (P, (v, (H1, H3))).
    inversion H1.
    rewrite H4 in H3.
    clear H4 H1 v.
    nextvc.
    exists j2.
    split.
   exists (nil (A:=nat)).
     exists P.
     assumption.
  exists j1.
    split.
   assumption.
  intros.
    split.
     intros.
     destruct H1.
     nextvc.
     destruct (H4 nil P H3).
     exists P2.
     exists x2.
     exists x.
     exists x0.
     split.
    trivial.
   exists j1.
     exists j4.
     split.
     eapply splits_permute.
       apply H0.
      PermutProve.
     split.
    assumption.
   assumption.
  intros.
    destruct H1.
    inversion H1.
 intros.
   destruct H0 as (y, (z, (H1, H3))).
   inversion H1.
intros.
  destruct H0 as (y, (z, (H1, H2))).
  inversion H1.
Defined.


Program Definition Test4 :
    STsep emp (Ac*Ai)%type 
	(fun y i m => exists P1, exists c1, exists it, Val (c1,it) = y /\
	    ((Icoll c1 (3 :: 4 :: nil) P1) # (Iiter it
	    ((c1,3::4::nil,P1)::nil) (3::4::nil))) m) :=
    sdo (c <-- Test2;
	 i <-- Inewiter c;
	 sret (c,i)).
Next Obligation.
simpl in |- *.
intros.
simpl in *.
 subst.
auto with *.
nextvc.
exists empty.
split.
 trivial.
exists empty.
  split.
 remove_empty.
   apply splits_refl.
intros.
  split.
   intros.
   destruct H0 as (P2, (c1, (H1, H2))).
   nextvc.
   exists j1.
   split.
  exists (3 :: 4 :: nil).
    exists P2.
    inversion H1.
    rewrite H0 in H2.
    clear H0 H1 c1.
    assumption.
 exists empty.
   split.
  remove_empty.
    apply splits_refl.
 intros.
   split.
    intros.
    destruct H0 as (a, (H3, H4)).
    inversion H3.
    rewrite H5 in H4.
    clear H5 H3 a.
    nextvc.
    exists P2.
    exists x.
    exists x0.
    split.
   trivial.
  inversion H1.
    rewrite H0 in H2.
    clear H0 H1 c1.
    destruct (H4 (3 :: 4 :: nil) P2 H2).
    destruct H as (h2, (H5, (H6, H7))).
    exists x1.
    exists h2.
    split.
   assumption.
  split.
   assumption.
  assumption.
 intros.
   destruct H0 as (y, (H3, H4)).
   inversion H3.
intros.
  destruct H0 as (y, (z, (H1, H2))).
  inversion H1.
Defined.

Definition inv (b : bool) := 
  match b with
  | true => false
  | false => true
  end.

Fixpoint even (n : nat) := 
  match n with
  | O => true
  | S(n) => inv (even n)
  end.

Program Definition Test5 :
  STsep emp (Ac * Ai)%type
    (fun y i m => exists P, exists c, exists it,
      y = Val (c, Filter even it) /\ 
       ((Icoll c (3 :: 4 :: nil) P) # 
        (Iiter (Filter even it) ((c, 3::4::nil, P)::nil) (filter even (3::4::nil)))) m) 
  := sdo(t <-- Test4;
         it <-- Ifilter even (snd t);
         sret (fst t, it)).
Next Obligation.
nextvc.
exists empty.
split; auto.
exists empty.
split; [ remove_empty; apply splits_refl | idtac ].
intros.
splits_rewrite.
split.
  Focus 2.
  intros.
  destruct H as [ p [ c [ it [ H1 _ ] ] ] ].
  inversion H1.
intros.
nextvc.
destruct H as [ P [ c [ it [ H1 H2 ] ] ] ].
inversion H1; clear H1.
destruct H2 as [ j2 [ j3 [ H3 [ H4 H5 ] ] ] ].
exists j3.
split.
  exists ((c, 3::4::nil, P)::nil).
  exists (3::4::nil).
  assumption.
exists j2.
split.
  apply splits_commute; assumption.
intros.
split.
  Focus 2.
  intros.
  destruct H1; inversion H1.
intros.
nextvc.
destruct H1 as [ H1 H2 ].
generalize(H2 ((c, 3::4::nil, P)::nil) (3::4::nil) H5); clear H2; intros H2.
destruct H2 as [ xs' [ H2 H6 ] ].
exists P; exists c; exists it.
simpl.
intuition.
inversion H1.
trivial.
exists j2; exists j0.
intuition.
apply splits_commute; assumption.
exists xs'.
intuition.
Defined.

Program Definition Test6 :
  STsep emp (option nat)
    (fun y i m => exists P, exists c, exists it,
      y = Val (Some 4) /\
       ((Icoll c (3 :: 4 :: nil) P) # 
        (Iiter (Filter even it) ((c, 3::4::nil, P)::nil) nil)) m) 
  := sdo(t <-- Test5;
         n <-- next (snd t);
         sret n).
Next Obligation.
nextvc.
exists empty.
split; auto.
exists empty.
split; [ remove_empty; apply splits_refl | idtac ].
intros.
splits_rewrite.
split.
  Focus 2.
  intros.
  destruct H as [ P [ c [ it [ H _ ] ] ] ].
  inversion H.
intros.
destruct H as [ P [ c [ it [ H H1 ] ] ] ].
nextvc.
inversion H; clear H.
exists j1.
assert(((Icoll c (3::4::nil) P # emp) # (fun h : heap =>
         exists xs' : list nat, 4::nil = filter even xs' /\
         Iiter it ((c, 3::4::nil, P)::nil) xs' h)) j1).
destruct H1 as [ j2 [ j3 [ H3 [ H4 H5 ] ] ] ].
exists j2; exists j3.
intuition.
exists j2; exists empty; intuition.
remove_empty; apply splits_refl.
split.
exists ((c, 3::4::nil, P)::nil).
simpl colls; simpl snd.
unfold Iiter; fold Iiter.
exists (4::nil).
assumption.
exists empty.
split; [ remove_empty; apply splits_refl | idtac ].
split.
  splits_rewrite.
  intros.
  simpl snd in H0.
  generalize(H0 ((c, 3::4::nil, P)::nil) (4::nil)); clear H0; intros H0.
  simpl colls in H.
  generalize(H0 H); clear H0; intros H0.
  nextvc.
  exists P; exists c.
  exists it.
  simpl opt_hd in H0.
  unfold Iiter in H0; fold Iiter in H0.
  simpl tail in H0.
  intuition.
  simpl colls in H3.
  destruct H3 as [ h1 [ h2 [ H3 [ H4 H5 ] ] ] ].
  rewrite star_unit_right in H4.
  exists h1; exists h2.
  intuition.
intros.
generalize(H3 ((c, 3::4::nil, P)::nil) (4::nil)); clear H3; intros H3.
simpl colls in H3.
destruct (H3 H) as [ H4 H5 ].
inversion H4.
Defined.