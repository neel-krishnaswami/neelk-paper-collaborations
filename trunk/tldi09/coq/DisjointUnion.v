(*********************************************)
(* N-ary connectives for                     *)
(* disjointness and union of heaps           *)
(*                                           *)
(* Generalizes usual binary heap operators   *) 
(* to lists of heaps                         *)
(*                                           *)
(* Practical in separation logic proofs      *)
(*                                           *)
(* Main results are proofs that disjointness *)
(* and union are invariant over permutation  *)
(* of heap lists.                            *)
(*********************************************)

Require Import Assumptions.
Require Import ProofIrrelevance.
Require Import BasicTactics.
Require Import List.
Require Import MemModel.


(* helper facts about lists and permutations *) 
(* should really be in the list library *)

Lemma Permutation_cons : 
    forall (A : Type) (a : A) (l k : list A), 
         Permutation (a::l) k -> 
            exists l1, exists l2, k = l1++(a::l2) /\ Permutation l (l1++l2).

intros.
assert (In a k).
  eapply Permutation_in.
    apply H.
   simpl in |- *.
   auto.
  destruct (In_split a k H0).
  destruct H1.
  exists x.
  exists x0.
  split.
 auto.
rewrite H1 in H.
   eapply Permutation_cons_app_inv.
  apply H.
Qed.

Implicit Arguments Permutation_cons [A a l k].


(******************************)
(* Definition of disjointness *)
(******************************)

Definition disjoint2 (h1 h2 : heap) : Prop :=
   forall (l : loc), valid_loc l h1 -> unused_loc l h2.

Fixpoint disjoint_heap_list (h : heap) (hs : list heap) {struct hs} : Prop :=
  match hs with
   | nil => True
   | hh::ht => disjoint2 h hh /\ disjoint_heap_list h ht
  end.

Fixpoint disjoint_list_list (hs1 hs2 : list heap) {struct hs1} : Prop :=
  match hs1 with
   | nil => True
   | hh::ht => disjoint_heap_list hh hs2 /\ disjoint_list_list ht hs2
  end.

Fixpoint disjoint (hs : list heap) : Prop :=
   match hs with
    | nil => True
    | hh::ht => disjoint ht /\ disjoint_heap_list hh ht
   end.   


(*****************************)
(* Lemmas about disjointness *)
(*****************************)


Lemma disjoint2_commute : 
   forall (h1 h2 : heap), disjoint2 h1 h2 -> disjoint2 h2 h1. 

unfold disjoint2 in |- *.
intros.
destruct (loc_em l h1).
 auto.
generalize (H l H1).
  intros.
  destruct (loc_ex H0 H2).
Qed.

Implicit Arguments disjoint2_commute [h1 h2].



Lemma disjoint_heap_list_app_intro : 
    forall (h : heap) (hs1 hs2 : list heap),
       disjoint_heap_list h hs1 -> disjoint_heap_list h hs2 ->
          disjoint_heap_list h (hs1 ++ hs2).

intros.
induction hs1.
 auto.
simpl in |- *.
  simpl in H.
   tauto.
Qed.

Implicit Arguments disjoint_heap_list_app_intro [h hs1 hs2].



Lemma disjoint_heap_list_app_elim : 
    forall (h : heap) (hs1 hs2 : list heap),
       disjoint_heap_list h (hs1 ++ hs2) -> 
            disjoint_heap_list h hs1 /\ 
            disjoint_heap_list h hs2.

intros.
induction hs1.
 simpl in H.
   simpl in |- *.
    tauto.
simpl in H.
  simpl in |- *.
   tauto.
Qed.

Implicit Arguments disjoint_heap_list_app_elim [h hs1 hs2].



Lemma disjoint_list_list_empty_left : 
    forall (hs : list heap), 
        disjoint_list_list hs nil.

induction hs.
 simpl in |- *.
   auto.
simpl in |- *.
  auto.
Qed.




Lemma disjoint_list_list_empty_right : 
    forall (hs : list heap), 
        disjoint_list_list nil hs.

induction hs.
simpl.
   auto.
auto.
Qed.



Lemma disjoint_list_list_cons_intro_left : 
   forall (h : heap) (hs1 hs2 : list heap), 
     disjoint_heap_list h hs2 -> disjoint_list_list hs1 hs2 -> 
       disjoint_list_list (h :: hs1) hs2.

induction hs1.
 simpl in |- *.
   auto.
simpl in |- *.
  auto.
Qed.

Implicit Arguments disjoint_list_list_cons_intro_left [h hs1 hs2].



Lemma disjoint_list_list_cons_intro_right : 
   forall (h : heap) (hs1 hs2 : list heap), 
      disjoint_heap_list h hs1 -> disjoint_list_list hs1 hs2 -> 
         disjoint_list_list hs1 (h :: hs2).

induction hs1.
 auto.
simpl in |- *.
  intros.
  split.
 split.
  apply disjoint2_commute.
     tauto.
  tauto.
apply IHhs1.
  tauto.
 tauto.
Qed.

Implicit Arguments disjoint_list_list_cons_intro_right [h hs1 hs2].




Lemma disjoint_list_list_cons_elim_left : 
   forall (h : heap) (hs1 hs2 : list heap), 
      disjoint_list_list (h :: hs1) hs2 -> 
        disjoint_heap_list h hs2 /\ disjoint_list_list hs1 hs2.

induction hs1.
 auto.
simpl in |- *.
  auto.
Qed.

Implicit Arguments disjoint_list_list_cons_elim_left [h hs1 hs2].



Lemma disjoint_list_list_cons_elim_right : 
   forall (h : heap) (hs1 hs2 : list heap), 
      disjoint_list_list hs1 (h :: hs2) -> 
        disjoint_heap_list h hs1 /\ disjoint_list_list hs1 hs2.

induction hs1.
 auto.
simpl in |- *.
  intros.
  destruct H.
  destruct (IHhs1 hs2 H0).
  destruct H.
  generalize (disjoint2_commute H).
  intros.
   tauto.
Qed.

Implicit Arguments disjoint_list_list_cons_elim_right [h hs1 hs2].



Lemma disjoint_list_list_commute : 
   forall (hs1 hs2 : list heap),
       disjoint_list_list hs1 hs2 -> disjoint_list_list hs2 hs1.

induction hs1.
 intros.
   apply disjoint_list_list_empty_left.
simpl in |- *.
  intros.
  apply disjoint_list_list_cons_intro_right.
  tauto.
apply IHhs1.
   tauto.
Qed.

Implicit Arguments disjoint_list_list_commute [hs1 hs2].



Lemma disjoint_app_intro : 
   forall (hs1 hs2 : list heap),
      disjoint hs1 -> disjoint hs2 -> disjoint_list_list hs1 hs2 -> 
         disjoint (hs1 ++ hs2).

intros.
induction hs1.
  tauto.
simpl in |- *.
  simpl in H1.
  simpl in H.
  generalize (@disjoint_heap_list_app_intro a hs1 hs2).
  intros.
   tauto.
Qed.

Implicit Arguments disjoint_app_intro [hs1 hs2].



Lemma disjoint_app_elim : 
   forall (hs1 hs2 : list heap), disjoint (hs1 ++ hs2) ->  
      disjoint hs1 /\ disjoint hs2 /\ disjoint_list_list hs1 hs2.

intros.
induction hs1.
 simpl in |- *.
    tauto.
simpl in H.
  simpl in |- *.
  generalize (@disjoint_heap_list_app_elim a hs1 hs2).
  intros.
   tauto.
Qed.

Implicit Arguments disjoint_app_elim [hs1 hs2].



Lemma disjoint_heap_list_permute : 
   forall (h : heap) (hs1 hs2 : list heap),
      disjoint_heap_list h hs1 -> Permutation hs1 hs2 -> 
            disjoint_heap_list h hs2.

intro.
induction hs1.
 intros.
   rewrite (Permutation_nil H0) in |- *.
   auto.
intros.
  destruct (Permutation_cons H0).
  destruct H1.
  destruct H1.
  simpl in H.
  assert (disjoint_heap_list h (x ++ x0)).
  eapply IHhs1.
   tauto.
 auto.
rewrite H1 in |- *.
   eapply disjoint_heap_list_app_intro.
 destruct (disjoint_heap_list_app_elim H3).
   auto.
simpl in |- *.
  destruct (disjoint_heap_list_app_elim H3).
   tauto.
Qed.

Implicit Arguments disjoint_heap_list_permute [h hs1 hs2].



Lemma disjoint_app : 
   forall (h : heap) (hs1 hs2 : list heap),
     disjoint (h :: (hs1++hs2)) -> disjoint (hs1 ++ h::hs2).

intros.
simpl in H.
destruct H.
destruct (disjoint_app_elim H).
destruct H2.
destruct (disjoint_heap_list_app_elim H0).
apply disjoint_app_intro.
 auto.
simpl in |- *.
   tauto.
apply disjoint_list_list_cons_intro_right.
 auto.
auto.
Qed.

Implicit Arguments disjoint_app [h hs1 hs2].



(************************************************)
(* Disjointness is invariant under permutations *)
(************************************************)

Theorem disjoint_permute : 
   forall (hs1 hs2 : list heap),
      disjoint hs1 -> Permutation hs1 hs2 -> disjoint hs2.

induction hs1.
 intros.
   rewrite (Permutation_nil H0) in |- *.
   auto.
simpl in |- *.
  intros.
  destruct (Permutation_cons H0).
  destruct H1.
  destruct H1.
  rewrite H1 in |- *.
  apply disjoint_app.
  simpl in |- *.
  destruct H.
  split.
 apply IHhs1.
  auto.
 auto.
 eapply disjoint_heap_list_permute.
   apply H3.
  auto.
Qed.

Implicit Arguments disjoint_permute [hs1 hs2].


(*************************************)
(* Further lemmas about disjointness *)
(*************************************)


Lemma disjoint_empty_left : 
   forall (h : heap), disjoint2 h empty.

unfold disjoint2 in |- *.
intros.
apply unused_loc_empty.
Qed.


Lemma disjoint_empty_right : 
   forall (h : heap), disjoint2 empty h.

intros.
apply disjoint2_commute.
apply disjoint_empty_left.
Qed.



Lemma disjoint_cons_intro : 
   forall (h : heap) (l : list heap),
      disjoint l -> disjoint_heap_list h l -> disjoint (h :: l).

simpl in |- *.
 tauto.
Qed.

Implicit Arguments disjoint_cons_intro [h l].



Lemma disjoint_cons_elim : 
   forall (h : heap) (l : list heap), 
      disjoint (h :: l) -> disjoint l /\ disjoint_heap_list h l.

simpl in |- *.
 tauto.
Qed.

Implicit Arguments disjoint_cons_elim [h l].



Lemma disjoint_heap_list_empty : 
       forall (hs : list heap), disjoint_heap_list empty hs.

induction hs.
 simpl in |- *.
   auto.
simpl in |- *.
  split.
 apply disjoint_empty_right.
auto.
Qed.



Lemma disjoint_heap_list_cons_intro : 
   forall (h1 h2 : heap) (hs : list heap),
      disjoint2 h1 h2 -> disjoint_heap_list h1 hs -> disjoint_heap_list h1 (h2 :: hs). 

simpl in |- *.
 tauto.
Qed.

Implicit Arguments disjoint_heap_list_cons_intro [h1 h2 hs].


Lemma disjoint_heap_list_cons_elim : 
   forall (h1 h2 : heap) (hs : list heap),
      disjoint_heap_list h1 (h2 :: hs) -> 
          disjoint2 h1 h2 /\ disjoint_heap_list h1 hs.

simpl in |- *.
 tauto.
Qed.

Implicit Arguments disjoint_heap_list_cons_elim [h1 h2 hs].



Lemma disjoint_list_list_app_intro_left : 
    forall (hs hs1 hs2 : list heap), 
       disjoint_list_list hs1 hs -> 
          disjoint_list_list hs2 hs -> disjoint_list_list (hs1 ++ hs2) hs.

induction hs1.
 auto.
intros.
  simpl in H.
  simpl in |- *.
  split.
  tauto.
apply IHhs1.
  tauto.
auto.
Qed.

Implicit Arguments disjoint_list_list_app_intro_left [hs hs1 hs2].



Lemma disjoint_list_list_app_intro_right : 
    forall (hs hs1 hs2 : list heap), 
           disjoint_list_list hs hs1 -> 
              disjoint_list_list hs hs2 -> 
                    disjoint_list_list hs (hs1 ++ hs2).

intros.
apply disjoint_list_list_commute.
apply disjoint_list_list_app_intro_left.
 apply (disjoint_list_list_commute H).
apply (disjoint_list_list_commute H0).
Qed.




Lemma disjoint_list_list_app_elim_left : 
    forall (hs hs1 hs2 : list heap), 
       disjoint_list_list (hs1 ++ hs2) hs ->
         disjoint_list_list hs1 hs /\ disjoint_list_list hs2 hs.

induction hs.
 intros.
   split.
  apply disjoint_list_list_empty_left.
 apply disjoint_list_list_empty_left.
intros.
  destruct (disjoint_list_list_cons_elim_right H).
  destruct (disjoint_heap_list_app_elim H0).
  split.
 apply disjoint_list_list_cons_intro_right.
  auto.
 apply (proj1 (IHhs hs1 hs2 H1)).
apply disjoint_list_list_cons_intro_right.
 auto.
apply (proj2 (IHhs hs1 hs2 H1)).
Qed.

Implicit Arguments disjoint_list_list_app_elim_left [hs hs1 hs2].



Lemma disjoint_list_list_app_elim_right : 
    forall (hs hs1 hs2 : list heap), 
       disjoint_list_list hs (hs1 ++ hs2) ->
         disjoint_list_list hs hs1 /\ disjoint_list_list hs hs2.

intros.
destruct (disjoint_list_list_app_elim_left (disjoint_list_list_commute H)).
split.
 apply (disjoint_list_list_commute H0).
apply (disjoint_list_list_commute H1).
Qed.

Implicit Arguments disjoint_list_list_app_elim_right [hs hs1 hs2].



(******************)
(* Disjoint union *)
(******************)

(* Definition of heap union must expose that heaps are functions. *)
(* Somewhat annoying during proving. *)

(* Definition is staged so that only union2 suffers from this problem *)


Definition union2 (h1 h2 : heap) (pf : disjoint2 h1 h2) : heap :=
  fun (l : loc) => 
      match (lookup_loc h1 l) with    
       | None => lookup_loc h2 l 
       | Some v => Some v
      end.



Lemma union2_commute : 
   forall (h1 h2 : heap) pf1 pf2, 
       union2 h1 h2 pf1 = union2 h2 h1 pf2. 

intros.
unfold union2 in |- *.
apply heap_extensional.
intro.
unfold lookup_loc in |- *.
destruct (loc_em l h1).
 unfold unused_loc in H.
   unfold lookup_loc in H.
   rewrite H in |- *.
   case (h2 l).
  auto.
 auto.
unfold disjoint2 in pf1.
  generalize (pf1 l H).
  intros.
  unfold unused_loc in H0.
  unfold lookup_loc in H0.
  rewrite H0 in |- *.
  case (h1 l).
 auto.
auto.
Qed.



Lemma union2_assoc : 
   forall (h1 h2 h3 : heap) pf1 pf2 pf3 pf4,
        union2 (union2 h1 h2 pf1) h3 pf2 = union2 h1 (union2 h2 h3 pf3) pf4. 

intros.
unfold union2 in |- *.
 eapply heap_extensional.
intros.
unfold lookup_loc in |- *.
case (h1 l).
 auto.
auto.
Qed.



Lemma union2_cong : 
   forall (h1 h2 : heap) pf1 pf2, 
      union2 h1 h2 pf1 = union2 h1 h2 pf2.

intros.
assert (pf1 = pf2).
 apply proof_irrelevance.
rewrite H in |- *.
  auto.
Qed.



Lemma union2_subst1 : 
   forall (h1 h2 h : heap) pf1 pf2, 
       h1 = h2 -> union2 h1 h pf1 = union2 h2 h pf2.

intros.
generalize pf1.
rewrite H in |- *.
intros.
apply union2_cong.
Qed.



Lemma union2_subst2 : 
   forall (h h1 h2 : heap) pf1 pf2, 
       h1 = h2 -> union2 h h1 pf1 = union2 h h2 pf2.

intros.
generalize pf1.
rewrite H in |- *.
intros.
apply union2_cong.
Qed.

(*******************************************)
(* Interaction of union2 with disjointness *)
(*******************************************)

(* for disjoint2 *)

Lemma disjoint2_union2_intro : 
   forall (h h1 h2 : heap) (pf : disjoint2 h1 h2),
        disjoint2 h h1 -> disjoint2 h h2 -> disjoint2 h (union2 h1 h2 pf).

intros.
unfold disjoint2 in |- *.
intros.
unfold union2 in |- *.
unfold unused_loc in |- *.
unfold lookup_loc in |- *.
assert (h1 l = None).
 unfold disjoint2 in H.
   unfold unused_loc in H.
   unfold lookup_loc in H.
   apply H.
   auto.
rewrite H2 in |- *.
  unfold disjoint2 in H0.
  unfold unused_loc in H0.
  unfold lookup_loc in H0.
  apply H0.
  auto.
Qed.

Implicit Arguments disjoint2_union2_intro [h h1 h2 pf].



Lemma disjoint2_union2_elim1 : 
   forall (h h1 h2 : heap) (pf : disjoint2 h1 h2), 
     disjoint2 (union2 h1 h2 pf) h -> disjoint2 h1 h.

intros.
unfold disjoint2 in |- *.
intros.
unfold disjoint2 in H.
 eapply H.
generalize H0.
unfold union2 in |- *.
unfold valid_loc in |- *.
unfold selects in |- *.
unfold lookup_loc in |- *.
intros.
destruct H1 as [A].
destruct H1 as [v].
rewrite H1 in |- *.
exists A.
exists v.
auto.
Qed.

Implicit Arguments disjoint2_union2_elim1 [h h1 h2 pf].


Lemma disjoint2_union2_elim2 : 
   forall (h h1 h2 : heap) (pf : disjoint2 h1 h2), 
     disjoint2 (union2 h1 h2 pf) h -> disjoint2 h2 h.

intros.
unfold disjoint2 in |- *.
intros.
unfold disjoint2 in H.
 eapply H.
generalize H0.
unfold valid_loc in |- *.
unfold selects in |- *.
unfold union2 in |- *.
intros.
destruct H1 as (A).
destruct H1 as (v).
exists A.
exists v.
generalize (disjoint2_commute pf l H0).
intros.
unfold unused_loc in H2.
rewrite H2 in |- *.
unfold lookup_loc in |- *.
auto.
Qed.

Implicit Arguments disjoint2_union2_elim2 [h h1 h2 pf].


(* for disjoint_heap_list *)

Lemma disjoint_heap_list_union2_intro : 
   forall (h1 h2 : heap) (hs : list heap) (pf : disjoint2 h1 h2),
       disjoint_heap_list h1 hs -> disjoint_heap_list h2 hs -> 
            disjoint_heap_list (union2 h1 h2 pf) hs.

intros.
induction hs.
 auto.
simpl in |- *.
  simpl in H.
  simpl in H0.
  split.
 apply disjoint2_commute.
   apply disjoint2_union2_intro.
  apply disjoint2_commute.
     tauto.
 apply disjoint2_commute.
    tauto.
 tauto.
Qed.

Implicit Arguments disjoint_heap_list_union2_intro [h1 h2 hs pf].



Lemma disjoint_heap_list_union2_elim : 
   forall  (h1 h2 : heap) (hs : list heap) (pf : disjoint2 h1 h2),
       disjoint_heap_list (union2 h1 h2 pf) hs -> 
          disjoint_heap_list h1 hs /\ disjoint_heap_list h2 hs.

intros h1 h2.
induction hs.
 simpl in |- *.
   auto.
simpl in |- *.
  intros.
  destruct H.
  generalize (disjoint2_union2_elim1 H).
  intros.
  generalize (disjoint2_union2_elim2 H).
  intros.
  destruct (IHhs pf H0).
   tauto.
Qed.

Implicit Arguments disjoint_heap_list_union2_elim [h1 h2 hs pf].




(****************************************************)
(* Union of a heap with a list of heaps             *)
(* Sets up the induction for general disjoint union *)
(****************************************************)
Program Fixpoint 
   union_heap_list (h : heap) (hs : list heap) (pf1 : disjoint hs)
                   (pf2 : disjoint_heap_list h hs) {struct hs} : heap :=

   match hs with
    | nil => h
    | hh::ht => union_heap_list (union2 h hh _) ht _ _
   end.
   
Next Obligation.
simpl in pf2.
 tauto.
Defined.

Next Obligation.
simpl in pf1.
 tauto.
Defined.

Next Obligation.
 eapply disjoint_heap_list_union2_intro.
 rewrite <- Heq_hs in pf2.
   simpl in pf2.
    tauto.
rewrite <- Heq_hs in pf1.
  simpl in pf1.
   tauto.
Defined.




Lemma union_heap_list_cong : 
   forall (h : heap) (hs : list heap) pf1 pf2 pf3 pf4,
         union_heap_list h hs pf1 pf2 = union_heap_list h hs pf3 pf4.

intros.
 replace pf1 with pf3.
  replace pf2 with pf4.
  auto.
 apply proof_irrelevance.
apply proof_irrelevance.
Qed.



Lemma union_heap_list_subst1 : 
   forall (h1 h2 : heap) (hs : list heap) pf1 pf2 pf3 pf4,
      h1 = h2 -> 
         union_heap_list h1 hs pf1 pf2 = union_heap_list h2 hs pf3 pf4.

intros.
generalize pf2.
rewrite H in |- *.
intros.
apply union_heap_list_cong.
Qed.




Lemma union_heap_list_subst2 : 
   forall (h : heap) (hs1 hs2 : list heap) pf1 pf2 pf3 pf4,
      hs1 = hs2 -> 
         union_heap_list h hs1 pf1 pf2 = union_heap_list h hs2 pf3 pf4.

intros.
generalize pf1 pf2.
rewrite H in |- *.
intros.
apply union_heap_list_cong.
Qed.



(****************************************************)
(* Interaction of union_heap_list with disjointness *)
(****************************************************)

(* first for disjoint2 *)

Lemma disjoint2_union_heap_list_intro : 
    forall (hs : list heap) (h h0 : heap) pf1 pf2,
         disjoint2 h0 h -> disjoint_heap_list h0 hs -> 
              disjoint2 h0 (union_heap_list h hs pf1 pf2).

induction hs.
 auto.
simpl in |- *.
  intros.
   eapply IHhs.
 apply disjoint2_union2_intro.
   tauto.
  tauto.
 tauto.
Qed.

Implicit Arguments disjoint2_union_heap_list_intro [hs h h0 pf1 pf2].




Lemma disjoint2_union_heap_list_elim : 
    forall (hs : list heap) (h h0 : heap) pf1 pf2,
           disjoint2 h0 (union_heap_list h hs pf1 pf2) -> 
                disjoint2 h0 h /\ disjoint_heap_list h0 hs.


induction hs.
 auto.
simpl in |- *.
  intros.
  assert
   (disjoint2 h0
      (union2 h a
         (and_ind
            (fun (H : disjoint2 h a) (_ : disjoint_heap_list h hs) => H) pf2)) /\
    disjoint_heap_list h0 hs).
  eapply IHhs.
   apply H.
  destruct H0.
  generalize (disjoint2_commute H0).
  intros.
  split.
 apply disjoint2_commute.
    eapply disjoint2_union2_elim1.
   apply H2.
  split.
 apply disjoint2_commute.
    eapply disjoint2_union2_elim2.
   apply H2.
  auto.
Qed.

Implicit Arguments disjoint2_union_heap_list_elim [hs h h0 pf1 pf2].


(* for disjoint_heap_list *)

Lemma disjoint_heap_list_union_heap_list_intro : 
    forall (hs1 hs2 : list heap) (h : heap) pf1 pf2,
         disjoint_heap_list h hs2 -> disjoint_list_list hs1 hs2 -> 
              disjoint_heap_list (union_heap_list h hs1 pf1 pf2) hs2.

induction hs1.
 auto.
simpl in |- *.
  intros.
  destruct H0.
  apply IHhs1.
 apply disjoint_heap_list_union2_intro.
  auto.
 auto.
auto.
Qed.

Implicit Arguments disjoint_heap_list_union_heap_list_intro [hs1 hs2 h pf1 pf2].




Lemma disjoint_heap_list_union_heap_list_elim : 
    forall (hs1 hs2 : list heap) (h : heap) pf1 pf2,
         disjoint_heap_list (union_heap_list h hs1 pf1 pf2) hs2 ->
            disjoint_heap_list h hs2 /\ disjoint_list_list hs1 hs2.

induction hs1.
 auto.
simpl in |- *.
  intros.
  assert
   (disjoint_heap_list
      (union2 h a
         (and_ind
            (fun (H : disjoint2 h a) (_ : disjoint_heap_list h hs1) => H) pf2))
      hs2 /\ disjoint_list_list hs1 hs2).
  eapply IHhs1.
   apply H.
  destruct H0.
  destruct (disjoint_heap_list_union2_elim H0).
   tauto.
Qed.

Implicit Arguments disjoint_heap_list_union_heap_list_elim [hs1 hs2 h pf1 pf2].




(**************************)
(* General disjoint union *)
(**************************)


Program Definition
   union (hs : list heap) (pf : disjoint hs) : heap :=
       match hs with 
        | nil => empty
        | hh :: ht => union_heap_list hh ht _ _
       end.

Next Obligation.
simpl in pf.
 tauto.
Defined.

Next Obligation.
simpl in pf.
 tauto.
Defined.



Lemma union_cong : 
   forall (hs : list heap) pf1 pf2, 
      union hs pf1 = union hs pf2.

intros.
assert (pf1 = pf2).
 apply proof_irrelevance.
rewrite H in |- *.
  auto.
Qed.


Lemma union_subst : 
   forall (hs1 hs2 : list heap) pf1 pf2,
      hs1 = hs2 -> union hs1 pf1 = union hs2 pf2.     

intros.
generalize pf1.
rewrite H in |- *.
intros.
apply union_cong.
Qed.


(******************************************)
(* Interaction of union with disjointness *)
(******************************************)

(* for disjoint2 *)


Lemma disjoint2_union_intro : 
    forall (h : heap) (hs : list heap) pf, 
          disjoint_heap_list h hs -> disjoint2 h (union hs pf).

induction hs.
 simpl in |- *.
   intros.
   apply disjoint_empty_left.
simpl in |- *.
  intros.
   eapply disjoint2_union_heap_list_intro.
  tauto.
 tauto.
Qed.

Implicit Arguments disjoint2_union_intro [h hs pf].



Lemma disjoint2_union_elim : 
    forall (h : heap) (hs : list heap) pf, 
         disjoint2 h (union hs pf) -> disjoint_heap_list h hs.

induction hs.
 auto.
simpl in |- *.
  intros.
   eapply disjoint2_union_heap_list_elim.
  apply H.
Qed.

Implicit Arguments disjoint2_union_elim [h hs pf].


(* for disjoint_heap_list *)

Lemma disjoint_heap_list_union_intro : 
    forall (hs1 hs2 : list heap) pf, 
       disjoint_list_list hs1 hs2 -> 
          disjoint_heap_list (union hs1 pf) hs2.

induction hs1.
 simpl in |- *.
   intros.
   apply disjoint_heap_list_empty.
simpl in |- *.
  intros.
  destruct H.
  apply disjoint_heap_list_union_heap_list_intro.
 auto.
auto.
Qed.

Implicit Arguments  disjoint_heap_list_union_intro [hs1 hs2 pf]. 



Lemma disjoint_heap_list_union_elim : 
    forall (hs1 hs2 : list heap) pf, 
       disjoint_heap_list (union hs1 pf) hs2 -> disjoint_list_list hs1 hs2. 

induction hs1.
 auto.
simpl in |- *.
  intros.
   eapply disjoint_heap_list_union_heap_list_elim.
  apply H.
Qed.


Implicit Arguments disjoint_heap_list_union_elim [hs1 hs2 pf].





(****************************************)
(* Union is invariant under permutation *)
(****************************************)


(* first some rewriting rules for commutativity and associativity *)
(* of union2. less useful than one may expect, because can't *)
(* support dependent rewriting *)

Lemma union2_commute_rewrite : 
   forall (h1 h2 : heap) (pf : disjoint2 h1 h2),
      union2 h1 h2 pf = 
      union2 h2 h1 (disjoint2_commute pf).

intros.
apply union2_commute.
Qed.



Lemma union2_assoc_rewrite1 :
   forall (h1 h2 h3 : heap) 
          (pf1 : disjoint2 h1 h2) 
          (pf3 : disjoint2 (union2 h1 h2 pf1) h3),

    union2 (union2 h1 h2 pf1) h3 pf3 = 
    union2 h1 (union2 h2 h3 (disjoint2_union2_elim2 pf3))
              (disjoint2_union2_intro pf1 (disjoint2_union2_elim1 pf3)).

intros.
apply union2_assoc.
Qed.



Lemma union2_assoc_rewrite2 : 
   forall (h1 h2 h3 : heap)
          (pf1 : disjoint2 h2 h3)
          (pf2 : disjoint2 h1 (union2 h2 h3 pf1)),

    union2 h1 (union2 h2 h3 pf1) pf2 = 
    union2 (union2 h1 h2 (disjoint2_commute (disjoint2_union2_elim1 (disjoint2_commute pf2)))) h3
           (disjoint2_commute (disjoint2_union2_intro 
               (disjoint2_union2_elim2 (disjoint2_commute pf2))
               (disjoint2_commute pf1))).

intros.
symmetry  in |- *.
apply union2_assoc.
Qed.



(* Union distributes over list concatenation *)

Lemma union_heap_list_app_cons : 
     forall (hs1 hs2 : list heap) (h1 h2 : heap) pf1 pf2 pf3 pf4 pf5,
        union_heap_list h1 (hs1 ++ h2 :: hs2) pf1 pf2 = 
        union_heap_list (union2 h1 h2 pf3) (hs1 ++ hs2) pf4 pf5.

induction hs1.
 simpl in |- *.
   intros.
   apply union_heap_list_cong.
assert
 (forall (hs2 : list heap) (h1 h2 t : heap)
    (pf1 : disjoint (hs1 ++ h2 :: hs2))
    (pf2 : disjoint_heap_list h1 (hs1 ++ h2 :: hs2))
    (pf4 : disjoint (hs1 ++ hs2))
    (Ht : t =
          union2 h1 h2
            (proj1
               (disjoint_heap_list_cons_elim
                  (proj2 (disjoint_heap_list_app_elim pf2)))))
    (pf5 : disjoint_heap_list t (hs1 ++ hs2)),
  union_heap_list h1 (hs1 ++ h2 :: hs2) pf1 pf2 =
  union_heap_list t (hs1 ++ hs2) pf4 pf5).
 intros.
   generalize pf5.
   rewrite Ht in |- *.
   intros.
   apply IHhs1.
intros.
  simpl in |- *.
  apply H.
  rewrite
   (union2_assoc_rewrite1 h1 h2 a pf3
      (and_ind
         (fun (H0 : disjoint2 (union2 h1 h2 pf3) a)
            (_ : disjoint_heap_list (union2 h1 h2 pf3) (hs1 ++ hs2)) => H0)
         pf5)) in |- *.
  rewrite
   (union2_assoc_rewrite1 h1 a h2
      (and_ind
         (fun (H0 : disjoint2 h1 a)
            (_ : disjoint_heap_list h1 (hs1 ++ h2 :: hs2)) => H0) pf2)
      (proj1
         (disjoint_heap_list_cons_elim
            (proj2
               (disjoint_heap_list_app_elim
                  (h:=union2 h1 a
                        (and_ind
                           (fun (H0 : disjoint2 h1 a)
                              (_ : disjoint_heap_list h1 (hs1 ++ h2 :: hs2)) =>
                            H0) pf2)) (hs1:=hs1) (hs2:=
                  h2 :: hs2)
                  (union_heap_list_obligation_3 
                    h1 (a :: hs1 ++ h2 :: hs2) pf1 pf2 a
                     (hs1 ++ h2 :: hs2) (refl_equal (a :: hs1 ++ h2 :: hs2))))))))
   in |- *.
  apply union2_subst2.
  apply union2_commute.
Qed.




Lemma union_heap_list_permute : 
    forall (hs1 hs2 : list heap) (h : heap) pf1 pf2 pf3 pf4,
        Permutation hs1 hs2 -> 
          union_heap_list h hs1 pf1 pf2 =
          union_heap_list h hs2 pf3 pf4.

induction hs1.
 simpl in |- *.
   intros.
   generalize pf3 pf4.
   rewrite (Permutation_nil H) in |- *.
   auto.
intros.
  destruct (Permutation_cons H).
  destruct H0.
  destruct H0.
  assert
   (exists pf3 : _,
      exists pf4 : _,
        exists pf5 : _,
          union_heap_list h (a :: hs1) pf1 pf2 =
          union_heap_list (union2 h a pf3) (x ++ x0) pf4 pf5).
 exists (proj1 pf2).
   exists (disjoint_permute (proj1 pf1) H1).
   assert (disjoint_heap_list (union2 h a (proj1 pf2)) (x ++ x0)).
  apply disjoint_heap_list_union2_intro.
   apply (disjoint_heap_list_permute (proj2 pf2) H1).
  apply (disjoint_heap_list_permute (proj2 pf1) H1).
 exists H2.
   simpl in |- *.
   apply IHhs1.
   auto.
destruct H2.
  destruct H2.
  destruct H2.
  rewrite H2 in |- *.
  symmetry  in |- *.
  generalize pf3 pf4.
  rewrite H0 in |- *.
  intros.
  apply union_heap_list_app_cons.
Qed.




Lemma union_app : 
   forall (hs1 hs2 : list heap) (h : heap) pf1 pf2 pf3, 
       union (hs1 ++ h :: hs2) pf1 = 
       union_heap_list h (hs1 ++ hs2) pf2 pf3.

induction hs1.
 simpl in |- *.
   intros.
   apply union_heap_list_cong.
intros.
  simpl in |- *.
  assert
   (exists epf1 : _,
      exists epf2 : _,
        exists epf3 : _,
          union_heap_list a (hs1 ++ h :: hs2)
            (and_ind
               (fun (H : disjoint (hs1 ++ h :: hs2))
                  (_ : disjoint_heap_list a (hs1 ++ h :: hs2)) => H) pf1)
            (and_ind
               (fun (_ : disjoint (hs1 ++ h :: hs2))
                  (H0 : disjoint_heap_list a (hs1 ++ h :: hs2)) => H0) pf1) =
          union_heap_list (union2 a h epf1) (hs1 ++ hs2) epf2 epf3).
 simpl in pf1.
   simpl in pf2.
   simpl in pf3.
   exists (disjoint2_commute (proj1 pf3)).
   exists (proj1 pf2).
   assert
    (disjoint_heap_list (union2 a h (disjoint2_commute (proj1 pf3)))
       (hs1 ++ hs2)).
  apply disjoint_heap_list_union2_intro.
    tauto.
   tauto.
 exists H.
   apply union_heap_list_app_cons.
  destruct H.
  destruct H.
  destruct H.
  rewrite H in |- *.
  apply union_heap_list_subst1.
  apply union2_commute.
Qed.


(****************)
(* Main theorem *)
(****************)


Theorem union_permute : 
    forall (hs1 hs2 : list heap) pf1 pf2, 
          Permutation hs1 hs2 -> union hs1 pf1 = union hs2 pf2.

induction hs1.
 simpl in |- *.
   intros.
   generalize pf2.
   rewrite (Permutation_nil H) in |- *.
   auto.
intros.
  destruct (Permutation_cons H).
  destruct H0.
  destruct H0.
  generalize pf2.
  rewrite H0 in |- *.
  intros.
  assert
   (exists pf2 : _,
      exists pf3 : _,
        union (x ++ a :: x0) pf0 = union_heap_list a (x ++ x0) pf2 pf3).
 exists (disjoint_permute (proj1 pf1) H1).
   exists (disjoint_heap_list_permute (proj2 pf1) H1).
   apply union_app.
destruct H2.
  destruct H2.
  rewrite H2 in |- *.
  simpl in |- *.
  apply union_heap_list_permute.
  auto.
Qed.


(******************************)
(* Further lemmas about union *)
(******************************)


(** unit laws **)

Lemma union2_empty_left : 
    forall (h : heap) pf, union2 h empty pf = h.

intros.
unfold union2 in |- *.
apply heap_extensional.
intros.
unfold lookup_loc in |- *.
unfold empty in |- *.
case (h l).
 auto.
auto.
Qed.



Lemma union2_empty_right : 
    forall (h : heap) pf, union2 empty h pf = h.

intros.
rewrite (union2_commute empty h pf (disjoint2_commute pf)) in |- *.
apply union2_empty_left.
Qed.

Lemma union_heap_list_empty :
   forall (hs : list heap) pf1 pf2 pf3, 
      union_heap_list empty hs pf1 pf2 = union hs pf3.

induction hs.
 simpl in |- *.
   auto.
intros.
  simpl in |- *.
  apply union_heap_list_subst1.
  apply union2_empty_right.
Qed.


Lemma union_heap_list_app : 
   forall (hs1 hs2 : list heap) (h : heap) pf1 pf2 pf3 pf4 pf5 pf6,    
    union_heap_list h (hs1 ++ hs2) pf1 pf2 = 
    union_heap_list (union_heap_list h hs1 pf3 pf4) hs2 pf5 pf6.

induction hs1.
 simpl in |- *.
   intros.
   apply union_heap_list_cong.
intros.
  simpl in |- *.
  apply IHhs1.
Qed.



(*************************)
(* Flattening theorem    *)
(* removes nested unions *)
(*************************)

Theorem union_assoc : 
   forall (hs1 hs2 : list heap) pf1 pf2 pf3,
    union ((union hs1 pf1) :: hs2) pf2 = union (hs1 ++ hs2) pf3.

induction hs1.
 simpl in |- *.
   intros.
   apply union_heap_list_empty.
intros.
  simpl in |- *.
  symmetry  in |- *.
  apply union_heap_list_app.
Qed.


(**********************)
(* Cancelation lemmas *)
(**********************)


Lemma union2_cancel1 : 
   forall (h1 h2 h : heap) pf1 pf2,
    union2 h1 h pf1 = union2 h2 h pf2 -> h1 = h2.

intros.
apply heap_extensional.
intros.
assert (forall h1 h2 : heap, h1 = h2 -> h1 l = h2 l).
 intros.
   rewrite H0 in |- *.
   auto.
generalize (H0 (union2 h1 h pf1) (union2 h2 h pf2) H).
  intros.
  unfold union2 in H1.
  unfold lookup_loc in H1.
  unfold lookup_loc in |- *.
  destruct (loc_em l h1).
 unfold unused_loc in H2.
   unfold lookup_loc in H2.
   rewrite H2 in H1.
   destruct (loc_em l h2).
  unfold unused_loc in H3.
    unfold lookup_loc in H3.
    rewrite H3 in H1.
    rewrite H2 in |- *.
    rewrite H3 in |- *.
    auto.
 unfold valid_loc in H3.
   destruct H3.
   destruct H3.
   unfold selects in H3.
   rewrite H3 in H1.
   unfold disjoint2 in pf2.
   unfold unused_loc in pf2.
   unfold lookup_loc in pf2.
   assert (valid_loc l h2).
  unfold valid_loc in |- *.
    exists x.
    exists x0.
    unfold selects in |- *.
    auto.
 generalize (pf2 l H4).
   intros.
    absurd (None = Some (dyn x x0)).
   discriminate.
 rewrite H5 in H1.
   auto.
unfold valid_loc in H2.
  destruct H2.
  destruct H2.
  unfold selects in H2.
  rewrite H2 in H1.
  destruct (loc_em l h2).
 unfold unused_loc in H3.
   unfold lookup_loc in H3.
   rewrite H3 in H1.
   assert (valid_loc l h1).
  unfold valid_loc in |- *.
    unfold selects in |- *.
    exists x.
    exists x0.
    auto.
 generalize (pf1 l H4).
   intros.
   assert (valid_loc l h).
  unfold valid_loc in |- *.
    unfold selects in |- *.
    exists x.
    exists x0.
    auto.
 destruct (loc_ex H6 H5).
unfold valid_loc in H3.
  destruct H3.
  destruct H3.
  unfold selects in H3.
  rewrite H3 in H1.
  rewrite H2 in |- *.
  rewrite H3 in |- *.
  auto.
Qed.

Implicit Arguments union2_cancel1 [h1 h2 h pf1 pf2].



Lemma union2_cancel2 : 
   forall (h1 h2 h : heap) pf1 pf2,
    union2 h h1 pf1 = union2 h h2 pf2 -> h1 = h2.

intros.
 replace (union2 h h1 pf1) with (union2 h1 h (disjoint2_commute pf1))in H.
  replace (union2 h h2 pf2) with (union2 h2 h (disjoint2_commute pf2))in H.
   eapply union2_cancel1.
    apply H.
   apply union2_commute.
  apply union2_commute.
Qed.

Implicit Arguments union2_cancel2 [h1 h2 h pf1 pf2].



Lemma union_heap_list_union2 : 
   forall (hs : list heap) (h : heap) pf1 pf2 pf3 pf4,
       union_heap_list h hs pf1 pf2 = union2 h (union hs pf3) pf4.

induction hs.
 simpl in |- *.
   intros.
   symmetry  in |- *.
   apply union2_empty_left.
intros.
  elim pf1.
  elim pf2.
  elim pf3.
  intros.
  assert
   (exists pf5 : _,
      exists pf6 : _,
        exists pf7 : _,
          union2 h (union (a :: hs) pf3) pf4 =
          union2 (union2 h a pf5) (union hs pf6) pf7).
 exists H1.
   exists H3.
   assert (disjoint2 (union2 h a H1) (union hs H3)).
  apply disjoint2_union_intro.
    apply disjoint_heap_list_union2_intro.
   auto.
  auto.
 exists H5.
   rewrite (union2_assoc_rewrite1 h a (union hs H3) H1 H5) in |- *.
   apply union2_subst2.
   simpl in |- *.
   apply IHhs.
destruct H5.
  destruct H5.
  destruct H5.
  rewrite H5 in |- *.
  simpl in |- *.
  apply IHhs.
Qed.


Lemma union_heap_list_cancel1 : 
   forall (hs : list heap) (h1 h2 : heap) pf1 pf2 pf3 pf4,
     union_heap_list h1 hs pf1 pf2 = 
     union_heap_list h2 hs pf3 pf4 -> h1 = h2.

induction hs.
 simpl in |- *.
   auto.
intros.
  assert (exists pf1 : _, exists pf2 : _, union2 h1 a pf1 = union2 h2 a pf2).
 simpl in pf2.
   exists (proj1 pf2).
   exists (proj1 pf4).
    eapply IHhs.
   simpl in H.
   apply H.
  destruct H0.
  destruct H0.
   eapply union2_cancel1.
  apply H0.
Qed.

Implicit Arguments union_heap_list_cancel1 [hs h1 h2 pf1 pf2 pf3 pf4].




Lemma union_heap_list_cancel2 : 
   forall (hs1 hs2 : list heap) (h : heap) pf1 pf2 pf3 pf4 pf5 pf6,
     union_heap_list h hs1 pf1 pf2 = 
     union_heap_list h hs2 pf3 pf4 -> union hs1 pf5 = union hs2 pf6.

intros.
assert
 (forall h hs pf1 pf2,
  exists pf3 : _,
    exists pf4 : _,
      union_heap_list h hs pf1 pf2 = union2 h (union hs pf3) pf4).
 intros.
   exists pf0.
   assert (disjoint2 h0 (union hs pf0)).
  apply disjoint2_union_intro.
    auto.
 exists H0.
   apply union_heap_list_union2.
destruct (H0 h hs1 pf1 pf2).
  destruct H1.
  rewrite H1 in H.
  destruct (H0 h hs2 pf3 pf4).
  destruct H2.
  rewrite H2 in H.
  generalize (union2_cancel2 H).
  assert (x = pf5).
 apply proof_irrelevance.
rewrite H3 in |- *.
  assert (x1 = pf6).
 apply proof_irrelevance.
rewrite H4 in |- *.
  auto.
Qed.


Implicit Arguments union_heap_list_cancel2 [hs1 hs2 h pf1 pf2 pf3 pf4 pf5 pf6].




Lemma union_cons_cancel1 : 
   forall (h1 h2 : heap) (hs : list heap) pf1 pf2,
     union (h1 :: hs) pf1 = union (h2 :: hs) pf2 -> h1 = h2. 

intros.
simpl in H.
 eapply union_heap_list_cancel1.
apply H.
Qed.

Implicit Arguments union_cons_cancel1 [h1 h2 hs pf1 pf2].



Lemma union_cons_cancel2 : 
   forall (hs1 hs2 : list heap) (h : heap) pf1 pf2 pf3 pf4,
     union (h :: hs1) pf1 = union (h :: hs2) pf2 -> 
        union hs1 pf3 = union hs2 pf4.

simpl in |- *.
intros.
 eapply union_heap_list_cancel2.
apply H.
Qed.

Implicit Arguments union_cons_cancel2 [hs1 hs2 h pf1 pf2 pf3 pf4].



Lemma union_app_cancel1 :
   forall (hs1 hs2 hs : list heap) pf1 pf2 pf3 pf4,
     union (hs1 ++ hs) pf1 = union (hs2 ++ hs) pf2 -> 
        union hs1 pf3 =  union hs2 pf4. 

intros.
destruct (disjoint_app_elim pf1).
destruct (disjoint_app_elim pf2).
destruct H1.
destruct H3.
assert
 (exists pf2 : _,
    exists pf3 : _, union (hs1 ++ hs) pf1 = union (union hs1 pf2 :: hs) pf3).
 exists H0.
   assert (disjoint (union hs1 H0 :: hs)).
  simpl in |- *.
    split.
   auto.
  apply disjoint_heap_list_union_intro.
    auto.
 exists H6.
   symmetry  in |- *.
   apply union_assoc.
destruct H6.
  destruct H6.
  rewrite H6 in H.
  assert
   (exists pf1 : _,
      exists pf3 : _, union (hs2 ++ hs) pf2 = union (union hs2 pf1 :: hs) pf3).
 exists H2.
   assert (disjoint (union hs2 H2 :: hs)).
  simpl in |- *.
    split.
   auto.
  apply disjoint_heap_list_union_intro.
    auto.
 exists H7.
   symmetry  in |- *.
   apply union_assoc.
destruct H7.
  destruct H7.
  rewrite H7 in H.
  generalize (union_cons_cancel1 H).
   replace x with pf3.
  replace x1 with pf4.
  auto.
 apply proof_irrelevance.
apply proof_irrelevance.
Qed.


Lemma union_app_cancel2 :
   forall (hs1 hs2 hs : list heap) pf1 pf2 pf3 pf4,
     union (hs ++ hs1) pf1 = union (hs ++ hs2) pf2 -> 
        union hs1 pf3 =  union hs2 pf4. 

intros.
destruct (disjoint_app_elim pf1).
destruct (disjoint_app_elim pf2).
destruct H1.
destruct H3.
assert
 (exists pf2 : _,
    exists pf3 : _, union (hs ++ hs1) pf1 = union (union hs pf2 :: hs1) pf3).
 exists H2.
   assert (disjoint (union hs H2 :: hs1)).
  simpl in |- *.
    split.
   auto.
  apply disjoint_heap_list_union_intro.
    auto.
 exists H6.
   symmetry  in |- *.
   apply union_assoc.
destruct H6.
  destruct H6.
  rewrite H6 in H.
  assert
   (exists pf3 : _, union (hs ++ hs2) pf2 = union (union hs x :: hs2) pf3).
 assert (disjoint (union hs x :: hs2)).
  simpl in |- *.
    split.
   auto.
  apply disjoint_heap_list_union_intro.
    auto.
 exists H7.
   symmetry  in |- *.
   apply union_assoc.
destruct H7.
  rewrite H7 in H.
   eapply union_cons_cancel2.
  apply H.
Qed.


(** introduction lemmas **)

Lemma union_heap_list_union_subst :
    forall (hs1 hs2 : list heap) (h : heap) pf1 pf2 pf3 pf4 pf5 pf6,
       union hs1 pf1 = union hs2 pf2 -> 
         union_heap_list h hs1 pf3 pf4  = union_heap_list h hs2 pf5 pf6.

intros.
assert
 (exists pf5 : _,
    exists pf6 : _,
      union_heap_list h hs1 pf3 pf4 = union2 h (union hs1 pf5) pf6).
 exists pf3.
   assert (disjoint2 h (union hs1 pf3)).
  apply disjoint2_union_intro.
    auto.
 exists H0.
   apply union_heap_list_union2.
destruct H0.
  destruct H0.
  rewrite H0 in |- *.
  assert
   (exists pf7 : _,
      exists pf8 : _,
        union_heap_list h hs2 pf5 pf6 = union2 h (union hs2 pf7) pf8).
 exists pf2.
   assert (disjoint2 h (union hs2 pf2)).
  apply disjoint2_union_intro.
    auto.
 exists H1.
   apply union_heap_list_union2.
destruct H1.
  destruct H1.
  rewrite H1 in |- *.
  apply union2_subst2.
   replace x with pf1.
  replace x1 with pf2.
  auto.
 apply proof_irrelevance.
apply proof_irrelevance.
Qed.


Implicit Arguments union_heap_list_union_subst [hs1 hs2 h pf1 pf2 pf3 pf4 pf5 pf6].


Lemma union_heap_list_app_intro : 
    forall (hs hs1 hs2 : list heap) (h : heap) pf1 pf2 pf3 pf4 pf5 pf6,
     union hs1 pf1 = union hs2 pf2 -> 
     union_heap_list h (hs ++ hs1) pf3 pf4 = union_heap_list h (hs ++ hs2) pf5 pf6.

induction hs.
 simpl in |- *.
   intros.
    eapply union_heap_list_union_subst.
   apply H.
  intros.
  simpl in |- *.
   eapply IHhs.
  apply H.
Qed.

Implicit Arguments union_heap_list_app_intro [hs hs1 hs2 h pf1 pf2 pf3 pf4 pf5 pf6].



Lemma union_app_intro : 
    forall (hs hs1 hs2 : list heap) pf1 pf2 pf3 pf4,
       disjoint_list_list hs hs1 -> disjoint_list_list hs hs2 -> 
         union hs1 pf1 = union hs2 pf2 -> 
            union (hs ++ hs1) pf3 = union (hs ++ hs2) pf4.

induction hs.
 simpl in |- *.
   intros.
    replace pf3 with pf1.
   replace pf4 with pf2.
   auto.
  apply proof_irrelevance.
 apply proof_irrelevance.
intros.
  simpl in |- *.
   eapply union_heap_list_app_intro.
 apply H1.
Qed.


Implicit Arguments union_app_intro [hs hs1 hs2 pf1 pf2 pf3 pf4].




Lemma union_empty : 
   forall (hs1 hs2 : list heap) pf1 pf2,
       union (hs1 ++ empty :: hs2) pf1 = union (hs1 ++ hs2) pf2.

intros.
destruct (disjoint_app_elim pf1).
destruct (disjoint_app_elim pf2).
destruct H0.
destruct H2.
apply
 (union_app_intro (hs:=hs1) (hs1:=empty :: hs2) (hs2:=hs2) (pf1:=H0)
    (pf2:=H2)).
 auto.
auto.
simpl in |- *.
apply union_heap_list_empty.
Qed.



(*****************************************)
(* Export the defining property of union *)
(*****************************************)

(* union with selects *)

Lemma selects_union2_intro : 
   forall (l : loc) (A : Type) (v : A) (h1 h2 : heap) pf, 
      (selects l v h1 \/ selects l v h2) -> 
         selects l v (union2 h1 h2 pf).

unfold selects in |- *.
intros.
unfold union2 in |- *.
unfold lookup_loc in |- *.
destruct H.
 rewrite H in |- *.
   auto.
assert (h1 l = None).
 generalize (disjoint2_commute pf).
   intros.
   unfold disjoint2 in H0.
   unfold unused_loc in H0.
   unfold lookup_loc in H0.
   apply H0.
   unfold valid_loc in |- *.
   unfold selects in |- *.
   exists A.
   exists v.
   auto.
rewrite H0 in |- *.
  auto.
Qed.

Implicit Arguments selects_union2_intro [l A v h1 h2 pf].



Lemma selects_union2_elim :
   forall (l : loc) (A : Type) (v : A) (h1 h2 : heap) pf, 
      selects l v (union2 h1 h2 pf) -> 
         selects l v h1 \/ selects l v h2.

unfold selects in |- *.
intros.
unfold union2 in H.
unfold lookup_loc in H.
destruct (loc_em l h1).
 unfold unused_loc in H0.
   unfold lookup_loc in H0.
   rewrite H0 in H.
    tauto.
unfold valid_loc in H0.
  destruct H0.
  destruct H0.
  unfold selects in H0.
  rewrite H0 in H.
  rewrite H in H0.
   tauto.
Qed.

Implicit Arguments selects_union2_elim [l A v h1 h2 pf].




Lemma selects_union_heap_list_intro :
   forall (l : loc) (A : Type) (v : A) 
          (hs : list heap) (h : heap) pf1 pf2, 
      ((selects l v h) \/ (exists h : heap, In h hs /\ selects l v h)) -> 
         selects l v (union_heap_list h hs pf1 pf2).

induction hs.
   simpl in |- *.
   intros.
   destruct H.
  auto.
 destruct H.
    tauto.
intros.
  simpl in pf1.
  simpl in pf2.
  assert
   (exists epf1 : _,
      exists epf2 : _,
        exists epf3 : _,
          union_heap_list h (nil ++ a :: hs) pf1 pf2 =
          union_heap_list (union2 h a epf1) (nil ++ hs) epf2 epf3).
 exists (proj1 pf2).
   exists (proj1 pf1).
   assert (disjoint_heap_list (union2 h a (proj1 pf2)) (nil ++ hs)).
  simpl in |- *.
    apply disjoint_heap_list_union2_intro.
    tauto.
   tauto.
 exists H0.
   apply union_heap_list_app_cons.
destruct H0.
  destruct H0.
  destruct H0.
  unfold app in H0.
  rewrite H0 in |- *.
  apply IHhs.
  destruct H.
 left.
   apply selects_union2_intro.
   auto.
destruct H.
  destruct H.
  simpl in H.
  destruct H.
 left.
   apply selects_union2_intro.
   right.
   rewrite H in |- *.
   auto.
right.
  exists x2.
   tauto.
Qed.

Implicit Arguments selects_union_heap_list_intro [l A v hs h pf1 pf2].



Lemma selects_union_heap_list_elim :
   forall (l : loc) (A : Type) (v : A) 
          (hs : list heap) (h : heap) pf1 pf2, 
        selects l v (union_heap_list h hs pf1 pf2) ->
           (selects l v h) \/ (exists h : heap, In h hs /\ selects l v h).

induction hs.
 simpl in |- *.
    tauto.
intros.
  assert
   (exists epf1 : _,
      exists epf2 : _,
        exists epf3 : _,
          union_heap_list h (nil ++ a :: hs) pf1 pf2 =
          union_heap_list (union2 h a epf1) (nil ++ hs) epf2 epf3).
 exists (proj1 pf2).
   exists (proj1 pf1).
   assert (disjoint_heap_list (union2 h a (proj1 pf2)) (nil ++ hs)).
  simpl in |- *.
    apply disjoint_heap_list_union2_intro.
   apply (proj2 pf2).
  apply (proj2 pf1).
 exists H0.
   apply union_heap_list_app_cons.
destruct H0.
  destruct H0.
  destruct H0.
  unfold app in H0.
  rewrite H0 in H.
  destruct (IHhs (union2 h a x) x0 x1 H).
 destruct (selects_union2_elim H1).
   tauto.
 right.
   exists a.
   simpl in |- *.
    tauto.
destruct H1.
  right.
  exists x2.
  simpl in |- *.
   tauto.
Defined.

Implicit Arguments selects_union_heap_list_elim [l A v hs h pf1 pf2].


Lemma selects_union_intro : 
   forall (l : loc) (A : Type) (v : A) (hs : list heap) pf, 
      (exists h : heap, In h hs /\ selects l v h) -> 
         selects l v (union hs pf).

induction hs.
 simpl in |- *.
   intros.
   destruct H.
    tauto.
intros.
  simpl in |- *.
  apply selects_union_heap_list_intro.
  destruct H.
  destruct H.
  simpl in H.
  destruct H.
 left.
   rewrite H in |- *.
   auto.
right.
  exists x.
   tauto.
Qed.

Implicit Arguments selects_union_intro [l A v hs pf].



Lemma selects_union_elim : 
   forall (l : loc) (A : Type) (v : A) (hs : list heap) pf, 
      selects l v (union hs pf) ->
         exists h : heap, In h hs /\ selects l v h.

induction hs.
 simpl in |- *.
   intros.
   intros.
   generalize (selects_valid l v empty H).
   intros.
   generalize (unused_loc_empty l).
   intros.
   destruct (loc_ex H0 H1).
intros.
  destruct (selects_union_heap_list_elim H).
 exists a.
   simpl in |- *.
    tauto.
destruct H0.
  exists x.
  simpl in |- *.
   tauto.
Qed.

Implicit Arguments selects_union_elim [l A v hs pf].



(* union with valid_loc *)

Lemma valid_loc_union2_intro : 
   forall (l : loc) (h1 h2 : heap) pf, 
      (valid_loc l h1 \/ valid_loc l h2) -> 
         valid_loc l (union2 h1 h2 pf).

unfold valid_loc in |- *.
intros.
destruct H.
 destruct H.
   destruct H.
   exists x.
   exists x0.
   apply selects_union2_intro.
   left.
   auto.
destruct H.
  destruct H.
  exists x.
  exists x0.
  apply selects_union2_intro.
  right.
  auto.
Qed.

Implicit Arguments valid_loc_union2_intro [l h1 h2 pf].


Lemma valid_loc_union2_elim : 
   forall (l : loc) (h1 h2 : heap) pf, 
      valid_loc l (union2 h1 h2 pf) ->
         valid_loc l h1 \/ valid_loc l h2.

unfold valid_loc in |- *.
intros.
destruct H.
destruct H.
destruct (selects_union2_elim H).
 left.
   exists x.
   exists x0.
   auto.
right.
  exists x.
  exists x0.
  auto.
Qed.

Implicit Arguments valid_loc_union2_elim [l h1 h2 pf].



Lemma valid_loc_union_heap_list_intro :
   forall (l : loc) (hs : list heap) (h : heap) pf1 pf2, 
      ((valid_loc l h) \/ (exists h : heap, In h hs /\ valid_loc l h)) -> 
         valid_loc l (union_heap_list h hs pf1 pf2).

unfold valid_loc in |- *.
intros.
destruct H.
 destruct H.
   destruct H.
   exists x.
   exists x0.
   apply selects_union_heap_list_intro.
   left.
   auto.
destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  exists x0.
  exists x1.
  apply selects_union_heap_list_intro.
  right.
  exists x.
   tauto.
Qed.

Implicit Arguments valid_loc_union_heap_list_intro [l hs h pf1 pf2].



Lemma valid_loc_union_heap_list_elim :
   forall (l : loc) (hs : list heap) (h : heap) pf1 pf2, 
        valid_loc l (union_heap_list h hs pf1 pf2) ->
           (valid_loc l h) \/ (exists h : heap, In h hs /\ valid_loc l h).

unfold valid_loc in |- *.
intros.
destruct H.
destruct H.
destruct (selects_union_heap_list_elim H).
 left.
   exists x.
   exists x0.
   auto.
destruct H0.
  destruct H0.
  right.
  exists x1.
  split.
 auto.
exists x.
  exists x0.
  auto.
Qed.

Implicit Arguments valid_loc_union_heap_list_elim [l hs h pf1 pf2].


Lemma valid_loc_union_intro : 
   forall (l : loc) (hs : list heap) pf, 
      (exists h : heap, In h hs /\ valid_loc l h) -> 
         valid_loc l (union hs pf).

unfold valid_loc in |- *.
intros.
destruct H.
destruct H.
destruct H0.
destruct H0.
exists x0.
exists x1.
apply selects_union_intro.
exists x.
 tauto.
Qed.

Implicit Arguments valid_loc_union_intro [l hs pf].



Lemma valid_loc_union_elim : 
   forall (l : loc) (hs : list heap) pf, 
      valid_loc l (union hs pf) ->
         exists h : heap, In h hs /\ valid_loc l h.

unfold valid_loc in |- *.
intros.
destruct H.
destruct H.
destruct (selects_union_elim H).
destruct H0.
exists x1.
split.
 auto.
exists x.
  exists x0.
  auto.
Qed.

Implicit Arguments valid_loc_union_elim [l hs pf].



(* unused_loc with union *)


Lemma unused_loc_union2_intro : 
   forall (l : loc) (h1 h2 : heap) pf,
      unused_loc l h1 -> unused_loc l h2 -> 
         unused_loc l (union2 h1 h2 pf).

unfold unused_loc in |- *.
unfold union2 in |- *.
unfold lookup_loc in |- *.
intros.
rewrite H in |- *.
auto.
Qed.

Implicit Arguments unused_loc_union2_intro [l h1 h2 pf].



Lemma unused_loc_union2_elim : 
   forall (l : loc) (h1 h2 : heap) pf,
      unused_loc l (union2 h1 h2 pf) ->
         unused_loc l h1 /\ unused_loc l h2.

intros l h1 h2 pf.
destruct (loc_em l h1).
 generalize H.
   unfold unused_loc in |- *.
   unfold union2 in |- *.
   unfold lookup_loc in |- *.
   intros.
   rewrite H0 in H1.
   auto.
  unfold valid_loc in H.
  destruct H.
  destruct H.
  unfold selects in H.
  intro.
  unfold unused_loc in H0.
  unfold union2 in H0.
  unfold lookup_loc in H0.
  rewrite H in H0.
   absurd (Some (dyn x x0) = None).
  discriminate.
auto.
Qed.

Implicit Arguments unused_loc_union2_elim [l h1 h2 pf].



Lemma unused_loc_union_heap_list_intro : 
   forall (l : loc) (hs : list heap) (h : heap) pf1 pf2,
      unused_loc l h -> 
         (forall h : heap, In h hs -> unused_loc l h) ->
             unused_loc l (union_heap_list h hs pf1 pf2).

induction hs.
 auto.
intros.
  simpl in |- *.
  apply IHhs.
 apply unused_loc_union2_intro.
  auto.
 apply H0.
   simpl in |- *.
   auto.
intros.
  apply H0.
  simpl in |- *.
  auto.
Qed.

Implicit Arguments unused_loc_union_heap_list_intro [l hs h pf1 pf2].


Lemma unused_loc_union_heap_list_elim : 
   forall (l : loc) (hs : list heap) (h : heap) pf1 pf2,
      unused_loc l (union_heap_list h hs pf1 pf2) ->
         unused_loc l h /\ forall h : heap, In h hs -> unused_loc l h.

induction hs.
 simpl in |- *.
   intros.
   split.
  auto.
 intros.
    absurd False.
  auto.
 auto.
intros.
  cut
   (unused_loc l (union2 h a (proj1 pf2)) /\
    (forall h0 : heap, In h0 hs -> unused_loc l h0)).
 intros.
   destruct H0.
   destruct (unused_loc_union2_elim H0).
   split.
  auto.
 intros.
   simpl in H4.
   destruct H4.
  rewrite <- H4 in |- *.
    auto.
 apply (H1 h0 H4).
 eapply IHhs.
  simpl in H.
   eexact H.
Qed.

Implicit Arguments unused_loc_union_heap_list_elim [l hs h pf1 pf2].



Lemma unused_loc_union_intro : 
   forall (l : loc) (hs : list heap) pf,
      (forall h : heap, In h hs -> unused_loc l h) ->
         unused_loc l (union hs pf).
     
intros.
induction hs.
 simpl in |- *.
   apply unused_loc_empty.
simpl in |- *.
  apply unused_loc_union_heap_list_intro.
 apply H.
   simpl in |- *.
   auto.
intros.
  apply H.
  simpl in |- *.
  auto.
Qed.

Implicit Arguments unused_loc_union_intro [l hs pf].


Lemma unused_loc_union_elim : 
    forall (l : loc) (hs : list heap) pf,
       unused_loc l (union hs pf) -> 
          forall h : heap, In h hs -> unused_loc l h.

induction hs.
 simpl in |- *.
   intros.
    absurd False.
  auto.
 auto.
intros.
  destruct (unused_loc_union_heap_list_elim H).
  simpl in H0.
  destruct H0.
 rewrite <- H0 in |- *.
   auto.
apply (H2 h H0).
Qed.

Implicit Arguments unused_loc_union_elim [l hs pf].




(**************************************************)
(* Export the defining properties of update_loc   *)
(**************************************************)

(* update_loc with disjointness *)

Lemma disjoint2_update_loc_intro : 
  forall (l : loc) (A : Type) (v : A) (h1 h2 : heap),
     disjoint2 h1 h2 -> unused_loc l h2 -> 
        disjoint2 (update_loc h1 l v) h2.

intros.
unfold disjoint2 in |- *.
intros.
destruct (valid_loc_update_loc H1).
 rewrite H2 in |- *.
   auto.
destruct H2.
  apply H.
  auto.
Qed.

Implicit Arguments disjoint2_update_loc_intro [l A v h1 h2].


Lemma disjoint2_update_loc_elim : 
  forall (l : loc) (A : Type) (v : A) (h1 h2 : heap),
     disjoint2 (update_loc h1 l v) h2 -> unused_loc l h2.

unfold disjoint2 in |- *.
intros.
apply H.
unfold valid_loc in |- *.
exists A.
exists v.
apply sel_eq.
Qed.

Implicit Arguments disjoint2_update_loc_elim [l A v h1 h2]. 



Lemma disjoint_heap_list_update_loc_intro : 
   forall (l : loc) (A : Type) (v : A) (h : heap) (hs : list heap),
     disjoint_heap_list h hs -> 
       (forall h:heap, In h hs -> unused_loc l h) ->
          disjoint_heap_list (update_loc h l v) hs.

induction hs.
 auto.
intros.
  simpl in |- *.
  split.
 apply disjoint2_update_loc_intro.
  apply (proj1 H).
 apply H0.
   simpl in |- *.
   auto.
apply IHhs.
 apply (proj2 H).
intros.
  apply H0.
  simpl in |- *.
  auto.
Qed.

Implicit Arguments disjoint_heap_list_update_loc_intro [l A v h hs].


Lemma disjoint_heap_list_update_loc_elim : 
   forall (l : loc) (A : Type) (v : A) (h : heap) (hs : list heap),
     disjoint_heap_list (update_loc h l v) hs ->
       forall h:heap, In h hs -> unused_loc l h.

induction hs.
 simpl in |- *.
   intros.
    absurd False.
  auto.
 auto.
intros.
  simpl in H.
  destruct H.
  simpl in H0.
  destruct H0.
 rewrite <- H0 in |- *.
    eapply disjoint2_update_loc_elim.
    eexact H.
  apply IHhs.
 apply H1.
auto.
Qed.

Implicit Arguments disjoint_heap_list_update_loc_elim [l A v h hs].


Lemma disjoint_update_loc_intro : 
   forall (l : loc) (A : Type) (v : A) (h : heap) (hs : list heap),
     disjoint (h :: hs) -> 
       (forall h:heap, In h hs -> unused_loc l h) ->
          disjoint (update_loc h l v :: hs).

intros.
simpl in |- *.
split.
 apply (proj1 H).
apply disjoint_heap_list_update_loc_intro.
 apply (proj2 H).
auto.
Qed.

Implicit Arguments disjoint_update_loc_intro [l A v h hs].



Lemma disjoint_update_loc_elim : 
   forall (l : loc) (A : Type) (v : A) (h : heap) (hs : list heap),
     disjoint (update_loc h l v :: hs) -> 
       forall h:heap, In h hs -> unused_loc l h.

intros.
simpl in H.
destruct H.
generalize (disjoint_heap_list_update_loc_elim H1).
intros.
apply (H2 h0 H0).
Qed.

Implicit Arguments disjoint_update_loc_elim [l A v h hs].




(* union with update_loc *)

Lemma update_loc_union2_left : 
   forall (l : loc) (A : Type) (v : A) (h1 h2 : heap) pf1 pf2,
      update_loc (union2 h1 h2 pf1) l v = union2 (update_loc h1 l v) h2 pf2.

intros.
unfold union2 in |- *.
unfold update_loc in |- *.
unfold modify_loc in |- *.
apply heap_extensional.
unfold lookup_loc in |- *.
intros.
case (loc_eq l0 l).
 auto.
auto.
Qed.

Implicit Arguments update_loc_union2_left [l A v h1 h2 pf1 pf2].


Lemma update_loc_union2_right : 
   forall (l : loc) (A : Type) (v : A) (h1 h2 : heap) pf1 pf2,
      update_loc (union2 h1 h2 pf1) l v = union2 h1 (update_loc h2 l v) pf2.

intros.
rewrite (union2_commute h1 h2 pf1 (disjoint2_commute pf1)) in |- *.
rewrite (union2_commute h1 (update_loc h2 l v) pf2 (disjoint2_commute pf2))
 in |- *.
apply (@update_loc_union2_left).
Qed.

Implicit Arguments update_loc_union2_right [l A v h1 h2 pf1 pf2].




Lemma update_loc_union_heap_list : 
   forall (l : loc) (A : Type) (v : A) (hs : list heap) (h : heap) pf1 pf2 pf3 pf4,
      update_loc (union_heap_list h hs pf1 pf2) l v = 
      union_heap_list (update_loc h l v) hs pf3 pf4.

induction hs.
 auto.
intros.
  assert
   (exists epf1 : _,
      exists epf2 : _,
        exists epf3 : _,
          union_heap_list (update_loc h l v) (a :: hs) pf3 pf4 =
          union_heap_list (update_loc (union2 h a epf1) l v) hs epf2 epf3).
 exists (proj1 pf2).
   exists (proj1 pf1).
   assert (disjoint_heap_list (update_loc (union2 h a (proj1 pf2)) l v) hs).
  simpl in pf4.
    destruct pf4.
    generalize (disjoint_heap_list_update_loc_elim H0).
    intros.
    apply disjoint_heap_list_update_loc_intro.
   apply disjoint_heap_list_union2_intro.
    apply (proj2 pf2).
   apply (proj2 pf1).
  auto.
 exists H.
   simpl in |- *.
   apply union_heap_list_subst1.
   symmetry  in |- *.
   apply (@update_loc_union2_left).
  destruct H.
  destruct H.
  destruct H.
  rewrite H in |- *.
  simpl in |- *.
  apply IHhs.
Qed.

Implicit Arguments update_loc_union_heap_list [l A v hs h pf1 pf2 pf3 pf4].



Lemma update_loc_union :
   forall (l : loc) (A : Type) (v : A) (hs : list heap) (h : heap) pf1 pf2 pf3,
      unused_loc l (union hs pf1) ->
        update_loc (union (h :: hs) pf2) l v = union (update_loc h l v :: hs) pf3.

intros.
simpl in |- *.
apply (@update_loc_union_heap_list).
Qed.

Implicit Arguments update_loc_union [l A v hs h pf1 pf2 pf3].



Lemma update_loc_union_empty : 
   forall (l : loc) (A : Type) (v : A) (hs : list heap) pf1 pf2,
       unused_loc l (union hs pf1) ->
         update_loc (union hs pf1) l v = union (update_loc empty l v :: hs) pf2.

intros.
assert (exists pf2 : _, union hs pf1 = union (empty :: hs) pf2).
 assert (disjoint (empty :: hs)).
  simpl in |- *.
    split.
   auto.
  apply disjoint_heap_list_empty.
 exists H0.
   symmetry  in |- *.
   simpl in |- *.
   apply union_heap_list_empty.
destruct H0.
  rewrite H0 in |- *.
   eapply update_loc_union.
   eexact H.
Qed.

Implicit Arguments update_loc_union_empty [l A v hs pf1 pf2].

(** empty unions **)
Lemma eq_fun_args (A:Type) (B:Type) (f1:A->B) (f2:A->B) :
  f1 = f2 -> forall a, f1 a = f2 a.
Proof.
  intros.
  rewrite H. reflexivity.
Qed.

Implicit Arguments eq_fun_args [A B f1 f2].

Lemma union2_empty_empty (h1 h2:heap) pf:
  empty = union2 h1 h2 pf -> h1 = empty /\ h2 = empty.
Proof.
  intros. pose H. clearbody e. unfold union2 in H.   assert (h2 = empty). apply heap_extensional.
  intros. pose (eq_fun_args H l). clearbody e0.
  unfold empty in e0. 
  destruct (lookup_loc h1 l). inversion e0. rewrite <- e0. auto.
  split. subst. rewrite -> (union2_empty_left h1 pf) in *. subst. trivial.
  trivial.
Qed.
  
Implicit Arguments union2_empty_empty [h1 h2 pf].

Lemma union_empty_empty (h1 h2:heap) pf:
  empty = union (h1::h2::nil) pf -> h1 = empty /\ h2 = empty.
Proof.
  intros. unfold union in H. simpl in H.
  pose (union2_empty_empty H). trivial.
Qed.

Implicit Arguments union_empty_empty [h1 h2 pf].

Lemma union_empty_emptys (h1:heap) (hs:list heap) pf :
  empty = union (h1::hs) pf -> h1 = empty /\ exists pf2, empty = union hs pf2.
Proof.
  intros.
  assert (disjoint (hs ++ (h1::nil))).
  eapply disjoint_permute. eexact pf. 
  assert ((h1 :: nil) ++ hs = h1 :: hs). auto. rewrite <- H0. apply Permutation_app_swap.
  assert (empty = union (hs ++ (h1::nil)) H0). rewrite H. eapply union_permute.
  assert ((h1 :: nil) ++ hs = h1 :: hs). auto. rewrite <- H1. apply Permutation_app_swap.
  destruct (disjoint_cons_elim pf).
  assert (disjoint ((union hs H2) :: h1 :: nil)). unfold disjoint. simpl. split.
  auto. split. pose (@disjoint2_union_intro h1 hs H2 H3). eapply disjoint2_commute. auto.
  auto.
  pose (union_assoc hs (h1 :: nil) H2 H4 H0).
  rewrite <- e in H1.
  destruct (union_empty_empty H1). split.  trivial. 
  exists H2. auto.
Qed.

Implicit Arguments union_empty_emptys [h1 hs pf].
