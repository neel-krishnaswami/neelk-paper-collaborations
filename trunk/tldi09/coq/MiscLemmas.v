(* Ynot imports *)
Require Import DisjointUnion.
Require Import List.
Require Import MemModel.
Require Import ST.
Require Import Separation.
Require Import STsep.
Require Import Assumptions.
Require Import ListSet.
Require Import Precise.
(* Extra tactics and lemmas *)
Require Import Tactics.

Set Implicit Arguments.
Unset Strict Implicit.

Lemma useful_splits_lemma :
  forall (A : Type) (h1 h2 h3 h4 : heap) (l1 l2 : loc) (v1 v2 : A)
         (pf : disjoint (h1::h2::nil)),
  splits (union (h1::h2::nil) pf) (h3::h4::nil) ->
  (l1 --> v1) h2 -> (l2 --> v2) h3 ->
  v1 <> v2 ->
  splits h1 (h3::(fun l : loc => if loc_eq l l2 then None else h1 l)::nil).
intros.
unfold splits.
assert(disjoint (h3 :: (fun l : loc => if loc_eq l l2 then None (A:=dynamic) else h1 l) :: nil)).
unfold disjoint.
split.
split; trivial.
unfold disjoint_heap_list.
split; trivial.
unfold disjoint_heap_list.
unfold disjoint2.
split; trivial.
intros.
unfold valid_loc in H3.
destruct H3 as [ A' [ v H4 ] ].
unfold selects in H4.
unfold points_to in H1.
rewrite H1 in H4.
unfold update_loc in H4.
unfold modify_loc in H4.
destruct (loc_eq l l2).
rewrite e.
unfold unused_loc.
unfold lookup_loc.
destruct (loc_eq l2 l2).
trivial.
contradiction n; trivial.
discriminate H4.
exists H3.
apply heap_extensional.
intros.
unfold lookup_loc.
unfold union.
unfold union_heap_list.
unfold union_obligation_1, union_obligation_2.
unfold union2.
unfold lookup_loc.
unfold points_to in H0, H1.
unfold update_loc in H0, H1.
unfold modify_loc in H0, H1.
rewrite H1.
clear H3.
assert(l1 <> l2).
destruct (loc_eq l1 l2).
rewrite e in H0.
destruct H.
assert(union (h1::h2::nil) pf l2 = union (h3::h4::nil) x l2).
rewrite H.
trivial.
unfold union in H3.
unfold union_heap_list in H3.
unfold union2 in H3.
rewrite H1 in H3.
unfold lookup_loc in H3.
rewrite H0 in H3.
destruct(loc_eq l2 l2).
clear H.
unfold disjoint in pf.
destruct pf as [ [ _ _ ] pf3 ].
unfold disjoint_heap_list in pf3.
destruct pf3 as [ pf4 _ ].
generalize(disjoint2_commute pf4); intros pf5; clear pf4.
unfold disjoint2 in pf5.
assert(valid_loc l2 h2).
rewrite H0.
unfold valid_loc.
exists A.
exists v1.
unfold selects.
rewrite loc_eq_refl.
trivial.
generalize(pf5 l2 H); intros H4.
unfold unused_loc in H4.
unfold lookup_loc in H4.
rewrite H4 in H3.
assert(v1 = v2).
apply (Some_dyn_inj H3).
contradiction H2.
contradiction n.
trivial.
assumption.
destruct(loc_eq l l2).
generalize(pf); intros pf1.
unfold disjoint in pf1.
destruct pf1 as [ [ _ _ ] pf1 ].
unfold disjoint_heap_list in pf1.
destruct pf1 as [ pf1 _ ].
generalize(disjoint2_commute pf1); intros pf2.
unfold disjoint2 in pf1, pf2.
destruct H as [ pf3 H4 ].
assert(union (h1::h2::nil) pf l = union (h3::h4::nil) pf3 l).
rewrite H4; trivial.
unfold union in H.
unfold union_heap_list in H.
unfold union2 in H.
unfold lookup_loc in H.
rewrite H0 in H.
rewrite e in H.
destruct (loc_eq l2 l1).
contradiction H3; symmetry; assumption.
unfold empty in H.
assert(match h1 l2 with | Some v => Some v | None => None end = h1 l2).
induction (h1 l2).
trivial.
trivial.
rewrite e.
rewrite <- H5.
rewrite H.
clear H H5.
rewrite H1.
rewrite loc_eq_refl; trivial.
unfold empty; trivial.
Qed.

Lemma useful_points_to_lemma :
  forall (A : Type) (l l' : loc) (k : A) (h1 h2 : heap) 
         (pf : disjoint (h1::h2::nil)),
    (l --> k) h2 -> ((l' --> k) # nopre) (union (h1::h2::nil) pf) ->
      not(valid_loc l' h1) -> l = l'.
intros.
unfold points_to in *.
destruct H0 as [ n1 [ n2 [ N1 [ N4 N5 ] ] ] ].
assert(unused_loc l' h1 \/ valid_loc l' h1).
apply loc_em.
destruct H0; [ idtac | contradiction H0 ].
unfold unused_loc in H0.
unfold lookup_loc in H0.
destruct N1 as [ pf1 N6 ].
assert(union (h1 :: h2 :: nil) pf l' = union (n1::n2::nil) pf1 l').
rewrite N6; trivial.
unfold union in H2.
unfold union_heap_list in H2.
unfold union2 in H2.
unfold lookup_loc in H2.
rewrite H0 in H2.
rewrite H in H2.
rewrite N4 in H2.
unfold update_loc in H2.
unfold modify_loc in H2.
rewrite loc_eq_refl in H2.
destruct(loc_eq l' l).
symmetry; assumption.
inversion H2.
Qed.

Lemma extend_nopre : forall (P : heap -> Prop) (h1 h2 : heap) (pf : disjoint (h1::h2::nil)),
  (P # nopre) h1 -> (P # nopre) (union (h1::h2::nil) pf).
intros.
destruct H as [ h3 [ h4 [ H1 [ H2 H3 ] ] ] ].
set (h := union (h1::h2::nil) pf).
assert(splits h (h1::h2::nil)).
exists pf; trivial.
splits_rewrite_in H1 H.
splits_join_in H0 (0::1::1::nil).
apply splits_commute in H4.
exists h3; exists (union (h4::h2::nil) pf1).
intuition.
Qed.

Lemma remove_points_to_loc_union2 : 
  forall (A : Type) (v : A) (l : loc) (h1 h2 : heap) (pf : disjoint(h1::h2::nil)),
    (l --> v) h1 -> [(union (h1::h2::nil) pf) \\ l] = h2.
intros.
apply heap_extensional.
intros.
unfold lookup_loc.
unfold remove_loc.
destruct(loc_eq l l0).
rewrite e in *; clear e l.
assert(valid_loc l0 h1).
eapply points_to_valid.
apply H.
destruct pf as [ _ pf ].
destruct pf as [ pf _ ].
unfold disjoint2 in pf.
assert(unused_loc l0 h2).
apply pf; trivial.
unfold unused_loc, lookup_loc in H1.
symmetry; trivial.
assert(valid_loc l h1).
eapply points_to_valid.
eauto.
assert(unused_loc l0 h1).
eapply points_to_unused.
eauto.
assumption.
assert(disjoint (h2::nil)).
unfold disjoint, disjoint_heap_list.
intuition.
assert(union (h1::h2::nil) pf l0 = union (h2::nil) H2 l0).
eapply union_unused_loc.
assumption.
rewrite H3.
simpl.
trivial.
Qed.

Lemma remove_loc_disjoint2 :
  forall (l : loc) (h1 h2 : heap),
    disjoint (h1::h2::nil) -> disjoint(h1::[h2 \\ l]::nil).
intros.
destruct H as [ _ H ].
destruct H as [ H _ ].
unfold disjoint.
intuition.
unfold disjoint_heap_list.
trivial.
unfold disjoint_heap_list.
intuition.
unfold disjoint2 in *.
intros.
assert(unused_loc l0 h2).
apply H; trivial.
unfold remove_loc, unused_loc, lookup_loc in *.
destruct(loc_eq l l0).
trivial.
trivial.
Qed.

Lemma unused_loc_in_union2 : 
  forall (l : loc) (h1 h2 : heap) (pf : disjoint (h1::h2::nil)),
    unused_loc l h1 -> 
      exists pf', [union (h1::h2::nil) pf \\ l] = union (h1::[h2 \\ l]::nil) pf'.
intros.
generalize(remove_loc_disjoint2 l pf); intros.
exists H0.
apply heap_extensional.
intros.
unfold union, union_heap_list, union2.
unfold lookup_loc, modify_loc, remove_loc.
unfold unused_loc, lookup_loc in H.
destruct(loc_eq l l0).
rewrite_clear.
rewrite H.
trivial.
trivial.
Qed.

Lemma remove_nopre : forall (B : Set) (l l' : loc) (o o' : B) (h1 h2 : heap) (pf : disjoint(h1::h2::nil)),
  o <> o' -> (l --> o) h2 -> ((l' --> o') # nopre) (union (h1::h2::nil) pf) ->
    ((l' --> o') # nopre) h1.
intros.
destruct H1 as [ h3 [ h4 [ H5 [ H6 H7 ] ] ] ].
generalize(loc_em l h3); intros.
destruct H1.
destruct H5.
assert(disjoint (h2::h1::nil)).
eapply disjoint_permute.
apply pf.
PermutProve.
assert([union (h2::h1::nil) H3 \\ l] = h1).
eapply remove_points_to_loc_union2.
apply H0.
assert(union (h2::h1::nil) H3 = union (h1::h2::nil) pf).
apply union_permute.
PermutProve.
rewrite H5 in H4; clear H5.
rewrite H2 in H4; clear H2.
generalize(unused_loc_in_union2 x H1); intros.
destruct H2.
rewrite H2 in H4; clear H2.
rewrite <- H4; clear H4.
exists h3; exists [h4 \\ l].
intuition.
exists x0; trivial.
unfold valid_loc in H1.
destruct H1 as [ A [ v H1 ] ].
unfold selects in H1.
copy H6 H8.
unfold points_to, update_loc, modify_loc in H8.
rewrite H8 in H1.
destruct(loc_eq l l').
rewrite e in *; clear e l.
clear H1.
destruct H5.
assert(union (h1::h2::nil) pf l' = union (h3::h4::nil) x l').
rewrite H1; trivial.
clear H1.
assert(union (h3::h4::nil) x l' = Some (dyn B o')).
apply union_points_to.
eauto.
assert(disjoint (h2::h1::nil)).
eapply disjoint_permute.
apply pf.
PermutProve.
assert(union (h2::h1::nil) H3 l' = Some (dyn B o)).
apply union_points_to.
eauto.
assert(union (h1::h2::nil) pf = union (h2::h1::nil) H3).
apply union_permute.
PermutProve.
assert(Some (dyn B o') = Some(dyn B o)).
congruence.
assert(o' = o).
apply Some_dyn_inj.
trivial.
contradiction H.
symmetry; trivial.
unfold empty in H1.
inversion H1.
Qed.