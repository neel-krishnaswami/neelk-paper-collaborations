Require Import MemModel.
Require Import Separation.
Require Import ListSet.
Require Import Assumptions.
Require Import List.
Require Import DisjointUnion.
Require Import ST.
Require Import STsep.

Set Implicit Arguments.
Unset Strict Implicit.

Ltac splits_eqto_subheap H :=
  let n1 := fresh "tmpH" in
  let n2 := fresh "tmpPF" in
  let n3 := fresh "tmpH" in
    generalize H; intros n1; repeat(remove_empty_in n1; clear n1; intros n1);
    destruct n1 as [ n2 n3 ]; simpl in n3; clear n2 H; generalize n3; 
    clear n3; intros H.

Ltac splits_refl_empty := solve[repeat(remove_empty; try (apply splits_refl))].

Ltac same_two_subheaps H2 H4 Hn :=
  match goal with 
  (* Needs a few extra cases to cover all situations. *)
  | H1 : splits ?h (?h1::?h2::nil), H2 : splits ?h (?h3::?h4::nil), 
    H3 : (?l --> ?v1) ?h1, H4 : (?l --> ?v2) ?h3 |- _ =>
        let n1 := fresh "tmpH" in
        let n2 := fresh "tmpH" in
        let n3 := fresh "tmpH" in
        let n4 := fresh "tmpH" in
          generalize (points_to_same_subheap H3 H4 H1 H2);
          intros [ n1 n2 ];
          rewrite <- n1 in H2;
          destruct (splits_same_tail H1 H2) as [ n3 [ n4 Hn ]];
          simpl in Hn; clear n3 n4; clear H2 H4;
          generalize n1 n2; intros H2 H4; clear n1 n2
  end.

Ltac copy H1 H2 := generalize H1; intros H2.

Ltac contra2 := match goal with
  | H : False |- _ => contradiction H
  | H : ?v <> ?v |- _ => contradiction H; reflexivity
  | H1 : ?v1 <> ?v2, H2 : ?v1 = ?v2 |- _ => contradiction v1; apply H2
  | H1 : ?v1 <> ?v2, H2 : ?v2 = ?v1 |- _ => contradiction v1; symmetry; apply H2
  | H1 : valid_loc ?l ?h, H2 : unused_loc ?l ?h |- _ => contradiction (loc_ex H1 H2)
  end.

Ltac contra := repeat contra2.

Ltac splits_rewrite2 := match goal with
  | H : splits ?h1 (?h2::empty::nil) |- _ =>
          let tmp := fresh "tmp" in
          remove_empty_in H; clear H; intros H;  
          destruct H as [ tmp H ]; simpl in H; clear tmp;
          ((rewrite H in *; clear H h1) || (rewrite <- H in *; clear H h2))
  | H : splits ?h1 (empty::?h2::nil) |- _ =>
          let tmp := fresh "tmp" in
          remove_empty_in H; clear H; intros H;  
          destruct H as [ tmp H ]; simpl in H; clear tmp;
          ((rewrite H in *; clear H h1) || (rewrite <- H in *; clear H h2))
  | H : splits ?h1 (?h2::nil) |- _ =>
          let tmp := fresh "tmp" in
          destruct H as [ tmp H ]; simpl in H; clear tmp;
          ((rewrite H in *; clear H h1) || (rewrite <- H in *; clear H h2))
  | H : emp ?h |- _ => unfold emp in H; rewrite H in *; clear H h
  end.

Ltac splits_rewrite := repeat(splits_rewrite2).

Ltac splits_prove := match goal with
  | H : splits ?h (?h1::?h2::?h3::nil) |- splits ?h (?h2::?h1::?h3::nil) =>
      apply (splits_permute H); PermutProve
  | H1 : splits ?h (?h3::?h2::nil), H2 : splits ?h2 (?h1::?h4::nil) 
           |- splits ?h (?h1::?h3::?h4::nil) =>
      splits_rewrite_in H2 H1; splits_prove 
  | H1 : splits ?h (?h1::?h2::nil), H2 : splits ?h1 (?h3::?h4::nil)
           |- splits ?h (?h4::?h3::?h2::nil) =>
      splits_rewrite_in H2 H1; splits_prove
  | H1 : splits ?h (?h1::?h2::nil), H2 : splits ?h1 (?h3::?h4::nil)
           |- splits ?h (?h3::?h4::?h2::nil) =>
      splits_rewrite_in H2 H1; assumption
  | H : splits ?h (?h1::?h2::nil) |- splits ?h (?h2::?h1::nil) =>
      apply (splits_permute H); PermutProve
  end.

Ltac disjoint_prove := match goal with
  | H : disjoint (?h1::?h2::?h3::nil) |- disjoint(?h2::?h1::?h3::nil) =>
      apply (disjoint_permute H (hs2 := (h2::h1::h3::nil))); PermutProve
  | H : disjoint (?h1::?h2::?h3::nil) |- disjoint(?h2::?h3::nil) =>
      let tmp := fresh "tmp" in
        destruct(disjoint_cons_elim H) as [ tmp _ ]; assumption
  | H : splits ?h (?h1::?h2::?h3::nil) |- disjoint(?h2::?h3::nil) =>
      let tmp := fresh "tmp" in
        copy H tmp; destruct tmp as [ tmp _ ]; disjoint_prove; clear tmp
  | H : splits ?h (?h1::?h2::?h3::nil) |- disjoint (?h1::?h3::nil) =>
      let tmp := fresh "tmp" in
        assert(tmp : splits h (h2::h1::h3::nil)); apply (splits_permute H);
	PermutProve; disjoint_prove; clear tmp
  | H1 : splits ?h (?h4::?h3::nil), H2 : splits ?h4 (?h1::?h2::nil) |-
           disjoint(?h2::?h3::nil) =>
      splits_rewrite_in H2 H1; disjoint_prove
  end.

Ltac rewrite_clear2 := match goal with
  | H : this empty ?h |- _ =>
      unfold this in H; rewrite <- H in *; clear H
  | H : ?v1 = ?v2 |- _ =>
      rewrite H in *; clear H v1
  | H : ?v1 = ?v2 /\ ?v3 = ?v4 |- _ =>
      let n  := fresh "tmp" in
      let n' := fresh "tmp" in
        destruct H as [ n n' ]
  | H1 : ?v, H2 : ?v |- _ => clear H2 
  | H : ?h1::?t1 = ?h2::?t2 |- _ => inversion H; clear H
  end.

Ltac rewrite_clear := repeat(rewrite_clear2).

Ltac union_prove := match goal with
  |  |- union (?h1::?h2::?h3::nil) ?pf1 = union (?h2::?h1::?h3::nil) ?pf2 =>
      eapply union_permute; PermutProve
  end.

Ltac replace_with_using_in t1 t2 H1 H2 := 
  let Hn := fresh "tmp" in
    cut (t1 = t2); [ intro Hn; rewrite Hn in H2; clear Hn | H1 ].

Tactic Notation "rewrite" "union" constr(t1) "to" constr(t2) "in" ident(H2) := 
  let Hn := fresh "tmp" in
    cut (t1 = t2); [ intro Hn; rewrite Hn in H2; clear Hn | (union_prove || idtac) ].

Lemma A_eq_refl (A : Type) (A_eq : forall x y : A, {x = y} + {x <> y}) : 
  forall (a : A), A_eq a a = left _ (refl_equal a).
intros.
destruct(A_eq a a).
f_equal.
apply proof_irrelevance.
contradiction n.
trivial.
Qed.

Definition loc_eq_refl := A_eq_refl loc_eq.

Lemma Some_dyn_inj :
  forall A : Type, forall x y : A, 
    Some (dyn A x) = Some (dyn A y) -> x = y.
Proof.
intros.
injection H.
intros.
apply (inj_pairT2 Type (fun t => t) A x y H0).
Qed.

Definition remove_loc (h : heap) (l : loc) : heap :=
  (fun l' : loc => if loc_eq l l' then None else h l').

Definition single_loc (l : loc) (s : option dynamic) : heap :=
  (fun l' : loc => if loc_eq l l' then s else None).

Definition remove_locs (h : heap) (ls : set loc) : heap :=
  (fun l' : loc => if set_In_dec loc_eq l' ls then None else h l').

Definition remove_heap (h1 : heap) (h2 : heap) : heap :=
  (fun l' : loc => match h2 l' with | Some v => None | None => h1 l' end).

Definition add_heap (h1 : heap) (h2 : heap) : heap :=
  (fun l' : loc => match h2 l' with | Some v => Some v | None => h1 l' end).

Notation "'[' h '\\' l ']'" := (remove_loc h l) (at level 5).
Notation "'[' l '|-->' s ']'" := (single_loc l s) (at level 5).
Notation "'[' h '\\\' s ']'" := (remove_locs h s) (at level 5).
Notation "'[' h1 '--' h2 ']'" := (remove_heap h1 h2) (at level 5).
Notation "'[' h1 '+++' h2 ']'" := (add_heap h1 h2) (at level 5).

Lemma removed_locs_unused : forall (h : heap) (l : loc) (ls : set loc),
  set_In l ls -> unused_loc l [h \\\ ls].
intros.
unfold remove_locs, unused_loc, lookup_loc.
destruct(set_In_dec loc_eq l ls).
  trivial.
contradiction n; assumption.
Qed.

Lemma remove_loc_unused : forall (h : heap) (l : loc),
  unused_loc l [h \\ l].
intros.
unfold remove_loc.
unfold unused_loc.
unfold lookup_loc.
rewrite loc_eq_refl.
trivial.
Qed.

Lemma valid_locs_removed : forall (h1 h2 : heap) (l : loc),
  valid_loc l h2 -> unused_loc l [h1 -- h2].
intros.
unfold remove_heap, unused_loc, lookup_loc.
destruct H as [ A [ v H ] ].
unfold selects in H.
rewrite H.
trivial.
Qed.

Lemma unremoved_locs_not_valid : forall (h1 h2 : heap) (l : loc),
  valid_loc l [h1 -- h2] -> (valid_loc l h1 /\ unused_loc l h2).
intros.
destruct H as [ A [ v H ] ].
unfold selects in H.
unfold remove_heap in H.
case_eq (h2 l).
intros.
rewrite H0 in H; inversion H.
intros.
split.
rewrite H0 in H.
exists A; exists v.
apply H.
apply H0.
Qed.

Lemma unremoved_locs_valid : forall (h : heap) (l : loc) (ls : set loc),
  valid_loc l h -> not(set_In l ls) -> valid_loc l [h \\\ ls].
intros.
unfold remove_locs.
destruct H as [ A [ v H1 ] ].
unfold valid_loc.
exists A; exists v.
unfold selects in *.
destruct(set_In_dec loc_eq l ls).
  contradiction H0; assumption.
congruence.
Qed.
 
Lemma unremove_locs_valid : forall (h : heap) (l1 l2 : loc),
  valid_loc l1 h -> l1 <> l2 -> valid_loc l1 [h \\ l2].
intros.
unfold remove_loc.
destruct H as [ A [ v H1 ] ].
unfold valid_loc.
exists A; exists v.
unfold selects in *.
destruct(loc_eq l2 l1).
contradiction H0; symmetry; trivial.
rewrite H1.
trivial.
Qed.

Lemma valid_locs_not_removed : forall (h : heap) (l : loc) (ls : set loc),
  valid_loc l [h \\\ ls] -> not(set_In l ls).
intros.
unfold remove_locs, valid_loc in H.
destruct H as [ A [ v H ] ].
unfold selects in H.
destruct(set_In_dec loc_eq l ls).
  inversion H.
assumption.
Qed.

Lemma valid_loc_not_removed : forall (h : heap) (l1 l2 : loc),
  valid_loc l1 [h \\ l2] -> l1 <> l2.
intros.
unfold remove_loc in H.
unfold valid_loc in H.
destruct H as [ A [ c H ] ].
unfold selects in H.
destruct(loc_eq l2 l1).
inversion H.
destruct(loc_eq l1 l2).
contradiction n; symmetry; trivial.
assumption.
Qed.

Lemma points_to_valid : forall (A : Type) (l : loc) (v : A) (h : heap),
  (l --> v) h -> valid_loc l h.
intros.
unfold points_to in H.
rewrite H.
unfold valid_loc.
exists A; exists v.
unfold selects, update_loc, modify_loc.
rewrite loc_eq_refl.
trivial.
Qed.

Lemma points_to_unused : forall (A : Type) (l1 l2 : loc) (v : A) (h : heap),
  (l1 --> v) h -> l1 <> l2 -> unused_loc l2 h.
intros.
unfold points_to in H.
rewrite H.
unfold update_loc, modify_loc, unused_loc, lookup_loc.
destruct(loc_eq l2 l1).
contradiction H0; symmetry; trivial.
auto.
Qed.

Lemma unremoved_locs_unaffected : forall (h : heap) (l : loc) (ls : set loc),
  not(set_In l ls) -> [h \\\ ls] l = h l.
intros.
unfold remove_locs.
destruct(set_In_dec loc_eq l ls).
  contradiction H; trivial.
trivial.
Qed.

Lemma unremoved_loc_unaffected : forall (h : heap) (l1 l2 : loc),
  l1 <> l2 -> [h \\ l1] l2 = h l2.
intros.
unfold remove_loc.
destruct(loc_eq l1 l2).
  contradiction H; trivial.
trivial.
Qed.

Lemma splits_singleton_unused : 
  forall (A : Type) (hh : heap) (hs : list heap)
         (l : loc) (v : A) (pf : disjoint hs),
    (l --> v) hh -> disjoint (hh::hs) -> unused_loc l (union hs pf).
intros.
assert(H1 : valid_loc l hh).
  eapply points_to_valid; eauto.
destruct H0 as [ _ H0 ].
induction hs.
  simpl.
  unfold unused_loc, lookup_loc; auto.
destruct H0 as [ H0 H2 ].
fold disjoint_heap_list in H2.
unfold disjoint2 in H0.
generalize(H0 l H1); intros H3.
destruct(disjoint_cons_elim pf) as [ pf1 _ ].
generalize(IHhs pf1 H2); intros H4.
apply unused_loc_union_intro.
intros.
generalize(in_inv H5); intros H6.
destruct H6.
  rewrite <- H6; assumption.
generalize(unused_loc_union_elim H4); intros H7.
generalize(H7 h H6); intros H8.
assumption.
Qed.

Lemma valid_loc_unused_in_disjoint_heaps :
  forall (l : loc) (h : heap) (hs : list heap),
    valid_loc l h -> disjoint_heap_list h hs -> 
      forall h, (In h hs -> unused_loc l h).
intros.
induction hs.
  inversion H1.
destruct(in_inv H1).
  rewrite <- H2.
  destruct H0 as [ H0 _ ].
  unfold disjoint2 in H0.
  apply H0.
  apply H.
destruct H0.
fold disjoint_heap_list in H3.
apply IHhs; assumption.
Qed.

Lemma valid_locs_unused_implies_disjoint :
  forall (h  : heap) (hs : list heap),
    (forall l hh, valid_loc l h /\ In hh hs -> unused_loc l hh) ->
    disjoint_heap_list h hs.
intros.
induction hs.
  unfold disjoint_heap_list.
  trivial.
unfold disjoint_heap_list.
fold disjoint_heap_list.
split.
  unfold disjoint2.
  intros.
  intuition.
apply IHhs.
intros.
apply H.
intuition.
Qed.

Lemma union_unused_loc :
  forall (l : loc) (h : heap) (hs : list heap) pf1 pf2,
    unused_loc l h -> union (h::hs) pf1 l = union hs pf2 l.
intros.
generalize(loc_em l (union hs pf2)); intros H1.
destruct H1 as [ H1 | H1 ].
  unfold unused_loc, lookup_loc in H1; rewrite H1.
  generalize(unused_loc_union_elim H1); intros H2.
  assert(H3 : forall h' : heap, In h' (h :: hs) -> unused_loc l h').
    intros.
    destruct(in_inv H0).
      rewrite <- H3; assumption.
    apply H2; assumption.
  generalize(unused_loc_union_intro H3 (pf := pf1)); intros H4.
  unfold unused_loc, lookup_loc in H4.
  rewrite H4; trivial.
unfold valid_loc in H1.
destruct H1 as [ A [ v H1 ] ].
destruct (selects_union_elim H1) as [ h2 [ H2 H3 ] ].
assert(H4 : selects l v (union (h::hs) pf1)).
  apply selects_union_intro; exists h2; intuition.
unfold selects in H1, H4.
congruence.
Qed.

Lemma remove_heap_in_splits : forall (h hh : heap) (hs : list heap),
  splits h (hh::hs) -> splits [h -- hh] hs.
intros.
destruct H as [ pf H ].
destruct(disjoint_cons_elim pf) as [ pf1 _ ].
exists pf1.
apply heap_extensional.
intros.
unfold lookup_loc, remove_heap.
case_eq (hh l).
intros.
destruct(disjoint_cons_elim pf).
assert(valid_loc l hh).
unfold valid_loc, selects.
case_eq d.
intros.
exists type_of; exists val_of.
unfold selects.
rewrite H3 in H0.
apply H0.
generalize(valid_loc_unused_in_disjoint_heaps H3 H2); intros H4.
generalize(unused_loc_union_intro H4 (pf := pf1)); intros H5.
unfold unused_loc, lookup_loc in H5.
symmetry; assumption.
intros.
rewrite H.
eapply union_unused_loc.
apply H0.
Qed.

Lemma remove_points_to_loc :
  forall (A : Type) (h hh : heap) (hs : list heap) (l : loc) (v : A),
    (l --> v) hh -> splits h (hh::hs) -> splits [h \\ l] hs.
intros.
generalize(remove_loc_unused h l); intros H1.
generalize(points_to_valid H); intros H2.
destruct H0 as [ pf H3 ].
copy pf pf1.
destruct pf1 as [ pf1 pf3 ].
exists pf1.
fold disjoint in pf1.
apply heap_extensional.
intros.
destruct hs.
  destruct(loc_eq l l0).
    rewrite e.
    unfold remove_loc, lookup_loc.
    rewrite loc_eq_refl.
    simpl; auto.
  unfold lookup_loc.
  rewrite (unremoved_loc_unaffected h n).
  rewrite H3.
  simpl.
  unfold points_to in H.
  rewrite H.
  unfold update_loc, modify_loc.
  destruct(loc_eq l0 l).
    contradiction n; symmetry; assumption.
  auto.
destruct(loc_eq l l0).
  rewrite <- e.
  unfold unused_loc in H1.
  rewrite H1.
  unfold union.
  generalize(valid_loc_unused_in_disjoint_heaps H2 pf3); intros H4.
  assert(H5 : unused_loc l h0).
    apply H4.
    intuition.
  assert(H6 : forall h : heap, In h hs -> unused_loc l h).
    intros.
    apply H4; intuition.
  assert(unused_loc l (union_heap_list h0 hs
          (union_obligation_1 (h0 :: hs) pf1 h0 hs (refl_equal (h0 :: hs)))
          (union_obligation_2 (h0 :: hs) pf1 h0 hs (refl_equal (h0 :: hs))))).
    apply unused_loc_union_heap_list_intro; assumption.
  unfold unused_loc in H0.
  rewrite H0.
  trivial.
unfold lookup_loc.
rewrite unremoved_loc_unaffected; try assumption.
rewrite H3.
apply union_unused_loc.
eapply points_to_unused; eauto.
Qed.

Lemma union_valid_loc:
  forall (A : Type) (hh : heap) (hs : list heap) (pf : disjoint(hh::hs))
         (l : loc) (v : A),
    valid_loc l hh -> union (hh::hs) pf l = hh l.
intros.
induction hs.
simpl.
trivial.
assert(H1 : disjoint (a::hh::hs)).
  eapply disjoint_permute.
  apply pf.
  apply perm_swap.
copy H1 H2.
destruct H2 as [ _ [ H2 _ ] ].
generalize(disjoint2_commute H2); clear H2; intros H2.
generalize(H2 l H); clear H2; intros H2.
assert(H3 : union (hh::a::hs) pf = union (a::hh::hs) H1).
  apply union_permute.
  apply perm_swap.
rewrite H3.
assert(H4 : disjoint(a::hh::hs)).
  assumption.
destruct H4 as [ H4 _ ].
fold disjoint in H4.
assert(H5 : disjoint(hh::hs)).
apply H4.
generalize(union_unused_loc H1 H5 H2 (l := l)); intros H6.
rewrite H6.
apply IHhs.
Qed.

Lemma splits_points_to :
  forall (A : Type) (h hh : heap) (hs : list heap) (l : loc) (v : A),
    (l --> v) hh -> splits h (hh::hs) -> h l = hh l.
intros.
destruct H0.
rewrite H0.
eapply union_valid_loc.
  apply (nil (A := nat)). (* apparently I can choose what I want to prove? *)
eapply points_to_valid.
apply H.
Qed.

Lemma remove_add_heap : forall (h hh : heap) (hs : list heap),
  splits h (hh::hs) -> [[h -- hh] +++ hh] = h.
intros.
unfold remove_heap, add_heap.
apply heap_extensional.
intros.
unfold lookup_loc.
case_eq (hh l).
intros.
destruct H.
assert(union (hh::hs) x l = hh l).
eapply union_valid_loc.
apply h.
case_eq d.
intros.
exists type_of; exists val_of.
rewrite H1 in H0.
apply H0.
congruence.
intros.
trivial.
Qed.

Lemma unremoved_locs_unremoved : forall (h1 h2 : heap) (l : loc),
  unused_loc l h2 -> [h1 -- h2] l = h1 l.
intros.
unfold remove_heap.
unfold unused_loc in H.
unfold lookup_loc in H.
rewrite H.
trivial.
Qed.

Lemma merge_heap : forall (h hh : heap) (hs1 hs2 : list heap),
  splits h (hh::hs1) -> splits [h -- hh] hs2 ->
    splits h (hh::hs2).
intros.
generalize(remove_add_heap H); intros H1.
rewrite <- H1.
assert(disjoint (hh::hs2)).
unfold disjoint.
fold disjoint.
destruct H0.
intuition.
eapply valid_locs_unused_implies_disjoint.
intros.
destruct H2 as [ H2 H3 ].
generalize(valid_locs_removed h H2); intros H4.
rewrite H0 in H4.
eapply unused_loc_union_elim; eauto.
exists H2.
apply heap_extensional.
intros.
unfold lookup_loc.
generalize(loc_em l hh); intros H3.
destruct H3.
destruct(disjoint_cons_elim H2) as [ H4 _ ].
assert(union (hh::hs2) H2 l = union hs2 H4 l).
eapply union_unused_loc; eauto.
rewrite H1.
rewrite H5.
destruct H0.
generalize(unremoved_locs_unremoved h H3); intros H6.
rewrite <- H6.
assert(union hs2 x = union hs2 H4).
eapply union_cong.
rewrite <- H7.
rewrite H0.
trivial.
assert(union (hh::hs2) H2 l = hh l).
eapply union_valid_loc; eauto.
rewrite H4.
unfold add_heap.
induction (hh l).
trivial.
assert(unused_loc l [h -- hh]).
eapply valid_locs_removed; eauto.
unfold unused_loc, lookup_loc in H5.
assumption.
Qed.

Lemma union_points_to:
  forall (A : Type) (hh : heap) (hs : list heap) (pf : disjoint(hh::hs))
         (l : loc) (v : A),
    (l --> v) hh -> union (hh::hs) pf l = Some (dyn A v).
intros.
assert(union (hh::hs) pf l = hh l).
eapply union_valid_loc.
apply (True).
eapply points_to_valid.
apply H.
rewrite H0.
unfold points_to, update_loc, modify_loc in H.
rewrite H.
rewrite loc_eq_refl.
trivial.
Qed.

Lemma distinct_valid_loc_in_splits :
  forall (l1 l2 : loc) (h h1 h2 : heap) (hs : list heap),
    valid_loc l1 h1 -> valid_loc l2 h2 -> splits h (h1::h2::hs) -> 
      l1 <> l2.
intros.
destruct H1 as [ pf H1 ].
destruct(loc_eq l1 l2).
  rewrite e in H.
  copy pf pf2.
  destruct pf2 as [ _ [ pf2 _ ] ].
  generalize(pf2 l2 H); intros H2.
  unfold valid_loc in H0.
  destruct H0 as [ A [ v H0 ] ].
  unfold selects in H0.
  unfold unused_loc, lookup_loc in H2.
  rewrite H0 in H2.
  inversion H2.
assumption.
Qed.

Lemma distinct_points_to_in_splits : forall 
  (A1 A2 : Type) (l1 l2 : loc) (h h1 h2 : heap) (hs : list heap) (v1 : A1) (v2 : A2),
    (l1 --> v1) h1 -> (l2 --> v2) h2 -> splits h (h1::h2::hs) ->
    l1 <> l2.
intros.
eapply distinct_valid_loc_in_splits.
eapply points_to_valid; eauto.
eapply points_to_valid; eauto.
eauto.
Qed.

(*
Lemma splits_into_points_to : forall (A1 A2 : Type) (l1 l2 : loc) (v1 : A1) (v2 : A2) (h h1 h2 : heap),
  (l1 --> v1) h1 -> (l2 --> v2) h2 -> splits h (h1::h2::nil) ->
    l1 <> l2.
intros.
destruct H1.
destruct(loc_eq l1 l2).
rewrite e in H.
generalize(x); intros y.
destruct y as [ _ pf ].
destruct pf as [ pf _ ].
unfold disjoint2 in pf.
assert(valid_loc l2 h1).
unfold valid_loc.
exists A1; exists v1.
unfold selects.
unfold points_to in H.
rewrite H.
unfold update_loc.
unfold modify_loc.
destruct(loc_eq l2 l2).
trivial.
contradiction n; trivial.
generalize(pf l2 H2); intros H4.
unfold unused_loc in H4.
unfold lookup_loc in H4.
unfold points_to in H0.
rewrite H0 in H4.
unfold update_loc in H4.
unfold modify_loc in H4.
destruct(loc_eq l2 l2).
inversion H4.
contradiction n; trivial.
trivial.
Qed.
*)

Lemma splits_into_remove_points_to : forall (l : loc) (h : heap),
  splits h ([h \\ l]::[l |--> h l]::nil).
intros.
assert(pf : disjoint([h \\ l]::[l |--> h l]::nil)).
  split.
    split.
      simpl; trivial.
    unfold disjoint_heap_list; trivial.
  unfold disjoint_heap_list.
  split; trivial.
  unfold disjoint2.
  intros.
  generalize(valid_loc_not_removed H); intros H1.
  unfold unused_loc, lookup_loc, single_loc.
  destruct(loc_eq l l0).
    contradiction H1; symmetry; trivial.
  trivial.
exists pf.
unfold union, union_heap_list, union2.
unfold lookup_loc, remove_loc, single_loc.
apply heap_extensional.
intros.
unfold lookup_loc.
destruct(loc_eq l l0).
  rewrite e; trivial.
induction (h l0); trivial.
Qed.

(*
Lemma splits_merge_removed_loc :
  forall (A : Type) (v : A) (l : loc) (h h1 h2 : heap) (hs : list heap),
    (l --> v) h2 -> h1 l = h2 l -> splits h ([h1 \\ l]::h2::hs) ->
    splits h (h1::hs).
intros.
assert(pf : disjoint(h1::hs)).
generalize dependent h.
induction hs.
intros.
simpl.
intuition.
intros.*)

Lemma splits_merge_removed_loc3 : 
  forall (A : Type) (v : A) (l : loc) (h h1 h2 h3 : heap),
    (l --> v) h2 -> h1 l = h2 l -> splits h ([h1 \\ l]::h2::h3::nil) ->
    splits h (h1::h3::nil).
intros.
assert(disjoint (h1::h3::nil)).
destruct H1 as [ pf _ ].
unfold disjoint.
split.
split; trivial.
unfold disjoint_heap_list; trivial.
unfold disjoint_heap_list.
split; trivial.
unfold disjoint2.
intros.
destruct pf as [ [ _ pf1 ] pf2 ].
unfold disjoint_heap_list in pf1, pf2.
destruct pf1 as [ pf1 _ ].
destruct pf2 as [ pf2 [ pf3 _ ] ].
assert(valid_loc l h2).
eapply points_to_valid; eauto.
unfold disjoint2 in pf1, pf2, pf3.
destruct(loc_eq l l0).
rewrite e in H2.
apply pf1; assumption.
apply pf3.
eapply unremove_locs_valid; eauto.
exists H2.
destruct H1.
rewrite H1.
unfold union.
unfold union_heap_list.
unfold union2.
apply heap_extensional.
intros.
unfold lookup_loc.
unfold remove_loc.
destruct(loc_eq l l0).
rewrite <- e.
rewrite H0.
trivial.
assert(unused_loc l0 h2).
eapply points_to_unused; eauto.
unfold unused_loc in H3.
unfold lookup_loc in H3.
rewrite H3.
assert(match h1 l0 with | Some v0 => Some v0 | None => None end = h1 l0).
induction (h1 l0); trivial.
rewrite H4.
trivial.
Qed.

Lemma splits_into_remove_points3 :
  forall (A : Type) (h1 h2 h3 h4 : heap) (l : loc) (v : A),
    splits [h1 \\ l] (h2::h3::nil) -> (l --> v) h4 ->
      h1 l = h4 l -> splits h1 (h2::h3::h4::nil).
intros.
assert(unused_loc l [h1 \\ l]).
eapply remove_loc_unused.
destruct H.
copy H2 H3.
rewrite H in H3.
generalize(unused_loc_union_elim H3).
intros.
assert(In h2 (h2::h3::nil)).
simpl.
left.
trivial.
assert(In h3 (h2::h3::nil)).
simpl.
right.
left.
trivial.
generalize(H4 h2 H5); intros H7.
generalize(H4 h3 H6); intros H8.
clear H3 H4 H5 H6.
assert(disjoint (h2::h3::h4::nil)).
unfold disjoint.
split.
split.
split.
trivial.
unfold disjoint_heap_list; trivial.
unfold disjoint_heap_list.
split; try trivial.
unfold disjoint2.
intros.
destruct(loc_eq l l0).
rewrite <- e in H3.
unfold valid_loc in H3.
destruct H3 as [ A' [ v' H4 ] ].
unfold selects in H4.
unfold unused_loc in H8.
unfold lookup_loc in H8.
rewrite H8 in H4.
inversion H4.
eapply points_to_unused; eauto.
unfold disjoint_heap_list.
split.
copy x y.
destruct y as [ _ H10 ].
unfold disjoint_heap_list in H10.
destruct H10 as [ H10 _ ].
assumption.
split.
unfold disjoint2.
intros.
destruct(loc_eq l l0).
rewrite <- e in H3.
contra.
eapply points_to_unused; eauto.
trivial.
exists H3.
unfold union.
unfold union_heap_list.
unfold union2.
apply heap_extensional.
intros.
assert([h1 \\ l] l0 = union (h2 :: h3 :: nil) x l0).
rewrite H; trivial.
destruct(loc_eq l l0).
unfold lookup_loc.
unfold unused_loc in H7, H8.
unfold lookup_loc in H7, H8.
rewrite <- e.
rewrite H7.
rewrite H8.
assumption.
rewrite unremoved_loc_unaffected in H4.
unfold union in H4.
unfold union_heap_list in H4.
unfold union2 in H4.
unfold lookup_loc.
rewrite H4.
unfold lookup_loc.
assert(unused_loc l0 h4).
eapply points_to_unused; eauto.
unfold unused_loc in H5.
unfold lookup_loc in H5.
rewrite H5.
induction (h2 l0).
trivial.
induction (h3 l0); trivial.
assumption.
Qed.

Lemma equal_unions_distinct_points_to :
  forall (A : Type) (v1 v2 : A) (l : loc) (h1 h2 : heap) 
         (hs1 hs2 : list heap) pf1 pf2,
    (l --> v1) h1 -> (l --> v2) h2 -> union (h1::hs1) pf1 = union (h2::hs2) pf2 ->
      v1 = v2.
intros.
assert(H2 : union (h1::hs1) pf1 l = union (h2::hs2) pf2 l).
  rewrite H1; trivial.
clear H1.
assert(union (h1::hs1) pf1 l = h1 l).
  eapply union_valid_loc.
  apply A.
  eapply points_to_valid; eauto.
assert(union (h2::hs2) pf2 l = h2 l).
  eapply union_valid_loc.
  apply A.
  eapply points_to_valid; eauto.
rewrite H1 in H2.
rewrite H3 in H2.
unfold points_to in H, H0.
rewrite H in H2.
rewrite H0 in H2.
unfold update_loc, modify_loc in H2.
rewrite loc_eq_refl in H2.
apply Some_dyn_inj.
assumption.
Qed.

Lemma points_to_lemma : 
  forall (A : Type) (v : A) (l : loc) (h hh : heap)
         (hs : list heap),
    splits h (hh::hs) -> (l --> v) hh -> hh = [l |--> h l].
intros.
unfold single_loc.
apply heap_extensional.
intros.
unfold lookup_loc.
destruct (loc_eq l l0).
rewrite <- e.
symmetry.
eapply splits_points_to; eauto.
generalize(points_to_unused H0 n); intros H1.
unfold unused_loc, lookup_loc in H1.
assumption.
Qed.

Lemma points_to_splits_selects : forall (A : Type) (v : A) (l : loc) (h hh : heap) (hs : list heap),
  (l --> v) hh -> splits h (hh::hs) -> selects l v h.
intros.
assert(h l = hh l).
eapply splits_points_to; eauto.
unfold selects.
rewrite H1.
unfold points_to, update_loc, modify_loc in H.
rewrite H.
rewrite loc_eq_refl.
trivial.
Qed.

Lemma same_selects_equal : forall (A : Type) (v1 v2 : A) (l : loc) (h : heap),
  selects l v1 h -> selects l v2 h -> v1 = v2.
intros.
unfold selects in H, H0.
rewrite H in H0.
apply Some_dyn_inj.
assumption.
Qed.

Lemma selects_extend : 
  forall (A : Type) (v : A) (h hh : heap) (hs : list heap) (l : loc),
    selects l v hh -> splits h (hh::hs) -> selects l v h.
intros.
assert(valid_loc l hh).
unfold valid_loc.
exists A; exists v; trivial.
destruct H0.
assert(union (hh::hs) x l = hh l).
eapply union_valid_loc; eauto.
rewrite <- H0 in H2.
unfold selects.
rewrite H2.
unfold selects in H.
assumption.
Qed.

Lemma points_to_selects : forall (A : Type) (v : A) (h : heap) (l : loc),
  (l --> v) h -> selects l v h.
intros.
unfold points_to in H.
unfold selects.
rewrite H.
unfold update_loc, modify_loc.
rewrite loc_eq_refl.
trivial.
Qed.

Lemma points_to_selects_nopre : forall (A : Type) (v : A) (h : heap) (l : loc),
  ((l --> v) # nopre) h -> selects l v h.
intros.
destruct H as [ h1 [ h2 [ H1 [ H2 H3 ] ] ] ].
eapply selects_extend.
instantiate (1 := h1).
apply points_to_selects.
assumption.
apply H1.
Qed.

Lemma valid_loc_points_to_equal : forall (A : Type) (v : A) (h : heap) (l l' : loc),
  valid_loc l h -> (l' --> v) h -> l = l'.
intros.
unfold points_to, valid_loc, selects, update_loc, modify_loc in *.
destruct H as [ A' [ v' H ] ].
assert(h l = (fun n : loc => if loc_eq n l' then Some (dyn A v) else empty n) l).
rewrite H0; trivial.
rewrite H in H1.
destruct(loc_eq l l').
trivial.
unfold empty in H1.
inversion H1.
Qed.

Lemma lolli_lemma : 
  forall (P : heap -> Prop) (Q : heap -> heap -> Prop) (h1 h2 : heap),
    (P --o Q) h1 h2 -> P h1 -> Q h1 h2.
intros.
generalize(H h1 H0); clear H H0; intros.
assert(splits h1 (h1::empty::nil)).
remove_empty.
apply splits_refl.
generalize(H empty H0); clear H H0; intros.
destruct H as [ h3 [ H1 H2 ] ].
splits_rewrite.
assumption.
Qed.

Lemma lolli_lemma2 :
  forall (P : heap -> Prop) (Q : heap -> heap -> Prop) (h1 h2 h3 : heap)
           (pf : disjoint(h1::h2::nil)),
    (P --o Q) (union (h1::h2::nil) pf) h3 -> P h1 -> 
       (exists h4, splits h3 (h4::h2::nil) /\ Q h1 h4).
intros.
generalize(H h1 H0); clear H H0; intros.
assert(splits (union (h1::h2::nil) pf) (h1::h2::nil)).
exists pf; trivial.
generalize(H h2 H0); clear H H0; intros.
assumption.
Qed.

Lemma sread_pre_lolli : 
  forall (Q : hhprop) (A : Type) (v : A) (l :loc) (h1 h2 h3 : heap) (pf : disjoint(h1::h2::nil)),
    (l --> v) h1 -> (sread_pre A l --o Q) (union (h1::h2::nil) pf) h3 ->
       (exists h4, splits h3 (h4::h2::nil) /\ Q h1 h4).
intros.
assert(sread_pre A l h1).
unfold sread_pre.
exists v; assumption.
eapply lolli_lemma2.
apply H0.
apply H1.
Qed.

Lemma star_replace_nopre : forall (P Q : hprop) (h : heap),
  (P # Q) h -> (P # nopre) h.
intros.
destruct H as [ h1 [ h2 [ H1 [ H2 H3 ] ] ] ].
exists h1; exists h2.
intuition.
Qed.