Require Import DisjointUnion.
Require Import List.
Require Import MemModel.
Require Import ST.
Require Import Separation.
Require Import STsep.
Require Import Assumptions.
Require Import ListSet.
Require Import Precise.
Require Import Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Open Local Scope stsep_scope.

Section Table.

Variable dom : Set.
Variable dom_eq : forall x y : dom, {x = y} + {x <> y}.

Inductive Seq : Set :=
    | Nil  : Seq
    | Cons : (dom * loc) -> loc -> Seq.

Definition dom_eq_refl := A_eq_refl dom_eq.

Inductive Seq_pred (c : loc) (xs : list (dom * loc)) (h : heap) : Prop :=
    | Seq_nil  : xs = nil /\ (c --> Nil) h -> Seq_pred c xs h
    | Seq_cons : (exists x, exists xs', exists c', 
	xs = x::xs' /\ ((c --> Cons x c') # Seq_pred c' xs') h) -> Seq_pred c xs h.

Fixpoint functional (ll : list (dom * loc)) : Prop :=
    match ll with
	| nil  => True
	| (o, l)::t => not(exists l : loc, In (o, l) t) /\ functional t
    end.

Lemma func_nil : functional nil.
unfold functional.
trivial.
Qed.

Lemma func_not_mem_sublist : forall (o : dom) (l l' : loc) (ll : list (dom * loc)),
  functional ((o, l)::ll) -> not(In (o, l') ll).
intros.
unfold functional in H; fold functional in H.
destruct H.
unfold not; intros.
apply H.
exists l'; assumption.
Qed.

Definition table (s : loc) (f : dom -> option loc) (h : heap) :=
  exists ll : list (dom * loc), 
    (forall (l : loc) (o : dom), f o = Some l -> In (o, l) ll) /\
    (forall (l : loc) (o : dom), In (o, l) ll -> f o = Some l) /\
       functional ll /\ Seq_pred s ll h.

Lemma points_to_lemma : 
  forall (A : Type) (l : loc) (v v' : A) (P : heap -> Prop) (h : heap),
    (l --> v) h -> ((l --> v') # P) h -> v = v'.
intros.
destruct H0 as [ h1 [ h2 [ H1 [ H2 H3 ] ] ] ].
assert(h l = h1 l).
eapply splits_points_to.
apply H2.
apply H1.
unfold points_to, update_loc, modify_loc, lookup_loc in H, H2.
rewrite H in H0.
rewrite H2 in H0.
rewrite loc_eq_refl in H0.
apply Some_dyn_inj.
assumption.
Qed.

Theorem splits_selects2 :
  forall (A : Type) (v : A) (l : loc) (h hh : heap) (hs : list heap) (P : heap -> Prop),
  (l --> v # P) hh -> splits h (hh::hs) -> selects l v h.
intros.
destruct H as [ h1 [ h2 [ H3 [ H4 H5 ] ] ] ].
splits_rewrite_in H3 H0.
eapply points_to_splits_selects.
apply H4.
apply H.
Qed.

Theorem Seq_pred_very_precise : 
  forall (s : loc) (h h1 h2 : heap) (l1 : list (dom * loc)),
     splits h (h1::h2::nil) -> Seq_pred s l1 h1 ->
     forall (h3 h4 : heap) (l2 : list (dom * loc)),
        splits h (h3::h4::nil) -> Seq_pred s l2 h3 -> 
           (h1 = h3 /\ h2 = h4 /\ l1 = l2). 
intros s h h1 h2 l1 H1 H2 h3 h4 l2 H3 H4.
generalize s h h1 l2 h3 h4 H1 H2 H3 H4.
clear s h h1 l2 h3 h4 H1 H2 H3 H4.
induction l1.
intros s h h1 l2 h3 h4 H1 H2 H3 H4.
destruct H2.
destruct H as [ _ H ].
destruct H4.
destruct H0 as [ H4 H5 ].
rewrite_clear.
same_two_subheaps H3 H5 H6.
intuition.
destruct H0 as [ x [ xs' [ s' [ H4 H5 ] ] ] ].
assert(Nil = Cons x s').
eapply same_selects_equal.
eapply points_to_splits_selects; eauto.
eapply splits_selects2; eauto.
inversion H0.
destruct H as [ x [ xs' [ s' [ H5 H6 ] ] ] ].
inversion H5.
intros s h h1 l2 h3 h4 H1 H2 H3 H4.
destruct H2.
destruct H.
inversion H.
destruct H as [ x [ xs' [ s' [ H5 H6 ] ] ] ].
destruct H6 as [ h5 [ h6 [ H7 [ H8 H9 ] ] ] ].
destruct H4.
destruct H as [ H10 H11 ].
assert(Nil = Cons x s').
eapply same_selects_equal.
eapply points_to_splits_selects; eauto.
splits_rewrite_in H7 H1.
eapply points_to_splits_selects; eauto.
inversion H.
destruct H as [ x' [ xs'' [ s'' [ H10 H11 ] ] ] ].
inversion H5.
rewrite_clear.
destruct H11 as [ h7 [ h8 [ H12 [ H13 H14 ] ] ] ].
assert(Cons x s' = Cons x' s'').
eapply same_selects_equal.
splits_rewrite_in H7 H1.
eapply points_to_splits_selects; eauto.
splits_rewrite_in H12 H3.
eapply points_to_splits_selects; eauto.
inversion H.
rewrite_clear.
clear H.
assert(h5 = h7).
unfold points_to in H13, H8.
rewrite H13.
rewrite H8.
trivial.
rewrite_clear.
splits_rewrite_in H7 H1.
splits_rewrite_in H12 H3.
assert(splits [h -- h7] (h6::h2::nil)).
apply remove_heap_in_splits.
assumption.
assert(splits [h -- h7] (h8::h4::nil)).
apply remove_heap_in_splits.
assumption.
assert(h6 = h8 /\ h2 = h4 /\ xs' = xs'').
eapply IHl1.
apply H2.
apply H9.
apply H4.
apply H14.
destruct H5 as [ H15 [ H16 H17 ] ].
rewrite_clear.
intuition.
destruct H12.
destruct H7.
rewrite H0.
rewrite H4.
trivial.
Qed.

Lemma Seq_pred_lemma' : forall (c : loc) (xs xs' : list (dom * loc)) (h : heap),
  Seq_pred c xs h -> Seq_pred c xs' h -> xs = xs'.
intros.
assert(splits h (h::empty::nil)).
remove_empty; apply splits_refl.
assert(h = h /\ empty = empty /\ xs = xs').
eapply Seq_pred_very_precise; eauto.
intuition.
Qed.

Theorem table_pp : forall (l : loc) (f f' : dom -> option loc) (h : heap),
  table l f h /\ table l f' h -> f = f'.
intros.
destruct H as [ H1 H2 ].
unfold table in H1, H2.
destruct H1 as [ ll [ H3 [ H4 [ _ H5 ] ] ] ].
destruct H2 as [ ll' [ H6 [ H7 [ _ H8 ] ] ] ].
assert(ll = ll').
eapply Seq_pred_lemma'; eauto.
rewrite_clear.
apply extensional; intros.
case_eq (f x); intros.
symmetry.
apply H7.
apply H3.
assumption.
case_eq (f' x); intros.
assert(f x = Some l0).
apply H4.
apply H6.
assumption.
rewrite H in H1.
inversion H1.
trivial.
Qed.

Theorem table_very_precise : forall (l : loc),
  precise (fun h => exists f : dom -> option loc, table l f h).
unfold precise.
intros.
destruct H0 as [ f H0 ].
destruct H2 as [ f' H2 ].
unfold table in H0, H2.
destruct H0 as [ l1 [ H3 [ H4 [ _ H5 ] ] ] ].
destruct H2 as [ l2 [ H6 [ H7 [ _ H8 ] ] ] ].
assert(h1 = h3 /\ h2 = h4 /\ l1 = l2).
eapply Seq_pred_very_precise; eauto.
intuition.
Qed.

Program Definition newtable :
  STsep emp loc (fun y i m => exists l : loc, y = Val l /\
    table l (fun x : dom => None) m) :=
  sdo(snew Nil).
Next Obligation.
unfold emp in H.
rewrite H in *; clear H i.
exists empty.
intuition.
exists empty; exists empty.
intuition.
remove_empty.
apply splits_refl.
unfold snew_pre.
auto.
destruct H as [ h1 [ h2 [ H [ h4 [ h5 [ H1 [ H2 [ H3 H4 ] ] ] ] ] ] ] ].
unfold this in H3, H4.
rewrite <- H3 in *; clear H3 h2.
rewrite <- H4 in *; clear H4 h5.
unfold snew_post in H2.
destruct H2 as [ l [ H2 H3 ] ].
exists l.
intuition.
unfold table.
exists (nil (A := dom * loc)).
intuition.
inversion H0.
simpl in H0.
contradiction H0.
apply func_nil.
apply Seq_nil.
intuition.
splits_rewrite.
intuition.
Qed.

Definition updateF (f : dom -> option loc) (k : dom) (v : loc) : (dom -> option loc) :=
   (fun k' => match dom_eq k k' with left _ => Some v | right _ => f k' end).

Definition single_loc_subheap (h : heap) (l : loc) :=
  (fun l' : loc => match loc_eq l l' with left _ => h l | right _ => None end).

Notation "'[' h ':=:' l ']'" := (single_loc_subheap h l) (at level 5).

Lemma single_valid_loc_subheap : forall (h : heap) (l l' : loc),
  valid_loc l [h :=: l'] -> l = l'.
intros.
unfold valid_loc in H.
destruct H as [ A [ v H ] ].
unfold single_loc_subheap in H.
unfold selects in H.
destruct(loc_eq l' l).
symmetry.
trivial.
inversion H.
Qed.

Lemma single_loc_subheap_splits : forall (h : heap) (l : loc),
  splits h ([h :=: l]::[h \\ l]::nil).
intros.
assert(disjoint ([h :=: l]::[h \\ l]::nil)).
unfold disjoint.
intuition.
simpl.
intuition.
simpl.
intuition.
unfold disjoint2.
intros.
unfold splits.
assert(l0 = l).
eapply single_valid_loc_subheap.
apply H.
rewrite H0 in *; clear H0 l0.
apply remove_loc_unused.
exists H.
unfold union, union_heap_list, union2.
apply heap_extensional.
intros.
unfold single_loc_subheap, remove_loc.
unfold lookup_loc.
destruct (loc_eq l l0).
rewrite e in *; clear e l.
case_eq (h l0); trivial.
trivial.
Qed.

Lemma single_loc_subheap_selects : forall (A : Type) (v : A) (h : heap) (l : loc),
  selects l v h -> (l --> v) [h :=: l].
intros.
unfold points_to, selects, update_loc, modify_loc in *.
apply heap_extensional.
intros.
unfold lookup_loc, single_loc_subheap.
destruct(loc_eq l l0).
rewrite e in *; clear e l.
rewrite loc_eq_refl.
assumption.
destruct(loc_eq l0 l).
contradiction n; symmetry; trivial.
unfold empty.
trivial.
Qed.

Lemma selects_nil_seq_pred : forall (h : heap) (l : loc) (ll : list (dom * loc)),
  Seq_pred l ll h -> selects l Nil h -> ll = nil.
intros.
destruct H.
intuition.
destruct H as [ x [ xs' [ c' [ H1 H2 ] ] ] ].
destruct H2 as [ h1 [ h2 [ H3 [ H4 H5 ] ] ] ].
assert(selects l (Cons x c') h).
eapply points_to_splits_selects; eauto.
assert(Nil = (Cons x c')).
eapply same_selects_equal; eauto.
inversion H2.
Qed.

Lemma selects_nil_table : forall (h : heap) (l : loc) (f : dom -> option loc),
  table l f h -> selects l Nil h -> f = (fun _ => None).
intros.
apply extensional.
intros.
destruct H as [ ll [ H1 [ H2 [ _ H3 ] ] ] ].
case_eq (f x); intros.
assert(ll = nil).
eapply selects_nil_seq_pred; eauto.
rewrite H4 in *; clear H4 ll.
assert(In (x, l0) nil).
apply H1; trivial.
contradiction H4.
trivial.
Qed.

Definition update_loop_pre (hd : Seq) (t : loc) :=
  (fun i => selects t hd i /\ exists f : (dom -> option loc), table t f i).

Definition update_loop_post (hd : Seq) (t : loc) (k : dom) (v : loc) :=
  (fun y i m => y = Val tt /\
      forall f : (dom -> option loc), (selects t hd i /\ table t f i) ->
          table t (updateF f k v) m).

Definition update_loop_spec (hd : Seq) (t : loc) (k : dom) (v : loc) :=
  STsep (update_loop_pre hd t) unit (update_loop_post hd t k v).

Lemma valid_loc_extend : forall (h hh : heap) (hs : list heap) (l : loc),
  valid_loc l hh -> splits h (hh::hs) -> valid_loc l h.
intros.
destruct H0.
assert(union (hh::hs) x l = hh l).
eapply union_valid_loc; eauto.
unfold valid_loc in H.
destruct H as [ A [ v H ] ].
unfold selects in H.
exists A; exists v.
unfold selects.
rewrite H0.
rewrite H1.
rewrite H.
trivial.
Qed.

Lemma splits_to_lemma2 : forall (A : Type) (v : A) (h h1 h2 : heap) (l : loc),
  splits h (h1::h2::nil) -> (l --> v) h -> valid_loc l h1 -> h2 = empty.
intros.
apply heap_extensional.
intros.
unfold lookup_loc.
unfold empty.
case_eq (h2 l0).
intros.
assert(valid_loc l0 h2).
unfold valid_loc.
case_eq d; intros.
exists type_of; exists val_of.
unfold selects.
rewrite H3 in H2; trivial.
assert(valid_loc l0 h).
eapply valid_loc_extend; eauto.
apply splits_commute in H; apply H.
assert(l0 = l).
eapply valid_loc_points_to_equal; eauto.
rewrite_clear.
destruct H.
clear H.
destruct x.
destruct H5.
unfold disjoint2 in H5.
assert(unused_loc l h2).
apply H5; assumption.
contradiction(loc_ex H3 H7).
trivial.
Qed.

Lemma emp_empty : emp empty.
trivial.
Qed.

Lemma splits_empty1 : forall (h : heap),
  splits h (empty::h::nil).
intros.
remove_empty.
apply splits_refl.
Qed.

Ltac lolli_auto H1 H2 := match goal with
  | H1 : (emp --o ?Q) ?h1 ?h2 |- _ =>
      let tmpH1 := fresh "H" in
      let tmpH2 := fresh "H" in
        generalize(emp_empty); intros tmpH1; 
        generalize(splits_empty1 h1); intros tmpH2;
        generalize(H1 empty tmpH1 h1 tmpH2); intros H2;
        clear tmpH1 tmpH2
  end.

Program Definition update_loop
     (hd : Seq) (t : loc) (k : dom) (v : loc) 
     (upd : forall (hd : Seq) (t : loc) (k : dom) (v : loc), update_loop_spec hd t k v) :
     update_loop_spec hd t k v :=
   match hd with
     | Nil => sdo (x <-- snew Nil; swrite t (Cons (k, v) x))
     | Cons (o, l) l' =>
          match dom_eq k o with
          | left _ => sdo(swrite t (Cons (k, v) l'))
          | right _ => sdo(hd' <-- sread l'; upd hd' l' k v)
          end
   end.
Next Obligation.
clear upd.
destruct H as [ H1 [ f H2 ] ].
econstructor.
intuition.
unfold sbind_pre.
unfold snew_pre.
exists i; exists empty.
intuition.
remove_empty.
apply splits_refl.
exists empty; exists i.
intuition.
remove_empty.
apply splits_refl.
unfold swrite_pre.
lolli_auto H H3; clear H.
destruct H3 as [ h1 [ H3 H4 ] ].
assert(selects t Nil h).
eapply selects_extend.
apply H1.
apply splits_commute in H3.
apply H3.
exists [h :=: t]; exists [h \\ t].
intuition.
apply single_loc_subheap_splits.
exists Seq; exists Nil.
apply single_loc_subheap_selects.
assumption.
destruct H as [ h1 [ h2 [ H3 [ h3 [ h4 [ H4 [ H5 [ H6 H7 ] ] ] ] ] ] ] ].
unfold this in H6, H7.
rewrite <- H6 in *; clear H6 h2.
rewrite <- H7 in *; clear H7 h4.
splits_rewrite.
unfold sbind_post in H5.
destruct H5 as [ H5 | H5 ].
destruct H5 as [ H5 [ x [ h [ H6 H7 ] ] ] ].
destruct H5 as [ h4 [ h5 [ H8 [ H9 _ ] ] ] ].
generalize(H6 h4 H9 h5 H8); clear H6; intros.
destruct H as [ h6 [ H10 H11 ] ].
destruct H11 as [ l [ H12 H13 ] ].
unfold snew_pre in H9.
unfold emp in H9.
rewrite H9 in *; clear H9 h4.
splits_rewrite.
assert(f = (fun _ => None)).
eapply selects_nil_table; eauto.
rewrite H in *; clear H f.
destruct H2 as [ ll [ H14 [ H15 [ N1 H16 ] ] ] ].
assert(ll = nil).
eapply selects_nil_seq_pred; eauto.
rewrite H in *; clear H ll.
destruct H16.
destruct H as [ _ H ].
assert(swrite_pre t h5).
exists Seq; exists Nil; assumption.
apply splits_commute in H10.
generalize(H7 h5 H0 h6 H10); clear H7; intros.
destruct H2 as [ h1 [ H16 H17 ] ].
destruct H17 as [ H17 H18 ].
unfold update_loop_post.
intuition.
assert(f = (fun _ => None)).
eapply selects_nil_table; eauto.
rewrite H2 in *; clear H2 f.
unfold table, updateF.
exists ((k, v)::nil).
intuition.
destruct(dom_eq k o).
inversion H2.
rewrite_clear.
left; trivial.
inversion H2.
destruct H2.
inversion H2.
destruct(dom_eq o o).
trivial.
contradiction f; trivial.
contradiction H2.
unfold functional.
intuition.
destruct H2.
simpl H2; contradiction H2.
apply Seq_cons.
inversion H12.
rewrite_clear.
exists (k, v); exists (nil (A := dom * loc)); exists l.
intuition.
exists h1; exists h6.
intuition.
apply Seq_nil.
intuition.
destruct H as [ x' [ xs' [ c' [ H16 H17 ] ] ] ].
inversion H16.
destruct H5 as [ e [ H6 H7 ] ].
assert(snew_pre empty); unfold snew_pre; trivial.
generalize(H7 empty H); clear H7; intros.
assert(splits h1 (empty::h1::nil)).
remove_empty.
apply splits_refl.
generalize(H0 h1 H3); clear H3 H0; intros.
destruct H0 as [ h2 [ H7 H8 ] ].
destruct H8 as [ l [ H8 H9 ] ].
inversion H8.
Defined.

Next Obligation.
rewrite <- Heq_hd in *; clear Heq_hd hd.
rewrite wildcard' in *; clear wildcard' k Heq_anonymous.
unfold update_loop_pre in H.
destruct H as [ H [ f  H1 ] ].
copy H1 N1.
destruct H1 as [ ll [ H2 [ H3 [ N2 H4 ] ] ] ].
destruct H4.
destruct H0.
assert(selects t Nil i).
apply points_to_selects; assumption.
assert(Nil = (Cons (o, l) l')).
eapply same_selects_equal; eauto.
inversion H5.
destruct H0 as [ x [ xs' [ c' [ H4 H5 ] ] ] ].
rewrite H4 in *; clear H4 ll.
case_eq x; intros.
rewrite H0 in *; clear x H0.
destruct H5 as [ i1 [ i2 [ I1 [ I2 I3 ] ] ] ].
exists i2.
intuition.
exists i1; exists i2.
intuition.
unfold swrite_pre.
eauto.
destruct H0 as [ i3 [ i4 [ H4 [ i5 [ i6 [ H5 [ H6 [ H7 H8 ] ] ] ] ] ] ] ].
unfold this in H7, H8.
rewrite_clear.
assert(i1 = i3).
eapply splits_same_head; eauto.
rewrite_clear.
destruct H6 as [ H6 H7 ].
unfold update_loop_post.
intuition.
assert(f = f0).
eapply table_pp; eauto.
rewrite H0 in *; clear H0 N1 f.
assert(Cons (o, l) l' = Cons (d, l0) c').
assert(selects t (Cons (d, l0) c') i3).
apply points_to_selects; assumption.
assert(selects t (Cons (d, l0) c') i).
eapply selects_extend; eauto.
eapply same_selects_equal; eauto.
inversion H0.
rewrite_clear.
clear H0.
unfold table.
exists ((d, v)::xs').
intuition.
unfold updateF in H.
destruct(dom_eq d o).
inversion H; clear H.
rewrite_clear.
left; trivial.
assert(In (o, l) ((d, l0) :: xs')).
apply H2; auto.
simpl in H0.
destruct H0.
inversion H0.
contradiction(f H10).
right.
assumption.
unfold updateF.
simpl in H.
destruct H.
inversion H; clear H.
rewrite_clear.
destruct(dom_eq o o).
trivial.
contradiction f; trivial.
assert(f0 o = Some l).
apply H3.
right; trivial.
rewrite H0.
destruct(dom_eq d o).
assert((d, l0)::xs' = (d, l0)::xs'); trivial.
rewrite_clear.
assert(not(In (o, l) xs')).
apply func_not_mem_sublist with (l := l0).
assumption.
contradiction(H9 H).
trivial.
apply Seq_cons.
exists (d, v); exists xs'; exists c'.
intuition.
exists i5; exists i4.
intuition.
Defined.

Next Obligation.
clear Heq_anonymous.
destruct H as [ H1 [ f H2 ] ].
copy H2 N100.
destruct H2 as [ ll [ H3 [ H4 [ H5 H6 ] ] ] ].
destruct H6.
destruct H.
assert(selects t Nil i).
apply points_to_selects; auto.
assert(Nil = Cons (o, l) l').
eapply same_selects_equal; eauto.
inversion H6.
destruct H as [ x [ xs' [ c' [ H6 H7 ] ] ] ].
destruct H7 as [ i1 [ i2 [ I1 [ I2 I3 ] ] ] ].
assert(selects t (Cons x c') i).
eapply selects_extend.
instantiate (1 := i1).
apply points_to_selects.
apply I2.
apply I1.
case_eq x; intros.
rewrite_clear.
assert(Cons (o, l) l' = Cons (d, l0) c').
eapply same_selects_equal; eauto.
inversion H0; clear H0.
rewrite_clear.
destruct I3.
destruct H0.
exists i1.
intuition.
exists i2; exists i1.
intuition.
apply splits_commute; assumption.
unfold sbind_pre.
intuition.
exists i2; exists empty.
intuition.
remove_empty.
apply splits_refl.
unfold sread_pre.
exists Nil; assumption.
assert(sread_pre Seq c' i2).
unfold sread_pre.
exists Nil; assumption.
generalize(H2 i2 H6); clear H2 H6; intros.
assert(splits i2 (i2::empty::nil)).
remove_empty.
apply splits_refl.
generalize(H2 empty H6); clear H2 H6; intros.
destruct H2 as [ h1 [ H6 H7 ] ].
splits_rewrite.
destruct H7.
rewrite_clear.
exists h1; exists empty.
intuition.
remove_empty.
apply splits_refl.
unfold update_loop_pre.
assert(Val x = Val Nil).
apply H6; assumption.
inversion H0; clear H0.
intuition.
apply points_to_selects; auto.
exists (fun x : dom => None (A := loc)).
unfold table.
exists (nil (A := dom * loc)).
intuition.
inversion H0.
simpl in H0.
contradiction H0.
apply func_nil.
apply Seq_nil.
intuition.
destruct H2 as [ j1 [ j2 [ J1 [ j3 [ j4 [ J2 [ J3 [ J4 J5 ] ] ] ] ] ] ] ].
unfold this in J4, J5.
rewrite <- J4 in *; clear J4 j2.
rewrite <- J5 in *; clear J5 j4.
unfold sbind_post in J3.
destruct J3.
destruct H2 as [ H6 H7 ].
destruct H7 as [ x [ h [ H8 H9 ] ] ].
destruct H6 as [ k1 [ k2 [ K1 [ K2 K3 ] ] ] ].
generalize(H8 k1 K2 k2 K1); clear H8; intros.
destruct H2 as [ k3 [ K4 K5 ] ].
apply splits_commute in I1.
assert(j1 = i2).
eapply splits_same_head; eauto.
rewrite_clear.
destruct K5.
rewrite_clear.
assert(h = i2).
destruct K4.
destruct K1.
rewrite_clear.
trivial.
rewrite_clear.
assert(k2 = empty).
eapply splits_to_lemma2.
apply K4.
apply H1.
unfold sread_pre in K2.
destruct K2.
eapply points_to_valid; eauto.
rewrite_clear.
splits_rewrite.
assert(update_loop_pre x c' k3).
unfold update_loop_pre.
assert(Val x = Val Nil).
apply H2.
assumption.
inversion H0.
rewrite_clear.
clear H0.
intuition.
apply points_to_selects.
assumption.
exists (fun x : dom => None (A := loc)).
unfold table.
exists (nil (A := dom * loc)).
intuition.
inversion H0.
simpl in H0.
contradiction H0.
apply Seq_nil.
intuition.
generalize(H9 k3 H0); clear H9 H0; intros.
assert(splits k3 (k3::empty::nil)).
remove_empty.
apply splits_refl.
generalize(H0 empty H6); clear H0 H6; intros.
destruct H0 as [ j4 [ K5 K6 ] ].
splits_rewrite.
unfold update_loop_post.
unfold update_loop_post in K6.
destruct K6.
intuition.
assert(Val x = Val Nil).
apply H2; trivial.
inversion H7; clear H7.
rewrite_clear.
assert(selects c' Nil k3 /\ table c' (fun _ => None) k3).
unfold table.
intuition.
eapply points_to_selects; eauto.
exists (nil (A := dom * loc)).
intuition.
inversion H7.
simpl in H7.
contradiction H7.
apply Seq_nil.
intuition.
assert(table c' (updateF (fun _ => None) k v) j4).
apply H6; assumption.
clear H7.
clear H6.
assert(table t (fun x => match dom_eq x d with left _ => Some l0 | right _ => None end) i).
unfold table.
exists ((d, l0)::nil).
intuition.
destruct(dom_eq o d).
inversion H6.
rewrite e.
left; trivial.
inversion H6.
simpl in H6.
destruct H6.
inversion H6.
destruct(dom_eq o o).
trivial.
contradiction f1; trivial.
contradiction H6.
apply Seq_cons.
exists (d, l0); exists (nil (A := dom * loc)); exists c'.
intuition.
exists i1; exists k3.
intuition.
apply splits_commute; assumption.
apply Seq_nil.
intuition.
assert(f0 = (fun x : dom => if dom_eq x d then Some l0 else None (A:=loc))).
eapply table_pp; eauto.
rewrite H7.
unfold table.
destruct H8 as [ ll' [ L1 [ L2 [ L3 L4 ] ] ] ].
exists ((d, l0)::ll').
unfold updateF.
intuition.
destruct(dom_eq k o).
rewrite_clear.
right.
apply L1.
unfold updateF.
destruct(dom_eq o o).
assumption.
contradiction f0; trivial.
destruct(dom_eq o d).
inversion H8.
rewrite_clear.
left; trivial.
inversion H8.
simpl in H8.
destruct H8.
inversion H8.
rewrite_clear.
destruct(dom_eq k o).
contradiction (wildcard' e).
destruct(dom_eq o o).
trivial.
contradiction f1; trivial.
assert(updateF (fun _ : dom => None) k v o = Some l).
apply L2; assumption.
unfold updateF in H10.
destruct(dom_eq k o).
assumption.
inversion H10.
unfold functional; fold functional.
intuition.
destruct H8.
assert(updateF (fun _ : dom => None) k v d = Some x).
apply L2; assumption.
unfold updateF in H10.
destruct(dom_eq k d).
contradiction (wildcard' e).
inversion H10.
apply Seq_cons.
exists (d, l0); exists ll'; exists c'.
intuition.
exists i1; exists j4.
intuition.
apply splits_commute; assumption.
destruct H2 as [ e [ T1 T2 ] ].
apply splits_commute in I1.
assert(j1 = i2).
eapply splits_same_head; eauto.
rewrite_clear.
assert(sread_pre Seq c' i2).
unfold sread_pre.
exists Nil; assumption.
generalize(T2 i2 H0); clear T2 H0; intros.
assert(splits i2 (i2::empty::nil)).
remove_empty.
apply splits_refl.
generalize(H0 empty H2); clear H0 H2; intros.
destruct H0 as [ j4 [ T4 T5 ] ].
splits_rewrite.
unfold sread_post in T5.
destruct T5.
assert(Exn e = Val Nil).
apply H2; assumption.
inversion H6.


(* The non-nil case. *)
destruct H0 as [ x [ xs'' [ c'' [ T1 T2 ] ] ] ].
destruct T2 as [ i3 [ i4 [ T3 [ T4 T5 ] ] ] ].
splits_rewrite_in T3 I1.
clear I1 T3.
splits_join_in H0 (0::1::1::nil).
exists i1.
intuition.
exists (union (i3::i4::nil) pf0); exists i1.
intuition.
unfold sbind_pre.
intuition.
exists i3; exists i4.
intuition.
exists pf0; trivial.
exists (Cons x c'').
assumption.
assert(sread_pre Seq c' i3).
exists (Cons x c''); assumption.
generalize(H2 i3 H6); clear H2 H6; intros.
assert(splits (union (i3::i4::nil) pf0) (i3::i4::nil)).
exists pf0; trivial.
generalize(H2 i4 H6); clear H2 H6; intros.
destruct H2 as [ i5 [ H10 H11 ] ].
unfold sread_post in H11.
destruct H11.
rewrite <- H2 in *; clear H2 i5.
exists h; exists empty.
intuition.
remove_empty.
apply splits_refl.
unfold update_loop_pre.
intuition.
eapply selects_extend.
instantiate (1 := i3).
apply points_to_selects.
assert(Val x0 = Val (Cons x c'')).
apply H6; assumption.
inversion H2.
assumption.
apply H10.
exists (fun x : dom => match dom_eq x d with left _ => None | right _ => f x end).
unfold table.
exists (x::xs'').
intuition.
destruct(dom_eq o d).
inversion H2.
assert(In (o, l) ((d, l0)::xs')).
apply H3; assumption.
simpl in H7.
destruct H7.
inversion H7.
rewrite_clear.
contradiction f0; trivial.
rewrite T1 in H7.
assumption.
destruct(dom_eq o d).
rewrite_clear.
assert((d, l0)::x::xs'' = (d, l0)::x::xs''); trivial.
assert(not(In (d, l) (x::xs''))).
apply func_not_mem_sublist with (l := l0).
assumption.
contradiction (H8 H2).
apply H4.
right.
rewrite T1.
assumption.
rewrite T1 in *; clear T1 xs'.
case_eq x; intros; rewrite_clear.
unfold functional in H5; fold functional in H5.
unfold functional; fold functional.
intuition.
apply Seq_cons.
exists x; exists xs''; exists c''.
intuition.
exists i3; exists i4.
intuition.
destruct H2 as [ j1 [ j2 [ J1 [ j3 [ j4 [ J2 [ J3 [ J4 J5 ] ] ] ] ] ] ] ].
unfold this in J4, J5.
rewrite <- J4 in *; clear J4 j2.
rewrite <- J5 in *; clear J5 j4.
assert(j1 = union(i3::i4::nil) pf0).
eapply splits_same_head; eauto.
rewrite H2 in *; clear H2 j1.
clear J1.
unfold sbind_post in J3.
destruct J3.
destruct H2.
destruct H6 as [ x' [ j5 [ H20 H21 ] ] ].
assert(exists j4, splits j5 (j4::i4::nil) /\ sread_post Seq c' (Val x') i3 j4).
apply sread_pre_lolli with (l := c') (v := (Cons x c'')) (pf := pf0); auto.
clear H20.
destruct H6 as [ j4 [ H22 H23 ] ].
unfold sread_post in H23.
destruct H23.
assert(Val x' = Val (Cons x c'')).
apply H7; assumption.
inversion H8.
rewrite H10 in *; clear H10 H8.
assert(selects c' (Cons x c'') j5 /\ (table c' (fun x : dom => match dom_eq x d with left _ => None | right _ => f x end) j5)).
intuition.
eapply selects_extend.
eapply points_to_selects.
eauto.
rewrite H6.
eauto.
unfold table.
exists xs'.
intuition.
rewrite T1.
destruct(dom_eq o d).
inversion H8.
assert(In (o, l) ((d, l0)::xs')).
apply H3; assumption.
simpl in H9.
destruct H9.
inversion H9.
rewrite_clear.
contradiction f0; trivial.
rewrite T1 in H9.
assumption.
rewrite T1 in H8.
destruct (dom_eq o d).
rewrite e in *; clear e o.
assert(not(In (d, l) xs')).
apply func_not_mem_sublist with (l := l0); auto.
rewrite T1 in H9.
contradiction (H9 H8).
apply H4.
right.
rewrite T1.
assumption.
unfold functional in H5; fold functional in H5.
intuition.
apply Seq_cons.
exists x; exists xs''; exists c''.
rewrite T1.
intuition.
exists i3; exists i4.
rewrite H6.
intuition.
rewrite <- H6.
assumption.
assert(update_loop_pre (Cons x c'') c' j5).
unfold update_loop_pre.
intuition.
exists (fun x : dom => match dom_eq x d with left _ => None | right _ => f x end).
assumption.
assert(update_loop_post (Cons x c'') c' k v y j5 j3).
apply lolli_lemma with (P := (update_loop_pre (Cons x c'') c')); auto.
clear H21.
unfold update_loop_post in H10.
unfold update_loop_post.
destruct H10.
split.
assumption.
intros.
generalize(H11 (fun x : dom => match dom_eq x d with left _ => None | right _ => f x end) H8); clear H8 H11; intros.
destruct H12.
assert(f0 = f).
eapply table_pp; eauto.
rewrite H13 in *; clear H13 f0.
destruct H8 as [ ll' [ U1 [ U2 [ U3 U4 ] ] ] ].
exists ((d, l0)::ll').
intuition.
unfold updateF in H8.
destruct(dom_eq k o).
inversion H8; clear H8.
rewrite_clear.
right.
apply U1.
unfold updateF.
destruct(dom_eq o o).
trivial.
contradiction f0; trivial.
assert(In (o, l) ((d, l0) :: xs')).
apply H3; auto.
simpl in H13.
destruct H13.
inversion H13.
left; trivial.
destruct(dom_eq o d).
assert(In (d, l0) ((d, l0) :: xs')).
left; trivial.
assert(not(In (d, l) xs')).
apply func_not_mem_sublist with (l := l0); auto.
rewrite e in H13.
contradiction(H15 H13).
assert(updateF (fun x : dom => if dom_eq x d then None else f x) k v o = Some l).
unfold updateF.
destruct(dom_eq k o).
contradiction (f0 e).
destruct(dom_eq o d).
contradiction (f1 e).
assumption.
assert(In (o, l) ll').
apply U1; assumption.
right.
assumption.
simpl in H8.
destruct H8.
inversion H8.
unfold updateF.
rewrite_clear.
destruct(dom_eq k o).
contradiction(wildcard' e).
apply H4.
left; trivial.
generalize(U2 l o H8); intros.
unfold updateF in H13.
unfold updateF.
destruct(dom_eq k o).
assumption.
destruct(dom_eq o d).
inversion H13.
assumption.
unfold functional; fold functional.
intuition.
destruct H8 as [ l1 H8 ].
generalize(U2 l1 d H8); intros.
unfold updateF in H13.
destruct(dom_eq k d).
contradiction(wildcard' e).
destruct(dom_eq d d).
inversion H13.
contradiction f1; trivial.
apply Seq_cons.
exists (d, l0); exists ll'; exists c'.
intuition.
exists i1; exists j3.
intuition.
apply splits_commute; assumption.
(* for sub-goal 2 *)
destruct H2 as [ e [ H10 H11 ] ].
assert(sread_pre Seq c' i3).
unfold sread_pre.
exists (Cons x c''); assumption.
assert(exists j4, splits j3 (j4::i4::nil) /\ sread_post Seq c' (Exn e) i3 j4).
apply sread_pre_lolli with (l := c') (v := Cons x c'') (pf := pf0); auto.
clear H11.
destruct H6 as [ j4 [ J10 J11 ] ].
unfold sread_post in J11.
destruct J11.
assert(Exn e = Val (Cons x c'')).
apply H7; assumption.
inversion H8.
Defined.

Program Definition update (t : loc) (k : dom) (v : loc) :
  STsep (fun i => exists f : (dom -> option loc), table t f i) unit
        (fun y i m => y = Val tt /\ 
          forall f : (dom -> option loc), table t f i ->
            table t (updateF f k v) m) :=
  sdo(x <-- sread t; sfix (fun upd x => update_loop (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x) (fun x t k v => upd (x, t, k, v))) (x, t, k, v)).
Next Obligation.
destruct H0 as [ ll [ H1 [ H2 [ H3 H4 ] ] ] ].
destruct H4.
destruct H0.
nextvc.
exists empty.
intuition.
exists i; exists empty.
intuition.
remove_empty.
apply splits_refl.
unfold update_loop_pre.
intuition.
apply points_to_selects.
assumption.
exists H.
unfold table.
exists (nil (A := dom * loc)).
intuition.
apply Seq_nil.
intuition.
destruct H0 as [ i1 [ i2 [ I1 [ i3 [ i4 [ I2 [ I3 [ I4 I5 ] ] ] ] ] ] ] ].
unfold this in I4, I5.
rewrite <- I4 in *; clear I4 i2.
rewrite <- I5 in *; clear I5 i4.
unfold update_loop_post in I3.
intuition.
destruct H0 as [ i1 [ i2 [ I1 [ i3 [ i4 [ I2 [ I3 [ I4 I5 ] ] ] ] ] ] ] ].
unfold this in I4, I5.
rewrite <- I4 in *; clear I4 i2.
rewrite <- I5 in *; clear I5 i4.
unfold update_loop_post in I3.
destruct I3.
splits_rewrite.
apply H6.
intuition.
apply points_to_selects; assumption.
destruct H0 as [ hd [ tail [ nextp [ H4 H5 ] ] ] ].
nextvc.
apply star_replace_nopre with (Q := (Seq_pred nextp tail)).
instantiate (1 := Cons hd nextp).
assumption.
exists empty.
intuition.
exists i; exists empty.
intuition.
remove_empty.
apply splits_refl.
unfold update_loop_pre.
destruct H5 as [ i1 [ i2 [ I1 [ I2 I3 ] ] ] ].
intuition.
apply selects_extend with (hh := i1) (hs := i2::nil).
apply points_to_selects.
assumption.
assumption.
exists H.
unfold table.
exists (hd::tail).
intuition.
apply Seq_cons.
exists hd; exists tail; exists nextp.
intuition.
exists i1; exists i2.
intuition.
destruct H0 as [ i1 [ i2 [ I1 [ i3 [ i4 [ I2 [ I3 [ I4 I5 ] ] ] ] ] ] ] ].
unfold this in I4, I5.
rewrite <- I4 in *; clear I4 i2.
rewrite <- I5 in *; clear I5 i4.
splits_rewrite.
unfold update_loop_post in I3.
intuition.
destruct H0 as [ i1 [ i2 [ I1 [ i3 [ i4 [ I2 [ I3 [ I4 I5 ] ] ] ] ] ] ] ].
unfold this in I4, I5.
rewrite <- I4 in *; clear I4 i2.
rewrite <- I5 in *; clear I5 i4.
splits_rewrite.
unfold update_loop_post in I3.
destruct I3.
apply H6.
intuition.
destruct H5 as [ j1 [ j2 [ J1 [ J2 J3 ] ] ] ].
apply selects_extend with (hh := j1) (hs := j2::nil).
apply points_to_selects; assumption.
assumption.
Qed.

Definition lookup_pre (hd : Seq) (t : loc) (k : dom) :=
  (fun i => selects t hd i /\ exists f : (dom -> option loc), table t f i).

Definition lookup_post (hd : Seq) (t : loc) (k : dom) :=
  (fun y i m => forall f : (dom -> option loc), (selects t hd i /\ table t f i) ->
           (table t f m /\ i = m /\ y = Val (f k))).

Definition lookup_spec (hd : Seq) (t : loc) (k : dom) :=
  STsep (lookup_pre hd t k) (option loc) (lookup_post hd t k).

Program Definition lookup_loop 
  (hd : Seq) (t : loc) (k : dom) 
  (look : forall (hd : Seq) (t : loc) (k : dom), lookup_spec hd t k) :
    lookup_spec hd t k :=
   match hd with
   | Nil => sdo(sret None)
   | Cons (o, l) l' =>
     match dom_eq o k with
     | left _ => sdo(sret (Some l))
     | right _ => sdo(x <-- sread l'; look x l' k)
     end
   end.
Next Obligation.
nextvc.
unfold lookup_pre in H.
destruct H.
destruct H0 as [ f H1 ].
copy H1 N1.
destruct H1 as [ ll [ H1 [ H2 [ H3 H4 ] ] ] ].
assert(ll = nil).
eapply selects_nil_seq_pred; eauto.
rewrite H0 in *; clear H0 ll.
unfold lookup_post.
intros.
destruct H0.
assert(f = f0).
eapply table_pp; eauto.
rewrite H6 in *; clear H6 f.
intuition.
f_equal.
case_eq (f0 k); intros.
generalize(H1 l k H6); clear H6; intros.
simpl in H6.
contradiction H6.
trivial.
Defined.

Next Obligation.
clear Heq_anonymous.
rewrite wildcard' in *; clear wildcard' o.
rewrite <- Heq_hd in *; clear Heq_hd hd.
unfold lookup_pre in H.
destruct H.
destruct H0 as [ f H1 ].
nextvc.
unfold lookup_post.
intros.
destruct H0.
assert(f = f0).
eapply table_pp; eauto.
rewrite H3 in *; clear H3 f.
clear H2.
intuition.
f_equal.
destruct H1 as [ ll [ H1 [ H2 [ H3 H4 ] ] ] ].
destruct H4.
destruct H4.
assert(Nil = Cons (k, l) l').
eapply same_selects_equal.
eapply points_to_selects.
apply H5.
apply H.
inversion H6.
destruct H4 as [ hd [ tail [ nextp [ H4 H5 ] ] ] ].
rewrite H4 in *; clear H4 ll.
destruct H5 as [ i1 [ i2 [ I1 [ I2 I3 ] ] ] ].
assert(Cons hd nextp = Cons (k, l) l').
eapply same_selects_equal.
eapply selects_extend.
apply points_to_selects.
apply I2.
apply I1.
assumption.
inversion H4.
rewrite_clear.
symmetry.
apply H2.
left; trivial.
Defined.

Next Obligation.
clear Heq_anonymous.
unfold lookup_pre in H.
destruct H.
destruct H0 as [ f H1 ].
copy H1 N1.
destruct H1 as [ ll [ H1 [ H2 [ H3 H4 ] ] ] ].
destruct H4.
destruct H0.
assert(Nil = Cons (o, l) l').
eapply same_selects_equal.
eapply points_to_selects.
apply H4.
apply H.
inversion H5.
destruct H0 as [ hd [ tail [ nextp [ H4 H5 ] ] ] ].
destruct H5 as [ i1 [ i2 [ H5 [ H6 H7 ] ] ] ].
rewrite_clear.
destruct H7.
destruct H0.
assert(Cons (o, l) l' = Cons hd nextp).
eapply same_selects_equal.
apply H.
eapply selects_extend.
apply points_to_selects.
apply H6.
apply H5.
inversion H7.
clear H7.
rewrite_clear.
rewrite <- H9 in *; clear H9 hd.
nextvc.
exists i2; exists i1.
intuition.
apply splits_commute; assumption.
apply H4.
exists i1.
intuition.
exists i2; exists i1.
intuition.
apply splits_commute; assumption.
unfold lookup_pre.
intuition.
apply points_to_selects; assumption.
exists (fun x : dom => (None (A := loc))).
unfold table.
exists (nil (A := dom * loc)).
intuition.
inversion H0.
simpl in H0.
contradiction H0.
apply func_nil.
apply Seq_nil.
intuition.
destruct H0 as [ i3 [ i4 [ I1 [ i5 [ i6 [ I2 [ I3 [ I4 I5 ] ] ] ] ] ] ] ].
unfold this in I4, I5.
rewrite <- I4 in *; clear I4 i4.
rewrite <- I5 in *; clear I5 i6.
apply splits_commute in H5.
assert(i2 = i3).
eapply splits_same_head; eauto.
rewrite_clear.
unfold lookup_post in I3.
assert(selects nextp Nil i3 /\ table nextp (fun x : dom => None (A := loc)) i3).
intuition.
apply points_to_selects; assumption.
unfold table.
exists (nil (A := dom * loc)).
intuition.
inversion H0.
simpl in H0.
contradiction H0.
apply func_nil.
apply Seq_nil.
intuition.
generalize(I3 (fun _ : dom => None (A := loc)) H0); clear H0; intros.
destruct H0 as [ H10 [ H11 H12 ] ].
unfold lookup_post.
intros.
destruct H0.
rewrite_clear.
assert(i = m).
destruct I2.
destruct I1.
rewrite H7.
rewrite H0.
trivial.
rewrite_clear.
intuition.
f_equal.
assert(f = f0).
eapply table_pp; eauto.
rewrite_clear.
case_eq (f0 k); intros.
generalize(H1 l0 k H0); intros.
simpl in H7.
destruct H7.
inversion H7.
contradiction (wildcard' H9).
contradiction H7.
trivial.

(* the non-nil case. *)
destruct H0 as [ hd' [ tail' [ nextp' [ H7 H8 ] ] ] ].
assert(Cons (o, l) l' = Cons hd nextp).
eapply same_selects_equal.
apply H.
eapply selects_extend.
apply points_to_selects.
apply H6.
apply H5.
inversion H0.
clear H0.
symmetry in H9.
rewrite_clear.
destruct H8 as [ i3 [ i4 [ H7 [ H8 H9 ] ] ] ].
splits_rewrite_in H7 H5; clear H5 H7.
nextvc.
splits_join_in H0 (1::0::1::nil).
apply splits_commute in H4.
exists i3; exists (union (i1::i4::nil) pf0).
intuition.
apply H8.
splits_join_in H0 (0::1::1::nil).
assert(table nextp (fun x : dom => if dom_eq x o then None (A:=loc) else f x)
  (union (i3 :: i4 :: nil) pf0)).
unfold table.
exists (hd'::tail').
intuition.
destruct(dom_eq o0 o).
inversion H5.
generalize(H1 l0 o0 H5); intros.
simpl in H7.
destruct H7.
inversion H7.
contradiction f0; symmetry; assumption.
destruct H7.
left; trivial.
right; trivial.
simpl in H5.
destruct H5.
destruct(dom_eq o0 o).
rewrite_clear.
assert(In (o, l) ((o, l)::(o, l0)::tail')).
left; trivial.
assert(not(In (o, l0) ((o, l0)::tail'))).
apply func_not_mem_sublist with (l := l); auto.
assert(In (o, l0) ((o, l0)::tail')).
left; trivial.
contradiction (H7 H10).
apply H2.
right.
left; trivial.
destruct(dom_eq o0 o).
rewrite_clear.
assert(not(In (o, l0) (hd'::tail'))).
apply func_not_mem_sublist with (l := l); auto.
contradiction H7.
right; assumption.
apply H2.
right.
right; trivial.
unfold functional in H3; fold functional in H3.
destruct H3.
unfold functional; fold functional.
apply H5.
apply Seq_cons.
exists hd'; exists tail'; exists nextp'.
intuition.
exists i3; exists i4.
intuition.
exists pf0; trivial.
exists i1.
intuition.
exists (union (i3::i4::nil) pf0); exists i1.
intuition.
unfold lookup_pre.
intuition.
eapply selects_extend.
apply points_to_selects.
apply H8.
instantiate (1 := i4::nil).
exists pf0; trivial.
exists (fun x : dom => match dom_eq x o with | left _ => None | right _ => f x end).
assumption.
destruct H7 as [ i5 [ i6 [ I1 [ i7 [ i8 [ I2 [ I3 [ I4 I5 ] ] ] ] ] ] ] ].
unfold this in I4, I5.
rewrite <- I4 in *; clear I4 i6.
rewrite <- I5 in *; clear I5 i8.
unfold lookup_post in I3.
unfold lookup_post.
intros.
apply splits_commute in I1.
generalize(splits_same_tail H0 I1); intros.
destruct H10 as [ pf1 [ pf2 H10 ] ].
assert(union (i5::nil) pf2 = i5).
simpl.
trivial.
rewrite H11 in H10.
clear H11.
rewrite <- H10 in *; clear H10 i5.
clear pf2.
assert(selects nextp (Cons hd' nextp') (union (i3::i4::nil) pf1) /\ table nextp (fun x : dom => if dom_eq x o then None (A:=loc) else f x) (union (i3::i4::nil) pf0)).
intuition.
eapply selects_extend.
apply points_to_selects.
apply H8.
instantiate (1 := i4::nil).
exists pf1; trivial.
generalize(I3 (fun x : dom => if dom_eq x o then None (A:=loc) else f x) H10); clear H10; intros.
destruct H10 as [ H10 [ H11 H12 ] ].
destruct H7.
assert(f0 = f).
eapply table_pp; eauto.
rewrite_clear.
rewrite <- H11 in *; clear H11 i7.
assert(i = m).
destruct H4; destruct I2.
rewrite H4; rewrite H7.
trivial.
rewrite_clear.
intuition.
destruct(dom_eq k o).
contradiction wildcard'; symmetry; trivial.
trivial.
Defined.

Lemma short_table : 
  forall (h : heap) (o : dom) (l : loc) (t next : loc) f,
  table t f h -> selects t (Cons (o, l) next) h ->
    ((t --> (Cons (o, l) next)) # (table next (fun x : dom => match dom_eq x o with | left _ => None | right _ => f x end))) h.
intros.
destruct H as [ ll [ H1 [ H2 [ H3 H4 ] ] ] ].
destruct H4.
destruct H.
assert(Nil = Cons (o, l) next).
eapply same_selects_equal.
apply points_to_selects.
apply H4.
assumption.
inversion H5.
destruct H as [ hd [ tail [ next' [ H4 H5 ] ] ] ].
destruct H5 as [ h3 [ h4 [ H6 [ H7 H8 ] ] ] ].
assert(Cons (o, l) next = Cons hd next').
eapply same_selects_equal.
apply H0.
eapply selects_extend.
apply points_to_selects.
apply H7.
apply H6.
inversion H; clear H.
symmetry in H9.
rewrite_clear.
unfold table.
exists h3; exists h4.
intuition.
exists tail.
intuition.
destruct(dom_eq o0 o).
inversion H.
generalize(H1 l0 o0 H); intros.
simpl in H4.
destruct H4.
inversion H4.
contradiction f0; symmetry; trivial.
assumption.
destruct(dom_eq o0 o).
rewrite_clear.
assert(not(In (o, l0) tail)).
apply func_not_mem_sublist with (l := l); auto.
contradiction(H4 H).
apply H2.
right; trivial.
unfold functional in H3; fold functional in H3.
intuition.
Qed.

Program Definition lookup (t : loc) (k : dom) :
  STsep (fun i => exists f : (dom -> option loc), table t f i) (option loc)
        (fun y i m => forall f : (dom -> option loc), table t f i ->
           (table t f m /\ i = m /\ y = Val (f k))) :=
  sdo(x <-- sread t; sfix (fun look x => lookup_loop (fst (fst x)) (snd (fst x)) (snd x) (fun x t k => look (x, t, k))) (x, t, k)).
Next Obligation.
copy H0 N1.
destruct H0 as [ ll [ H1 [ H2 [ H3 H4 ] ] ] ].
destruct H4.
destruct H0.
nextvc.
exists empty.
split.
exists i; exists empty.
intuition.
remove_empty.
apply splits_refl.
unfold lookup_pre.
intuition.
eapply points_to_selects; eauto.
exists H; assumption.
intros.
destruct H0 as [ i1 [ i2 [ H6 [ i3 [ i4 [ H7 [ H8 [ H9 H10 ] ] ] ] ] ] ] ].
unfold this in H9, H10.
rewrite <- H9 in *; clear H9 i2.
rewrite <- H10 in *; clear H10 i4.
splits_rewrite.
unfold lookup_post in H8.
assert(f = H).
eapply table_pp; eauto.
rewrite_clear.
apply H8.
intuition.
apply points_to_selects.
assumption.
destruct H0 as [ hd [ tail [ nextp [ H4 H5 ] ] ] ].
nextvc.
destruct H5 as [ i1 [ i2 [ I1 [ I2 I3 ] ] ] ].
exists i1; exists i2.
intuition.
apply I2.
destruct H5 as [ i1 [ i2 [ I1 [ I2 I3 ] ] ] ].
exists empty.
split.
exists i; exists empty.
intuition.
remove_empty.
apply splits_refl.
unfold lookup_pre.
intuition.
eapply selects_extend.
apply points_to_selects.
apply I2.
apply I1.
exists H; assumption.
intros.
destruct H0 as [ k1 [ k2 [ K1 [ k3 [ k4 [ K2 [ K3 [ K4 K5 ] ] ] ] ] ] ] ].
unfold this in K4, K5.
rewrite <- K4 in *; clear K4 k2.
rewrite <- K5 in *; clear K5 k4.
splits_rewrite.
unfold lookup_post in K3.
apply K3.
intuition.
eapply selects_extend.
apply points_to_selects.
apply I2.
apply I1.
Qed.

End Table.