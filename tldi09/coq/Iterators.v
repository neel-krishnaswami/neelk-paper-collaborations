(* Ynot imports *)
Require Import DisjointUnion.
Require Import List.
Require Import MemModel.
Require Import ST.
Require Import Separation.
Require Import STsep.
Require Import Assumptions.
Require Import Precise.
Require Import Coq.Lists.ListSet.
(* Extra tactics *)
Require Import Tactics.
(* Misc lemmas and definitions about the iterator *)
Require Import IteratorsSpec.

Set Implicit Arguments.
Unset Strict Implicit.

Open Local Scope stsep_scope.
Open Local Scope hprop_scope.

(* Create a new collection. *)
Program Definition Inewcoll : 
    STsep emp Ac 
    (fun y i m => exists P, exists v : Ac, Val v = y /\ Icoll v nil P m) :=
	sdo (snew Nil).
Next Obligation.
nextvc.
exists (exact_pred h).
exists x.
split.
reflexivity.
unfold Icoll.
split.
apply Seq_nil.
split; auto.
split.
unfold exact_pred.
trivial.
eapply exact_pred_exact.
Defined.

(* Return the size of a collection. *)
Program Definition Isize (c : Ac) (xs : list nat) (P : hprop) :
    STsep (fun i => Icoll c xs P i) nat 
	  (fun y i m => i = m /\ exists n : nat, Icoll c xs P m /\ y = Val n /\ length xs = n) :=
	  sdo (x <-- !!c;
	       sfix (fun s x =>
                       (match x with
			    | Nil      => sdo 
					  (p2 := fun h => (x = Nil /\ emp h) \/ 
						          (exists t, exists zs, exists n, 
							   x = Cons n t /\ Seq_pred t zs h))
					  (q2 := fun y i m => (i = m /\ 
					  	 (forall n t zs, x = Cons n t /\ Seq_pred t zs i -> 
						  y = Val (1 + length zs)) /\ (x = Nil -> y = Val 0)))
                                              (sret 0)
			    | Cons _ t => sdo (z <-- (sread (A:=Seq) t) ; n <-- s z ; sret (n + 1))
		     end)) x).
Next Obligation.
nextvc.
inversion H0.
Qed.
Next Obligation.
destruct H.
destruct H; congruence.
destruct H as [t0 [zs [n [H1 H2]]]].
injection H1; intros; subst.
induction H2.
nextvc.
assert (((t0 --> Nil) # nopre) i).
destruct H as [H5 H6].
unfold star1.
exists i; exists empty.
intuition.
remove_empty; apply splits_refl.
eexact H0.
nextvc.
destruct H as [H H2].
exists empty; split.
left; auto.
exists i; split.
remove_empty; apply splits_refl.
intros j j1 H5.
split.
intros x0 [H6 [H7 H8]].
subst j1.
remove_empty_in H5; intro H9; clear H5.
rewrites.
generalize (H8 (refl_equal _)); intro H9; injection H9; intros; subst; clear H8 H9.
simpl.
nextvc.
injection H; intros; subst; clear H.
destruct H0.
rewrite (proj1 H); simpl; auto.
destruct H as [x1 [x2 [c' [H11 H12]]]].
unfold star1 in H12.
destruct H12 as [h1 [h2 [H13 [H14 H15]]]].
assert (H16 : h1 = i /\ Cons x1 c' = Nil) by eauto using points_to_same_subheap, splits_refl. 
destruct H16; congruence.
congruence.
intros e [H6 [H7 H8]].
assert (H9 : Exn e = Val 0) by auto.
discriminate H9.
clear H1.
destruct H as [x0 [xs' [c' [H5 [h1 [h2 [H6 [H7 H8]]]]]]]].
subst zs.
nextvc.
exists h2; split.
right; eauto.
exists h1; split.
apply splits_commute; trivial.
intros j j1 H5.
split.
intros x1 [H8' [H9 H10]].
subst j1.
assert (Val x1 = Val (S (length xs'))).
eapply H9; eauto.
injection H; intros; subst; clear H.
nextvc.
assert (splits j (h1 :: h2 :: nil)) by (apply splits_commute; auto).
rewrites; auto.
injection H; intros; subst; clear H.
f_equal.
simpl; apply eq_S.
destruct H0.
destruct H.
assert (h1 = i /\ Cons x0 c' = Nil) by eauto using points_to_same_subheap, splits_refl.
destruct H1 as [_ H1].
discriminate H1.
destruct H as [x1 [xs1 [c2 [H14 [h3 [h4 [H11 [H12 H13]]]]]]]].
subst zs; simpl.
assert (Val (S (length xs')) = Val (S (length xs1))).
eapply H9; eauto.
split; eauto.
assert (h3 = h1 /\ Cons x1 c2 = Cons x0 c') by eauto using points_to_same_subheap, splits_refl.
destruct H as [H H14]; subst h3; injection H14; intros; subst; clear H14.
replace h2 with h4; trivial.
rewrites; auto.
injection H; omega.
congruence.
intros e [H8' [H9 H10]].
subst j1.
assert (Exn e = Val (S (length xs'))).
apply (H9 x0 c' xs').
(* eapply H9; eauto. *)
split; eauto.
discriminate H.
Defined.

(* Here! *)

Next Obligation.
unfold Icoll in H.
destruct H.
destruct H.
nextvc.
exists i; exists empty.
split.
remove_empty.
apply splits_refl.
split.
destruct H; apply H1.
auto.
exists i.
split.
exists empty.
exists i.
split.
remove_empty.
apply splits_refl.
split.
left.
intuition.
auto.
intros y m [h6 [h7 [H9 H10]]].
destruct H10 as [h1 [h2 [H10 [[H11 [H12 H13]] H14]]]].
subst h6.
unfold delta, this in H14.
destruct H14; subst h7; subst h2.
rewrites_once.
split; trivial.
exists 0; intuition.
unfold Icoll.
auto using Seq_nil.
rewrite H1.
unfold length.
trivial.
destruct H as [x [xs' [c' [H4 [h1 [h2 [H6 [H7 H8]]]]]]]].
subst xs.
nextvc.
exists h1; split.
unfold star1.
exists h2; exists h1; split.
apply splits_commute; auto.
split; auto.
right; eauto.
intros y m [h6 [h7 [H9 H10]]].
destruct H10 as [h3 [h4 [H10 [[H11 [H12 H13]] H14]]]].
subst h6.
unfold delta, this in H14.
destruct H14; subst h7; subst h4.
rewrites_once.
split; trivial.
exists (S (length xs')).
unfold Icoll.
intuition.
apply Seq_cons.
unfold star1.
eauto 10.
assert (splits i (h1 :: h3 :: nil)) by (apply splits_commute; auto).
rewrites_once.
eauto.
Defined.

(* Add an element to a collection. *)
Program Definition Iadd (c : Ac) (x : nat) :
    STsep (fun i => exists xs, exists P, Icoll c xs P i) unit
          (fun y i m => y = Val tt /\ forall xs P, Icoll c xs P i
	  -> exists Q, Icoll c (x::xs) Q m) :=
	  sdo (cell <-- (sread (A:=Seq) c);
	       r    <-- snew (A := Seq) cell;
	       c    ::= Cons x r).
Next Obligation.
unfold Icoll in H1.
destruct H1 as [ H2 [ H3 H4 ] ].
destruct H2 as [ [ Hnil Hpointsnil ] | SeqH ].
nextvc.
nextvc.
exists i.
split; [ exists Seq; exists Nil; assumption | idtac ].
exists t.
split; [ assumption | idtac ].
intros.
split.
trivial.
intros.
unfold Icoll in H6.
destruct H6 as [ H7 [ H8 H9 ] ].
destruct H7.
destruct H6 as [ H10 H11 ].
rewrite_clear.
assert(Seq_pred_exact c (x::nil) (x0::nil) j0).
apply Seq_exact_cons.
exists x; exists (nil (A := nat)); exists x0; exists (nil (A := loc)).
repeat(split; trivial).
exists j1; exists t.
repeat(split; try assumption).
apply Seq_exact_nil.
repeat(split; trivial).
assert(Seq_pred c (x::nil) j0).
eapply Seq_pred_lemma.
apply H6.
exists (Seq_pred_exact c (x::nil) (x0::nil)).
unfold Icoll.
repeat(split; try assumption).
eapply Seq_pred_exact_is_exact.
destruct H6 as [ x' [ xs' [ c' [ H10 [ h1 [ h2 [ H11 [ H12 H13 ] ] ] ] ] ] ] ].
assert(splits i (i::nil)).
apply splits_refl.
assert(i = h1 /\ Nil = (Cons x' c')).
eapply points_to_same_subheap; eauto.
destruct H7 as [ H14 H15 ].
inversion H15.
destruct SeqH as [ x' [ xs' [ c' [ H5 H6 ] ] ] ].
destruct H6 as [ i1 [ i2 [ H7 [ H8 H9 ] ] ] ].
nextvc.
nextvc.
exists i1.
split.
exists Seq; exists (Cons x' c'); assumption.
splits_rewrite_in H7 H.
rename H2 into N100.
assert(disjoint (i2::t::nil)).
disjoint_prove.
exists (union (i2::t::nil) H2).
split.
splits_flatten.
splits_prove.
intros.
split.
trivial.
intros.
unfold Icoll in H10.
destruct H10 as [ H11 [ H12 H13 ] ].
unfold Icoll.
destruct H11.
destruct H10.
assert(splits i (i::nil)).
apply splits_refl.
assert(i = i1 /\ Nil = (Cons x' c')).
eapply points_to_same_subheap; eauto.
destruct H15.
inversion H16.
destruct H10 as [ x'' [ xs'' [ c'' [ H14 H15 ] ] ] ].
rewrite_clear.
destruct H15 as [ i3 [ i4 [ H16 [ H17 H18 ] ] ] ].
assert(i1 = i3 /\ (Cons x' c') = (Cons x'' c'')).
eapply points_to_same_subheap.
apply H8.
apply H17.
apply H7.
apply H16.
destruct H10.
inversion H11.
clear H11.
rewrite_clear.
generalize(splits_same_tail H16 H7).
intros.
destruct H8 as [ pf1 [ pf2 H19 ] ].
simpl in H19.
rewrite_clear.
assert(Seq_pred x0 (x''::xs'') (union (i2::t::nil) H2)).
apply Seq_cons.
exists x''; exists xs''; exists c''.
split; [ trivial | idtac ].
exists t; exists i2.
split.
assert(disjoint(t::i2::nil)).
eapply disjoint_permute.
apply H2.
PermutProve.
exists H7.
eapply union_permute; PermutProve.
split; trivial.
exists (exact_pred j0).
split.
apply Seq_cons.
exists x; exists (x''::xs''); exists x0.
split.
trivial.
exists j1; exists (union (i2::t::nil) H2).
split.
assumption.
split.
assumption.
assumption.
split.
unfold exact_pred; trivial.
eapply exact_pred_exact.
Defined.

(* Return a new coll iterator. *)
Program Definition Inewiter (c : Ac) :
    STsep (fun i => exists xs, exists P, Icoll c xs P i) Ai
          (fun y i m => exists a:Ai, Val a = y /\ forall xs P, Icoll c xs P i ->
	  ((Icoll c xs P) # (Iiter a ((c, xs, P)::nil) xs)) m) :=
    sdo (r <-- snew c; sret (Coll r)).
Next Obligation.
nextvc.
nextvc.
exists (Coll x).
split.
auto.
intros.
exists i.
exists t.
split.
assumption.
split.
assumption.
unfold Iiter.
exists c.
exists (nil (A:=nat)).
split.
simpl.
auto.
exists t.
exists empty.
split.
remove_empty.
apply splits_refl.
split.
assumption.
unfold wand.
intros.
split.
splits_auto.
assumption.
exists empty.
exists h2.
split.
remove_empty.
apply splits_refl.
split.
unfold Isegment.
split.
auto.
auto.
splits_auto.
unfold Icoll in H4.
unfold Icoll in H5.
destruct H5.
assumption.
Qed.

(* Return a filter iterator. *)
Program Definition Ifilter (p : nat -> bool) (it : Ai) :
  STsep 
    (fun i => exists S, exists xs, Iiter it S xs i) Ai
    (fun y i m => y = Val (Filter p it) /\ forall S, forall xs, 
       Iiter it S xs i -> Iiter (Filter p it) S (filter p xs) m) :=
	sdo (sret (Filter p it)).
Next Obligation.
nextvc.
exists xs.
intuition.
Qed.

Definition next_type := forall (it : Ai), 
  STsep 
    (fun i => exists S, exists xs, (colls S # Iiter it S xs) i)
    (option nat)
    (fun y i m => forall S xs, (colls S # Iiter it S xs) i ->
      (y = Val (opt_hd xs) /\ (colls S # Iiter it S (tail xs)) m)).

Definition next_coll_nil_pre (r : Ac) (i : heap) :=
  exists S, exists xs, exists lst, exists cell, 
     ((colls S) # (Iiter (Coll r) S xs)) i /\
     ((r --> lst) # (lst --> cell) # nopre) i /\ seqopt(cell) = None.

Definition next_coll_nil_post (r : Ac) : post (option nat) :=
  fun y i m =>
  forall S xs lst cell, 
     (((colls S) # (Iiter (Coll r) S xs)) i /\
      ((r --> lst) # (lst --> cell) # nopre) i /\ seqopt(cell) = None) ->
     (y = Val (opt_hd xs) /\ ((colls S) # (Iiter (Coll r) S (tail xs))) m).

(* The next computation for the coll iterator, in the case where
   the collection is empty. *)
Program Definition next_coll_nil (r : Ac) : 
  STsep (next_coll_nil_pre r)
        (option nat)
       	(next_coll_nil_post r) :=
  sdo (sret None).
Next Obligation.
nextvc.
unfold next_coll_nil_pre in H.
unfold next_coll_nil_post.
intros. 
destruct H0 as [ H1 [ H2 H3 ] ].
unfold seqopt in H3.
case_eq cell.
Focus 2.
intros.
rewrite H0 in H3.
inversion H3.
intros.
clear H3.
clear H.
rewrite H0 in H2; clear H0.
assert(xs = nil).
  eapply colls_Iiter_lemma.
  apply H1.
  exists lst.
    destruct H2 as [ h1 [ h2 [ H3 [ H4 H5 ] ] ] ].
    destruct H4 as [ h3 [ h4 [ H6 [ H7 H8 ] ] ] ].
    splits_rewrite_in H6 H3.
    clear H5 H3 H6.
    split.
    eapply selects_points_to_lemma; eauto.
  eapply selects_points_to_lemma.
  apply H8.
  instantiate (1 := (h3::h2::nil)).
  splits_prove.
rewrite_clear.
simpl tail.
simpl opt_hd.
split; trivial.
Defined.

Definition next_coll_cons_pre (r : Ac) (v : (nat * loc)%type) (i : heap) :=
  exists S, exists xs, exists lst, exists cell, 
     ((colls S) # (Iiter (Coll r) S xs)) i /\
     ((r --> lst) # (lst --> cell) # nopre) i /\ seqopt(cell) = Some v.

Definition next_coll_cons_post (r : Ac) (v : (nat * loc)%type) : post (option nat) :=
  fun y i m =>
  forall S xs lst cell, 
     (((colls S) # (Iiter (Coll r) S xs)) i /\
      ((r --> lst) # (lst --> cell) # nopre) i /\ seqopt(cell) = Some v) ->
     (y = Val (opt_hd xs) /\ ((colls S) # (Iiter (Coll r) S (tail xs))) m).

(* The next computation for the coll iterator, in the case where
   the collection is non-empty. *)
Program Definition next_coll_cons (r : Ac) (v : (nat * loc)%type) : 
  STsep (next_coll_cons_pre r v)
        (option nat)
       	(next_coll_cons_post r v) :=
  sdo (r ::= (snd v) ;;
       sret (Some (fst v))).
Next Obligation.
unfold next_coll_cons_pre in H.
destruct H as [ S [ xs [ lst [ cell [ H1 [ H2 H3 ] ] ] ] ] ].
induction cell.
unfold seqopt in H3.
inversion H3.
clear H3.
rename H1 into G1.
destruct H2 as [ i1 [ i2 [ I1 [ [ i3 [ i4 [ I4 [ I5 I6 ] ] ] ] I3 ] ] ] ].
splits_rewrite_in I4 I1; clear I1 I4 I3.
nextvc.
exists i3.
split.
exists loc; exists lst; assumption.
generalize(splits_into_remove_points_to r i); intros I7.
generalize(points_to_lemma H I5); intros I8.
rewrite <- I8 in I7.
exists [i \\ r].
split.
apply splits_commute; assumption.
intros.
clear I8 I7.
nextvc.
unfold next_coll_cons_post.
intros.
destruct H2 as [ H2 [ H3 H4 ] ].
induction cell.
unfold seqopt in H4; inversion H4.
unfold seqopt in H4.
inversion H4; clear H4.
rewrite_clear.
destruct H3 as [ d1 [ d2 [ D1 [ [ d3 [ d4 [ D4 [ D5 D6 ] ] ] ] D3 ] ] ] ].
splits_rewrite_in D4 D1; clear D4 D1 D3.
assert(i3 = d3 /\ lst = lst0).
eapply points_to_same_subheap; eauto.
rewrite_clear.
assert(d4 = i4 /\ Cons n l = Cons n0 l0).
eapply points_to_same_subheap; eauto.
instantiate (1 := (d3::d2::nil)).
instantiate (1 := i).
splits_prove.
instantiate (1 := (d3::i2::nil)).
splits_prove.
destruct H4.
inversion H5; clear H5.
rewrite_clear.
assert((((r --> lst0) # (lst0 --> Cons n0 l0)) # nopre) i).
splits_join_in H (1::1::0::nil).
exists (union (d3::i4::nil) pf0); exists i2.
intuition.
exists d3; exists i4.
intuition.
exists pf0; trivial.
clear D5 D6 H3 H d3 d2 i4.
generalize(unfold_colls_Icoll1 H2 H4); clear H2 H4; intros H5.
destruct H5 as [ h1 [ h2 [ h3 [ h4 [ h5 [ h6 [ a [ ys [ P [ H6 [ H7 [ H8 [ H9 [ H10 [ H11 [ H12 [ H13 H14 ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
destruct H14.
destruct H as [ H14 H15 ].
splits_rewrite_in H8 H7.
assert(h2 = h6 /\ Cons n0 l0 = Nil).
eapply points_to_same_subheap; eauto.
instantiate (1 := (h1::h3::nil)).
instantiate (1 := i).
splits_prove.
instantiate (1 := (h5::h1::nil)).
splits_prove.
destruct H2 as [ H16 H17 ]; inversion H17.
destruct H as [ x [ xs' [ c' [ H14 H15 ] ] ] ].
destruct H15 as [ h7 [ h8 [ H16 [ H17 H18 ] ] ] ].
splits_rewrite_in H8 H7.
splits_rewrite_in H16 H; clear H.
assert(h2 = h7 /\ Cons n0 l0 = Cons x c').
eapply points_to_same_subheap.
apply H10.
apply H17.
instantiate (1 := (h1::h3::nil)).
instantiate (1 := i).
splits_prove.
instantiate (1 := (h5::h8::h1::nil)).
apply (splits_permute H2).
PermutProve.
destruct H as [ H19 H20 ].
inversion H20; clear H20.
rewrite_clear.
simpl opt_hd.
intuition.
simpl tail.
generalize(splits_into_remove_points_to r i); intros H21.
assert(h1 = [r |--> i r]).
eapply points_to_lemma.
instantiate (1 := (h4::nil)).
splits_prove.
apply H9.
rewrite <- H in H21; clear H.
generalize(splits_same_head H7 H21); clear H21; intros H21.
exists h4.
exists j1.
rewrite_clear.
unfold colls.
split.
apply splits_commute; assumption.
split.
rewrite star_unit_right.
assumption.
unfold Iiter.
exists c'; exists (ys ++ (x :: nil)).
split.
apply useful_lists_lemma.
exists j1.
exists empty.
split.
remove_empty; apply splits_refl.
intuition.
unfold wand.
intros.
splits_rewrite.
split.
assumption.
assert(h0 = [i \\ r]).
unfold Icoll in H11, H.
destruct H11 as [ H22 [ H23 H24 ] ].
destruct H as [ H25 [ H26 H27 ] ].
eapply H24; eauto.
rewrite_clear.
splits_rewrite_in H16 H8.
splits_join_in H (1::1::0::nil).
exists (union (h5::h7::nil) pf0); exists h8.
intuition.
eapply Isegment_lemma; eauto.
exists pf0; trivial.
Defined.

(* Put together the next computation for the coll iterator. *)
Program Definition next_coll (next : next_type) (r : Ac)  :
    STsep (fun i => exists S, exists xs, ((colls S) # (Iiter (Coll r) S xs)) i)
	  (option nat)
	  (fun y i m => forall S xs, ((colls S) # (Iiter (Coll r) S xs)) i ->
			(y = Val (opt_hd xs) /\ ((colls S) # (Iiter (Coll r) S (tail xs))) m)) :=
    sdo(list <-- sread (A:=loc) r ;
	cell <-- sread (A:=Seq) list ;
        case_option (seqopt cell) (fun _ _ => next_coll_nil r)
                                  (fun v : nat * loc => fun _ =>
                                       next_coll_cons r v)).
Next Obligation.
generalize(colls_Iter_lemma H1); intros H2.
rename H1 into G1.
destruct H2 as [ lst [ cell H2 ] ].
copy H2 G2.
destruct H2 as [ i1 [ i2 [ H3 [ H4 H5 ] ] ] ].
destruct H4 as [ i3 [ i4 [ H6 [ H7 H8 ] ] ] ].
splits_rewrite_in H6 H3; clear H6 H3 H5.
nextvc.
splits_join_in H1 (0::1::1::nil).
exists i3; exists (union (i4::i2::nil) pf0).
intuition.
apply splits_commute; assumption.
apply H7.
nextvc.
splits_join_in H1 (1::0::1::nil).
exists i4; exists (union (i3::i2::nil) pf0).
intuition.
apply splits_commute; assumption.
apply H8.
nextvc.
exists empty.
split.
exists i; exists empty.
intuition.
remove_empty; apply splits_refl.
unfold next_coll_nil_pre.
exists H; exists H0; exists lst; exists cell.
intuition.
unfold opt2sum in H2.
unfold seqopt in H2.
induction cell.
unfold seqopt; trivial.
inversion H2.
intros. 
destruct H3 as [ j1 [ j2 [ J1 [ j3 [ j4 [ J2 [ J3 J4 ] ] ] ] ] ] ].
destruct J4 as [ J5 J6 ]; unfold this in J5, J6.
rewrite <- J5 in *; rewrite <- J6 in *; clear J5 J6 j2 j4.
splits_rewrite.
unfold next_coll_nil_post in J3.
unfold opt2sum, seqopt in H2.
induction cell.
assert((colls S # Iiter (Coll r) S xs) j1 /\
       (((r --> lst) # (lst --> Nil)) # nopre) j1 /\ seqopt Nil = None).
intuition.
generalize(J3 S xs lst Nil H3).
trivial.
inversion H2.
exists empty.
split.
exists i; exists empty.
intuition.
remove_empty; apply splits_refl.
unfold next_coll_cons_pre.
exists H; exists H0; exists lst; exists cell.
intuition.
unfold opt2sum, seqopt in H2.
induction cell.
inversion H2.
inversion H2.
unfold seqopt; trivial.
intros.
destruct H3 as [ j1 [ j2 [ J1 [ j3 [ j4 [ J2 [ J3 J4 ] ] ] ] ] ] ].
destruct J4 as [ J5 J6 ]; unfold this in J5, J6.
rewrite <- J5 in *; rewrite <- J6 in *; clear J5 J6 j2 j4.
splits_rewrite.
unfold next_coll_cons_post in J3.
unfold opt2sum, seqopt in H2.
induction cell.
inversion H2.
assert((colls S # Iiter (Coll r) S xs) j1 /\
       (((r --> lst) # (lst --> (Cons n l))) # nopre) j1 /\ seqopt (Cons n l) = Some y).
intuition.
inversion H2; unfold seqopt; trivial.
generalize(J3 S xs lst (Cons n l) H3).
trivial.
Defined.

Definition p2 (x : nat) (p : nat -> bool) (it : Ai) :=
  (fun i =>
    (true = p x -> (exists S, exists xs, exists xs',
      (colls S # Iiter it S (tail xs')) i /\ 
         xs = x::(filter p (tail xs')))) /\
    (false = p x -> (exists S, exists xs, exists xs',
      (colls S # Iiter it S (tail xs')) i /\ xs = filter p (tail xs')))).

(* The next computation for the filter iterator, for the
   case where the underlying iterator is empty. *)
Program Definition next_filter_none (v : option nat) (p : nat -> bool) (it : Ai) :
  STsep (fun i => exists S, exists xs, exists xs',
    xs = filter p xs' /\ (colls S # Iiter it S (tail xs')) i /\
    v = opt_hd xs' /\ v = None)
    (option nat)
    (fun y i m => forall S xs xs',
      (xs = filter p xs' /\ (colls S # Iiter it S (tail xs')) i /\ 
       v = opt_hd xs' /\ v = None) ->
       ((colls S # Iiter (Filter p it) S (tail xs)) m /\
         y = Val (opt_hd xs))) :=
  sdo(sret None).
Next Obligation.
unfold opt_hd in H5.
case_eq (H1).
intros.
Focus 2.
intros.
rewrite H0 in H5.
inversion H5.
rewrite H0 in H5.
clear H5.
nextvc.
destruct H0 as [ i1 [ i2 [ H4 [ H5 H6 ] ] ] ].
exists i1; exists i2.
intuition.
unfold opt_hd in H2.
case_eq xs'.
intros.
clear H2.
exists (nil (A := nat)).
simpl filter.
simpl tail.
rewrite H0 in H6.
simpl tail in H6.
intuition.
intros.
rewrite H0 in H2; inversion H2.
unfold opt_hd in H2.
case_eq xs'.
intros.
clear H2.
simpl.
trivial.
intros.
rewrite H4 in H2; inversion H2.
Defined.

Definition boolopt (b : bool) : option nat := 
  match b with
  | true => Some 0
  | false => None
  end.

Lemma lists_lemma : forall (x : nat) (l : list nat),
  (opt_hd l) = Some x -> l = x::(tail l).
intros.
induction l.
unfold opt_hd in H.
inversion H.
unfold opt_hd in H.
inversion H.
rewrite H1 in *; clear H H1 a.
simpl tail.
trivial.
Qed.

(* The next computation for the filter iterator, for the
   case where the underlying iterator is non-empty and the
   given predicate is true for its next element. *)
Program Definition next_filter_some_true (v : option nat) (x : nat) (p : nat -> bool) (it : Ai) :
  STsep (fun i => exists S, exists xs, exists xs',
    xs = filter p xs' /\ (colls S # Iiter it S (tail xs')) i /\
    v = opt_hd xs' /\ v = Some x /\ boolopt (p x) = Some 0)
    (option nat)
    (fun y i m => forall S xs xs',
      (xs = filter p xs' /\ (colls S # Iiter it S (tail xs')) i /\ 
       v = opt_hd xs' /\ v = Some x /\ boolopt (p x) = Some 0) ->
       ((colls S # Iiter (Filter p it) S (tail xs)) m /\
         y = Val (opt_hd xs)))
  := sdo(sret (Some x)).
Next Obligation.
nextvc.
unfold boolopt in H7.
case_eq (p x).
intros.
clear H7.
destruct H0 as [ i1 [ i2 [ H9 [ H10 H11 ] ] ] ].
exists i1; exists i2.
intuition.
exists (tail xs').
intuition.
pattern xs' at 1.
rewrite (lists_lemma H4).
unfold filter.
fold filter.
rewrite H8.
simpl tail.
trivial.
intros.
rewrite H8 in H7.
inversion H7.
rewrite (lists_lemma H4).
unfold filter.
fold filter.
unfold boolopt in H7.
case_eq (p x).
intros.
simpl opt_hd.
trivial.
intros.
rewrite H8 in H7.
inversion H7.
Defined.

(* The next computation for the filter iterator, for the
   case where the underlying iterator is non-empty and the
   given predicate is false for its next element. *)
Program Definition next_filter_some_false (next : next_type) (v : option nat) (x : nat) (p : nat -> bool) (it : Ai) :
  STsep (fun i => exists S, exists xs, exists xs',
    (colls S # Iiter it S (tail xs')) i /\ xs = filter p xs' /\
    v = opt_hd xs' /\ v = Some x /\ boolopt (p x) = None)
    (option nat)
    (fun y i m => forall S xs xs',
      (xs = filter p xs' /\ (colls S # Iiter it S (tail xs')) i /\ 
       v = opt_hd xs' /\ v = Some x /\ boolopt (p x) = None) ->
       ((colls S # Iiter (Filter p it) S (tail xs)) m /\
         y = Val (opt_hd xs)))
  := sdo(next(Filter p it)).
Next Obligation.
unfold boolopt in H6.
case_eq (p x); intros.
rewrite H0 in H6; inversion H6.
clear H6.
exists empty.
split.
exists i; exists empty.
intuition.
remove_empty; apply splits_refl.
exists H; exists (filter p (tail H1)).
destruct H2 as [ i1 [ i2 [ I3 [ I4 I5 ] ] ] ].
exists i1; exists i2.
intuition.
exists (tail H1).
intuition.
intros.
destruct H4 as [ H6 [ H7 [ H8 [ H9 H10 ] ] ] ].
destruct H3 as [ h1 [ h2 [ H11 [ h3 [ h4 [ H12 [ H13 H14 ] ] ] ] ] ] ].
destruct H14 as [ H15 H16 ].
unfold this in H15, H16.
rewrite <- H15 in *; rewrite <- H16 in *.
clear H15 H16 h2 h4.
splits_rewrite.
assert((colls S # (fun h : heap => exists xs' : list nat, xs = filter p xs' /\ Iiter it S xs' h)) h1).
destruct H7 as [ i1 [ i2 [ I1 [ I2 I3 ] ] ] ].
exists i1; exists i2.
intuition.
exists (tail xs').
intuition.
rewrite H8 in H9.
rewrite (lists_lemma H9) in H6.
unfold filter in H6.
fold filter in H6.
rewrite H0 in H6.
assumption.
generalize(H13 S xs H3); clear H13; intros H13.
destruct H13.
split; assumption.
Defined.

(* The next computation for the filter iterator, for the
   case where the underlying iterator is not empty. *)
Program Definition next_filter_some (next : next_type) (v : option nat) (x : nat) (p : nat -> bool) (it : Ai) :
  STsep (fun i => exists S, exists xs, exists xs',
    xs = filter p xs' /\ (colls S # Iiter it S (tail xs')) i /\
    v = opt_hd xs' /\ v = Some x)
    (option nat)
    (fun y i m => forall S xs xs',
      (xs = filter p xs' /\ (colls S # Iiter it S (tail xs')) i /\ 
       v = opt_hd xs' /\ v = Some x) ->
       ((colls S # Iiter (Filter p it) S (tail xs)) m /\
         y = Val (opt_hd xs))) :=
  sdo(case_option (boolopt (p x)) 
      (fun _ _ => next_filter_some_false next v x p it)
      (fun _ _ => next_filter_some_true v x p it)).
Next Obligation.
nextvc.
unfold opt2sum, boolopt in H0.
case_eq (p x); intros.
rewrite H2 in H0.
inversion H0.
clear H0 x0.
exists empty.
split.
exists i; exists empty.
intuition.
remove_empty; apply splits_refl.
exists H; exists (filter p (tail H1)); exists H1.
intuition.
pattern H1 at 2.
rewrite (lists_lemma H5).
unfold filter; fold filter.
rewrite H2.
trivial.
intros. 
destruct H4 as [ H12 [ H13 [ H14 H15 ] ] ].
destruct H0 as [ k1 [ k2 [ K1 [ k3 [ k4 [ K2 [ K3 K4 ] ] ] ] ] ] ].
destruct K4 as [ K5 K6 ]; unfold this in K5, K6.
rewrite <- K5 in *; rewrite <- K6 in *; clear K5 K6 k2 k4.
splits_rewrite.
assert(xs = filter p xs' /\ (colls S # Iiter it S (tail xs')) k1 /\
       opt_hd H1 = opt_hd xs' /\ opt_hd H1 = Some x /\ boolopt false = None).
intuition.
generalize(K3 S xs xs' H0); clear K3; intros K3.
destruct K3.
intuition.
unfold opt2sum, boolopt in H0.
case_eq (p x); intros.
clear H0.
exists empty.
split.
exists i; exists empty.
intuition.
remove_empty; apply splits_refl.
exists H; exists (filter p H1); exists H1.
intuition.
intros.
destruct H0 as [ l1 [ l2 [ L1 [ l3 [ l4 [ L2 [ L3 L4 ] ] ] ] ] ] ].
destruct L4 as [ L5 L6 ]; unfold this in L5, L6.
rewrite <- L5 in *; rewrite <- L6 in *; clear L5 L6 l2 l4.
splits_rewrite.
assert(xs = filter p xs' /\ (colls S # Iiter it S (tail xs')) l1 /\
       opt_hd H1 = opt_hd xs' /\ opt_hd H1 = Some x /\ boolopt true = Some 0).
intuition.
generalize(L3 S xs xs' H0); clear L3; intros L3.
intuition.
rewrite H2 in H0.
inversion H0.
Defined.

Lemma star_unit_left : forall (P : hprop) (h : heap),
  (emp # P) h <-> P h.
intros.
split.
intros.
destruct H as [ h1 [ h2 [ H1 [ H2 H3 ] ] ] ].
splits_rewrite.
assumption.
intros.
exists empty; exists h.
intuition.
remove_empty; apply splits_refl.
Qed.

Lemma seq_pred_lemma''' : 
  forall (l : loc) (h h1 h2 h3 h4 : heap) (l1 l2 : list nat),
    splits h (h1::h2::nil) -> splits h (h3::h4::nil) ->
      Seq_pred l l1 h1 -> Seq_pred l l2 h3 -> (l1 = l2 /\ h1 = h3).
intros.
generalize dependent l.
generalize l2 h1 h2 h3 h4 H H0.
elim l1.
clear l2 h2 h3 h4 H H0.
intros.
destruct H1.
destruct H2.
intuition.
unfold points_to in H4, H5.
congruence.
destruct H2 as [ x [ xs' [ c' [ H3 H4 ] ] ] ].
destruct H4 as [ h5 [ h6 [ H5 [ H6 H7 ] ] ] ].
splits_rewrite_in H5 H0.
assert(h0 = h5 /\ Nil = Cons x c').
destruct H1.
eapply points_to_same_subheap; eauto.
destruct H4.
inversion H8.
destruct H1 as[ x [ xs' [ c' [ H3 H4 ] ] ] ].
inversion H3.
intros.
destruct H4.
destruct H4.
inversion H4.
destruct H4 as [ x [ xs' [ c' [ H6 H7 ] ] ] ].
destruct H7 as [ h8 [ h9 [ H8 [ H9 H10 ] ] ] ].
inversion H6.
rewrite_clear.
destruct H5.
destruct H4.
assert(h6 = h8 /\ Nil = Cons x c').
splits_rewrite_in H8 H2.
eapply points_to_same_subheap; eauto.
destruct H6.
inversion H7.
destruct H4 as [ x' [ xs'' [ c'' [ H11 H12 ] ] ] ].
destruct H12 as [ h10 [ h11 [ H13 [ H14 H15 ] ] ] ].
splits_rewrite_in H8 H2; clear H8.
splits_rewrite_in H13 H3; clear H13.
assert(h10 = h8 /\ Cons x' c'' = Cons x c').
eapply points_to_same_subheap; eauto.
destruct H6.
inversion H7; clear H7.
rewrite_clear.
assert(xs' = xs'' /\ h9 = h11).
splits_join_in H4 (1::0::1::nil).
splits_join_in H5 (1::0::1::nil).
apply splits_commute in H6.
apply splits_commute in H7.
eapply H1.
apply H6.
apply H7.
apply H10.
apply H15.
destruct H6.
rewrite_clear.
intuition.
assert(h5 = h7).
eapply splits_same_head.
instantiate (1 := (h8::h11::nil)).
instantiate (1 := h).
apply (splits_permute H4).
PermutProve.
apply (splits_permute H5).
PermutProve.
rewrite_clear.
eapply splits_same_head; eauto.
Qed.

Lemma Isegment_lemma'' :
  forall (l l' : loc) (ll : list nat) (h : heap),
    Isegment l l' ll h -> nil <> ll -> 
      (exists l'' : loc, exists x : nat, exists ll' : list nat,
        ll = ll' ++ (x::nil) /\ (l'' --> Cons x l' # Isegment l l'' ll') h).
intros.
generalize l h H H0.
elim ll.
intros.
contradiction H2; trivial.
clear H0 H l.
intros.
clear H1.
case_eq l; intros; rewrite_clear.
unfold Isegment in H0.
destruct H0 as [ c'' [ h1 [ h2 [ H1 [ H2 [ H3 H4 ] ] ] ] ] ].
unfold emp in H4; rewrite H4 in H1; clear H4 h2.
splits_rewrite.
exists l0; exists a; exists (nil (A := nat)).
intuition.
exists h1; exists empty.
intuition.
remove_empty; apply splits_refl.
rewrite <- H3; assumption.
unfold Isegment.
intuition.
unfold Isegment in H0; fold Isegment in H0.
destruct H0 as [ c'' [ h1 [ h2 [ H1 [ H2 H3 ] ] ] ] ].
assert(Isegment c'' l' (n::l1) h2).
apply H3.
clear H3.
assert(nil <> n :: l1).
apply nil_cons.
generalize(H c''  h2 H0 H3); clear H; intros H.
destruct H as [ l'' [ x [ ll' [ H5 H6 ] ] ] ].
destruct H6 as [ h3 [ h4 [ H7 [ H8 H9 ] ] ] ].
splits_rewrite_in H7 H1; clear H1 H7.
splits_join_in H (1::0::1::nil).
assert(Isegment l0 l'' (a::ll') (union (h1::h4::nil) pf0)).
unfold Isegment.
exists c''.
exists h1; exists h4.
split.
exists pf0; trivial.
split; assumption.
exists l''; exists x; exists (a::ll').
split.
rewrite H5.
simpl.
trivial.
exists h3; exists (union (h1::h4::nil) pf0).
intuition.
apply splits_commute.
trivial.
Qed.

Lemma points_to_emp_left : 
  forall (A : Type) (v : A) (l : loc) (h : heap) (Q : hprop),
    ((l --> v) # Q) h -> emp h -> False.
intros.
destruct H as [ h1 [ h2 [ H1 [ H2 H3 ] ] ] ].
assert(h l = h1 l).
eapply splits_points_to; eauto.
unfold emp in H0.
rewrite H0 in H.
unfold points_to, update_loc, modify_loc in H2.
rewrite H2 in H.
rewrite loc_eq_refl in H.
unfold empty in H.
inversion H.
Qed.

(* Put together the next computation for the filter iterator *)
Program Definition next_filter (next : next_type) (p : nat -> bool) (it : Ai) :
  STsep
    (fun i => exists S, exists xs, 
      (colls S # Iiter (Filter p it) S xs) i)
    (option nat)
    (fun y i m => forall S xs,
      (colls S # Iiter (Filter p it) S xs) i ->
        (y = Val (opt_hd xs) /\ 
          (colls S # Iiter (Filter p it) S (tail xs)) m))
  := sdo(v <-- next it;
         case_option v 
             (fun _ _ => next_filter_none v p it)
             (fun x : nat => fun _ => next_filter_some next v x p it)).
Next Obligation.
nextvc.
exists i.
split.
destruct H1 as [ i1 [ i2 [ H2 [ H3 H4 ] ] ] ].
destruct H4 as [ xs' [ H5 H6 ] ].
exists H; exists xs'.
exists i1; exists i2; intuition.
exists empty.
split.
remove_empty; apply splits_refl.
intros.
splits_rewrite.
split.
Focus 2.
intros.
destruct H1 as [ i1 [ i2 [ I1 [ I2 [ l [ I3 I4 ] ] ] ] ] ].
assert((colls H # Iiter it H l) i).
exists i1; exists i2; intuition.
generalize(H2 H l H1); clear H2; intros H2.
destruct H2; inversion H2.
intros.
destruct H1 as [ i1 [ i2 [ I1 [ I2 [ xs' [ I3 I4 ] ] ] ] ] ].
assert((colls H # Iiter it H xs') i).
exists i1; exists i2; intuition.
generalize(H2 H xs' H1); rename H2 into N5; intros H2.
destruct H2 as [ H3 H4 ].
exists empty.
split.
unfold case_sum_pre.
exists j1; exists empty.
intuition.
remove_empty; apply splits_refl.
unfold opt2sum in H2.
case_eq x; intros.
rewrite H5 in H2; inversion H2.
clear H2.
exists H; exists H0; exists xs'.
intuition.
inversion H3.
rewrite H5 in H6.
assumption.
unfold opt2sum in H2.
case_eq x; intros.
rewrite H5 in H2; inversion H2.
rewrite H7 in *; clear H7 H2 n.
exists H; exists H0; exists xs'.
intuition.
inversion H3.
rewrite H5 in H6; assumption.
rewrite H5 in H2; inversion H2.
intros.
unfold case_sum_post in H2.
destruct H2 as [ l1 [ l2 [ L1 [ l3 [ l4 [ L2 [ L3 L4 ] ] ] ] ] ] ].
destruct L4 as [ L5 L6 ]; unfold this in L5, L6.
rewrite <- L5 in *; rewrite <- L6 in *; clear L5 L6 l2 l4.
splits_rewrite.
destruct L3 as [ L7 L8 ].
destruct H5 as [ j1 [ j2 [ J1 [ J2 [ xs'' [ J3 J4 ] ] ] ] ] ].
assert((colls S # Iiter it S xs'') i).
exists j1; exists j2; intuition.
destruct(N5 S xs'' H2) as [ H5 H6 ].
unfold opt2sum in L7, L8.
case_eq x; intros.
rewrite H7 in L8.
clear L7.
assert(inr unit n = inr unit n); trivial.
generalize(L8 n H8); clear L8; intros L8.
assert(xs = filter p xs'' /\ (colls S # Iiter it S (tail xs'')) l1 /\
       Some n = opt_hd xs'' /\ Some n = Some n).
intuition.
inversion H5.
rewrite H7 in H10; assumption.
generalize(L8 S xs xs'' H9); clear L8; intros L8.
intuition.
rewrite H7 in L7.
clear L8.
assert(inl nat tt = inl nat tt); trivial.
generalize(L7 tt H8); clear L7; intros L7.
clear H8.
assert(xs = filter p xs'' /\ (colls S # Iiter it S (tail xs'')) l1 /\
       None = opt_hd xs'' /\ None (A := nat) = None).
intuition.
inversion H5.
rewrite H7 in H9; assumption.
generalize(L7 S xs xs'' H8); clear H8; intros H8.
intuition.
Defined.

(* Put the next computation together a take its fixpoint. *)
Program Definition next' (next : next_type) (it : Ai)  :
  STsep 
    (fun i => exists S, exists xs, (colls S # Iiter it S xs) i)
    (option nat)
    (fun y i m => forall S xs, (colls S # Iiter it S xs) i ->
      (y = Val (opt_hd xs) /\ (colls S # Iiter it S (tail xs)) m)) :=
    match it with 
    | Coll r => next_coll next r 
    | Filter p it => next_filter next p it 
    end.

Definition next := sfix next'.