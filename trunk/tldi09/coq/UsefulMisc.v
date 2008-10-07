(* This file is meant to be a dumping ground for stuff that
   should be in the standard library.
   i.e., it is not ynot specific.  So this file should not include
   ynot header files (that way we can reuse it later)
   We can create another file for ynot-specific miscellaneous stuff *)

Require Import List.
Require Import Omega.
Require Import Plus.
Require Import ETactics.
Require Import Coq.Arith.Compare.
Require Import Bool.

Set Implicit Arguments.
Unset Strict Implicit.

Section NatFacts.

(* less-than on naturals -- from arith/Compare library *)
Definition nat_cmp (n: nat) (m: nat) : {m > n} + {n = m} + {n > m} := 
  gt_eq_gt_dec n m.


Definition nat_eq (n : nat) (m : nat) : {n=m} + {n<>m}.
 intros. destruct (nat_cmp n m).
 destruct s. right. omega.
 left. auto. right. omega.
Defined.

Lemma le_witness (n:nat) (m:nat) : n <= m -> exists d:nat, n+d = m.
Proof.
  intros. induction H.
  exists 0. omega.
  destruct IHle. exists (S x). omega.
Qed.

Lemma lt_witness (n:nat) (m:nat) : n < m -> exists d:nat, d <> 0 /\ n+d = m.
Proof.
  intros. assert (n <= m). omega.
  destruct (le_witness H0).
  exists x. split. 
  omega.
  trivial.
Qed.

End NatFacts.

Implicit Arguments le_witness [n m].
Implicit Arguments lt_witness [n m].

Section ListFacts.

Section Length.

Variable A : Type.

Lemma length_nil (l:list A) : length l = 0 -> l = nil.
Proof.
  induction l; simpl; intros.
  trivial.
  discriminate.
Qed.

End Length.

Section Fold.
Variable A : Type.

Lemma fold_right_rev_left : forall (B:Type)(f:B->A->B) l i,
    fold_left f (rev l) i = fold_right (fun x y => f y x) i l.
  Proof.
    intros.
    poses (fold_left_rev_right (fun x y => f y x) (rev l) i).
    rewrite (rev_involutive l) in HU. rewrite HU.
    auto.
Qed.

Lemma fold_right_length :
  forall (l:list A), fold_right (fun _ x => S x) 0 l = length l.
Proof.
  intros. poses (fold_left_rev_right (fun _ x => S x) (rev l) 0).
  rewrite (rev_involutive l) in HU. rewrite HU. rewrite <- (rev_length l).
  apply fold_left_length.
Qed.

End Fold.

Section Nth.
Variable A : Type.

Lemma nth_nth_default (n:nat) (l:list A) (default:A) : nth n l default = nth_default default l n.
Proof.
  intros n l. generalize n. unfold nth_default. 
  induction l; induction n0; simpl; intros; trivial.
Qed.

Lemma last_nth (l:list A) (default:A): last l default = nth (length l - 1) l default.
Proof.
  induction l; intros. 
  simpl. trivial.
  replace (length (a :: l)) with (S (length (l))) by auto.
  replace (S (length l) - 1) with (length l) by omega.
  induction l.
  simpl. trivial.
  replace (last (a :: a0 :: l) default) with (last (a0 :: l) default) by auto.
  replace (nth (length (a0 :: l)) (a :: a0 :: l) default)
    with (nth (length (a0 :: l) - 1) (a0 :: l) default).
  apply IHl.
  simpl.  replace (length l - 0) with (length l) by omega.
  trivial.
Qed.

Lemma hd_nth (l:list A) (default:A): hd default l = nth 0 l default.
Proof.
  induction l; intros; simpl* .
Qed.

End Nth.

Section Bool.
Variable A : Type.

Lemma incl_nil : forall (l:list A), incl l nil -> l = nil.
Proof.
  intros l H. induction l.
    trivial.
    poses (H a).
    simpl in HU.
    assert False. apply HU. left. trivial. contradiction.
Qed.

Variable f : A -> bool.

Lemma existsb_incl (l1:list A) (l2:list A) : incl l1 l2 -> existsb f l1 = true -> existsb f l2 = true.
Proof.
  intros. rewrite existsb_exists in H0.
  destruct H0. destruct H0.
  rewrite existsb_exists. exists x.
  auto.
Qed.

Lemma forallb_incl (l1:list A) (l2:list A) : incl l1 l2 -> forallb f l2 = true -> forallb f l1 = true.
Proof.
  intros. rewrite forallb_forall in H0.
  rewrite forallb_forall. intros.
  auto.
Qed.

End Bool.

Section Drop.
Variable A : Type.

(* this should probably be in the standard library *)
(* arg! it is called skipn (and subtly different definition) 
   this happens all of the time. 
   however, amusingly, the proofs did not transparently carry over,
   so it is staying for now, with an equivalence proof
*)
 Fixpoint drop (n:nat) (l:list A) {struct n} : list A := 
   match n with 
     | 0 => l 
     | S m => drop m (tail l) 
  end.

Lemma drop_nil (m:nat) : drop m nil = nil.
Proof.
  intros. induction m; simpl* .
Qed.

Lemma skipn_drop (n:nat) (l:list A) : drop n l = skipn n l. 
Proof.
  intros n l. generalize n. 
  induction l; induction n0; simpl* .
  use drop_nil.
Qed.

Lemma drop_tail (l:list A) : drop 1 l = tail l.
Proof.
  intros. simpl* .
Qed.

Lemma drop_drop (m:nat) (n:nat) (l:list A) : drop m (drop n l) = drop (m+n) l.
Proof.
  assert (forall n a l, tail (drop n (a::l)) = drop n l).
  induction n. intros. simpl. trivial.
  intros. simpl. induction l. simpl. 
  rewrite (drop_nil n). simpl. trivial.
  simpl. apply* IHn.
  induction m. intros; simpl* .
  intros.
  generalize n. induction l. intros.
  do 3 rewrite -> drop_nil. trivial.
  intros.  simpl.
  rewrite <- (IHm n0 l). 
  rewrite -> H. trivial.
Qed.
  
Lemma drop_cons (n:nat) (a:A) (l:list A) : drop (S n) (a::l) = drop n l.
Proof.
  intros.
  replace (S n) with (n + 1) by omega.
  rewrite <- (drop_drop n 1 (a::l)). 
  simpl. trivial.
Qed.

Lemma drop_length_nil (l:list A) : drop (length l) l = nil.
Proof.
  induction l; simpl* .
Qed.

Lemma drop_large_nil (n:nat) (l:list A) : length l <= n -> drop n l = nil.
Proof.
  intros.
  destruct (le_witness H). rewrite (plus_comm (length l) x) in H0. rewrite <- H0.
  rewrite <- (drop_drop x (length l)). rewrite (drop_length_nil l). apply* drop_nil.
Qed.

Lemma drop_nil_large (n:nat) (l:list A) : drop n l = nil -> (length l) <= n.
Proof.
  induction n. intros. simpl in H. subst. simpl. trivial. 
  induction l; simpl; intros.
  omega.
  poses (IHn l H). omega.
Qed.

(* note that if n > length l this still works out, since - is truncated subtraction *)
Lemma drop_length (n:nat) (l:list A) : length (drop n l) = length l - n.
Proof.
  induction n; intros; simpl. omega.
  rewrite (IHn (tail l)).
  induction l; simpl. trivial.
  omega.
Qed.

(* some lemmas about the interactions of drop and other list functions in the standard library *)

Lemma drop_incl (n:nat) (l:list A) : incl (drop n l) l.
Proof.
  unfold incl. intros n l. generalize n. induction l; simpl; intros.
  rewrite (drop_nil n0) in H. simpl in H. trivial.
  induction n0. simpl in H. trivial.
  simpl in H. right. apply* IHl.
Qed.

Lemma nth_drop (n:nat) (m:nat) (l:list A) (default:A) : nth m (drop n l) default = nth (m+n) l default.
Proof.
  intros n m l. generalize n m. induction l; intros.
  rewrite (drop_nil n0). simpl. induction m0; induction n0; simpl* .
  induction n0; induction m0. 
  simpl. trivial.
  simpl. replace l with (drop 0 l) by auto. apply* IHl.
  simpl. replace n0 with (0 + n0) by auto. apply* IHl.
  simpl. replace (m0 + S n0) with (S m0 + n0) by omega.
  apply* IHl.
Qed.

Lemma nth_ok_drop (n:nat) (m:nat) (l:list A) (default:A) : nth_ok m (drop n l) default = nth_ok (m+n) l default.
  intros n m l. generalize n m. induction l; intros.
  rewrite (drop_nil n0). simpl. induction m0; induction n0; simpl* .
  induction n0; induction m0. 
  simpl. trivial.
  simpl. replace l with (drop 0 l) by auto. apply* IHl.
  simpl. replace n0 with (0 + n0) by auto. apply* IHl.
  simpl. replace (m0 + S n0) with (S m0 + n0) by omega.
  apply* IHl.
Qed.

Lemma nth_error_drop (n:nat) (m:nat) (l:list A)  : nth_error (drop n l) m = nth_error l (m+n).
  intros n m l. generalize n m. induction l; intros.
  rewrite (drop_nil n0). simpl. induction m0; induction n0; simpl* .
  induction n0; induction m0. 
  simpl. trivial.
  simpl. replace l with (drop 0 l) by auto. apply* IHl.
  replace (drop (S n0) (a :: l)) with (drop n0 l) by auto.
  replace (nth_error (a :: l) (0 + S n0)) with (nth_error l (0 + n0)) by auto.
  apply* IHl.
  replace (drop (S n0) (a :: l)) with (drop n0 l) by auto.
  replace (nth_error (a :: l) (S m0 + S n0)) with (nth_error l (m0 + S n0)) by auto.
  replace (m0 + S n0) with (S m0 + n0) by omega. apply* IHl.
Qed.

Lemma nth_default_drop (n:nat) (m:nat) (l:list A) (default:A) : nth_default default (drop n l) m = nth_default default l (m+n).
Proof.
  intros. unfold nth_default. rewrite* nth_error_drop.
Qed.

Lemma last_drop (l:list A) (default:A): last l default = hd default (drop (length l - 1) l).
Proof.
  intros. rewrite* last_nth. rewrite -> hd_nth.
  use (nth_drop (length l - 1) 0 l default).
Qed.

Lemma existsb_drop (n:nat) (l:list A) (f:A->bool) : existsb f (drop n l) = true -> existsb f l = true.
Proof.
  intros. use2 existsb_incl drop_incl.
Qed.

Lemma forallb_drop (n:nat) (l:list A) (f:A->bool) : forallb f l = true -> forallb f (drop n l) = true.
  intros. use2 forallb_incl drop_incl.
Qed.

End Drop.

Section DropMap.

Variables A B : Type.
  
Lemma map_drop (n:nat) (l:list A) (f:A->B) : map f (drop n l) = drop n (map f l).
Proof.
  intros. generalize n. induction l; simpl; intros.
  rewrite (drop_nil A n0). rewrite (drop_nil B n0). simpl. trivial.
  induction n0; simpl* .
Qed.

End DropMap.

Section DropPair.

Variables A B : Type.

Lemma split_drop (n:nat) (l:list (A * B)) : let (x,y) := (split l) in (drop n x, drop n y) = split (drop n l).
Proof.
  intros n l. generalize n. induction l; simpl; intros.
  try progress repeat (rewrite -> drop_nil); trivial.
  destruct a. induction n0; simpl; destruct (split l).
  trivial.
  use drop_tail.
Qed.

Lemma combine_drop (n:nat) (l1:list A) (l2:list B) : drop n (combine l1 l2) = combine (drop n l1) (drop n l2).
Proof.
  intros n l1. generalize n. induction l1; destruct l2; simpl; 
  try progress repeat (rewrite -> drop_nil); trivial.
  assert (combine (drop n0 (a :: l1)) nil (B:=B) = nil).
  poses (combine_length (drop n0 (a :: l1)) nil (B:=B)). simpl in HU.
  replace (min (length (drop n0 (a :: l1))) 0) with 0 in HU by auto with arith.
  use length_nil. symmetry. trivial.
  induction n0; simpl* .
Qed.

End DropPair.

Section DropListMisc.

Variable A : Type.

Lemma lel_drop (n:nat) (l1: list A) (l2: list A) : lel l1 l2 -> lel (drop n l1) (drop n l2).
Proof.
  intros. unfold lel in * .
  rewrite -> drop_length. rewrite -> drop_length. omega.
Qed.

Lemma NoDup_drop (n:nat) (l: list A) : NoDup l -> NoDup (drop n l).
Proof.
  intros n l. generalize n. clear n. induction l.
  intros. rewrite -> drop_nil. trivial.
  induction n; simpl; intros. trivial.
  inversions H. 
  apply* IHl.
Qed.

End DropListMisc.

Lemma seq_drop (n:nat) (start:nat) (len:nat) : drop n (seq start len) = seq (start + n) (len - n).
Proof.
  induction n. intros. simpl.
  replace (start + 0) with start by omega.
  replace (len - 0) with len by omega. trivial.
  intros. simpl. induction len; simpl.
  use drop_nil.
  replace (start + S n) with (S start + n) by omega.
  apply* IHn.
Qed.

End ListFacts.

Implicit Arguments fold_right_rev_left [A B].
Implicit Arguments fold_right_length [A].
Implicit Arguments nth_nth_default [A].
Implicit Arguments last_nth [A].
Implicit Arguments hd_nth [A].

Implicit Arguments incl_nil [A].
Implicit Arguments existsb_incl [A l1 l2].
Implicit Arguments forallb_incl [A l1 l2].

Implicit Arguments drop [A].
Implicit Arguments drop_nil [A].
Implicit Arguments skipn_drop [A].
Implicit Arguments drop_tail [A].
Implicit Arguments drop_drop [A].
Implicit Arguments drop_cons [A].
Implicit Arguments drop_length_nil [A].
Implicit Arguments drop_large_nil [A n l].
Implicit Arguments drop_nil_large [A n l].
Implicit Arguments drop_length [A].
Implicit Arguments drop_incl [A].
Implicit Arguments nth_drop [A].
Implicit Arguments nth_ok_drop [A].
Implicit Arguments nth_error_drop [A].
Implicit Arguments nth_default_drop [A].
Implicit Arguments last_drop [A].
Implicit Arguments existsb_drop [A n l f].
Implicit Arguments forallb_drop [A n l f].
Implicit Arguments split_drop [A B].
Implicit Arguments combine_drop [A B].

Implicit Arguments lel_drop [A n l1 l2].
Implicit Arguments NoDup_drop [A l].

Section Logic.

Definition xor (A:Prop) (B:Prop) := (A \/ B) /\ ~(A /\ B).

Lemma xor_irref : forall (A:Prop), ~ xor A A.
Proof.
  intros. unfold xor. intuition.
Qed.

Lemma xor_sym : forall (A:Prop) (B:Prop), xor A B -> xor B A.
Proof.
  unfold xor. intros. intuition.
Qed.

Implicit Arguments xor_sym [A B].

Lemma xor_iff : forall (A:Prop) (B:Prop), xor A B -> (A <-> B) -> False.
Proof.
  unfold xor, iff. intros. destruct H. destruct H0.
  apply* H1.
Qed.

Implicit Arguments xor_iff [A B].

End Logic.