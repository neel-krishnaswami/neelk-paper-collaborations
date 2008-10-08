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

Set Implicit Arguments.
Unset Strict Implicit.

Open Local Scope stsep_scope.
Open Local Scope hprop_scope.

(* We need to use our own list type because the tail is a location (see page 2
in the paper).
Since we only use it with type nat, it is hardcoded here to reduce clutter,
but it would be very easy to generalize. *)
Inductive Seq : Set :=
    | Nil  : Seq
    | Cons : nat -> loc -> Seq.

(* Collection *)
Definition Ac := loc%type.

(* Iterator *)
Inductive Ai : Type :=
    | Coll   : loc -> Ai
    | Filter : (nat -> bool) -> Ai -> Ai
(*    | Map2   : (nat * nat -> nat) -> Ai -> Ai -> Ai. *)

Definition iterT := (Ac * list nat * hprop)%type.

Inductive Seq_pred (c : Ac) (xs : list nat) (h : heap) : Prop :=
    | Seq_nil  : xs = nil /\ (c --> Nil) h -> Seq_pred c xs h
    | Seq_cons : (exists x, exists xs', exists c', 
	xs = x::xs' /\ ((c --> Cons x c') # Seq_pred c' xs') h) -> Seq_pred c xs h.

Inductive Seq_pred_exact (c : Ac) (xs : list nat) (ls : list loc) (h : heap) : Prop :=
    | Seq_exact_nil  : xs = nil /\ ls = nil /\ (c --> Nil) h -> Seq_pred_exact c xs ls h
    | Seq_exact_cons : (exists x, exists xs', exists l, exists ls', 
         xs = x::xs' /\ ls = l::ls' /\ ((c --> Cons x l) # Seq_pred_exact l xs' ls') h) ->
           Seq_pred_exact c xs ls h.

Definition exact (P : hprop) :=
  forall h1 h2 : heap, P h1 -> P h2 -> h1 = h2.

Definition exact_pred (h : heap) := (fun h' : heap => h = h').

Lemma exact_pred_exact : forall h : heap,
  exact (exact_pred h).
unfold exact.
intros.
unfold exact_pred in H, H0.
rewrite <- H.
rewrite <- H0.
trivial.
Qed.

Lemma Seq_pred_lemma : forall (c : Ac) (xs : list nat) (ls : list loc) (h : heap),
  Seq_pred_exact c xs ls h -> Seq_pred c xs h.
intros.
generalize dependent xs.
generalize dependent h.
generalize dependent c.
induction ls.
intros.
inversion H.
destruct H0 as [ H1 [ H2 H3 ] ].
rewrite H1.
apply Seq_nil.
split; trivial.
destruct H0 as [ x [ xs' [ l [ ls' [ H1 [ H2 H3 ] ] ] ] ] ].
inversion H2.
intros.
destruct H.
destruct H as [ H1 [ H2 H3 ] ].
inversion H2.
destruct H as [ x [ xs' [ l [ ls' [ H1 [ H2 H3 ] ] ] ] ] ].
rewrite_clear.
clear H0 a.
destruct H3 as [ h1 [ h2 [ H4 [ H5 H6 ] ] ] ].
apply Seq_cons.
exists x.
exists xs'.
exists l.
split; trivial.
exists h1.
exists h2.
repeat(split; try assumption).
apply IHls.
assumption.
Qed.

Lemma Seq_pred_exact_extend : 
  forall (c : Ac) (x : nat) (xs : list nat) (l : loc) (ls : list loc) (h h1 h2 : heap),
    splits h (h1::h2::nil) -> Seq_pred_exact c xs ls h1 -> (l --> Cons x c) h2 -> 
      Seq_pred_exact l (x::xs) (c::ls) h.
intros.
apply Seq_exact_cons.
exists x; exists xs; exists c; exists ls.
repeat(split; try trivial).
exists h2.
exists h1.
split.
splits_prove.
split; assumption.
Qed.

Lemma Seq_pred_exact_is_exact : forall (c : Ac) (xs : list nat) (ls : list loc),
  exact (Seq_pred_exact c xs ls).
intros.
unfold exact.
intros.
generalize dependent c.
generalize dependent xs.
generalize dependent h1.
generalize dependent h2.
induction ls.
intros.
destruct H.
destruct H as [ H1 [ H2 H3 ] ].
destruct H0.
destruct H as [ H4 [ H5 H6 ] ].
unfold points_to in H3, H6.
rewrite H3.
rewrite H6.
trivial.
destruct H as [ x [ xs' [ l [ H4 [ H5 H6 ] ] ] ] ].
rewrite H1 in H5.
inversion H5.
destruct H as [ x [ xs' [ l [ H1 [ H2 H3 ] ] ] ] ].
destruct H3 as [ H4 [ H5 H6 ] ].
inversion H4.
intros.
destruct H0.
destruct H0 as [ H1 [ H2 H3 ] ].
inversion H2.
destruct H0 as [ x [ xs' [ l [ ls' [ H1 [ H2 H3 ] ] ] ] ] ].
destruct H.
destruct H as [ H4 [ H5 H6 ] ].
inversion H5.
destruct H as [ x' [ xs'' [ l' [ ls'' [ H4 [ H5 H6 ] ] ] ] ] ].
rewrite_clear.
destruct H6 as [ h3 [ h4 [ H7 [ H8 H9 ] ] ] ].
destruct H3 as [ h5 [ h6 [ H10 [ H11 H12 ] ] ] ].
assert(h4 = h6).
eapply IHls; eauto.
assert(h3 = h5).
unfold points_to in H8, H11.
rewrite H8; rewrite H11.
trivial.
rewrite_clear.
destruct H10; destruct H7.
rewrite H; rewrite H0.
trivial.
Qed.

Definition Icoll (c : Ac) (xs : list nat) (P : hprop) (h : heap) := 
    Seq_pred c xs h /\ P h /\ exact P.

Fixpoint Isegment (c c' : loc) (l : list nat) : hprop :=
    fun h => match l with
	| nil   => c = c' /\ emp h
	| x::xs => exists c'', ((c --> Cons x c'') # (Isegment c'' c' xs)) h
    end.

(* Move that stuff in utilities .v file *)

Definition opt_hd (l : list nat) : option nat :=
    match l with
	| nil => None
	| x::_ => Some x
    end.

Fixpoint filter (P : nat -> bool) (l : list nat) : list nat :=
    match l with
	| nil  => nil
	| h::t => if P h then h :: (filter P t) else filter P t
    end.

Fixpoint zip (l1 l2 : list nat) {struct l1} : list (nat * nat) :=
    match l1 with
	| h1::t1 => match l2 with
	    | h2::t2 => (h1,h2)::(zip t1 t2)
	    | nil    => (* your bad *) nil
	end
	| nil => nil
    end.

Lemma zip_right_nil : forall (l : list nat),
  zip l nil = nil.
intros.
induction l; trivial.
Qed.

Fixpoint disjoint_lists (A : Type) (l1 l2 : list A) {struct l1} : Prop :=
    match l1 with
	| nil      => True
	| h1 :: t1 => ~ (In h1 l2) /\ disjoint_lists t1 l2
    end.

Fixpoint Iiter (it : Ai) (S : list iterT) (xs : list nat) {struct it} : hprop :=
    fun h => match it with
	| Coll l => match S with
	    | (c,zs,P) :: nil => exists c', exists ys,
				 zs = ys ++ xs /\
				 ((l --> c') #
				    ((Icoll c zs P) --# 
					(Icoll c zs P /#\ 
					    (Isegment c c' ys # Seq_pred c' xs)))) h
	    | _               => (* This case should never happen but coq will
				    be upset if we're not exhaustive, so let's
				    make him happy with a dummy term of the
				    right type. *) False
	end
	| Filter p i => exists xs', xs = filter p xs' /\ Iiter i S xs' h
	| Map2 f i1 i2 => exists xs1, exists xs2, exists S1, exists S2,
	    xs = map f (zip xs1 xs2) /\ disjoint_lists S1 S2 /\ S = S1 ++ S2 /\
	    ((Iiter i1 S1 xs1) # (Iiter i2 S2 xs2)) h
    end.

Ltac splits_full_nopre := 
    match goal with
	| |- (star1 _ _) ?h =>
	    exists h; exists empty; split; 
	    [ remove_empty; apply splits_refl | split; [assumption | auto ] ]
	| _ => idtac "This is not a split goal"; fail
    end.

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


Lemma Seq_pred_lemma' : forall (c : loc) (xs xs' : list nat) (h : heap),
  Seq_pred c xs h -> Seq_pred c xs' h -> xs = xs'.
intros c xs.
generalize c.
induction xs.
intros.
destruct H as [ H | H ].
destruct H.
destruct H0.
destruct H0.
rewrite H0.
trivial.
destruct H0 as [ x [ xs'' [ c' [ H2 H3 ] ] ] ].
destruct H3 as [ x' [ xs''' [ c'' [ H4 H5 ] ] ] ].
unfold points_to in H1, H4.
destruct c''.
rewrite H1 in H0.
assert(update_loc empty c0 Nil c0 = union (x' :: xs''' :: nil) x0 c0).
rewrite H0; trivial.
unfold union in H3.
unfold union_heap_list in H3.
unfold union2 in H3.
rewrite H4 in H3.
unfold update_loc in H3.
unfold lookup_loc in H3.
unfold modify_loc in H3.
destruct(loc_eq c0 c0).
assert(Nil = Cons x c').
apply Some_dyn_inj.
assumption.
inversion H6.
contradiction n; trivial.
destruct H as [ x [ xs'' [ c' [ H1 H2 ] ] ] ].
inversion H1.
intros.
destruct H.
destruct H.
inversion H.
destruct H as [ x [ xs'' [ c' [ H1 H2 ] ] ] ].
destruct H2 as [ h1 [ h2 [ H3 [ H4 H5 ] ] ] ].
destruct H0.
destruct H.
unfold points_to in H0, H4.
destruct H3.
rewrite H0 in H2.
assert(update_loc empty c0 Nil c0 = union (h1 :: h2 :: nil) x0 c0).
rewrite H2; trivial.
unfold union in H3.
unfold union_heap_list in H3.
unfold union2 in H3.
rewrite H4 in H3.
unfold update_loc in H3.
unfold lookup_loc in H3.
unfold modify_loc in H3.
destruct(loc_eq c0 c0).
assert(Nil = Cons x c').
apply Some_dyn_inj; assumption.
inversion H6.
contradiction n; trivial.
destruct H as [ x' [ xs''' [ c'' [ H6 H7 ] ] ] ].
destruct H7 as [ h3 [ h4 [ H8 [ H9 H10 ] ] ] ].
same_two_subheaps H3 H4 H11.
inversion H9.
rewrite H1.
rewrite H6.
rewrite H0.
rewrite <- H2 in H10.
rewrite H11 in H5.
inversion H1.
rewrite <- H12 in H5.
generalize(IHxs c' xs''' h4 H5 H10).
intros.
rewrite <- H12.
rewrite H.
trivial.
Qed.

Lemma splits_lemma : forall (h h1 h2 : heap) (l : loc) (s1 s2 : Seq),
  splits h (h1::h2::nil) -> (l --> s1) h1 -> (l --> s2) h ->
    s1 = s2.
intros.
unfold points_to in H0, H1.
destruct H.
rewrite H1 in H.
assert(update_loc empty l s2 l = union (h1 :: h2 :: nil) x l).
rewrite H; trivial.
unfold union in H2.
unfold union_heap_list in H2.
unfold union2 in H2.
rewrite H0 in H2.
unfold lookup_loc in H2.
unfold update_loc in H2.
unfold modify_loc in H2.
destruct(loc_eq l l).
apply Some_dyn_inj.
symmetry; assumption.
contradiction n; trivial.
Qed.

Lemma useful_disjoint_lemma : forall (A : Type) (h1 h2 h3 : heap) (l : loc) (v : A),
  (l --> v) h2 -> disjoint(h1::h2::h3::nil) -> (not(valid_loc l h1) /\ not(valid_loc l h3)).
intros.
split.
unfold not.
intros.
unfold disjoint in H0.
destruct H0 as [ _ H0 ].
unfold disjoint_heap_list in H0.
destruct H0 as [ H0 _ ].
unfold disjoint2 in H0.
generalize(H0 l H1); intros H2.
unfold points_to in H.
rewrite H in H2.
unfold unused_loc in H2.
unfold update_loc in H2.
unfold lookup_loc in H2.
unfold modify_loc in H2.
destruct(loc_eq l l).
inversion H2.
contradiction n; trivial.
unfold not.
intros.
destruct H0 as [ H0 [ H2 H3 ] ].
destruct H0 as [ _ H0 ].
unfold disjoint_heap_list in H0.
destruct H0 as [ H0 _ ].
assert(disjoint2 h3 h2).
apply disjoint2_commute.
assumption.
unfold disjoint2 in H4.
generalize(H4 l H1); intros H5.
unfold points_to in H.
rewrite H in H5.
unfold update_loc in H5.
unfold modify_loc in H5.
unfold unused_loc in H5.
unfold lookup_loc in H5.
destruct(loc_eq l l).
inversion H5.
contradiction n; trivial.
Qed. 


Ltac splits_auto :=
  match goal with
  | H : splits ?h1 (?h2::empty::nil) |- _ =>
          let tmp := fresh "tmp" in
          remove_empty_in H; clear H; intros H;  
          destruct H as [ tmp H ]; simpl in H; clear tmp;
          ((rewrite H in *; clear H h1) || (rewrite <- H in *; clear H h2))
  end.


Fixpoint colls (S : list iterT) : hprop :=
    match S with
	| nil => emp
	| (c,xs',n) :: xs => (Icoll c xs' n) # colls xs
    end.

Lemma colls_lemma : forall (S S1 S2 : list iterT) (h : heap),
  S = S1 ++ S2 -> colls S h ->
    (exists h1, exists h2, splits h (h1::h2::nil) /\ colls S1 h1 /\ colls S2 h2).
intros.
generalize h S2 S H H0.
elim S1.
clear h H H0 S2 S.
intros.
simpl in H.
exists empty; exists h.
simpl colls.
rewrite H in H0.
intuition.
remove_empty; apply splits_refl.
clear h H H0 S2 S.
intros.
simpl in H0.
rewrite H0 in H1.
case_eq a; intros; rewrite_clear.
case_eq p; intros; rewrite_clear.
simpl in H1.
destruct H1 as [ h1 [ h2 [ H5 [ H6 H7 ] ] ] ].
assert(l ++ S2 = l ++ S2); trivial.
generalize(H h2 S2 (l ++ S2) H1 H7); clear H; intros H.
destruct H as [ h3 [ h4 [ H8 [ H9 H10 ] ] ] ].
clear H1.
splits_rewrite_in H8 H5; clear H8 H5.
splits_join_in H (1::1::0::nil).
exists (union (h1::h3::nil) pf0); exists h4; intuition.
unfold colls; fold colls.
exists h1; exists h3; intuition.
exists pf0; trivial.
Qed.

Lemma colls_lemma2 : 
  forall (h h1 h2 : heap) (S1 S2 : list iterT),
    splits h (h1::h2::nil) -> colls S1 h1 -> colls S2 h2 ->
      colls (S1 ++ S2) h.
intros.
generalize S2 h h1 h2 H H0 H1.
elim S1.
clear S2 h h1 h2 H H0 H1.
intros.
simpl app.
simpl colls in H0.
splits_rewrite.
assumption.
intros.
simpl app.
case_eq a; intros; rewrite_clear.
case_eq p; intros; rewrite_clear.
unfold colls in H4; fold colls in H4.
destruct H4 as [ h6 [ h7 [ H6 [ H7 H8 ] ] ] ].
splits_rewrite_in H6 H3; clear H3 H6.
splits_join_in H4 (0::1::1::nil).
assert(splits (union (h7::h4::nil) pf0) (h7::h4::nil)).
exists pf0; trivial.
generalize(H2 S0 (union (h7::h4::nil) pf0) h7 h4 H6 H8 H5); intros H10.
unfold colls; fold colls.
exists h6; exists (union (h7::h4::nil) pf0).
intuition.
apply splits_commute; assumption.
Qed.
  
Definition seqopt (l : Seq) : option (nat * loc) :=
  match l with
   | Nil => None
   | Cons x t => Some (x, t)
  end.

Lemma selects_points_to :
  forall (A : Type) (l : loc) (v1 v2 : A) (h hh : heap) (hs : list heap),
    selects l v1 h -> (l --> v2) hh -> splits h (hh::hs) -> v1 = v2.
intros.
destruct H1.
assert(H2 : union (hh::hs) x l = hh l).
  eapply union_valid_loc.
    apply A.
  eapply points_to_valid; eauto.
assert(H3 : h l = union (hh::hs) x l).
  rewrite H1; trivial.
rewrite H2 in H3.
unfold selects, points_to, update_loc, modify_loc in H, H0.
rewrite H in H3.
rewrite H0 in H3.
rewrite loc_eq_refl in H3.
apply Some_dyn_inj.
assumption.
Qed.

Lemma colls_Iiter_lemma : 
  forall (S : list iterT) (r : Ac) (xs : list nat) (h : heap),
    (colls S # Iiter (Coll r) S xs) h ->
    (exists l : loc, selects r l h /\ selects l Nil h) ->
    xs = nil.
intros.
destruct H0 as [ l [ H1 H2 ] ].
destruct H as [ h1 [ h2 [ H3 [ H4 H5 ] ] ] ].
case_eq S.
intros H.
  rewrite H in H5.
  unfold Iiter in H5; contra.
intros.
rewrite H in H4, H5. clear H.
unfold colls in H4.
unfold Iiter in H5.
case_eq i.
intros.
case_eq p.
intros.
rewrite_clear.
case_eq l0.
intros.
Focus 2.
intros.
rewrite H in H5.
contra.
rewrite H in H4, H5; clear H.
destruct H4 as [ h3 [ h4 [ H6 [ H7 H8 ] ] ] ].
splits_rewrite.
destruct H5 as [ c' [ ys [ H8 H9 ] ] ].
rewrite_clear.
destruct H9 as [ h5 [ h6 [ H10 [ H11 H12 ] ] ] ].
splits_rewrite_in H10 H3; clear H10 H3.
unfold wand in H12.
generalize(H12 h3 H7); clear H12 H7; intros H13.
splits_join_in H (1::0::1::nil).
assert(H14 : splits (union (h3::h6::nil) pf0) (h3::h6::nil)).
  exists pf0; trivial.
generalize(H13 (union (h3::h6::nil) pf0) H14); intros H15; clear H13 H14.
assert(l = c').
eapply selects_points_to.
apply H1.
apply H11.
instantiate (1 := (h3::h6::nil)).
splits_prove.
rewrite_clear.
clear H1.
destruct H15 as [ H16 H17 ].
destruct H17 as [ h7 [ h8 [ H18 [ H19 H20 ] ] ] ].
destruct H20 as [ H20 | H20 ].
destruct H20; assumption.
destruct H20 as [ x [ xs' [ c'0 [ H21 H22 ] ] ] ].
splits_rewrite_in H18 H0.
destruct H22 as [ h9 [ h10 [ H23 [ H24 H25 ] ] ] ].
splits_rewrite_in H23 H1.
assert(Nil = Cons x c'0).
  eapply selects_points_to.
  apply H2.
  apply H24.
  instantiate (1 := (h7::h10::h5::nil)).
  apply (splits_permute H3).
  PermutProve.
inversion H4.
Qed.

Lemma useful_lists_lemma : forall (A : Type) (l1 l2 : list A) (x : A),
  l1 ++ x :: l2 = (l1 ++ x :: nil) ++ l2.
intros.
induction l1.
simpl.
trivial.
rewrite <- app_comm_cons.
rewrite IHl1.
simpl.
trivial.
Qed.

Lemma Isegment_lemma : forall (h h1 h2 : heap) (l1 l2 l3 : loc) (x : nat) (xs : list nat),
  splits h (h1::h2::nil) -> Isegment l1 l2 xs h1 -> (l2 --> Cons x l3) h2 ->
    Isegment l1 l3 (xs ++ (x::nil)) h.
intros.
generalize dependent l1.
generalize dependent h.
generalize dependent h1.
generalize dependent h2.
induction xs.
simpl app.
unfold Isegment.
intros.
destruct H0.
splits_rewrite.
rewrite_clear.
exists l3.
exists h2; exists empty.
split.
remove_empty; apply splits_refl.
split.
assumption.
split; auto.
intros.
rewrite <- app_comm_cons.
unfold Isegment.
fold Isegment.
unfold Isegment in H0.
fold Isegment in H0.
destruct H0 as [ c [ h3 [ h4 [ H2 [ H3 H4 ] ] ] ] ].
splits_rewrite_in H2 H.
exists c.
exists h3.
assert(disjoint (h4::h2::nil)).
disjoint_prove.
exists (union (h4::h2::nil) H5).
split.
splits_flatten.
assumption.
split.
assumption.
eapply IHxs.
apply H1.
instantiate (1 := h4).
exists H5; trivial.
assumption.
Qed.

Lemma selects_points_to_lemma :
  forall (A : Type) (l : loc) (v : A) (h hh : heap) (hs : list heap),
    (l --> v) hh -> splits h (hh::hs) -> selects l v h.
intros.
destruct H0.
assert(h l = hh l).
  rewrite H0.
  eapply union_valid_loc.
  apply A.
  eapply points_to_valid; eauto.
unfold selects.
rewrite H1.
unfold points_to in H.
rewrite H.
unfold update_loc, modify_loc.
rewrite loc_eq_refl.
trivial.
Qed.

Lemma Isegment_lemma'' : forall (h h1 h2 : heap) (l1 l2 : loc) (xs : list nat),
  splits h (h1::h2::nil) -> Isegment l1 l2 xs h1 -> (l2 --> Nil) h2 ->
    Seq_pred l1 xs h.
intros.
generalize dependent l1.
generalize dependent h.
generalize dependent h1.
induction xs.
intros.
inversion H0.
splits_rewrite.
rewrite_clear.
apply Seq_nil.
split; trivial.
intros.
unfold Isegment in H0.
fold Isegment in H0.
destruct H0 as [ c [ h3 [ h4 [ H2 [ H3 H4 ] ] ] ] ].
apply Seq_cons.
exists a; exists xs; exists c.
split.
trivial.
splits_rewrite_in H2 H.
assert(disjoint (h4::h2::nil)).
disjoint_prove.
exists h3.
exists (union (h4::h2::nil) H5).
split.
splits_flatten; assumption.
split.
assumption.
eapply IHxs.
instantiate (1 := h4).
exists H5; trivial.
assumption.
Qed.

Lemma star_unit_right : forall (P : hprop) (h : heap),
  (P # emp) h <-> P h.
intros.
split.
intros.
destruct H as [ h1 [ h2 [ H1 [ H2 H3 ] ] ] ].
splits_rewrite.
assumption.
intros.
exists h; exists empty.
intuition.
remove_empty; apply splits_refl.
Qed.

Lemma unfold_colls_Icoll1 :
  forall (S : list iterT) (xs : list nat) 
         (r lst : loc) (cell : Seq) (i : heap),
    (colls S # Iiter (Coll r) S xs) i -> 
    (((r --> lst) # (lst --> cell)) # nopre) i ->
      (exists h1, exists h2, exists h3, exists h4, exists h5, 
       exists h6, exists a, exists ys, exists P,
         splits i (h1::h2::h3::nil) /\
         splits i (h4::h1::nil) /\ splits h4 (h5::h6::nil) /\
         (r --> lst) h1 /\ (lst --> cell) h2 /\
         Icoll a (ys ++ xs) P h4 /\
         Isegment a lst ys h5 /\
         S = (a, ys ++ xs, P)::nil /\
         Seq_pred lst xs h6).
intros.
destruct H as [ i1 [ i2 [ I3 [ I4 I5 ] ] ] ].
destruct H0 as [ i3 [ i4 [ I6 [ I7 I8 ] ] ] ].
destruct I7 as [ i5 [ i6 [ I9 [ I10 I11 ] ] ] ].
splits_rewrite_in I9 I6; clear I9 I6 I8.
case_eq S.
intros.
rewrite H0 in I5.
unfold Iiter in I5.
contra.
intros.
case_eq i0.
intros.
case_eq p.
intros.
case_eq l.
intros.
rewrite H1 in H0.
rewrite H2 in H0.
rewrite H3 in H0.
clear H1 H2 H3 p l i0.
rewrite H0 in I4, I5.
unfold colls, Iiter in I4, I5.
rewrite star_unit_right in I4.
destruct I5 as [ c [ ys [ I12 I13 ] ] ].
destruct I13 as [ i7 [ i8 [ I14 [ I15 I16 ] ] ] ].
splits_rewrite_in I14 I3; clear I14 I3.
assert(i7 = i5 /\ c = lst).
eapply points_to_same_subheap.
apply I15.
apply I10.
instantiate (1 := (i1::i8::nil)).
instantiate (1 := i).
splits_prove.
apply H.
rewrite_clear.
unfold wand in I16.
generalize(I16 i1 I4); clear I16; intros I16.
splits_join_in H1 (1::0::1::nil).
assert(splits (union(i1::i8::nil) pf0) (i1::i8::nil)).
exists pf0; trivial.
generalize(I16 (union (i1::i8::nil) pf0) H3); clear I16; intros I16.
destruct I16 as [ I17 I18 ].
assert(i1 = union (i1::i8::nil) pf0).
unfold Icoll in I4, I17.
destruct I4 as [ I19 [ I20 I21 ] ].
destruct I17 as [ I22 [ I23 I24 ] ].
eapply I24; eauto.
assert(i8 = empty).
assert(splits i1 (i1::i8::nil)).
exists pf0; assumption.
eapply splits_empty_right; eauto.
rewrite H5 in *.
rewrite <- H4 in *.
remove_empty_in H1; clear H1 H2 H3 pf0 H4 H5 I17; intros H1.
destruct I18 as [ i9 [ i10 [ I25 [ I26 I27 ] ] ] ].
exists i5; exists i6; exists i4; exists i1; exists i9; exists i10.
exists a; exists ys; exists h.
intuition.
intros.
rewrite_clear.
unfold Iiter in I5.
contra.
Qed.
 

Lemma colls_Iter_lemma : forall S xs r i,
  ((colls S) # (Iiter (Coll r) S xs)) i -> 
     (exists lst : loc, exists cell : Seq,
     (((r --> lst) # (lst --> cell)) # nopre) i).
intros.
destruct H as [ i1 [ i2 [ H1 [ H2 H3 ] ] ] ].
case_eq S.
intros.
rewrite H in *.
unfold Iiter in H3.
contra.
intros.
case_eq i0; intros; case_eq p; intros; case_eq l; intros; rewrite_clear.
Focus 2.
unfold Iiter in H3; contra.
unfold colls in H2.
unfold Iiter in H3.
destruct H3 as [ c' [ ys [ H4 H5 ] ] ].
destruct H5 as [ i3 [ i4 [ H6 [ H7 H8 ] ] ] ].
rewrite star_unit_right in H2.
unfold wand in H8.
generalize(H8 i1 H2); clear H8; intros H8.
splits_rewrite_in H6 H1.
assert(splits i (i3::i1::i4::nil)).
splits_prove.
generalize(remove_heap_in_splits H0); clear H H0; intros H.
generalize(H8 [i -- i3] H); clear H8; intros H8.
destruct H8 as [ H8 H9 ].
destruct H9 as [ i5 [ i6 [ H10 [ H11 H12 ] ] ] ].
destruct H12.
destruct H0.
splits_rewrite_in H6 H1.
assert(splits i (i3::i1::i4::nil)).
splits_prove.
clear H5.
generalize(merge_heap H9 H10); intros H12.
exists c'; exists Nil.
splits_join_in H12 (1::0::1::nil).
exists (union (i3::i6::nil) pf0); exists i5.
intuition.
exists i3; exists i6.
intuition.
exists pf0; trivial.
destruct H0 as [ x [ xs' [ c'0 [ H12 H13 ] ] ] ].
destruct H13 as [ i7 [ i8 [ H14 [ H15 H16 ] ] ] ].
splits_rewrite_in H6 H1.
assert(splits i (i3::i1::i4::nil)).
splits_prove.
clear H0.
splits_rewrite_in H14 H10.
generalize(merge_heap H3 H0); intros H17.
splits_join_in H17 (1::0::1::0::nil).
exists c'; exists (Cons x c'0).
splits_join_in H5 (0::1::1::nil).
exists (union (i3::i7::nil) pf0); exists (union (i5::i8::nil) pf1).
intuition.
apply splits_commute; assumption.
exists i3; exists i7.
intuition.
exists pf0; trivial.
Qed.

Lemma lsts_lemma : forall (A : Type) (l1 l2 : list A),
  nil = (l1 ++ l2) -> (l1 = nil /\ l2 = nil).
intros.
case_eq l1.
intros.
rewrite H0 in H.
simpl app in H.
intuition.
intros.
rewrite H0 in H.
simpl app in H.
inversion H.
Qed.

Lemma Iiter_lemma : forall (it : Ai) (xs : list nat) (h : heap),
  Iiter it nil xs h -> False.
intros.
generalize dependent xs.
generalize dependent h.
induction it.
intros.
simpl in H.
contra.
intros.
simpl in H.
destruct H as [ xs' [ H1 H2 ] ].
eapply IHit; eauto.
intros.
simpl in H.
destruct H as [ xs1 [ xs2 [ S1 [ S2 [ H1 [ H2 [ H3 H4 ] ] ] ] ] ] ].
destruct H4 as [ h1 [ h2 [ H5 [ H6 H7 ] ] ] ].
destruct (lsts_lemma H3) as [ H8 H9 ].
rewrite_clear.
eapply IHit1; eauto.
Qed.

Lemma lst_lemma2 : forall (A : Type) (x : A) (l1 l2 l3 : list A),
  x::l1 = l2 ++ l3 -> (l2 = nil \/ exists l : list A, l2 = x::l).
intros.
generalize dependent l2.
generalize dependent l3.
generalize dependent x.
induction l1.
intros.
induction l2.
left; trivial.
right.
simpl app in H.
inversion H.
destruct(lsts_lemma H2) as [ H3 H4 ].
rewrite_clear.
exists (nil (A := A)).
trivial.
intros.
induction l2.
left; trivial.
simpl app in H.
inversion H.
right.
exists l2; trivial.
Qed.