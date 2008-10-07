Require Import DisjointUnion.
Require Import List.
Require Import MemModel.
Require Import ST.
Require Import Separation.
Require Import STsep.
Require Import Assumptions.
Require Import ListSet.
Require Import FiniteMap.
Require Import Hashtable.
Require Import HashtableType.
Require Import Precise.
Require Import Flyweight.

Set Implicit Arguments.
Unset Strict Implicit.
Open Local Scope stsep_scope.

Program Definition c1 (F : Flyweight) (c : char) (f : font) :
  STsep emp (char * font)%type (fun y i m => y = Val (c, f) /\ nopre m) :=
  sdo (x <-- FlyNew F; sret (c, f)).
Next Obligation.
nextvc.
exists empty.
split; trivial.
exists empty.
split.
remove_empty.
apply splits_refl.
intros.
splits_eqto_subheap H.
split.
intros.
assert(Val x = Val x); trivial.
destruct H0 as [ H0 [ N0 N1 ] ].
exists j.
split.
exists empty; exists j.
split; try splits_refl_empty.
split; trivial.
unfold sret_pre.
trivial.
intros.
destruct H2 as [ h1 [ h2 [ H3 [ h3 [ h5 [ H4 [ H5 H6 ] ] ] ] ] ] ].
unfold sret_post in H5.
destruct H5 as [ H7 H8 ].
split; try assumption.
unfold nopre.
trivial.
intros.
destruct H0 as [ H0 [ H1 H2 ] ].
inversion H1.
Defined.

(*Program Definition locsToChars (F : Flyweight) (ll : list loc) (h : loc) :
  STsep 
     (fun i => exists f : HashKey -> option HashValue, exists S : set T,
        chars (FlyGlyph F) S i /\ FlyRefs F f i /\
        forall l : loc, In l ll -> exists c : char, exists fo : font,
          f (c, fo) = Some l /\ set_In (l, c, fo) S)
     (char * font)%type list
     (fun y i m => 
       forall f : HashKey -> option HashValue, forall S : set T,
         (chars (FlyGlyph F) S i /\ FlyRefs F f i /\
         forall l : loc, In l ll -> exists c : char, exists fo : font,
          f (c, fo) = Some l /\ set_In (l, c, fo) S) ->
       i = m /\ exists ll' : (char * font)%type list,
       y = Val l'' /\ 
         In (c, f) l'' -> f (c, f) ).*)

Lemma updateF_lemma : forall (f : HashKey -> option HashValue) (c : char) (fo : font) (l : loc),
  updateF f (c, fo) l (c, fo) = Some l.
intros.
unfold updateF.
destruct (HashKey_eq (c, fo) (c, fo)).
trivial.
contradiction n.
trivial.
Qed.

Lemma updateF_lemma2 : forall (f : HashKey -> option HashValue) (c : char) (fo : font) (l : loc),
  updateF (updateF f (c, fo) l) (c, fo) l = updateF f (c, fo) l.
intros.
apply extensional.
intros.
unfold updateF.
destruct(HashKey_eq (c, fo) x).
trivial.
trivial.
Qed.

Ltac splits_auto :=
  match goal with
  | H : splits ?h1 (?h2::empty::nil) |- _ =>
          let tmp := fresh "tmp" in
          remove_empty_in H; clear H; intros H; 
          destruct H as [ tmp H ]; simpl in H; clear tmp;
          ((rewrite H in *; clear H h1) || (rewrite <- H in *; clear H h2))
  end.

Ltac FlyState H H' f S :=
  match goal with 
  | H1 : splits ?h (?h1::?h2::nil), 
    H2 : FlyTable ?F ?x f ?h1,
    H3 : chars (FlyGlyph ?F) ?S ?h2,
    H4 : FlyRefs ?F ?f ?h2 |- _ =>  
  assert(H : (FlyTable F x f # (fun h : heap => chars (FlyGlyph F) S h /\
                                                FlyRefs F f h)) h);
  [ exists h1; exists h2; repeat(split; try assumption) | idtac ];
  assert(H' : exists S : set T, exists f : HashKey -> option HashValue,
             (FlyTable F x f # (fun h : heap => chars (FlyGlyph F) S h /\
                                                FlyRefs F f h)) h);
  [ exists S; exists f; assumption | idtac ]
  end.
 
Program Definition c2 (F : Flyweight) (c : char) (f : font) :
  STsep emp unit (fun y i m => y = Val tt /\ exists l : loc, exists l' : loc,
     (FlyTable F l (fun k => if HashKey_eq (c, f) k then Some l' else None) # 
        (fun h => chars (FlyGlyph F) (set_add T_eq (l', c, f) (empty_set T)) h /\
          FlyRefs F (fun k => if HashKey_eq (c, f) k then Some l' else None) h))
      m) :=
  sdo (x <-- FlyNew F; y <-- FlyNewchar F x f c; y <-- FlyNewchar F x f c; sret tt).
Next Obligation.
nextvc.
exists empty.
split; [ trivial | idtac ].
exists empty.
split.
splits_refl_empty.
intros j j0 H.
splits_auto.
split.
intros x H0.
destruct H0 as [ l [ H1 H2 ] ].
injection H1 as H3.
clear H1.
clear i.
rewrite <- H3 in *.
clear H3 l.
destruct H2 as [ j1 [ j2 [ H3 [ H4 [ H5 H6 ] ] ] ] ].
unfold sbind_pre.
exists empty.
split.
exists j0.
exists empty.
split.
splits_refl_empty.
split.
FlyState H7 H8 (fun _ : HashKey => None (A := HashValue)) (empty_set T).
split.
exists j0.
exists empty.
split.
splits_refl_empty.
split.
assumption.
auto.
intros x0 h H0.
unfold diff1 in H0.
generalize(H0 j0 H8); intros H1.
assert(H2 : splits j0 (j0::empty::nil)).
splits_refl_empty.
generalize(H1 empty H2); intros N7.
destruct N7 as [ h1 [ H9 H10 ] ].
generalize(H10 (empty_set T) (fun _ : HashKey => None) H7); intros H11.
clear H7 H10 H1 H0 H8 H2.
destruct H11 as [ l [ H12 [ N1 H13 ] ] ].
destruct H13 as [ h3 [ h4 [ H14 [ H15 [ H16 H17 ] ] ] ] ].
inversion H12.
rewrite H0 in *.
clear H0 x0 H12.
splits_auto.
copy H14 H18.
destruct H18 as [ pf _ ].
exists (union (h3::h4::nil) pf).
exists empty.
split.
splits_flatten.
remove_empty.
assumption.
split.
split.
exists (union (h3::h4::nil) pf).
exists empty.
split.
remove_empty.
apply splits_refl.
split.
exists (set_add T_eq (l, c, f) (empty_set T)).
exists (updateF (fun _ : HashKey => None) (c, f) l).
exists h3.
exists h4.
split.
exists pf; trivial.
repeat(split; try assumption).
auto.
intros.
unfold sret_pre.
exists empty.
exists h.
split.
splits_refl_empty.
split; auto.
auto.
auto.
intros.
unfold sbind_post in H.
unfold diff1 in H.
destruct H as [ h1 [ h2 [ H2 [ h3 [ h4 [ H7 [ H8 H9 ] ] ] ] ] ] ].
unfold delta in H9.
destruct H9 as [ H10 H11 ].
unfold this in H10, H11.
rewrite <- H10 in *.
rewrite <- H11 in *.
clear H10 H11 h2 h4.
splits_eqto_subheap H2.
splits_eqto_subheap H7.
rewrite H2 in *.
rewrite H7 in *.
clear H2 H7 j0 m.
destruct H8 as [ H8 | H8 ].
destruct H8 as [ H9 [ l [ h4 [ H10 H11 ] ] ] ].
copy H3 H12.
destruct H12 as [ pf N1 ].
FlyState H1 H (fun _ : HashKey => None (A := HashValue)) (empty_set T).
rewrite N1 in H1, H.
generalize(H10 (union (j1::j2::nil) pf) H); intros H12.
assert(splits h1 (union (j1 :: j2 :: nil) pf :: empty :: nil)).
splits_flatten.
remove_empty.
assumption.
generalize(H12 empty H0); intros H13.
destruct H13 as [ h5 [ H14 H15 ] ].
splits_auto.
generalize(H15 (empty_set T) (fun _ : HashKey => None (A := HashValue)) H1); intros H16.
destruct H16 as [ l0 [ H17 [ N2 [ h6 [ h7 [ H18 [ H19 [ H20 H21 ] ] ] ] ] ] ] ].
inversion H17.
rewrite H7 in *; clear H7 l H17.
clear H1 H15 H12 H H10.
copy H18 H22; destruct H22 as [ pf1 _ ].
assert(H : ((fun i : heap =>
          exists S : set T,
            exists f' : HashKey -> option HashValue,
              (FlyTable F x f'
               # (fun h : heap => chars (FlyGlyph F) S h /\ FlyRefs F f' h))
                i) # nopre) (union (h6::h7::nil) pf1) /\
        (forall (x0 : loc) (h : heap),
         (forall i2 : heap,
          (exists S : set T,
             exists f' : HashKey -> option HashValue,
               (FlyTable F x f'
                # (fun h0 : heap =>
                   chars (FlyGlyph F) S h0 /\ FlyRefs F f' h0)) i2) ->
          forall m : heap,
          splits (union (h6::h7::nil) pf1) (i2 :: m :: nil) ->
          exists h1 : heap,
            splits h (h1 :: m :: nil) /\
            (forall (S : set T) (f' : HashKey -> option HashValue),
             (FlyTable F x f'
              # (fun h0 : heap => chars (FlyGlyph F) S h0 /\ FlyRefs F f' h0))
               i2 ->
             exists l : loc,
               Val x0 = Val l /\
               (forall l' : loc, f' (c, f) = Some l' -> l = l') /\
               (FlyTable F x (updateF f' (c, f) l)
                # (fun h0 : heap =>
                   chars (FlyGlyph F) (set_add T_eq (l, c, f) S) h0 /\
                   FlyRefs F (updateF f' (c, f) l) h0)) h1)) ->
         (sret_pre # nopre) h)).
split.
exists (union (h6::h7::nil) pf1).
exists empty.
split.
remove_empty; apply splits_refl.
split.
exists (set_add T_eq (l0, c, f) (empty_set T)).
exists (updateF (fun _ : HashKey => None) (c, f) l0).
exists h6; exists h7.
split.
exists pf1; trivial.
repeat(split; try assumption).
auto.
intros.
exists empty; exists h.
split.
remove_empty; apply splits_refl.
split; [ unfold sret_pre; trivial | auto ].
generalize(H11 (union (h6::h7::nil) pf1) H); intros H12.
assert(H1 : splits h5 (union (h6 :: h7 :: nil) pf1 :: empty :: nil)).
splits_flatten.
remove_empty.
assumption.
generalize(H12 empty H1); intros H13.
clear H11 H H12.
destruct H13 as [ h8 [ H14 H15 ] ].
destruct H15 as [ H15 | H15 ].
destruct H15 as [ [ h9 [ h10 [ H16 [ H17 H22 ] ] ] ] H23 ].
destruct H23 as [ x0 [ h11 [ H24 H25 ] ] ].
unfold sret_pre in H25.
unfold sret_post in H25.
assert(H26 : emp empty); trivial.
assert(H27 : splits h11 (empty::h11::nil)).
remove_empty; apply splits_refl.
generalize(H25 empty H26 h11 H27); intros H28.
clear H25 H26 H27.
destruct H28 as [ h12 [ H29 [ H30 H31 ] ] ].
split; trivial.
splits_eqto_subheap H14.
rewrite H14 in *; clear H14 h3.
rewrite <- H30 in *; clear H30 h12. 
splits_eqto_subheap H29.
rewrite H29 in *; clear h8 H29.
FlyState J1 J2 (updateF (fun _ : HashKey => None) (c, f) l0)
               (set_add T_eq (l0, c, f) (empty_set T)).
copy H18 J3; destruct J3 as [ Jpf J4 ]; rewrite J4 in J1, J2; clear J4.
generalize(H24 (union (h6::h7::nil) pf1) J2); intros H25.
clear H24 J2.
assert(H27 : splits (union (h6 :: h7 :: nil) pf1)
          (union (h6 :: h7 :: nil) pf1 :: empty :: nil)).
remove_empty; apply splits_refl.
generalize(H25 empty H27); intros H28.
clear H25 H27. 
destruct H28 as [ h13 [ H29 H30 ] ].
splits_eqto_subheap H29.
rewrite H29 in *; clear H29 h11.
generalize(H30 (set_add T_eq (l0, c, f) (empty_set T))
               (updateF (fun _ : HashKey => None) (c, f) l0) J1); intros H32.
clear H30.
destruct H32 as [ l [ H33 H34 ] ].
destruct H34 as [ H35 H36 ].
assert(l = l0).
apply H35.
apply updateF_lemma.
rewrite H in H36.
assert((updateF (updateF (fun _ : HashKey => None) (c, f) l0) 
                 (c, f) l0) = (updateF (fun _ : HashKey => None) (c, f) l0)).
apply updateF_lemma2.
rewrite H2 in H36.
simpl in H36.
destruct(T_eq (l0, c, f) (l0, c, f)).
exists x; exists l0.
unfold updateF in H36.
apply H36.
contradiction n.
trivial.
destruct H15 as [ e [ H16 H17 ] ].
assert((exists S : set T,
           exists f' : HashKey -> option HashValue,
             (FlyTable F x f'
              # (fun h : heap => chars (FlyGlyph F) S h /\ FlyRefs F f' h))
               (union (h6::h7::nil) pf1))).
exists (set_add T_eq (l0, c, f) (empty_set T)).
exists (updateF (fun _ : HashKey => None) (c, f) l0).
exists h6; exists h7.
split.
exists pf1; trivial.
repeat(split; try assumption).
generalize(H17 (union (h6::h7::nil) pf1) H); intros H22.
assert(splits (union (h6 :: h7 :: nil) pf1)
          (union (h6 :: h7 :: nil) pf1 :: empty :: nil)).
remove_empty.
apply splits_refl.
generalize(H22 empty H2); intros H23.
destruct H23 as [ h15 [ H24 H25 ] ].
FlyState H7 H8 (updateF (fun _ : HashKey => None) (c, f) l0) 
               (set_add T_eq (l0, c, f) (empty_set T)).
copy H18 N20; destruct N20 as [ Npf N21 ]; rewrite N21 in H7, H8; clear N21.
generalize(H25 (set_add T_eq (l0, c, f) (empty_set T))
               (updateF (fun _ : HashKey => None) (c, f) l0) H7); intros H26.
destruct H26 as [ l [ H27 H28 ] ].
inversion H27.
copy H3 H7.
destruct H7 as [ pf _ ].
FlyState N7 N8 (fun _ : HashKey => None (A := HashValue)) (empty_set T).
copy H3 N3; destruct N3 as [ Npf N31 ]; rewrite N31 in N7, N8; clear N31.
destruct H8 as [ e [ H9 H10 ] ].
assert(splits h1 (union(j1::j2::nil) pf::empty::nil)).
splits_flatten.
remove_empty.
assumption.
generalize(H10 (union(j1::j2::nil) pf) N8 empty H); intros H11.
destruct H11 as [ h11 [ H12 H13 ] ].
generalize(H13 (empty_set T) (fun _ : HashKey => None (A := HashValue)) N7); intros H14.
destruct H14 as [ l [ H15 H16 ] ].
inversion H15.
intros.
destruct H as [ l [ H1 H2 ] ].
inversion H1.
Defined.

Program Definition c3 (F : Flyweight) (c : char) (f : font) :
  STsep emp (loc*loc)%type (fun y i m => exists l : loc, exists l' : loc,
     (FlyTable F l (fun k => if HashKey_eq (c, f) k then Some l' else None) # 
        (fun h => chars (FlyGlyph F) (set_add T_eq (l', c, f) (empty_set T)) h /\
          FlyRefs F (fun k => if HashKey_eq (c, f) k then Some l' else None) h))
      m /\ y = Val (l, l')) :=
  sdo (x <-- FlyNew F; 
       y <-- FlyNewchar F x f c;
       y <-- FlyNewchar F x f c;
       sret (x, y)).
Next Obligation.
nextvc.
exists empty.
split; [ trivial | idtac ].
exists empty.
split.
splits_refl_empty.
intros j j0 H.
splits_auto.
split.
intros x H0.
destruct H0 as [ l [ H1 H2 ] ].
injection H1 as H3.
clear H1.
clear i.
rewrite <- H3 in *.
clear H3 l.
destruct H2 as [ j1 [ j2 [ H3 [ H4 [ H5 H6 ] ] ] ] ].
unfold sbind_pre.
exists empty.
split.
exists j0.
exists empty.
split.
splits_refl_empty.
split.
FlyState H7 H8 (fun _ : HashKey => None (A := HashValue)) (empty_set T).
split.
exists j0.
exists empty.
split.
splits_refl_empty.
split.
assumption.
auto.
intros x0 h H0.
unfold diff1 in H0.
generalize(H0 j0 H8); intros H1.
assert(H2 : splits j0 (j0::empty::nil)).
splits_refl_empty.
generalize(H1 empty H2); intros N7.
destruct N7 as [ h1 [ H9 H10 ] ].
generalize(H10 (empty_set T) (fun _ : HashKey => None) H7); intros H11.
clear H7 H10 H1 H0 H8 H2.
destruct H11 as [ l [ H12 [ N1 H13 ] ] ].
destruct H13 as [ h3 [ h4 [ H14 [ H15 [ H16 H17 ] ] ] ] ].
inversion H12.
rewrite H0 in *.
clear H0 x0 H12.
splits_auto.
copy H14 H18.
destruct H18 as [ pf _ ].
exists (union (h3::h4::nil) pf).
exists empty.
split.
splits_flatten.
remove_empty.
assumption.
split.
split.
exists (union (h3::h4::nil) pf).
exists empty.
split.
remove_empty.
apply splits_refl.
split.
exists (set_add T_eq (l, c, f) (empty_set T)).
exists (updateF (fun _ : HashKey => None) (c, f) l).
exists h3.
exists h4.
split.
exists pf; trivial.
repeat(split; try assumption).
auto.
intros.
unfold sret_pre.
exists empty.
exists h.
split.
splits_refl_empty.
split; auto.
auto.
auto.
intros.
unfold sbind_post in H.
unfold diff1 in H.
destruct H as [ h1 [ h2 [ H2 [ h3 [ h4 [ H7 [ H8 H9 ] ] ] ] ] ] ].
unfold delta in H9.
destruct H9 as [ H10 H11 ].
unfold this in H10, H11.
rewrite <- H10 in *.
rewrite <- H11 in *.
clear H10 H11 h2 h4.
splits_eqto_subheap H2.
splits_eqto_subheap H7.
rewrite H2 in *.
rewrite H7 in *.
clear H2 H7 j0 m.
destruct H8 as [ H8 | H8 ].
destruct H8 as [ H9 [ l [ h4 [ H10 H11 ] ] ] ].
copy H3 H12.
destruct H12 as [ pf N1 ].
FlyState H1 H (fun _ : HashKey => None (A := HashValue)) (empty_set T).
rewrite N1 in H1, H.
generalize(H10 (union (j1::j2::nil) pf) H); intros H12.
assert(splits h1 (union (j1 :: j2 :: nil) pf :: empty :: nil)).
splits_flatten.
remove_empty.
assumption.
generalize(H12 empty H0); intros H13.
destruct H13 as [ h5 [ H14 H15 ] ].
splits_auto.
generalize(H15 (empty_set T) (fun _ : HashKey => None (A := HashValue)) H1); intros H16.
destruct H16 as [ l0 [ H17 [ N2 [ h6 [ h7 [ H18 [ H19 [ H20 H21 ] ] ] ] ] ] ] ].
inversion H17.
rewrite H7 in *; clear H7 l H17.
clear H1 H15 H12 H H10.
copy H18 H22; destruct H22 as [ pf1 _ ].
assert(H : ((fun i : heap =>
          exists S : set T,
            exists f' : HashKey -> option HashValue,
              (FlyTable F x f'
               # (fun h : heap => chars (FlyGlyph F) S h /\ FlyRefs F f' h))
                i) # nopre) (union (h6::h7::nil) pf1) /\
        (forall (x0 : loc) (h : heap),
         (forall i2 : heap,
          (exists S : set T,
             exists f' : HashKey -> option HashValue,
               (FlyTable F x f'
                # (fun h0 : heap =>
                   chars (FlyGlyph F) S h0 /\ FlyRefs F f' h0)) i2) ->
          forall m : heap,
          splits (union (h6::h7::nil) pf1) (i2 :: m :: nil) ->
          exists h1 : heap,
            splits h (h1 :: m :: nil) /\
            (forall (S : set T) (f' : HashKey -> option HashValue),
             (FlyTable F x f'
              # (fun h0 : heap => chars (FlyGlyph F) S h0 /\ FlyRefs F f' h0))
               i2 ->
             exists l : loc,
               Val x0 = Val l /\
               (forall l' : loc, f' (c, f) = Some l' -> l = l') /\
               (FlyTable F x (updateF f' (c, f) l)
                # (fun h0 : heap =>
                   chars (FlyGlyph F) (set_add T_eq (l, c, f) S) h0 /\
                   FlyRefs F (updateF f' (c, f) l) h0)) h1)) ->
         (sret_pre # nopre) h)).
split.
exists (union (h6::h7::nil) pf1).
exists empty.
split.
remove_empty; apply splits_refl.
split.
exists (set_add T_eq (l0, c, f) (empty_set T)).
exists (updateF (fun _ : HashKey => None) (c, f) l0).
exists h6; exists h7.
split.
exists pf1; trivial.
repeat(split; try assumption).
auto.
intros.
exists empty; exists h.
split.
remove_empty; apply splits_refl.
split; [ unfold sret_pre; trivial | auto ].
generalize(H11 (union (h6::h7::nil) pf1) H); intros H12.
assert(H1 : splits h5 (union (h6 :: h7 :: nil) pf1 :: empty :: nil)).
splits_flatten.
remove_empty.
assumption.
generalize(H12 empty H1); intros H13.
clear H11 H H12.
destruct H13 as [ h8 [ H14 H15 ] ].
destruct H15 as [ H15 | H15 ].
destruct H15 as [ [ h9 [ h10 [ H16 [ H17 H22 ] ] ] ] H23 ].
destruct H23 as [ x0 [ h11 [ H24 H25 ] ] ].
unfold sret_pre in H25.
unfold sret_post in H25.
assert(H26 : emp empty); trivial.
assert(H27 : splits h11 (empty::h11::nil)).
remove_empty; apply splits_refl.
generalize(H25 empty H26 h11 H27); intros H28.
clear H25 H26 H27.
destruct H28 as [ h12 [ H29 [ H30 H31 ] ] ].
(* exists x. exists 
split; trivial. *)
splits_eqto_subheap H14.
rewrite H14 in *; clear H14 h3.
rewrite <- H30 in *; clear H30 h12. 
splits_eqto_subheap H29.
rewrite H29 in *; clear h8 H29.
FlyState J1 J2 (updateF (fun _ : HashKey => None) (c, f) l0)
               (set_add T_eq (l0, c, f) (empty_set T)).
copy H18 J3; destruct J3 as [ Jpf J4 ]; rewrite J4 in J1, J2; clear J4.
generalize(H24 (union (h6::h7::nil) pf1) J2); intros H25.
clear H24 J2.
assert(H27 : splits (union (h6 :: h7 :: nil) pf1)
          (union (h6 :: h7 :: nil) pf1 :: empty :: nil)).
remove_empty; apply splits_refl.
generalize(H25 empty H27); intros H28.
clear H25 H27. 
destruct H28 as [ h13 [ H29 H30 ] ].
splits_eqto_subheap H29.
rewrite H29 in *; clear H29 h11.
generalize(H30 (set_add T_eq (l0, c, f) (empty_set T))
               (updateF (fun _ : HashKey => None) (c, f) l0) J1); intros H32.
clear H30.
destruct H32 as [ l [ H33 H34 ] ].
destruct H34 as [ H35 H36 ].
assert(l = l0).
apply H35.
apply updateF_lemma.
rewrite H in H36.
assert((updateF (updateF (fun _ : HashKey => None) (c, f) l0) 
                 (c, f) l0) = (updateF (fun _ : HashKey => None) (c, f) l0)).
apply updateF_lemma2.
rewrite H2 in H36.
simpl in H36.
destruct(T_eq (l0, c, f) (l0, c, f)).
exists x; exists l0.
unfold updateF in H36.
split.
apply H36.
trivial.
inversion H33.
rewrite <- H.
rewrite <- H8.
assumption.
contradiction n.
trivial.
destruct H15 as [ e [ H16 H17 ] ].
assert((exists S : set T,
           exists f' : HashKey -> option HashValue,
             (FlyTable F x f'
              # (fun h : heap => chars (FlyGlyph F) S h /\ FlyRefs F f' h))
               (union (h6::h7::nil) pf1))).
exists (set_add T_eq (l0, c, f) (empty_set T)).
exists (updateF (fun _ : HashKey => None) (c, f) l0).
exists h6; exists h7.
split.
exists pf1; trivial.
repeat(split; try assumption).
generalize(H17 (union (h6::h7::nil) pf1) H); intros H22.
assert(splits (union (h6 :: h7 :: nil) pf1)
          (union (h6 :: h7 :: nil) pf1 :: empty :: nil)).
remove_empty.
apply splits_refl.
generalize(H22 empty H2); intros H23.
destruct H23 as [ h15 [ H24 H25 ] ].
FlyState H7 H8 (updateF (fun _ : HashKey => None) (c, f) l0) 
               (set_add T_eq (l0, c, f) (empty_set T)).
copy H18 N20; destruct N20 as [ Npf N21 ]; rewrite N21 in H7, H8; clear N21.
generalize(H25 (set_add T_eq (l0, c, f) (empty_set T))
               (updateF (fun _ : HashKey => None) (c, f) l0) H7); intros H26.
destruct H26 as [ l [ H27 H28 ] ].
inversion H27.
copy H3 H7.
destruct H7 as [ pf _ ].
FlyState N7 N8 (fun _ : HashKey => None (A := HashValue)) (empty_set T).
copy H3 N3; destruct N3 as [ Npf N31 ]; rewrite N31 in N7, N8; clear N31.
destruct H8 as [ e [ H9 H10 ] ].
assert(splits h1 (union(j1::j2::nil) pf::empty::nil)).
splits_flatten.
remove_empty.
assumption.
generalize(H10 (union(j1::j2::nil) pf) N8 empty H); intros H11.
destruct H11 as [ h11 [ H12 H13 ] ].
generalize(H13 (empty_set T) (fun _ : HashKey => None (A := HashValue)) N7); intros H14.
destruct H14 as [ l [ H15 H16 ] ].
inversion H15.
intros.
destruct H as [ l [ H1 H2 ] ].
inversion H1.
Defined.

Program Definition c4 (F : Flyweight) (c : char) (f : font) :
  STsep emp (char*font)%type (fun y i m => y = Val (c, f) /\ exists l : loc, exists l' : loc,
     (FlyTable F l (fun k => if HashKey_eq (c, f) k then Some l' else None) # 
        (fun h => chars (FlyGlyph F) (set_add T_eq (l', c, f) (empty_set T)) h /\
          FlyRefs F (fun k => if HashKey_eq (c, f) k then Some l' else None) h))
      m) :=
  sdo (x <-- c3 F c f; FlyGetdata F (snd x)).
Next Obligation.
nextvc.
exists empty.
split.
auto.
exists empty.
split.
splits_refl_empty.
intros.
splits_auto.
split.
intros.
destruct H as [ l [ l' [ H1 H2 ] ] ].
destruct H1 as [ h1 [ h2 [ H3 [ H4 [ H5 H6 ] ] ] ] ].
inversion H2.
rewrite H0 in *; clear H2 H0 x.
copy H5 H7.
unfold chars in H7.
assert(set_In (l', c, f) ((l', c, f) :: nil)).
simpl.
left.
trivial.
generalize(H7 l' c f H); intros H8.
destruct H8 as [ h3 [ h4 [ H10 [ H11 H12 ] ] ] ].
splits_rewrite_in H10 H3.
assert(splits j1 (h3::h1::h4::nil)).
eapply splits_permute.
apply H0.
PermutProve.
copy H1 H13.
destruct H13 as [ pf _ ].
destruct(disjoint_cons_elim pf) as [ pf' _ ].
exists (union (h1::h4::nil) pf').
split.
exists h3.
exists (union (h1::h4::nil) pf').
split.
splits_flatten.
assumption.
split.
exists f; exists c.
assumption.
auto.
trivial.
intros.
destruct H2 as [ h5 [ h6 [ H13 [ H14 [ h7 [ h8 [ H15 [ H16 H17 ] ] ] ] ] ] ] ].
unfold this in H16, H17.
assert(splits h6 (h1::h4::nil)).
exists pf'; symmetry; trivial.
splits_rewrite_in H2 H13.
assert(h5 = h3).
eapply splits_same_head.
apply H8.
assumption.
rewrite H9 in *; clear H9 h5.
assert(splits h7 (h1::h4::nil)).
exists pf'; symmetry; trivial.
splits_rewrite_in H9 h8.
generalize(H15 f c H11); intros H20.
destruct H20 as [ H21 H22 ].
split.
trivial.
rewrite <- H21 in H18.
assert(m = j1).
copy H1 H23.
copy H18 H24.
destruct H23 as [ x H23 ].
destruct H24 as [ x' H24 ].
rewrite H23; rewrite H24; trivial.
rewrite H19.
exists l; exists l'.
exists h1; exists h2.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
intros.
destruct H as [ l [ l' [ H1 H2 ] ] ].
inversion H2.
Defined.