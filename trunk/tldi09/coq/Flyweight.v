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
(* Finite table implementation. *)
Require Import Table.
Require Import MiscLemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Open Local Scope stsep_scope.

Section Flyweight.

(* The simulated objects consists of a value of the following type. *)
Variable obj : Set.
(* We need an equality decision procedure for the table implementation *)
Variable obj_eq : forall x y : obj, {x = y} + {x <> y}.

Definition T := (loc * obj)%type.

Lemma T_eq : forall x y : T, {x = y} + {x <> y}.
intros.
decide equality.
apply loc_eq.
Qed.

(* The finite table computations *)
Definition update := update obj_eq.
Definition lookup := lookup obj_eq.
Definition newtable := newtable obj.
Definition updateF := updateF obj_eq.
Definition table_very_precise := table_very_precise (dom := obj).

Definition allobjat (objat : loc -> obj -> hprop) (f : obj -> option loc) (h : heap) : Prop :=
  forall (l : loc) (o : obj),
    f o = Some l -> (objat l o # (fun _ => True)) h. 

(* Define the refs and objat predicate of our implementation. *)
Definition refs (f : obj -> option loc) (h : heap) : Prop :=
  (forall k : obj, forall v : loc, f k = Some v -> 
     (v --> k # nopre) h) /\
  (forall l : loc, forall k : obj,
     ((l --> k # nopre) h -> f k = Some l)) /\
  (forall l : loc, valid_loc l h ->
      exists o : obj, f o = Some l).

Definition objat (r : loc) (x : obj) (h : heap) :=
  ((r --> x) # nopre) h.

(* The flyweight provides referencial transparency for the simulated objects. *)
Lemma objat_lemma : 
  forall (h : heap) (l l' : loc) (o o' : obj) (f : obj -> option loc),
      (objat l o h /\ objat l' o' h /\ refs f h) -> (l = l' <-> o = o').
intros.
destruct H as [ H1 [ H2 H3 ] ].
destruct H1 as [ h1 [ h2 [ H4 [ H5 H6 ] ] ] ].
destruct H2 as [ h3 [ h4 [ H7 [ H8 H9 ] ] ] ].
destruct H3 as [ H10 [ H11 H12 ] ].
split.
intros.
rewrite <- H in H8.
same_two_subheaps H4 H5 H13.
trivial.
intros.
rewrite <- H in H8.
assert(((l --> o) # nopre) h).
exists h1; exists h2.
repeat(split; try assumption).
generalize(H11 l o H0); intros H14.
assert(((l' --> o) # nopre) h).
exists h3; exists h4.
repeat(split; try assumption).
generalize(H11 l' o H1); intros H15.
destruct H14 as [ v1 H16 ].
destruct H15 as [ v2 H17 ].
generalize(H11 l o H0); intros H14.
generalize(H11 l' o H1); intros H15.
rewrite H14 in H15.
inversion H15.
trivial.
Qed.

(* Lemma to extend allobjat with a simulated object. *)
Lemma extend_allobjat : 
  forall (f : obj -> option loc) (o : obj) (l : loc) 
         (h1 h2 : heap) (pf : disjoint(h1::h2::nil)),
     (l --> o) h2 -> allobjat objat f h1 -> 
     allobjat objat (updateF f o l) (union (h1::h2::nil) pf).
intros.
unfold allobjat, updateF, Table.updateF, objat in *; intros.
destruct (obj_eq o o0).
inversion H1; clear H1.
rewrite_clear.
exists h2; exists h1.
intuition.
apply splits_commute.
exists pf; trivial.
exists h2; exists empty.
intuition.
splits_refl_empty.
generalize(H0 l0 o0 H1); clear H0 H1; intros.
apply extend_nopre.
assumption.
Qed.

Lemma refs_unused_loc :
  forall (h1 h2 : heap) (f' : obj -> option loc) (o : obj)
         (l : loc) (pf : disjoint (h1::h2::nil)),
    refs f' h2 -> f' o = None -> 
    ((l --> o) # nopre) (union (h1::h2::nil) pf) ->
      unused_loc l h2.
intros.
destruct H as [ H2 [ H3 H4 ] ].
generalize(loc_em l h2).
intuition.
generalize(H4 l H5); intros.
destruct H.
generalize(H2 x l H); intros H6.
assert(selects l x h2).
apply points_to_selects_nopre; assumption.
assert(selects l o (union (h1::h2::nil) pf)).
unfold selects.
destruct H1 as [ j1 [ j2 [ J1 [ J2 J3 ] ] ] ].
destruct J1.
rewrite H1.
apply union_points_to.
assumption.
assert(selects l x (union (h1::h2::nil) pf)).
assert(splits (union (h1::h2::nil) pf) (h1::h2::nil)).
exists pf; trivial.
apply splits_commute in H9.
eapply selects_extend.
apply H7.
apply H9.
assert(o = x).
eapply same_selects_equal; eauto.
rewrite_clear.
rewrite H in H0.
inversion H0.
Qed.

(* Lemma to extend refs with a new simulated object. *)
Lemma extend_refs :
  forall (f : obj -> option loc) (o : obj) 
         (l : loc) (h1 h2 : heap) (pf : disjoint(h1::h2::nil)),
    (l --> o) h2 -> f o = None -> refs f h1 -> 
    refs (updateF f o l) (union (h1::h2::nil) pf).
intros.
unfold refs, updateF, Table.updateF.
split.
unfold refs in H1.
destruct H1 as [ H1 [ H2 N10 ] ].
intros.
destruct(obj_eq o k).
inversion H3; clear H3.
rewrite_clear.
exists h2; exists h1.
intuition.
apply splits_commute.
exists pf; trivial.
generalize(H1 k v H3); clear H3; intros.
apply extend_nopre.
assumption.
split.
intros.
destruct(obj_eq o k).
rewrite_clear.
assert(disjoint (h2::h1::nil)).
eapply disjoint_permute.
apply pf.
PermutProve.
assert(union (h1::h2::nil) pf = union (h2::h1::nil) H3).
apply union_permute.
PermutProve.
rewrite H4 in H2.
assert(unused_loc l0 h1).
eapply refs_unused_loc.
apply H1.
apply H0.
apply H2.
assert(l = l0).
eapply useful_points_to_lemma.
apply H.
rewrite <- H4 in H2.
apply H2.
unfold not; intros.
apply (loc_ex H6 H5).
rewrite H6; trivial.
unfold refs in H1.
destruct H1 as [ H1 [ H3 N10 ] ].
assert(((l0 --> k) # nopre) h1).
apply (remove_nopre (pf := pf) (l := l) (l' := l0) (o := o) (o' := k)).
apply n.
apply H.
apply H2.
apply H3.
assumption.
intros.
unfold union, union_heap_list in H2.
generalize(valid_loc_union2_elim H2); clear H2; intros H2.
destruct H2.
destruct H1 as [ N1 [ N2 N3 ] ].
generalize(N3 l0 H2); intros H3.
destruct H3.
exists x.
destruct(obj_eq o x).
rewrite_clear.
rewrite H0 in H1.
inversion H1.
assumption.
assert(l0 = l).
eapply valid_loc_points_to_equal; eauto.
rewrite_clear.
exists o.
destruct(obj_eq o o).
trivial.
contradiction n; trivial.
Qed.

(* Part of the new computation (if the simulated object is not already in the table) *)
Program Definition Fnewcharinner' (hash : loc) (o : obj) :
  STsep (fun i => exists f : (obj -> option loc),
           (table hash f # (fun h => allobjat objat f h /\ refs f h)) i /\
           f o = None) loc
        (fun y i m => forall f : (obj -> option loc),
           ((table hash f # (fun h => allobjat objat f h /\ refs f h)) i /\
            f o = None) -> (exists l : loc, y = Val l /\
              ((table hash (updateF f o l) #
                (fun h => allobjat objat (updateF f o l) h /\ refs (updateF f o l) h)) m))) := 
  sdo (l <-- snew o; update hash o l;; sret l).
Next Obligation.
nextvc.
unfold sret_pre.
destruct H0 as [ h1 [ h2 [ H6 [ H7 H8 ] ] ] ].
unfold sbind_pre.
splits_rewrite_in H6 H2.
splits_join_in H0 (0::1::1::nil).
exists (union (h2::t::nil) pf0).
split.
exists h1.
exists (union (h2::t::nil) pf0).
split.
apply splits_commute.
assumption.
intuition.
exists h1.
exists empty.
intuition.
splits_refl_empty.
exists H.
assumption.
exists empty.
exists h.
intuition.
splits_refl_empty.
intros y m H10 f H11.
destruct H10 as [ h10 [ h11 [ H12 [ h13 [ h14 [ H15 [ H16 [ h17 H18 ] ] ] ] ] ] ] ].
unfold this in h17, H18.
rewrite <- h17 in *; clear h17 h11.
rewrite <- H18 in *; clear H18 h14.
assert(h1 = h10).
apply splits_commute in H4.
eapply splits_same_head.
eauto.
assumption.
rewrite H5 in *; clear H5 h1.
destruct H16 as [ H19 | H19 ].
destruct H19 as [ H20 H100 ].
generalize(table_very_precise (l := hash) H12).
destruct H100 as [ H21 [ h22 [ H23 H24 ] ] ].
unfold diff1 in H23.
destruct H20 as [ h25 [ h26 [ H27 [ [ H28 H30 ] H29 ] ] ] ].
assert(h10 = h25 /\ empty = h26).
generalize (table_very_precise (l := hash)).
intros.
eapply H5.
instantiate (1 := h10).
splits_refl_empty.
eauto.
assumption.
eauto.
destruct H5 as [ N1 N2 ].
rewrite_clear.
rewrite <- N2 in *; clear N2 h26.
intros.
clear H5 H29 H27.
assert(exists f : obj -> option loc, table hash f h25).
eauto.
generalize(H23 h25 H5 empty); intros.
assert(splits h25 (h25::empty::nil)).
splits_refl_empty.
generalize(H9 H10); clear H9 H10; intros H9.
destruct H9 as [ h100 [ H45 [ H47 H48 ] ] ].
generalize(H48 H H7); clear H48; intros.
splits_rewrite.
unfold diff1 in H24.
assert(emp empty).
auto.
generalize(H24 empty H10); clear H10 H24; intros.
assert(splits h100 (empty::h100::nil)).
splits_refl_empty.
generalize(H10 h100 H13); clear H10 H13; intros.
destruct H10 as [ h101 [ H49 H51 ] ].
unfold sret_post in H51.
destruct H51 as [ H52 H53 ].
rewrite <- H52 in *; clear H52 h101.
splits_rewrite.
exists x.
intuition.
destruct H8 as [ h57 [ h58 [ H59 [ H60 ] ] ] ].
generalize(table_very_precise (l := hash) H59); intros.
assert(exists f : obj -> option loc, table hash f h57).
eauto.
generalize(H8 H16 h25 h2 H6); clear H8 H16; intros.
assert(exists f : obj -> option loc, table hash f h25); eauto.
generalize(H8 H16); clear H8 H16; intros.
rewrite_clear.
assert(H = f).
eapply table_pp.
instantiate (1 := h25).
instantiate (1 := hash).
intuition.
rewrite_clear.
exists h100; exists (union (h2::t::nil) pf0).
intuition.
apply extend_allobjat.
assumption.
assumption.
apply extend_refs.
assumption.
assumption.
assumption.
destruct H19 as [ e [ H19 H20 ] ].
unfold diff1 in H20.
assert(exists f : obj -> option loc, table hash f h10).
eauto.
generalize(H20 h10 H5); clear H20 H5; intros.
assert(splits h10 (h10::empty::nil)).
splits_refl_empty.
generalize(H5 empty H9); clear H5 H9; intros.
destruct H5 as [ h46 [ H99 [ H100 H101 ] ] ].
inversion H100.
Qed.

Lemma useful_updateF_lemma : 
  forall (f : obj -> option loc) (o : obj) (l : loc),
    f o = Some l -> (updateF f o l) = f.
intros.
apply extensional.
intros.
unfold updateF, Table.updateF.
destruct (obj_eq o x).
rewrite <- e.
rewrite H.
trivial.
trivial.
Qed.

(* First we define a functional version of the flyweight, which takes as argument a location to a flyweight,
   then we define a computation that creates a new flyweight and returns all the relevant flyweight operations
   instantiated with the location to the newly created flyweight, to obtain a flyweight factory. *)

(* Part of the new computation (if the simulated object already exists in the flyweight) *)
Program Definition Fnewcharinner'' (hash : loc) (o : obj) (l : loc) :
  STsep (fun i => exists f : (obj -> option loc),
           (table hash f # (fun h => allobjat objat f h /\ refs f h)) i /\
           Some l = f o) loc
        (fun y i m => forall f : (obj -> option loc),
          ((table hash f # (fun h => allobjat objat f h /\ refs f h)) i) ->
          y = Val l /\ i = m /\ (table hash (updateF f o l) # 
            (fun h => allobjat objat (updateF f o l) h /\
               refs (updateF f o l) h)) m)
  := sdo (sret l).
Next Obligation.
nextvc.
destruct H0 as [ h1 [ h2 [ H4 [ H5 ] ] ] ].
destruct H2 as [ h3 [ h4 [ H6 [ H7 ] ] ] ].
assert(h1 = h3 /\ h2 = h4).
assert(exists f : obj -> option loc, table hash f h1).
eauto.
assert(exists f : obj -> option loc, table hash f h3).
eauto.
apply (table_very_precise (l := hash) H4).
assumption.
assumption.
assumption.
destruct H0 as [ H10 H11 ].
rewrite_clear.
assert(f = H).
eapply table_pp.
split; [ apply H7 | apply H5 ].
rewrite_clear.
intros.
clear H2.
assert(updateF H o l = H).
apply useful_updateF_lemma.
symmetry; trivial.
rewrite H2 in *; clear H2.
exists h3; exists h4.
intuition.
Qed.

(* The new computation *)
Program Definition Fnewchar (hash : loc) (o : obj) :
  STsep (fun i => exists f : (obj -> option loc),
          (table hash f # (fun h => allobjat objat f h /\ refs f h)) i) loc
        (fun y i m => forall f : (obj -> option loc),
          ((table hash f # (fun h => allobjat objat f h /\ refs f h)) i) ->
          exists l : loc, y = Val l /\ 
                             (forall l' : loc, f o = Some l' -> l = l') /\ 
          (table hash (updateF f o l) # 
            (fun h => allobjat objat (updateF f o l) h /\
               refs (updateF f o l) h)) m) :=
  sdo (x <-- lookup hash o;
       case_option x (fun _ _ => Fnewcharinner' hash o)
                     (fun y : loc => fun _ => Fnewcharinner'' hash o y)).
Next Obligation.
nextvc.
destruct H0 as [ h1 [ h2 [ H3 [ H4 [ H5 H6 ] ] ] ] ].
exists h1.
split.
eauto.
exists h2.
split; try assumption.
intros.
split.
intros.
generalize(H1 H H4); intros H7.
destruct H7 as [ H8 H9 ].
destruct H9 as [ H40 H41 ].
assert(i = j).
rewrite_clear.
generalize(H3); intros H42; destruct H42 as [ pf34 H44 ].
generalize(H0); intros H45; destruct H45 as [ pf35 H46 ].
rewrite H44.
rewrite H46.
trivial.
injection H41.
intros H10.
unfold sret_pre.
unfold star1.
unfold case_sum_pre.
exists empty.
split.
exists j.
exists empty.
split; [ splits_refl_empty | idtac ].
split.
split.
intros.
exists H.
unfold opt2sum in H7.
induction x.
inversion H7.
inversion H7.
intuition.
exists j1; exists h2.
repeat (split; try assumption).
intros.
unfold opt2sum in H7.
induction x.
exists H.
injection H7.
intros.
rewrite <- H9.
split; [ idtac | assumption ].
exists j1; exists h2.
repeat (split; try assumption).
inversion H7.
trivial.
intros.
destruct H7 as [ h3 [ h4 [ H14 [ h5 [ h6 [ H15 H16 ] ] ] ] ] ].
unfold case_sum_post in H16.
destruct H16 as [ [ H17 H18 ] H19 ].
unfold delta in H19.
destruct H19 as [ H20 H21 ].
unfold this in H20, H21.
rewrite <- H20 in *.
rewrite <- H21 in *.
splits_eqto_subheap H15.
rewrite H15 in *.
induction x.
unfold opt2sum in H18. 
assert(inr unit a = inr unit a); trivial.
generalize(H18 a H7); clear H18; intros H22.
splits_eqto_subheap H14.
rewrite <- H14 in *; clear H14 h3.
rewrite <- H15 in *; clear H15 h5.
rewrite_clear.
generalize(H22 f H9); clear H22; intros H23.
destruct H23 as [ H24 H25 ].
exists a.
split.
assumption.
unfold opt2sum in H17.
assert(inl loc tt = inl loc tt); trivial.
destruct H25 as [ D1 D2 ].
destruct D2 as [ d1 [ d2 [ D3 [ D4 [ D5 D6 ] ] ] ] ].
rewrite <- D1 in D3.
assert(j1 = d1 /\ h2 = d2).
apply (table_very_precise (l := hash) H0).
eauto.
assumption.
eauto.
destruct H3.
rewrite_clear.
clear H20 h4.
clear H21 h6.
clear H2.
clear H41 H7.
destruct H9 as [ b1 [ b2 [ B1 [ B2 B3 ] ] ] ].
assert(b1 = d1 /\ b2 = d2).
apply (table_very_precise (l := hash) B1).
eauto.
assumption.
eauto.
rewrite_clear.
assert(f = H).
eapply table_pp.
instantiate (1 := d1).
instantiate (1 := hash).
intuition.
rewrite_clear.
split.
intros.
rewrite <- H10 in H0.
inversion H0; trivial.
exists d1; exists d2.
intuition.
clear H15 m.
clear H20 h4 H21 h6.
splits_rewrite.
rewrite_clear.
unfold opt2sum in H17, H18.
assert(inl loc tt = inl loc tt); trivial.
generalize(H17 tt H2); clear H17 H18; intros H22.
destruct H9 as [ b1 [ b2 [ B1 [ B2 B3 ] ] ] ].
assert(j1 = b1 /\ h2 = b2).
apply (table_very_precise (l := hash) H0).
eauto.
assumption.
eauto.
rewrite_clear.
assert(H = f).
eapply table_pp.
instantiate (1 := b1).
instantiate (1 := hash).
intuition.
rewrite_clear.
assert((exists h1 : heap,
           exists h2 : heap,
             splits h3 (h1 :: h2 :: nil) /\
             table hash f h1 /\ allobjat objat f h2 /\ refs f h2) /\
        f o = None).
intuition.
exists b1; exists b2.
intuition.
generalize(H22 f H); clear H22 H; intros H28.
destruct H28 as [ l [ H29 H30 ] ].
exists l.
intuition.
rewrite <- H10 in H3.
inversion H3.
intros.
generalize(H1 H H4); intros.
destruct H7 as [ H9 [ H10 H11 ] ].
inversion H11.
Defined.

(* Return a new flyweight. *)
Program Definition Fnew : 
  STsep emp loc 
    (fun y i m => exists l : loc, y = Val l /\
       (table l (fun x : obj => None) # (fun h : heap =>
         allobjat objat (fun x => None) h /\ refs (fun x => None) h)) m)
  := sdo (newtable).
Next Obligation.
nextvc.
exists empty.
split.
exists empty; exists empty.
intuition.
remove_empty.
apply splits_refl.
intros.
destruct H as [ h1 [ h2 [ H3 [ h3 [ h4 [ H4 [ N1 [ H8 H9 ] ] ] ] ] ] ] ].
destruct N1 as [ l [ N1 N2 ] ].
rewrite_clear.
splits_rewrite.
clear H3.
exists l.
intuition.
exists h3; exists empty.
intuition.
splits_refl_empty.
unfold allobjat.
intros.
inversion H.
unfold refs.
intuition.
inversion H.
destruct H as [ h10 [ h11 [ H12 [ H13 H14 ] ] ] ].
assert(emp h10 /\ emp h11).
apply splits_empty_empty; assumption.
unfold emp in H; destruct H.
rewrite_clear.
unfold points_to in H13.
assert(empty l0 = update_loc empty l0 k l0).
rewrite <- H13; trivial.
unfold empty, update_loc, modify_loc in H.
rewrite loc_eq_refl in H.
inversion H.
destruct H as [ A [ v H ] ].
unfold selects in H.
unfold empty in H.
inversion H.
Defined.

(* Lookup the value of a simulated object in the flyweight. *)
Program Definition Fgetdata (l : loc) : 
  STsep (fun i => exists o : obj,  objat l o i) obj
            (fun y i m => forall o : obj, objat l o i -> (i = m /\ y = Val o)) :=
  sdo (sread l).
Next Obligation.
destruct H0 as [ h0 [ h1 [ H3 [ H4 H5 ] ] ] ].
nextvc.
destruct H0 as [ h2 [ h3 [ H6 [ H7 H8 ] ] ] ].
assert(h0 = h2).
same_two_subheaps H3 H4 H9.
assumption.
rewrite <- H0 in H7.
f_equal.
eapply points_to_same.
apply H4.
apply H7.
Defined.

(* A type for the functional flyweight. *)
Record Flyweight : Type :=
  FlyweightCon {
    FlyTable : loc -> (obj -> option loc) -> heap -> Prop;
    FlyRefs : (obj -> option loc) -> heap -> Prop;
    FlyObjAt : loc -> obj -> heap -> Prop;
    FlyPf :  forall (h : heap) (l l' : loc) (o o' : obj) 
                 (f : obj -> option loc),
        (FlyObjAt l o h /\ FlyObjAt l' o' h /\ FlyRefs f h) -> 
          (l = l' <-> o = o');
  FlyNewchar : forall (hash : loc) (o : obj),
  STsep (fun i => exists f : (obj -> option loc),
        (FlyTable hash f # (fun h => allobjat FlyObjAt f h /\ FlyRefs f h)) i) loc
        (fun y i m => forall f : (obj -> option loc),
          ((FlyTable hash f # (fun h => allobjat FlyObjAt f h /\ FlyRefs f h)) i) ->
          exists l : loc, y = Val l /\ (forall l' : loc, f o = Some l' -> l = l') /\
          (FlyTable hash (updateF f o l) # 
            (fun h => allobjat FlyObjAt (updateF f o l) h /\
               FlyRefs (updateF f o l) h)) m);
  FlyGetdata : forall (l : loc),
  STsep (fun i => exists o : obj, FlyObjAt l o i) obj
            (fun y i m => forall o : obj, 
               (FlyObjAt l o i) -> 
               (i = m /\ y = Val o));
  FlyNew : STsep emp loc 
    (fun y i m => exists l : loc, y = Val l /\
       (FlyTable l (fun _ => None) # (fun h : heap =>
         allobjat FlyObjAt (fun _ => None) h /\ FlyRefs (fun _ => None) h)) m)
 }.

(* An implementation of the functional flyweight type. *)
Program Definition FlyweightImpl : Flyweight :=
   FlyweightCon (objat_lemma)
                (Fnewchar)
                (Fgetdata)
                (Fnew).

(* A type for a non-functional flyweight. *)
Record Flyweight2 : Type :=
  FlyweightCon2 {
    FlyTable2 : (obj -> option loc) -> heap -> Prop;
    FlyRefs2 : (obj -> option loc) -> heap -> Prop;
    FlyObjAt2 : loc -> obj -> heap -> Prop;
    FlyPf2 :  forall (h : heap) (l l' : loc) (o o' : obj) 
                 (f : obj -> option loc),
        (FlyObjAt2 l o h /\ FlyObjAt2 l' o' h /\ FlyRefs2 f h) -> 
          (l = l' <-> o = o');
  FlyNewchar2 : forall (o : obj),
  STsep (fun i => exists f : (obj -> option loc),
        (FlyTable2 f # (fun h => allobjat FlyObjAt2 f h /\ FlyRefs2 f h)) i) loc
        (fun y i m => forall f : (obj -> option loc),
          ((FlyTable2 f # (fun h => allobjat FlyObjAt2 f h /\ FlyRefs2 f h)) i) ->
          exists l : loc, y = Val l /\ (forall l' : loc, f o = Some l' -> l = l') /\
          (FlyTable2 (updateF f o l) # 
            (fun h => allobjat FlyObjAt2 (updateF f o l) h /\
               FlyRefs2 (updateF f o l) h)) m);
  FlyGetdata2 : forall (l : loc),
  STsep (fun i => exists o : obj, FlyObjAt2 l o i) obj
            (fun y i m => forall o : obj, 
               (FlyObjAt2 l o i) -> 
               (i = m /\ y = Val o))
 }.

(* A flyweight factory. *)
Program Definition makeFlyweight :
  STsep emp Flyweight2 (fun y i m => exists f : Flyweight2,
     y = Val f /\ (FlyTable2 f (fun _ => None) # (fun h : heap =>
         allobjat (FlyObjAt2 f) (fun _ => None) h /\ FlyRefs2 f (fun _ => None) h)) m) :=
  sdo(hash <-- Fnew; sret (FlyweightCon2 (objat_lemma)
                (Fnewchar hash)
                (Fgetdata))).
Next Obligation.
unfold emp in H.
rewrite H in *; clear H i.
econstructor.
split.
exists empty.
exists empty.
intuition.
splits_refl_empty.
unfold sbind_pre.
intuition.
exists empty; exists empty.
intuition.
splits_refl_empty.
unfold diff1 in H.
unfold sret_pre.
assert(emp empty); trivial.
generalize(H empty H0); clear H H0; intros.
assert(splits empty (empty::empty::nil)).
splits_refl_empty.
exists empty; exists h.
intuition.
splits_refl_empty.
intros.
destruct H as [ h1 [ h2 [ H1 [ h3 [ h4 [ H2 [ H3 [ H4 H5 ] ] ] ] ] ] ] ].
unfold this in H4, H5.
rewrite <- H4 in *; clear H4 h2.
rewrite <- H5 in *; clear H5 h4.
unfold sbind_post in H3.
splits_rewrite.
destruct H3.
destruct H as [ _ [ x [ h1 [ H1 H2 ] ] ] ].
unfold diff1, sret_pre, sret_post in H1, H2.
assert(emp empty); trivial.
generalize(H1 empty H); clear H1; intros.
generalize(H2 empty H); clear H2 H; intros.
assert(splits empty (empty::empty::nil)).
splits_refl_empty.
generalize(H0 empty H1); clear H1 H0; intros.
destruct H0 as [ h2 [ H1 [ l [ H2 H3 ] ] ] ].
splits_rewrite.
assert(splits h2 (empty::h2::nil)).
splits_refl_empty.
generalize(H h2 H0); clear H H0; intros.
destruct H as [ h1 [ H4 [ H5 H6 ] ] ].
rewrite <- H5 in *; clear H5 h1.
splits_rewrite.
inversion H2; clear H2.
rewrite_clear.
exists (FlyweightCon2 (FlyTable2:=table l) (FlyRefs2:=refs) objat_lemma
       (Fnewchar l) Fgetdata).
intuition.
destruct H as [ e [ H1 H2 ] ].
unfold diff1 in H2.
assert(emp empty); trivial.
generalize(H2 empty H); clear H H2; intros.
assert(splits empty (empty::empty::nil)).
splits_refl_empty.
generalize(H empty H0); clear H H0; intros.
destruct H as [ h4 [ H2 [ l [ H3 H4 ] ] ] ].
inversion H3.
Qed.

End Flyweight.