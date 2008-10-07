Require Import DisjointUnion.
Require Import List.
Require Import MemModel.
Require Import ST.
Require Import Separation.
Require Import STsep.
Require Import Assumptions.

Set Implicit Arguments.
Unset Strict Implicit.
Open Local Scope stsep_scope.

Parameter null : loc.
Parameter null_never_points : forall (A : Type) (v : A) (h : heap), ((null --> v) h) -> False.

(*
(* copied from MemModel.v *)
Record dynamic : Type := dyn {type_of : Type; val_of : type_of}.

(* The heap is just a map from locations to maybe dynamics. *)
Definition heap := loc -> option dynamic.
Definition empty : heap := fun _ => None.

Definition hprop := heap -> Prop.

(* copied from Separation.v *)
Definition emp : hprop := fun h => h = empty.

Definition splits (h : heap) (hs : list heap) : Prop := 
   exists pf : disjoint hs, h = union hs pf.
(* disjoint and union is defined in DisjointUnion.v *)

Definition star1 (p1 p2 : hprop) : hprop :=
   fun h => exists h1, exists h2, splits h (h1::h2::nil) /\ p1 h1 /\ p2 h2.              
Definition this (m : heap) : hprop :=
   fun h => m = h.

Definition points_to (l : loc) (A : Type) (v : A) : hprop :=
   fun h => h = update_loc empty l v.

Notation "p1 '#' p2"   := (star1 p1 p2)               (at level 50).
Notation "l '-->' v"   := (points_to l v)             (at level 50).

(* copied from MemModel.v *)
Definition selects (l : loc) (A : Type) (val : A) (h : heap) : Prop :=
   h l = Some (dyn A val).

Definition valid_loc (l : loc) (h : heap) : Prop :=
   exists A : Type, exists v : A, selects l v h.

(* copied from ST.v *)
Definition pre := heap -> Prop
Definition post (A : Type) := ans A -> heap -> heap -> Prop.
Definition nopre : pre := fun h => True.

Parameter ST : forall (A: Type), pre -> post A -> Type.

(* defines the non-separation logic version of write. *)
Definition write_post(A:Type)(r:loc)(v:A) :=
  fun y i m => y = Val tt /\ m = update_loc i r v.

(* added as an axiom. *)
Parameter write : 
  forall (A : Type) (r : loc) (v : A), ST (valid_loc r) (write_post r v).

(* copied from STsep.v *)
(* defines the separation logic version of write, in terms of the
   non-separation logic version. *)
Definition swrite_pre (l : loc) : pre :=
    fun i => exists b, exists y : b, (l --> y) i.

Definition swrite_post (A : Type) (l : loc) (v : A) : post unit :=
    fun y i m => (l --> v) m /\ y = Val tt. 

Program Definition 
    swrite (A : Type) (l : loc) (v : A) : 
        STsep (swrite_pre l) unit (swrite_post A l v) :=

    do (write l v) (conj _ _).

Computations defined in STsep.v
sret, sbind, sdo, sread, snew, sfree, swrite, sthrow, stry, scond, case_sum
*)

Ltac splits_eqto_subheap H :=
  let n1 := fresh "tmpH" in
  let n2 := fresh "tmpPF" in
  let n3 := fresh "tmpH" in
    generalize H; intros n1; repeat(remove_empty_in n1; clear n1; intros n1);
    destruct n1 as [ n2 n3 ]; simpl in n3; clear n2 H; generalize n3; 
    clear n3; intros H.

Lemma test_splits_eqto_subheap : 
  forall (i h : heap), splits i (empty :: h :: empty :: nil) -> i = h.
Proof.
intros i h H.
splits_eqto_subheap H.
auto.
Qed.

Ltac splits_refl_empty := solve[repeat(remove_empty); apply splits_refl].

Lemma test_splits_refl_empty :
  forall (h : heap), splits h (empty :: empty :: h :: empty :: empty :: nil).
Proof.
intros.
splits_refl_empty.
Qed.

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

Ltac same_two_subheaps2 H1 H2 H3 :=
  same_two_subheaps H1 H2 H3; destruct H1; destruct H2; destruct H3.

Lemma test_two_subheaps :
  forall (i h1 h2 h3 h4 : heap) (l : loc) (v v' : nat), 
    splits i (h1::h2::nil) -> (l --> v) h1 ->
    splits i (h3::h4::nil) -> (l --> v') h3 ->
      h1 = h3.
Proof.
intros.
same_two_subheaps H1 H2 H3.
auto.
Qed.

Inductive LL (A : Type) (y : loc) (l : list A) (i : heap) : Prop :=
  | empLL : l = nil /\ y = null /\ emp i -> LL y l i
  | consLL : (exists a : A, exists l' : list A, l = a::l' /\
                 (exists s' : loc, ((y --> (a, s')) # LL s' l') i)) ->
                      LL y l i. 

Program Definition new (A : Type) : 
  STsep emp 
        loc 
        (fun r i m => exists l : loc, r = (Val l) /\
           (exists y : loc, ((l --> y) # (LL y (@nil A))) m))
  :=
  sdo (snew null).
Next Obligation.
nextvc.
exists x.
split; [ trivial | idtac ].
exists null; exists h; exists empty.
split; [ splits_refl_empty | idtac ].
split; [ assumption | apply empLL; auto ].
Qed.

Program Definition push (A : Type) (s : loc) (x : A) :
  STsep (fun i => exists l : list A, exists y : loc, ((s --> y) # LL y l) i)
        unit
        (fun r i m => r = Val tt /\
           forall l : list A,  (exists y : loc, ((s --> y) # LL y l) i) -> 
             exists y : loc, ((s --> y) # LL y (x::l)) m)
  :=
  sdo (y <-- !! s ;
       z <-- snew (x, y:loc) ;
       s ::= z).
Next Obligation.
destruct H1 as [x0 [x1 [H2 [H3 H4]]]].
nextvc.
nextvc.
exists x0.
split; [ eauto | idtac ]. 
splits_rewrite_in H2 H1.
splits_join_in H6 (0::1::1::nil).
exists (union (x1::t::nil) pf0).
split.
  apply (splits_permute H7); PermutProve.
intros j0 j1 H8 H9.
split; auto.
intros l [y0 [y1 [H10 [H11 H12]]]].
exists x2; exists j1.
exists (union (x1::t::nil) pf0).
repeat split; auto.
apply consLL.
exists x. exists l. 
split; auto.
exists H0; exists t; exists x1; split.
apply splits_commute; unfold splits; exists pf0; auto.
split; try assumption.
destruct H12.
same_two_subheaps2 H11 H12 H14.
assumption.
Qed.

Program Definition pop (A : Type) (s : loc) :
  STsep (fun i => exists x : A, exists l : list A, exists y : loc, 
           ((s --> y) # LL y (x::l)) i)
        A
        (fun r i m => forall x : A, forall l : list A,
           ((exists y : loc, ((s --> y) # LL y (x::l)) i) ->
            (exists y : loc, ((s --> y) # LL y l) m) /\ r = (Val x)))
  :=
  sdo (sbind (!! s) (fun y : loc =>
       sbind (!! y) (fun z : A * loc =>
       sbind (s ::= (snd z)) (fun n : unit =>
       sbind (sfree y) (fun n' : unit =>
       sret (fst z)))))).
Next Obligation.
destruct H2 as [ x0 [ x1 [ H3 [ H4 H5 ]]]].
destruct H5 as [ H5 | H5 ].
destruct H5 as [? _]; discriminate.
destruct H5 as [ x2 [ x3 [ H5 [ H6 H7 ]]]].
injection H5; intros t1 t2; destruct t1; destruct t2; clear H5.
destruct H7 as [ x4 [ x5 [ H8 [ H9 H10 ]]]].
splits_rewrite_in H8 H3.
splits_join_in H2 (1::0::1::nil).
nextvc.
exists x4; exists (union(x0::x5::nil) pf0).
split.
  apply (splits_commute H5).
  unfold nopre; eauto.
nextvc.
exists x0.
  split; eauto.
  exists x1.
  split; auto.
intros j j1 H11 H12.
nextvc.
  exists x4. 
  splits_rewrite_in H8 H11.
  splits_join_in H7 (1::0::1::nil).
  exists (union (j1::x5::nil) pf1).
  split; eauto.
  split; auto.
nextvc.
destruct H14 as [y0 [y1 [H15 [H16 H17]]]].
same_two_subheaps2 H15 H16 H18.
destruct H17 as [H17 | H17].
   destruct H17 as [? _]; discriminate.

destruct H17 as [a [l' [H18 [s' [y0 [y1 [H19 [H20 H21]]]]]]]].
injection H18; intros t1 t2; destruct t1; destruct t2; clear H18.

same_two_subheaps H19 H20 H22. destruct H22; destruct H19.
injection H20; intros t1 t2; destruct t1; destruct t2.
exists H6.
exists j1.
exists x5.
split; auto.
exists pf1.
auto.
destruct H14 as [ h6 [ h7 [ H15 [ H16 H17 ] ] ] ].
same_two_subheaps2 H15 H16 H18.
destruct H17 as [ [ H18 H19 ] | [ a [ l' [ H18 [ s' [ h8 [ h9 [ H21 [ H22 H23 ] ] ] ] ] ] ] ] ].
discriminate.
injection H18; intros t1 t2; destruct t1; destruct t2.
same_two_subheaps H21 H22 H24.
injection H22; intros H25 H26; rewrite H26.
trivial.
Qed.

Definition del_loop_pre (A : Type) (y : loc) : pre :=
  (fun i => exists l : list A, LL y l i).

Definition del_loop_post (A : Type) (y : loc) : post unit :=
  (fun r i m => r = Val tt /\ emp m).

Definition del_loop_spec (A : Type) (y : loc) : Type :=
  STsep (del_loop_pre A y) unit (del_loop_post A y).

Program Definition del_loop 
    (A : Type) (y : loc) 
    (del : forall (A : Type) (y : loc), del_loop_spec A y)
    : del_loop_spec A y :=

    match loc_eq null y with
      | left _ => sdo (sret tt)
      | right _ => 
          sdo (t <-- (!! y); sfree y;; del A ((snd (t : A*loc))))
    end.

Next Obligation.
nextvc.
clear Heq_anonymous del; destruct wildcard'.
unfold del_loop_post.
destruct H as [ l [ H | H ] ]; try tauto.
destruct H as [ a [ l' [ H1 [ H2 [ h1 [ _ [ _ [ H4 _ ]]]]]]]].
contradiction (null_never_points H4).
Defined.

Next Obligation.
destruct H as [ l [ [ H1 [ H2 H3 ] ] | [ a [ l' [ H1 [ s [ h1 [ h2 [ H2 [ H3 H4 ] ] ] ] ] ] ] ] ] ].
contradiction (wildcard'); auto.
nextvc.
exists h1; exists h2.
split; [ exists (prod A loc); exists (a, s); assumption | idtac ].
split; [ apply splits_commute; assumption | idtac ].
exists empty.
split; [ exists h2; exists empty | idtac ].
split; [ remove_empty; apply splits_refl | idtac ].
split; [ idtac | trivial ].
exists l'; assumption.
intros y0 m H5.
destruct H5 as [ h3 [ h4 [ H6 [ h5 [ h6 [ H7 [ H8 [ H9 H10 ] ] ] ] ] ] ] ].
destruct H9; destruct H10.
splits_eqto_subheap H7.
rewrite H7. trivial.
Qed.

Program Definition del (A : Type) (s : loc) : 
  STsep (fun i => exists l : list A, exists y : loc, ((s --> y) # LL y l) i)
        unit
        (fun r i m => r = Val tt /\ emp m)
 := 
  sdo (y <-- (!! s); sfree s;;
         sfix (fun del x => del_loop (fst x) (snd x) (fun A y => del (A, y)))
  (A, y)).

Next Obligation.
destruct H1 as [ h1 [ h2 [ H2 [ H3 H4 ] ] ] ].
nextvc.
exists h1; exists h2.
split; [ exists loc; exists H0; assumption | idtac ].
split; [ apply splits_commute; assumption | idtac ].
exists empty.
split.
  exists h2; exists empty.
  split; [ remove_empty; apply splits_refl | idtac ].
  split; try trivial.
  exists H; assumption.
intros y m H5.
destruct H5 as [ h3 [ _ [ _ [ h5 [ h6 [ H8 [ H9 [ _ H11 ] ] ] ] ] ] ] ]. 
destruct H11; splits_eqto_subheap H8.
rewrite H8; apply H9.
Qed. 

Record stack (A : Type) : Type :=
   Stack {stinv : forall (x:loc) (l:list A), hprop;
          stinvpre : forall (x : loc) (l1 l2 : list A) (h : heap),
                        stinv x l1 h -> stinv x l2 h -> l1 = l2;
          stnew : STsep emp loc (fun y i m => exists x, y = Val x /\ stinv x nil m); 
          stpush : forall (x:loc) (v:A), 
                   STsep (fun i => exists l, stinv x l i) unit  
                         (fun y i m => y = Val tt /\
                              forall l, stinv x l i -> stinv x (v::l) m);
          stpop : forall (x:loc),
                   STsep (fun i => exists v, exists l, stinv x (v::l) i) A
                         (fun y i m => forall v l, stinv x (v::l) i -> 
                                          stinv x l m /\ y = Val v);
          stdel : forall (x:loc),
                   STsep (fun i => exists l, stinv x l i) unit
                         (fun y i m => y = Val tt /\ emp m)}.

Lemma tmpinv : forall (A : Type) (x : loc) (l1 l2 : list A) (h : heap),
                  LL x l1 h -> LL x l2 h -> l1 = l2.
Proof.
intros A x l1.
generalize x.
induction l1.
  intros x0 l2 h H1 H2.
  destruct H1 as [ [ H6 [ H7 H8 ] ] | H6 ].
    destruct H2 as [ [ H13 [ H14 H15 ] ] | H16 ].
      symmetry; assumption.
    destruct H16 as [ a [ l' [ H17 [ s' [ h3 [ h4 [ H18 [ H19 H20 ] ] ] ] ] ] ] ].
    unfold emp in H8; rewrite H8 in H18.
    destruct (splits_empty_emptys H18) as [ H21 H22 ].
    unfold emp in H21; rewrite H21 in H19.
    unfold points_to in H19.
    assert(empty x0 = (update_loc empty x0 (a, s')) x0) as H23.
    rewrite <- H19; trivial.
    unfold update_loc in H23; unfold modify_loc in H23; unfold empty in H23.
    generalize (loc_eq_refl x0); intros H24.
    rewrite H24 in H23.
    discriminate H23.
  destruct H6 as [ a [ l' [ H7 H8 ] ] ].
  discriminate H7.
intros x0 l2 h H1 H2.
destruct H1 as [ [ H3 [ H4 H5 ] ] | H3 ].
  discriminate H3.
destruct H3 as [ a0 [ l' [ H4 [ s' [ h1 [ h2 [ H5 [ H6 H7 ] ] ] ] ] ] ] ].
destruct H2 as [ [ H8 [ H9 H10 ] ] | H8 ].
  unfold emp in H10; rewrite H10 in H5.
  destruct (splits_empty_emptys H5) as [ H11 H12 ].
  unfold emp in H11; rewrite H11 in H6.
  unfold points_to in H6.
  assert(empty x0 = (update_loc empty x0 (a0, s')) x0) as H13.
  rewrite <- H6; trivial.
  unfold update_loc in H13; unfold modify_loc in H13; unfold empty in H13.
  generalize (loc_eq_refl x0); intros H14.
  rewrite H14 in H13.
  discriminate H13.
destruct H8 as [ a' [ l'' [ H9 [ s'' [ h3 [ h4 [ H10 [ H11 H12 ] ] ] ] ] ] ] ].
same_two_subheaps H10 H11 H13; injection H11; intros H14 H15.
destruct H13; destruct H10; destruct H14; destruct H15; clear H11.
rewrite H4; rewrite H9.
injection H4; intros H13 H14; destruct H13; destruct H14.
generalize (IHl1 s' l'' h2 H7 H12); intros H13; destruct H13.
trivial.
Qed.

Lemma tmpinv' : forall (A : Type) (x : loc) (l1 l2 : list A) (h : heap),
                  (exists y : loc, ((x --> y) # (LL y l1)) h) -> 
                  (exists y : loc, ((x --> y) # (LL y l2)) h) ->
                     l1 = l2.
Proof.
intros A x l1 l2 h H1 H2.
destruct H1 as [ y1 [ h1 [ h2 [ H3 [ H4 H5 ] ] ] ] ].
destruct H2 as [ y2 [ h3 [ h4 [ H6 [ H7 H8 ] ] ] ] ].
same_two_subheaps2 H6 H7 H9.
apply (tmpinv H5 H8).
Qed.

Program Definition stackImpl (A : Type) : stack A :=
   Stack (stinv:=(fun x l m => exists y : loc, ((x --> y) # (LL y l)) m))
         (tmpinv' (A:=A))
         (new A)
         (push (A:=A))
         (pop A)
         (del A).

Program Definition
client (S: stack nat) :
  STsep emp nat (fun n i m => emp m /\ n = Val 4) :=
  sdo (s <-- stnew S;
       stpush S s 4;;
       n <-- stpop S s;
       stdel S s;;
       sret n).
Next Obligation.
nextvc.
exists empty.
split; try trivial.
exists empty.
split; [ remove_empty; apply splits_refl | idtac ].
intros j j1 H1.
remove_empty_in H1; intros H2; destruct H2 as [ pf1 H3 ]; simpl in H3.
destruct H3; clear pf1.
split; [ idtac | intros e [ ? [ t ] ]; discriminate ].
intros x0 [ x1 [ H3 H4 ]].
injection H3; intros T; destruct T.
clear H3 H1 i.
nextvc.
exists j.
split; [ eauto | idtac ].
exists empty.
split; [ remove_empty; apply splits_refl | idtac ].
intros j0 j1 H5.
splits_eqto_subheap H5; destruct H5. 
split; [ idtac | intros e [ t ]; discriminate ].
intros x [ _ H8 ].
generalize (H8 nil H4); intros H9; clear H8 j H4.
nextvc.
exists j0.
split. eauto.
exists empty.
split; [ remove_empty; apply splits_refl | idtac ].
intros j j1 H10. 
splits_eqto_subheap H10; destruct H10.
split; [ idtac | intros e H18; destruct (H18 4 nil H9) as [ T ]; discriminate ].
clear x. intros x H12.
destruct (H12 4 nil H9) as [H13 H14]. 
injection H14; intros T; symmetry in T; destruct T.
clear H14 H12.
nextvc.
exists j.
split; [ eauto | idtac ].
exists empty.
split; [ remove_empty; apply splits_refl | idtac ].
intros j1 j2 H10. 
splits_eqto_subheap H10; destruct H10.
clear H9 j0.
split; [ idtac | intros e [ t ]; discriminate ].
intros x H15.
nextvc.
destruct H15 as [ H16 H17 ].
trivial.
Defined.

Program Definition C1_init (S : stack nat) (x : loc) :  
  STsep emp loc (fun r i m => exists y : loc, r = (Val y) /\ (y --> x) m) :=
  sdo (snew x).
Next Obligation.
nextvc.
exists x0.
split; trivial.
Defined.

Program Definition C1_op (S : stack nat) (x : loc) :
  STsep (fun i => exists y : loc, exists l : list nat,
                    ((x --> y) # stinv S y l) i)
        unit
        (fun r i m => forall (y : loc) (l : list nat),
                        ((x --> y) # stinv S y l) i ->
                        ((x --> y) # stinv S y (2::l)) m /\ r = (Val tt)) :=
  sdo (s <-- (!! x); stpush S s 2).
Next Obligation.
destruct H1 as [ h1 [ h2 [ H2 [ H3 H4 ] ] ] ].
nextvc.
exists h1.
split.
  exists h2; exists h1.
  split; [ apply splits_commute; assumption | idtac ].
  split; [ exists H0 | idtac ]; trivial.
intros y m H5 y0 l H13.
destruct H5 as [ h3 [ h4 [ H6 [ h5 [ h6 [ H7 [ [ H9 H10 ] H8 ] ] ] ] ] ] ].
destruct H8 as [ H11 H12 ]; destruct H11; destruct H12.
generalize (splits_commute H6); clear H6; intros H6.
destruct (splits_same_tail H2 H6) as [ pf1 [ pf2 H14 ] ]; simpl in H14; clear pf1 pf2 H6; destruct H14.
split; [ idtac | trivial ].
exists h1; exists h5.
split; [ apply splits_commute; assumption | idtac ].
destruct H13 as [ h6 [ h7 [ H14 [ H15 H16 ] ] ] ].
same_two_subheaps2 H14 H15 H17.
split; [ assumption | idtac ].
apply H10; assumption.
Defined.

Program Definition C1_del (S : stack nat) (x : loc) :
  STsep (fun i => exists y : loc, (x --> y) i) unit
        (fun r i m => forall y : loc, (x --> y) i -> emp m /\ r = (Val tt)) :=
  sdo (sfree x).
Next Obligation.
nextvc.
exists empty; exists i.
split; [ exists loc; exists H; assumption | idtac ].
split; [ remove_empty; apply splits_refl | idtac ].
intros y H1.
split; trivial.
Defined.

Record c1 (S : stack nat) : Type :=
   C1 {c1inv : forall (x:loc) (y:loc), hprop;
          c1init : forall (x : loc),
                  STsep emp loc (fun r i m => exists y, r = Val y /\ c1inv y x m);
          c1op : forall (x : loc),
                  STsep (fun i => exists y : loc, exists l : list nat,
                           (c1inv x y # stinv S y l) i) unit
                        (fun r i m => forall (y : loc) (l : list nat),
                           (c1inv x y # stinv S y l) i ->
                           (c1inv x y # stinv S y (2::l)) m /\ r = Val tt);
          c1del : forall (x : loc),
                  STsep (fun i => exists y : loc, c1inv x y i) unit
                        (fun r i m => forall y : loc, c1inv x y i -> 
                                         emp m /\ r = Val tt)}.

Program Definition c1Impl (S : stack nat) : c1 S :=
   C1 (c1inv:= (fun x y m => (x --> y) m))
      (C1_init S)
      (C1_op S)
      (C1_del S).

Program Definition C2_init (S : stack nat) (x : loc) :  
  STsep emp loc (fun r i m => exists y : loc, r = (Val y) /\ (y --> x) m) :=
  sdo (snew x).
Next Obligation.
nextvc.
exists x0.
split; trivial.
Defined.

Program Definition C2_op (S : stack nat) (x : loc) :
  STsep (fun i => 
    exists y : loc * loc, exists v : nat, exists l : list nat,
      ((x --> y) # stinv S (fst y) (v::l) # stinv S (snd y) (v::l)) i)
        nat
        (fun r i m => 
    forall (y : loc * loc) (v : nat) (l : list nat),
       ((x --> y) # stinv S (fst y) (v::l) # stinv S (snd y) (v::l)) i ->
       ((x --> y) # stinv S (fst y) l # stinv S (snd y) l) m /\ r = (Val v)) :=
  sdo (s <-- (!! x); stpop S (fst s);; stpop S (snd s)).
Next Obligation.


Program Definition C2_op (S : stack nat) (x : loc) :
  STsep (fun i => exists y : loc, exists v : nat, exists l : list nat,
                    ((x --> y) # stinv S y (v::l)) i)
        nat
        (fun r i m => forall (y : loc) (v : nat) (l : list nat),
                        ((x --> y) # stinv S y (v::l)) i ->
                        ((x --> y) # stinv S y l) m /\ r = (Val v)) :=
  sdo (s <-- (!! x); stpop S s).
Next Obligation.
destruct H2 as [ h1 [ h2 [ H2 [ H3 H4 ] ] ] ].
nextvc.
exists h1.
split.
  exists h2; exists h1.
  split; [ apply splits_commute; assumption | idtac ].
  split; [ exists H0; exists H1 | idtac ]; trivial.
intros y m H5 y0 v l H6.
destruct H5 as [ h3 [ h4 [ H7 [ h5 [ h6 [ H8 [ H9 H10 ] ] ] ] ] ] ].
destruct H10 as [ H11 H12 ]; destruct H11; destruct H12.
destruct H6 as [ h7 [ h8 [ H13 [ H14 H15 ] ] ] ].
apply splits_commute in H2.
generalize (splits_same_head H2 H7).
intros. rewrite H5 in *; clear H5 h2.
clear H2.
apply splits_commute in H7.
same_two_subheaps H13 H14 H16.
rewrite H16 in *; clear H16 h3.
rewrite H13 in *; clear H13 h1.
rewrite H14 in *; clear H14 H.
generalize (H9 v l H15); intros H16.
destruct H16.
intuition.
exists h7; exists h5.
intuition.
apply splits_commute; assumption.
Defined.

(*
generalize (stinvpre H4 H15); intros H17.
injection H17; intros H18 H19.
destruct H18; destruct H19.
destruct H16 as [ H18 H19 ].
split; [ idtac | assumption ].
exists h1; exists h5.
split; [ apply splits_commute; assumption | idtac ].
split; assumption.
Defined.
*)

Program Definition C2_del (S : stack nat) (x : loc) :
  STsep (fun i => exists y : loc, (x --> y) i) unit
        (fun r i m => forall y : loc, (x --> y) i -> emp m /\ r = (Val tt)) :=
  sdo (sfree x).
Next Obligation.
nextvc.
exists empty; exists i.
split; [ exists loc; exists H; assumption | idtac ].
split; [ remove_empty; apply splits_refl | idtac ].
intros y H1.
split; trivial.
Defined.

Record c2 (S : stack nat) : Type :=
   C2 {c2inv : forall (x:loc) (y:loc), hprop;
          c2init : forall (x : loc),
                  STsep emp loc (fun r i m => exists y, r = Val y /\ c2inv y x m);
          c2op : forall (x : loc),
                  STsep (fun i => exists y : loc, exists v : nat, exists l : list nat,
                           (c2inv x y # stinv S y (v::l)) i) nat
                        (fun r i m => forall (y : loc) (v : nat) (l : list nat),
                           (c2inv x y # stinv S y (v::l)) i ->
                           (c2inv x y # stinv S y (l)) m /\ r = Val v);
          c2del : forall (x : loc),
                  STsep (fun i => exists y : loc, c2inv x y i) unit
                        (fun r i m => forall y : loc, c2inv x y i -> 
                                         emp m /\ r = Val tt)}.

Program Definition c2Impl (S : stack nat) : c2 S :=
   C2 (c2inv:= (fun x y m => (x --> y) m))
      (C2_init S)
      (C2_op S)
      (C2_del S).

Record m1 : Type :=
  M1 { st1 : stack nat;
       impl1 : c1 st1 }.

Record m2 : Type :=
  M2 { st2 : stack nat;
       impl2 : c2 st2 }.

Definition f1 : m1 := M1 (c1Impl (stackImpl nat)).
Definition f2 : m2 := M2 (c2Impl (stackImpl nat)).

Program Definition m3 (S : stack nat) (f1 : m1) (f2 : m2) :
  STsep (fun i => (st1 f1) = S /\ (st2 f2) = S /\ emp i) nat (fun r i m => emp m /\ r = Val 2) :=
  sdo (s <-- stnew S; 
       c1 <-- c1init (impl1 f1) s;
       c2 <-- c2init (impl2 f2) s;
       c1op (impl1 f1) c1;;
       n <-- c2op (impl2 f2) c2;
       c1del (impl1 f1) c1;;
       c2del (impl2 f2) c2;;
       stdel S s;;
       sret n).
Next Obligation.
nextvc.
exists empty.
split; [ trivial | idtac ].
exists empty.
split; [ remove_empty; apply splits_refl | idtac ].
intros j j1 H1.
split; [ idtac | intros e [ x [ H2 H3 ] ]; discriminate ].
intros x H2.
destruct H2 as [ x0 [ H3 H4 ] ].
injection H3; intros H5; destruct H5; clear H3.
nextvc.
exists empty.
split; [ trivial | idtac ].
exists j1.
split; [ remove_empty; apply splits_refl | idtac ].
intros j0 j2 H5.
split; [ idtac | intros e [ y [ H6 H7 ] ]; discriminate ].
intros x0 H8.
destruct H8 as [ y [ H9 H10 ] ].
injection H9; intros H11; destruct H11; clear H9.
nextvc.
exists empty.
split; [ trivial | idtac ].
exists j0.
split; [ remove_empty; apply splits_refl | idtac ].
intros j3 j4 H11.
split; [ idtac | intros e [ y [ H12 H13 ] ]; discriminate ].
intros x1 H14.
destruct H14 as [ y [ H15 H16 ] ].
injection H15; intros H17; destruct H17; clear H15.
nextvc.
exists j0.
split.
  exists x; exists (nil : list nat).
  exists j2; exists j1.
  split; [ assumption | split; assumption ].
exists j4.
split; [ apply splits_commute; assumption | idtac ].
intros j5 j6 H17.
split.
  intros x2 H18.
  assert((c1inv (impl1 f3) x0 x # stinv (st1 f3) x nil) j0) as H19.
  exists j2; exists j1.
  split; [ assumption | split; assumption ].
  destruct (H18 x nil H19) as [ H20 H21 ].
  destruct H20 as [ j7 [ j8 [ H22 [ H23 H24 ] ] ] ].
  nextvc.
  rewrite <- H0 in H24.
  splits_rewrite_in H22 H17.
  splits_join_in H (0::1::1::nil).
  exists (union (j8::j4::nil) pf0).
  split; [ exists x; exists 2; exists (nil : list nat) | idtac ].
    exists j4; exists j8.
    split; [ idtac | split; assumption ].
    apply splits_commute; exists pf0; trivial.
  exists j7.
  split; [ assumption | idtac ].
  intros j9 j10 H25.
  split.
    intros x3 H26.
    assert((c2inv (impl2 f4) x1 x # stinv (st2 f4) x (2::nil)) (union (j8::j4::nil) pf0)) as H27.
      exists j4; exists j8.
      split; [ idtac | split; assumption ].
      apply splits_commute; exists pf0; trivial.
    destruct (H26 x 2 (nil : list nat) H27) as [ H28 H29 ].
    destruct H28 as [ j11 [ j12 [ H30 [ H31 H32 ] ] ] ].
    nextvc.
    exists j7.
    split; [ exists x; assumption | idtac ].
    exists j10.
    split; [ apply splits_commute; assumption | idtac ].
    intros j13 j14 H33.
    split.
      intros x4 H34.
      destruct (H34 x H23) as [ H35 H36 ].
      nextvc.
      exists j11.
      split; [ exists x; assumption | idtac ].
      exists j12.
      split; [ assumption | idtac ].
      intros j15 j16 H37.
      split.
        intros x5 H38.
        destruct (H38 x H31) as [ H39 H40 ].
        rewrite H39 in H37.
        nextvc.
        exists j12.
        rewrite H0 in H32.
        split; [ exists (nil : list nat); assumption | idtac ].
        exists empty.
        split; [ remove_empty; apply splits_refl | idtac ].
        intros j17 j18 H41.
        splits_eqto_subheap H41.
        rewrite H41.
        split; [ idtac | intros e [ H42 H43 ]; discriminate ].
        intros x6 H44.
        nextvc.
        destruct H44 as [ H45 H46 ]; trivial.
      intros e H47.
      destruct (H47 x H31) as [ H48 H49 ]; discriminate.
    intros e H50.
    destruct (H50 x H23) as [ H51 H52 ]; discriminate.
  intros e H53.
  assert((c2inv (impl2 f4) x1 x # stinv (st2 f4) x (2::nil)) (union (j8::j4::nil) pf0)) as H54.
    exists j4; exists j8.
    split; [ idtac | split; assumption ].
    apply splits_commute; exists pf0; trivial.
  destruct (H53 x 2 (nil : list nat) H54) as [ H55 H56 ]; discriminate.
intros e H57.
assert((c1inv (impl1 f3) x0 x # stinv (st1 f3) x nil) j0) as H58.
exists j2; exists j1.
split; [ assumption | split; assumption ].
destruct (H57 x nil H58) as [ H59 H60 ].
discriminate.
Defined.

Program Definition f3 : STsep emp nat (fun r i m => emp m /\ r = Val 2) :=
  sdo (m3 (stackImpl nat) f1 f2).
Next Obligation.
exists empty.
rewrite H.
split.
exists empty; exists empty.
split; [ remove_empty; apply splits_refl | idtac ].
split; trivial.
split; trivial.
split; trivial.
intros y m H1.
destruct H1 as [ h1 [ h2 [ H2 [ h3 [ h4 [ H3 [ H4 H5 ] ] ] ] ] ] ].
destruct H5 as [ H6 H7 ].
destruct H6; destruct H7.
splits_eqto_subheap H3.
rewrite H3.
assumption.
Defined.

(** * Sharing of abstracted types%\label{sec:coq-sharetype}% *)

Record t1 : Type :=
  T1 { t1b : Type;
       t1c : STsep emp t1b (fun r i m => emp m /\ exists t : t1b, r = (Val t)) }.

Record t2 : Type :=
  T2 { t2b : Type;
       t2c : forall n : t2b, STsep emp unit (fun r i m => emp m /\ r = Val tt) }.

Definition coerce (A B : Type) : (A = B) -> A -> B.
intros; destruct H; assumption.
Qed.

Program Definition p3 (p1 : t1) (p2 : t2) (pf : t1b p1 = t2b p2):
  STsep (fun i => emp i) unit (fun r i m => emp m /\ r = Val tt) :=
  sdo (n <-- t1c p1; t2c (coerce pf n)).
Next Obligation.
nextvc.
exists empty.
split; [ trivial | idtac ].
exists empty.
split; [ remove_empty; apply splits_refl | idtac].
intros j j1 H1.
splits_eqto_subheap H1.
split.
  intros x [ H2 H2' ].
  exists j.
  split; [ exists empty; exists j | idtac ].
    split; [ remove_empty; apply splits_refl | split; trivial ].
  intros y m H3.
  destruct H3 as [ h1 [ h2 [ H4 [ H5 [ h3 [ H6 [ [ H7 H7' ] H8 ] ] ] ] ] ] ].
  destruct H1; rewrite H7 in H6.
  splits_eqto_subheap H6.
  destruct H6.
  destruct H8.
  rewrite <- H0.
  split; trivial.
intros e [ H2 [ t H3 ] ].
discriminate H3.
Defined.

Check coerce.
Check p3.  

(*

Program Definition p3' (p1 : t1) (p2 : t2) :
  STsep (fun i => emp i /\ t1b p1 = t2b p2) unit (fun r i m => emp m /\ r = Val tt) :=
  sdo (n <-- t1c p1; t2c (coerce (A:=t1b p1) (B:=t2b p2) _ n)) _.
Next Obligation.

*)
