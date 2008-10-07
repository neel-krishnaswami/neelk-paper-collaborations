(*****************************************)
(* Signatures for the monadic operations *)
(* in the small footprint style          *)
(*****************************************)

Require Import Assumptions.
Require Import ProofIrrelevance.
Require Import BasicTactics.
Require Import MemModel.
Require Import List.
Require Import DisjointUnion.
Require Import ST.
Require Import Separation.

Definition pre := hprop.
Definition post (A : Type) := ans A -> hhprop.

Definition STsep (p : pre) (A : Type) (q : post A) : Type :=
   ST (p # nopre) (fun x => p --o q x).


Definition sret_pre : pre := emp.

Definition sret_post (A : Type) (x : A) : post A :=
   fun y i m => i = m /\ y = Val x.
  
Program Definition 
    sret (A : Type) (x : A) : STsep sret_pre A (sret_post A x) :=
  do (ret x) _.

Next Obligation.
unfold sret_post.
avcsimps.
unfold diff1 in |- *.
avcsimps.
exists i1.
 tauto.
Defined.

Implicit Arguments sret [A].

(***********************)
(**** monadic bind *****)
(***********************)

(*
Record sbind_pre (A : Type) (p1 : pre) (q1 : post A) (p2 : A -> pre) (i : heap) : Prop :=
  Sbind_pre { _ : (p1 # nopre) i; _ : forall x h, (p1 --o q1 (Val x)) i h -> (p2 x # nopre) h}.
*)

Definition sbind_pre (A : Type) (p1 : pre) (q1 : post A) (p2 : A -> pre) : pre :=
      (fun i => (p1 # nopre) i /\ forall x h, (p1 --o q1 (Val x)) i h -> (p2 x # nopre) h). 

Definition sbind_post (A B : Type) (p1 : pre) (q1 : post A) (p2 : A -> pre) (q2 : A -> post B) : post B :=
      (fun y i m => (p1 # nopre) i /\ 
           (exists x, exists h, (p1 --o q1 (Val x)) i h /\ (p2 x --o q2 x y) h m) \/
           (exists e, y = Exn e /\ (p1 --o q1 (Exn e)) i m)).

Program Definition 
    sbind (A B : Type)
          (p1 : pre)
          (q1 : post A)
          (e1 : STsep p1 A q1)
          (p2 : A -> pre)
          (q2 : A -> post B)
          (e2 : forall x : A, STsep (p2 x) B (q2 x)) 

      : STsep (sbind_pre A p1 q1 p2) B (sbind_post A B p1 q1 p2 q2) :=

    do (bind e1 e2) (conj _ _).

Next Obligation.
destruct H.
destruct H.
destruct H.
destruct H0.
clear H1.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H2.
clear H3.
unfold bind_pre in |- *.
splits_rewrite_in H0 H.
split.
 unfold star1 in |- *.
   exists x1.
   splits_join_in H3 (0 :: 1 :: 1 :: nil).
   exists (union (x2 :: x0 :: nil) pf0).
   split.
  apply (splits_permute H4).
    PermutProve.
 unfold nopre in |- *.
    tauto.
intros.
  assert
   (exists m1 : _, splits m (x0 :: m1 :: nil) /\ (p1 --o q1 (Val x3)) x m1).
  eapply diff1_frame_ex.
    apply H4.
   apply (splits_permute H).
   PermutProve.
   unfold star1 in |- *.
   exists x1.
   exists x2.
   unfold nopre in |- *.
    tauto.
  destruct H5.
  destruct H5.
  destruct (H1 x3 x4 H6).
  destruct H7.
  destruct H7.
  destruct H8.
  unfold star1 in |- *.
  exists x5.
  splits_rewrite_in H7 H5.
  splits_join_in H10 (1 :: 0 :: 1 :: nil).
  exists (union (x0 :: x6 :: nil) pf0).
  split.
 apply (splits_permute H11).
   PermutProve.
unfold nopre in |- *.
   tauto.
Defined.


Next Obligation.
clear H.
destruct H0.
destruct H0.
 destruct H0.
   destruct H0.
   destruct H0.
   unfold diff1 at 1 in |- *.
   intros.
   destruct H2.
   destruct (diff1_frame_ex H0 (splits_commute H3) H2).
   destruct H5.
   generalize (H4 x0 x2 H6).
   intros.
   destruct (diff1_frame_ex H1 H5 H7).
   destruct H8.
   exists x3.
   split.
  apply (splits_commute H8).
 left.
   split.
  auto.
 exists x0.
   exists x2.
    tauto.
  destruct H0.
  destruct H0.
  unfold diff1 at 1 in |- *.
  intros.
  destruct H2.
  destruct (diff1_frame_ex H1 (splits_commute H3) H2).
  destruct H5.
  exists x1.
  split.
 apply (splits_commute H5).
right.
  exists x0.
   tauto.
Defined.

Implicit Arguments sbind [A B p1 q1 p2 q2].




(*********************)
(**** monadic do *****)
(*********************)

(* bakes in the rules of frame and consequence *)

Program Definition 
    sdo' (A : Type) (p1 p2 : pre) (q1 : post A) (q2 : post A)  
        (e : STsep p1 A q1) 
        (pf : forall i, p2 i -> 
                  exists h, (p1 # this h) i /\
                            (forall y m, (q1 y ## delta(this h)) i m -> q2 y i m)) : STsep p2 A q2 
    :=

    do e (conj _ _).

Next Obligation.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct (pf x H0).
destruct H2.
unfold star1 in |- *.
destruct H2.
destruct H2.
destruct H2.
destruct H4.
exists x2.
splits_rewrite_in H2 H.
splits_join_in H6 (0 :: 1 :: 1 :: nil).
exists (union (x3 :: x0 :: nil) pf1).
split.
 apply (splits_commute H7).
unfold nopre in |- *.
   tauto.
Defined.


Next Obligation.
unfold diff1 in |- *.
intros.
clear H.
destruct (pf i1 H1).
destruct H.
assert ((p1 # nopre) i1).
 destruct H.
   destruct H.
   destruct H.
   unfold star1 in |- *.
   exists x1.
   exists x2.
   unfold nopre in |- *.
    tauto.
destruct (diff1_frame_ex H0 (splits_commute H2) H4).
  destruct H5.
  exists x1.
  split.
 apply (splits_commute H5).
apply (H3 x x1).
  unfold star2 in |- *.
  unfold diff1 in H6.
  destruct H.
  destruct H.
  destruct H.
  destruct H7.
  destruct (H6 x2 H7 x3 H).
  destruct H9.
  exists x2.
  exists x3.
  split.
 auto.
exists x4.
  exists x3.
   unfold delta.
   tauto.
Defined.

Implicit Arguments sdo' [A p1 p2 q1 q2].

Program Definition 
    sdo (A : Type) (p1 p2 : pre) (q1 : post A) (q2 : post A)  
        (e : STsep p1 A q1 |
          forall i, p2 i -> 
            exists h, (p1 # this h) i /\
              (forall y m, (q1 y ## delta(this h)) i m -> q2 y i m)) : STsep p2 A q2 
    := sdo' e _.

Implicit Arguments sdo [A p1 p2 q1 q2].

(****************)
(***** read *****)
(****************)

Definition sread_pre (A : Type) (x : loc) : pre :=
   fun i => exists v : A, (x --> v) i.

Definition sread_post (A : Type) (x : loc) : post A :=
   fun y i m => i = m /\ forall v : A, (x --> v) i -> y = Val v.

Program Definition 
   sread (A : Type) (x : loc) :
     STsep (sread_pre A x) A (sread_post A x) :=

   do (read x) (conj _ _).

Next Obligation.
unfold read_pre in |- *.
destruct H.
destruct H.
destruct H.
destruct H0.
clear H1.
destruct H0 as (v).
exists v.
 eapply splits_selects_intro.
   apply H.
  unfold points_to in H0.
  rewrite H0 in |- *.
  exists (update_loc empty x v).
  split.
 simpl in |- *.
   auto.
apply sel_eq.
Defined.

Next Obligation.
destruct H0.
unfold diff1 in |- *.
intros.
exists i1.
split.
 rewrite H0 in |- *.
   auto.
split.
 auto.
intros.
  apply H1.
  unfold points_to in H4.
   eapply splits_selects_intro.
   apply H3.
  exists i1.
  split.
 simpl in |- *.
   auto.
rewrite H4 in |- *.
  apply sel_eq.
Defined.


Implicit Arguments sread [A].


(******************)
(*** allocation ***)
(******************)

Definition snew_pre : pre := emp.

Definition snew_post (A : Type) (v : A) : post loc :=
  fun y i m => exists l:loc, y = Val l /\ (l --> v) m.

Program Definition
  snew (A : Type) (v : A) :
       STsep (snew_pre) loc (snew_post A v) := 

  do (new v) (conj _ _).

Next Obligation.
unfold nopre in |- *; auto. 
Defined.

Next Obligation.
destruct H0 as [x0 [eqx [uloc eqm]]].
unfold diff1.
intros i1 empi1 m0 H0.
exists (update_loc empty x0 v).
subst_emp_in empi1 H0; intros H6.
destruct H6 as [x1 H5].
simpl in H5.
split.
 apply splits_update_loc_intro.
  rewrite <- H5 in |- *.
    auto.
 rewrite <- H5 in |- *.
   auto.
exists x0.
  split.
 auto.
unfold points_to in |- *.
  auto.
Defined.

Implicit Arguments snew [A].


(********************)
(*** deallocation ***)
(********************)

Definition sfree_pre (l : loc) : pre :=
   fun i => exists A:Type, exists v:A, (l --> v) i.

Definition sfree_post (l : loc) : post unit :=
   fun y i m => y = Val tt /\ emp m.

Program Definition 
   sfree (l : loc) :
       STsep (sfree_pre l) unit (sfree_post l) :=

   do (free l) (conj _ _).

Next Obligation.
destruct H.
destruct H.
destruct H.
destruct H0.
clear H1.
destruct H0 as (A).
destruct H0 as (v).
unfold points_to in H0.
rewrite H0 in H.
destruct (splits_update_loc_elim H).
rewrite H1 in |- *.
 eapply selects_valid.
apply sel_eq.
Defined.

Next Obligation.
unfold sfree_post.
destruct H0.
unfold diff1 in |- *.
intros.
destruct H2 as (A).
destruct H2 as (v).
unfold points_to in H2.
exists empty.
split.
 rewrite H2 in H3.
   destruct (splits_update_loc_elim H3).
   rewrite H4 in H1.
   rewrite (free_loc_update_loc (v:=v) H5) in H1.
   rewrite <- H1 in |- *.
   remove_empty.
   apply splits_refl.
unfold emp in |- *.
  auto.
Defined.


(**************)
(*** update ***)
(**************)

Definition swrite_pre (l : loc) : pre :=
    fun i => exists b, exists y : b, (l --> y) i.

Definition swrite_post (A : Type) (l : loc) (v : A) : post unit :=
    fun y i m => (l --> v) m /\ y = Val tt. 

Program Definition 
    swrite (A : Type) (l : loc) (v : A) : 
        STsep (swrite_pre l) unit (swrite_post A l v) :=

    do (write l v) (conj _ _).

Next Obligation.
destruct H.
destruct H.
destruct H.
destruct H0.
clear H1.
destruct H0 as (b).
destruct H0 as (y).
unfold points_to in H0.
rewrite H0 in H.
destruct (splits_update_loc_elim H).
rewrite H1 in |- *.
 eapply selects_valid.
apply sel_eq.
Defined.

Next Obligation.
unfold swrite_post.
destruct H0.
unfold diff1 in |- *.
intros.
destruct H2 as (b).
destruct H2 as (y).
unfold points_to in H2.
rewrite H2 in H3.
destruct (splits_update_loc_elim H3).
exists (update_loc empty l v).
split.
 apply splits_update_loc_intro.
  rewrite H1 in |- *.
    rewrite H4 in |- *.
    apply (@update_loc_update_loc l).
 auto.
  unfold points_to in |- *.
  auto.
Defined.

Implicit Arguments swrite [A].

(*******************)
(* exception throw *)
(*******************)

(* dual of sret *)

Definition sthrow_pre : pre := emp.

Definition sthrow_post (A : Type) (e : exn) : post A :=
    fun y i m => m = i /\ y = Exn e.

Program Definition 
    sthrow (A : Type) (e : exn) : 
        STsep (sthrow_pre) A (sthrow_post A e) :=

    do (throw A e) (conj _ _).  

Next Obligation.
unfold nopre in |- *.
auto.
Defined.

Next Obligation.
unfold sthrow_post.
destruct H0.
unfold diff1 in |- *.
intros.
exists empty.
unfold emp in H2.
rewrite H2 in H3.
rewrite H0 in |- *.
auto.
Qed.


(*****************)
(* exception try *)
(*****************)

(* associative try in the style of Kennedy and Benton *)
(* requires two continuations: one for the value case *)
(* and one for the exceptional case *)

(* sbind is the special case when the exceptional *)
(* continuation is identity *)

Definition stry_pre (A : Type) (p1 : pre) (q1 : post A) (p2 : A -> pre) (p3 : exn -> pre) : pre :=
   fun i => (p1 # nopre) i /\ (forall x h, (p1 --o q1 (Val x)) i h -> (p2 x # nopre) h) 
                           /\ (forall e h, (p1 --o q1 (Exn e)) i h -> (p3 e # nopre) h).

Definition stry_post (A B : Type) (p1 : pre) (q1 : post A) 
                     (p2 : A -> pre) (q2 : A -> post B) 
                     (p3 : exn -> pre) (q3 : exn -> post B) : post B := 
   fun y i m => (p1 # nopre) i /\ 
            ((exists x, exists h, (p1 --o q1 (Val x)) i h /\ (p2 x --o q2 x y) h m) \/
             (exists e, exists h, (p1 --o q1 (Exn e)) i h /\ (p3 e --o q3 e y) h m)).
   
Program Definition 
    stry (A B : Type)
         (p1 : pre) (q1 : post A) (c1 : STsep p1 A q1)
         (p2 : A -> pre) (q2 : A -> post B) (c2 : forall x:A, STsep (p2 x) B (q2 x))
         (p3 : exn -> pre) (q3 : exn -> post B) (c3 : forall e:exn, STsep (p3 e) B (q3 e))
      : STsep (stry_pre A p1 q1 p2 p3) B (stry_post A B p1 q1 p2 q2 p3 q3) :=
    do (try c1 c2 c3) (conj _ _).

Next Obligation.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H0.
destruct H1.
elim H0.
intros.
destruct H1.
destruct H1.
destruct H3.
destruct H4.
unfold try_pre in |- *.
split.
 exists x1.
   splits_rewrite_in H1 H.
   splits_join_in H4 (0 :: 1 :: 1 :: nil).
   unfold nopre in |- *.
   generalize (splits_commute H5).
    eauto.
  split.
 intros.
   destruct (diff1_frame_ex H4 (splits_commute H) H0).
   destruct H5.
   destruct H2.
   destruct (H2 x3 x4 H6).
   destruct H8.
   destruct H8.
   destruct H9.
   exists x5.
   splits_rewrite_in H8 H5.
   splits_join_in H11 (1 :: 0 :: 1 :: nil).
   generalize (splits_commute H12).
    eauto.
  destruct H2.
  intros.
  destruct (diff1_frame_ex H5 (splits_commute H) H0).
  destruct H6.
  destruct (H4 e x3 H7).
  destruct H8.
  destruct H8.
  destruct H9.
  exists x4.
  splits_rewrite_in H8 H6.
  splits_join_in H11 (1 :: 0 :: 1 :: nil).
  generalize (splits_commute H12).
   eauto.
Defined.

Next Obligation.
destruct H0.
destruct H1.
 destruct H1.
   destruct H1.
   destruct H1.
   unfold diff1 in |- *.
   intros.
   destruct H3.
   destruct H5.
   destruct (diff1_frame_ex H1 (splits_commute H4) H3).
   destruct H7.
   generalize (H5 x0 x2 H8).
   intros.
   destruct (diff1_frame_ex H2 H7 H9).
   destruct H10.
   exists x3.
   split.
  apply (splits_commute H10).
 unfold stry_post in |- *.
   split.
  auto.
 left.
    eauto.
  destruct H1.
  destruct H1.
  destruct H1.
  unfold diff1 in |- *.
  intros.
  destruct H3.
  destruct H5.
  destruct (diff1_frame_ex H1 (splits_commute H4) H3).
  destruct H7.
  generalize (H6 x0 x2 H8).
  intros.
  destruct (diff1_frame_ex H2 H7 H9).
  exists x3.
  destruct H10.
  split.
 apply (splits_commute H10).
unfold stry_post in |- *.
  split.
 auto.
right.
   eauto.
Defined.


Implicit Arguments stry [A B p1 q1 p2 q2 p3 q3].


(********************)
(*** conditionals ***)
(********************)

Definition scond_pre (b : bool) (p1 p2 : pre) : pre :=
   fun i => (b = true -> p1 i) /\ (b = false -> p2 i).

Definition scond_post (A : Type) (b : bool) (q1 q2 : post A) : post A :=
   fun x i m => (b = true -> q1 x i m) /\ (b = false -> q2 x i m).

Program Definition
    scond (A : Type)
          (b : bool)
          (p1 : pre) (q1 : post A)
          (e1 : STsep p1 A q1)
          (p2 : pre) (q2 : post A)
          (e2 : STsep p2 A q2) 

      : STsep (scond_pre b p1 p2) A (scond_post A b q1 q2) :=

      do (cond b e1 e2) (conj _ _).

Next Obligation.
destruct H.
destruct H.
destruct H.
destruct H0.
clear H1.
destruct H0.
split.
 intros.
   unfold star1 in |- *.
   exists x.
   exists x0.
   unfold nopre in |- *.
   auto.
intros.
  unfold star1 in |- *.
  exists x.
  exists x0.
  unfold nopre in |- *.
  auto.
Defined.

Next Obligation.
unfold diff1 in |- *.
intros.
destruct b.
 unfold diff1 in H0.
   destruct H2.
   destruct (H0 (refl_equal true) i1 (H2 (refl_equal true)) m0 H3).
   destruct H5.
   exists x0.
   split.
  auto.
 split.
  auto.
 intros.
    absurd (true = false).
   discriminate.
 auto.
  destruct H2.
  unfold diff1 in H1.
  destruct (H1 (refl_equal false) i1 (H4 (refl_equal false)) m0 H3).
  destruct H5.
  exists x0.
  split.
 auto.
split.
 intro.
    absurd (false = true).
   discriminate.
 auto.
auto.
Defined.

Implicit Arguments scond [A p1 q1 p2 q2]. 

(* recursion -- not the most general type, but we'll see how far it
 * gets us.
 *)
Definition sfix : 
  forall (A : Type)
         (B : A -> Type)
         (p : A -> pre)
         (q : forall x : A, post (B x))
         (f : (forall x:A, STsep (p x) (B x) (q x)) ->
                (forall x:A, STsep (p x) (B x) (q x))),
    forall (x:A), STsep (p x) (B x) (q x) :=
  fun A B p q f x => ffix f x.
Implicit Arguments sfix [A B p q].

(* a tactic that gets rid of some redundant splits, some empty
 * heaps, etc. and takes care of some simple goals.   Needs to go
 * here because I used it to define case_sum below.
 *)
Ltac simple_split := 
  match goal with
  | [H:splits ?h1 (?h1 :: nil) |- _] => clear H
  | [H:splits ?h1 (?h2 :: nil) |- _] =>
    cut (h1 = h2) ; 
      [ clear H ; intro H ; rewrite H in * | apply (splits_singleton H) ]
  | [H:splits _ (empty :: _) |- _] => remove_empty_in H; clear H; intro
  | [H:splits _ (_ :: empty :: _) |- _] => remove_empty_in H; clear H; intro
  | [H:emp ?h |- _] => rewrite H in * ; clear H
  | [H:(emp # ?P) ?h |- _] => let simH := fresh "simH" in
                               pose (simH := elim_emp_left_hyp H) ; clearbody simH ; clear H ; rename simH into H
  | [H:(?P # emp) ?h |- _] => let simH := fresh "simH" in
                               pose (simH := elim_emp_right_hyp H) ; clearbody simH ; clear H ; rename simH into H
  | [|- (emp # ?P) ?h] => apply (elim_emp_left P h)
  | [|- (?P # emp) ?h] => apply (elim_emp_right P h)
  | [H:(?x --> ?v) ?h |- ((?x --> _) # nopre) ?h] => 
      apply (ptsto_star_nopre (x --> v) h H)
  | [H1:splits ?h (?h1::?h2::nil), H2:(?x --> ?v) ?h1 |- ((?x --> _) # nopre) ?h] => apply (ptsto_star_nopre2 (x --> v) h h1 h2 H1 H2)
  | [H:(?x --> ?v) ?h |- exists a:Type, exists w:a, (?x-->w) ?h] => eauto
  | [H:(?x --> ?v) ?h |- exists w:?a, (?x-->w) ?h] => exists v; auto
  | [|- swrite_pre ?x ?h] => unfold swrite_pre 
  | [|- sfree_pre ?x ?h] => unfold sfree_pre 
  | [|- sread_pre ?A ?x ?h] => unfold sread_pre 
  | [|- splits (union ?hs ?pf) ?hs] => unfold splits; exists pf; auto  
  | [|- splits _ (empty :: _)] => remove_empty
  | [|- splits _ (_ :: empty :: _)] => remove_empty
  | [|- splits ?h (?h :: nil)] => apply splits_refl
  | [|- this _ _] => unfold this
  | [|- emp _] => unfold emp
  | [|- splits empty nil] => apply splits_empty_nil
  | _ => idtac
  end.

(* overwrite ST notation with STsep notation *)
Delimit Scope stsep_scope with stsep. 

Notation "x '<--' c1 ';' c2" := (sbind c1 (fun x => c2))
  (at level 80, right associativity) : stsep_scope.

Notation "c1 ';;' c2" := (sbind c1 (fun _ => c2))
  (at level 80, right associativity) : stsep_scope.

Notation "'!!' x" := (sread x)
  (at level 50) : stsep_scope.

Notation "e1 '::=' e2" := (swrite e1 e2)
  (at level 60) : stsep_scope.

Open Local Scope stsep_scope.

(* compose above tactic with cvcsimp from ST to get some bigger help *)
Ltac simple_splits := repeat (progress (try rewrites; simple_split; cvcsimp; try subst)).

(* A new conditional command that operates on binary sums.
 * It's much more useful than scond above.   
 * Still need the eval_sbind_case_sum lemma.
 *)
Definition case_sum_pre(A B:Type)(v:sum A B)(p1 : A -> pre)(p2 : B -> pre) :
           pre := 
  fun i => ((forall x:A, v = inl B x -> p1 x i) /\
            (forall y:B, v = inr A y -> p2 y i)).
Implicit Arguments case_sum_pre [A B].

Definition case_sum_post(A B C:Type)(v:sum A B)(q1:A->post C)(q2:B->post C) :
           post C := 
  fun a i m => ((forall x:A, v = inl B x -> q1 x a i m) /\
                (forall y:B, v = inr A y -> q2 y a i m)).
Implicit Arguments case_sum_post [A B C].

Program Definition case_sum(A B C:Type)(v : sum A B)
                       (p1 : A -> pre)(q1 : A -> post C)
                       (p2 : B -> pre)(q2 : B -> post C)
                       (c1 : forall (x:A), (v = inl B x) -> 
                               STsep (p1 x) C (q1 x))
                       (c2 : forall (y:B), (v = inr A y) -> 
                               STsep (p2 y) C (q2 y))
  : STsep (case_sum_pre v p1 p2) C (case_sum_post v q1 q2) := 
  match v with
  | inl x => sdo (c1 x _)
  | inr y => sdo (c2 y _)
  end.

Next Obligation.
unfold case_sum_pre, case_sum_post in *.
destruct H.
assert (inl B x = inl B x).
 auto.
pose (H _ H1).
  exists empty.
  split.
 unfold star1, this in |- *.
   exists i.
   exists empty.
   simple_splits.
intros.
  unfold star2, delta, this in H2.
  destructs_in H2.
  rewrite <- H5 in *.
  rewrite <- H6 in *.
  clear H5 x1 H6 x3.
  remove_empty_in H2; intros H5.
  remove_empty_in H3; intros H6.
  clear H2 H3.
  pose (splits_singleton H5).
  pose (splits_singleton H6).
  rewrite <- e in *.
  rewrite <- e0 in *.
  split.
 intros.
   assert (x1 = x).
   congruence.
 rewrite H3 in |- *.
   auto.
intros.
   congruence.
Defined.

Next Obligation.
unfold case_sum_pre, case_sum_post in *.
assert (inr A y = inr A y).
 auto.
destruct H.
pose (H1 _ H0).
  exists empty.
  split.
 unfold star1, this in |- *.
   exists i.
   exists empty.
   simple_splits.
intros.
  unfold star2, delta, this in H2.
  destructs_in H2.
  rewrite <- H5 in *.
  rewrite <- H6 in *.
  clear H5 H6 x0 x2.
  remove_empty_in H2; intros H5.
  remove_empty_in H3; intros H6.
  clear H2 H3.
  pose (splits_singleton H5).
  pose (splits_singleton H6).
  rewrite <- e in *.
  rewrite <- e0 in *.
  split.
 intros.
    congruence.
intros.
  assert (y = y1).
  congruence.
rewrite <- H3 in |- *.
  auto.
Defined.

Implicit Arguments case_sum [A B C p1 q1 p2 q2].

(* A helper function to convert an option into a sum.  note that other
 * inductive type definitions can be broken apart in a similar way so
 * that we can use case_sum to deconstruct them.  This, in turn, allows
 * us to use eval_case_sum in proofs to simplify the VCs. *)
Definition opt2sum(A:Type)(v:option A) : sum unit A := 
  match v with
  | None => inl A tt
  | Some x => inr unit x
  end.
Implicit Arguments opt2sum [A].

(* a case operation on options *)
Definition case_option(B:Type)(C:Type)(v: option B) p1 q1 p2 q2
                      (c1 : forall (x:unit), (opt2sum v) = inl B x -> 
                              STsep (p1 x) C (q1 x))
                      (c2 : forall (y:B), (opt2sum v) = inr unit y ->
                              STsep (p2 y) C (q2 y)) :=
  case_sum (opt2sum v) c1 c2.

Implicit Arguments case_option [B C p1 q1 p2 q2].

(******************)
(*** divergence ***)
(******************)

Definition nopost (A : Type) : post A := fun y i m => False.

Program Definition 
    sdiverge (A : Type) 
      : STsep emp A (nopost A) :=
    do (diverge A) _.

Next Obligation.
split.
 unfold nopre in |- *.
   auto.
intros.
   absurd False.
 auto.
auto.
Defined.



(***********************************************)
(* Lemmas for symbolic evaluation of programs. *)
(* Automation of vc-genning.                   *)
(***********************************************)

(* The specs generated via typechecking have a very special form. *)
(* The following lemmas make use of this fact. *)
(* Try "applying" the lemma corresponding to the *)
(* first do-encapsulated command *)

(* for each primitive command there are *)
(* base-case, bind-case and try-case *)


(* base case for return *)

Lemma eval_sret : forall
          (A : Type) 
          (v : A) 
          (i : heap) (Q : ans A -> hprop),
    Q (Val v) i -> 
       exists h, 
         (sret_pre # this h) i /\
         forall y m, (sret_post A v y ## delta(this h)) i m -> Q y m.

intros.
exists i.
split.
 unfold sret_pre in |- *.
   unfold star1 in |- *.
   exists empty.
   exists i.
   split.
  remove_empty.
    apply splits_refl.
 unfold emp, this in |- *.
   auto.
intros.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct H2.
  destruct H3.
  unfold this in H3.
  unfold this in H5.
  rewrite <- H3 in H0.
  generalize (splits_empty_left H0).
  intros.
  rewrite H6 in H2.
  rewrite <- H2 in H1.
  remove_empty_in H1; intros H7.
  rewrite <- H5 in H7.
  destruct (splits_refl i).
  destruct H7.
  rewrite H7 in |- *.
   replace x4 with x3.
 rewrite <- H8 in |- *.
   rewrite H4 in |- *.
   auto.
apply proof_irrelevance.
Qed.


(* testing the eval_sret lemma *)

Program Definition 
   test_eval_sret (x : nat) : STsep (nopre) nat (fun y i m => i = m /\ y = Val (x+1)) :=
      sdo (sret (x+1)).

Next Obligation.
 apply eval_sret.
auto.
Qed.


(* bind case for return *)

Lemma eval_sbind_sret : forall
          (A B : Type) 
          (v : A) 
          (p2 : A -> pre) (q2 : A -> post B) 
          (i : heap) (Q : ans B -> hprop),
    (exists h, (p2 v # this h) i /\ 
           forall y m, (q2 v y ## delta(this h)) i m -> Q y m) -> 
    exists h, 
       (sbind_pre A (sret_pre) (sret_post A v) p2 # this h) i /\
       forall y m, (sbind_post A B (sret_pre) (sret_post A v) p2 q2 y ## delta(this h)) i m -> Q y m.

intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H2.
 econstructor.
split.
 unfold star1, sbind_pre, sret_pre, sret_post, this in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  split.
   unfold star1, emp, nopre in |- *.
     exists empty.
     exists i.
     split.
    remove_empty.
      apply splits_refl.
   auto.
  intros.
    destruct (H2 empty (refl_equal empty) i).
   remove_empty.
     apply splits_refl.
  destruct H3.
    destruct H4.
    destruct H4.
    remove_empty_in H3; intros H4.
    destruct H4.
    simpl in H4.
    destruct H4.
    clear x2.
     injection H5.
    intros.
    destruct H4.
    clear H5.
    unfold star1 in |- *.
    exists x0.
    exists x.
    unfold nopre in |- *.
    auto.
 auto.
  intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  remove_empty_in H2; intros H5.
  remove_empty_in H3; intros H6.
  destruct H5.
  destruct H6.
  simpl in H5.
  simpl in H6.
  destruct H5.
  destruct H6.
  clear H2 H3 x2 x4.
  destruct H4.
 destruct H2.
   destruct H3.
   destruct H3.
   destruct H3.
   destruct (H3 empty (refl_equal empty) i).
  remove_empty.
    apply splits_refl.
 destruct H5.
   destruct H6.
   destruct H6.
    injection H7.
   intros.
   destruct H6.
   clear H7.
   remove_empty_in H5; intros H6.
   destruct H6.
   simpl in H6.
   destruct H6.
   clear H5 x3 H2.
   destruct (H4 x0 H1 x H).
   destruct H2.
   apply H0.
   unfold this, delta, star2 in |- *.
   exists x0.
   exists x.
   split.
  auto.
 exists x3.
   exists x.
   auto.
destruct H2.
  destruct H2.
  destruct (H3 empty (refl_equal empty) i).
 remove_empty.
   apply splits_refl.
destruct H4.
  destruct H5.
  destruct H5.
   absurd (Exn x1 = Val v).
  discriminate.
auto.
Qed.


(* testing the eval_sbind_sret lemma *)

Program Definition 
   test_eval_sbind_sret (x : nat) : STsep (nopre) nat (fun y i m => i = m /\ y = Val (x+3)) :=
      sdo (sbind (sret (x+1))
           (fun y => sret (y+2))).

Next Obligation.
 apply eval_sbind_sret.
apply eval_sret.
split; auto.
f_equal. 
omega.
Qed.


(* try case for return *)

Lemma eval_stry_sret : forall
         (A B : Type) (v : A)
         (p1 : A -> pre) (q1 : A -> post B)
         (p2 : exn -> pre) (q2 : exn -> post B) (i : heap) (Q : ans B -> hprop), 
   (exists h : heap,
        (p1 v # this h) i /\
           (forall y m, (q1 v y ## delta (this h)) i m -> Q y m)) ->
    exists h : heap,
     (stry_pre A sret_pre (sret_post A v) p1 p2 # this h) i /\
       (forall y m, (stry_post A B sret_pre (sret_post A v) p1 q1 p2 q2 y ## delta (this h)) i m -> Q y m).

intros.
destruct H.
destruct H.
exists empty.
split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold stry_pre at 1 in |- *.
    split.
   unfold sret_pre, star1, nopre in |- *.
     exists empty.
     exists i.
     split.
    remove_empty.
      apply splits_refl.
   unfold emp in |- *.
     auto.
  split.
   intros.
     destruct (H1 empty (refl_equal empty) i).
    remove_empty.
      apply splits_refl.
   destruct H2.
     destruct H3.
     destruct H3.
     remove_empty_in H2; intros H3.
     destruct H3.
     simpl in H3.
     destruct H3.
      injection H4.
     intros.
     destruct H3.
     destruct H.
     destruct H.
     destruct H.
     destruct H3.
     exists x2.
     unfold nopre in |- *.
      eauto.
    intros.
    destruct (H1 empty (refl_equal empty) i).
   remove_empty.
     apply splits_refl.
  destruct H2.
    destruct H3.
     absurd (Exn e = Val v).
    discriminate.
  auto.
   unfold this in |- *.
   auto.
  intros.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H4.
  destruct H4.
  destruct H5.
  remove_empty_in H1; intros H4.
  remove_empty_in H2; intros H5.
  destruct H4.
  destruct H5.
  simpl in H4.
  simpl in H5.
  destruct H4.
  destruct H5.
  clear H1 H2 x1 x3.
  destruct H3.
  destruct H2.
 destruct H2.
   destruct H2.
   destruct H2.
   apply H0.
   destruct (H2 empty (refl_equal empty) i).
  remove_empty.
    apply splits_refl.
 destruct H4.
   destruct H5.
   destruct H5.
   remove_empty_in H4; intros H5.
   destruct H5.
   simpl in H5.
   destruct H5.
   clear H4 x2.
    injection H6.
   intros.
   destruct H4.
   clear H6.
   destruct H.
   destruct H.
   destruct H.
   destruct H4.
   destruct H5.
   destruct (H3 x2 H4 x H).
   destruct H5.
   exists x2.
   exists x.
   unfold delta, this in |- *.
   split.
  auto.
 exists x3.
    eauto.
  destruct H2.
  destruct H2.
  destruct H2.
  apply H0.
  destruct (H2 empty (refl_equal empty) i).
 remove_empty.
   apply splits_refl.
destruct H4.
  destruct H5.
  destruct H5.
   absurd (Exn x0 = Val v).
  discriminate.
auto.
Qed.


Program Definition 
   test_eval_stry_sret (x : nat) : STsep (emp) nat (fun y i m => emp m /\ y = Val (x+1)) :=
       sdo (stry (sret x) (fun y => sret (y+1))
                          (fun e => sret 0)).

Next Obligation.
apply eval_stry_sret.
apply eval_sret.
auto.
Defined.



(* base case for read *)

Lemma eval_sread : forall
          (A : Type) (x : loc)
          (v : A) 
          (i : heap) (Q : ans A -> hprop),
    ((x --> v) # nopre) i ->
      Q (Val v) i -> 
        exists h, 
         (sread_pre A x # this h) i /\
           forall y m, (sread_post A x y ## delta(this h)) i m -> Q y m.

intros.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H2.
 econstructor.
split.
 unfold star1, sread_pre, this in |- *.
   exists x0.
   exists x1.
   split.
  auto.
 split.
  exists v.
    auto.
 auto.
  intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H4.
  destruct H4.
  destruct H.
  destruct H2.
  rewrite H in H2.
  union_cancel_in H2.
  simpl in H4.
  destruct H4.
  destruct H3.
   replace x2 with x3 in H3.
 rewrite <- H in H3.
   destruct H3.
   destruct (H5 v H1).
   auto.
apply proof_irrelevance.
Qed.


(* testing the eval_sread lemma *)

Program Definition 
   test_eval_sread (l : loc) : STsep (l --> 1) nat (fun y i m => i = m /\ y = Val 1) :=
  sdo (sread l).

Next Obligation.
 eapply eval_sread.
   unfold star1, nopre in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
  eauto.
  auto.
Qed.


(* bind case for read *)

Lemma eval_sbind_sread : forall
          (A B : Type) (x : loc)
          (v : A) 
          (p2 : A -> pre) (q2 : A -> post B) 
          (i : heap) (Q : ans B -> hprop),
  ((x --> v) # nopre) i ->
  (exists h, (p2 v # this h) i /\ 
        forall y m, (q2 v y ## delta(this h)) i m -> Q y m) -> 
   exists h, 
        (sbind_pre A (sread_pre A x) (sread_post A x) p2 # this h) i /\
         forall y m, (sbind_post A B (sread_pre A x) (sread_post A x) p2 q2 y ## delta(this h)) i m -> Q y m.

intros.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H2.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H3.
destruct H4.
 econstructor.
split.
 unfold star1, sbind_pre, sread_pre, sread_post in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  split.
   unfold star1, nopre in |- *.
     exists x0.
     exists x1.
      eauto.
    intros.
    generalize (H4 x0).
    intros.
    assert (exists v : A, (x --> v) x0).
    eauto.
    destruct (H5 H6 x1).
   auto.
  clear H5 H6.
    destruct H7.
    destruct H6.
    destruct H6.
    generalize (H7 v H1).
    intros.
     injection H6.
    intros.
    destruct H8.
    clear H6 H7.
    destruct H.
    destruct H5.
     replace x6 with x5 in H5.
   rewrite <- H in H5.
     destruct H5.
     clear x6.
     unfold star1 in |- *.
     exists x3.
     exists x2.
     unfold nopre in |- *.
     auto.
  apply proof_irrelevance.
   unfold this in |- *.
   auto.
  intros.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H7.
  destruct H7.
  destruct H8.
  remove_empty_in H4; intros H7.
  remove_empty_in H5; intros H8.
  destruct H7.
  destruct H8.
  simpl in H7.
  simpl in H8.
  destruct H7.
  destruct H8.
  clear x5 x7 H4 H5.
  destruct H6.
 destruct H4.
   destruct H4.
   destruct H4.
   destruct H4.
   destruct H6.
   clear H7.
   destruct H5.
   destruct H5.
   destruct H5.
   destruct (H5 x4 H6 x5 H4).
   destruct H8.
   destruct H9.
   destruct H9.
   destruct H6.
   generalize (H10 x8 H6).
   intros.
    injection H9.
   intros.
   destruct H11.
   clear H9 H10.
   destruct (points_to_same_subheap H1 H6 H H4).
   destruct H9.
   destruct H10.
   destruct H4.
   destruct H8.
    replace x6 with x4 in H8.
  rewrite <- H4 in H8.
    destruct H8.
    clear x6.
    destruct H.
    rewrite H in H4.
    union_cancel_in H4.
    simpl in H8.
    destruct H8.
    clear pf1 pf2 H4 x4.
    destruct (H7 x3 H3 x2 H0).
    destruct H4.
    apply H2.
    unfold star2, delta, this in |- *.
    exists x3.
    exists x2.
    split.
   auto.
  exists x4.
     eauto.
   apply proof_irrelevance.
  destruct H4.
  destruct H4.
  assert (sread_pre A x x0).
 unfold sread_pre in |- *.
    eauto.
  destruct (H5 x0 H6 x1 H).
  destruct H7.
  destruct H8.
  destruct H8.
  generalize (H9 v H1).
  intros.
   absurd (Exn x4 = Val v).
  discriminate.
auto.
Qed.


Program Definition 
  test_eval_sbind_sread (x : loc) :  STsep (fun i => exists v : nat, (x --> v) i) 
                                     nat
                                    (fun y i m => forall v : nat, ((x --> v) i) -> ((x --> v) m) /\ y = Val(v+1)) :=
     sdo (sbind (sread x) (fun xv => sret (xv+1))). 

Next Obligation.
eapply eval_sbind_sread.
   unfold star1, nopre in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
  eauto.
  apply eval_sret.
  intros.
  split.
 auto.
 replace H with v.
 auto.
apply (points_to_same H1 H0).
Qed.


(* try case for read *)

Lemma eval_stry_sread : forall
         (A B : Type) (x : loc) (v : A)
         (p1 : A -> pre) (q1 : A -> post B)
         (p2 : exn -> pre) (q2 : exn -> post B) (i : heap) (Q : ans B -> hprop), 
  ((x --> v) # nopre) i ->
  (exists h, (p1 v # this h) i /\ 
        forall y m, (q1 v y ## delta(this h)) i m -> Q y m) -> 
   exists h : heap,
     (stry_pre A (sread_pre A x) (sread_post A x) p1 p2 # this h) i /\
     (forall y m, (stry_post A B (sread_pre A x) (sread_post A x) p1 q1 p2 q2 y ## delta (this h)) i m -> Q y m).

intros.
destruct H0.
destruct H0.
exists empty.
split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold stry_pre at 1 in |- *.
    split.
   destruct H.
     destruct H.
     destruct H.
     destruct H2.
     exists x1.
     exists x2.
     split.
    auto.
   unfold sread_pre, nopre in |- *.
     split.
    exists v.
       eauto.
   auto.
    split.
   intros.
     destruct H.
     destruct H.
     destruct H.
     destruct H3.
     assert (sread_pre A x x2).
    unfold sread_pre in |- *.
       eauto.
     destruct (H2 x2 H5 x3 H).
     destruct H6.
     destruct H7.
     destruct H7.
     generalize (H8 v H3).
     intros.
      injection H7.
     intros.
     destruct H9.
     destruct H.
     destruct H6.
      replace x5 with x4 in H6.
    rewrite <- H in H6.
      destruct H6.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H6.
      exists x6.
       eauto.
     apply proof_irrelevance.
    intros.
    destruct H.
    destruct H.
    destruct H.
    destruct H3.
    assert (sread_pre A x x1).
   unfold sread_pre in |- *.
      eauto.
    destruct (H2 x1 H5 x2 H).
    destruct H6.
    destruct H7.
    generalize (H8 v H3).
    intros.
     absurd (Exn e = Val v).
    discriminate.
  auto.
   unfold this in |- *.
   auto.
  intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  remove_empty_in H2; intros H5.
  remove_empty_in H3; intros H6.
  destruct H5.
  destruct H6.
  simpl in H5.
  simpl in H6.
  destruct H5.
  destruct H6.
  clear H2 H3 x2 x4.
  apply H1.
  destruct H4.
  destruct H3.
 destruct H3.
   destruct H3.
   destruct H3.
   destruct H.
   destruct H.
   destruct H.
   destruct H5.
   assert (sread_pre A x x3).
  unfold sread_pre in |- *.
     eauto.
   destruct (H3 x3 H7 x4 H).
   destruct H8.
   destruct H9.
   destruct H9.
   generalize (H10 v H5).
   intros.
    injection H9.
   intros.
   destruct H11.
   elim H.
   intros.
   destruct H8.
    replace x5 with x6 in H11.
  rewrite <- H8 in H11.
    destruct H11.
    destruct H0.
    destruct H0.
    destruct H0.
    destruct H11.
    destruct (H4 x2 H11 x7).
   auto.
  destruct H13.
    exists x2.
    exists x7.
    split.
   auto.
  exists x8.
    exists x7.
    destruct H12.
    unfold delta, this in |- *.
    auto.
 apply proof_irrelevance.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H5.
  destruct (H3 x3 H5 x4 H2).
  destruct H7.
  destruct H8.
  destruct H5.
  generalize (H9 x6 H5).
  intros.
   absurd (Exn x1 = Val x6).
  discriminate.
auto.
Qed.



Program Definition test_eval_stry_sread (x : loc) : STsep (x --> 1) nat (fun y i m => (x --> 1) m /\ y = Val 5) :=
  sdo (stry (sread x) (fun y => sret (y+4))
                      (fun _ => sret 10)).

Next Obligation.
 eapply eval_stry_sread.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
   eexact H.
    unfold nopre in |- *.
   auto.
  apply eval_sret.
   replace (1 + 4) with 5.
 auto.
 omega.
Defined.




(* base case for write *)

Lemma eval_swrite : forall
          (A : Type) (x : loc)
          (v : A) 
          (i : heap) (Q : ans unit -> hprop),

   (exists i1, (exists a, exists w:a, (x --> w) i1) /\
      exists i2, splits i (i1::i2::nil) /\
          forall j j1, splits j (j1::i2::nil) -> 
                    (x --> v) j1 -> Q (Val tt) j) -> 
    exists h, 
        (swrite_pre x # this h) i /\
        forall y m, (swrite_post A x v y ## delta(this h)) i m -> Q y m.

intros.
destruct H.
destruct H.
destruct H0.
destruct H0.
 econstructor.
split.
 exists x0.
   exists x1.
   split.
  auto.
 unfold swrite_pre, this in |- *.
    eauto.
  intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H4.
  rewrite H5 in |- *.
  clear H5.
   eapply H1.
   apply H3.
  auto.
Qed.



Program Definition 
  test_eval_swrite (l : loc) (x : nat) : STsep (l --> 1) unit (fun y i m => (l --> x) m) :=
  sdo (swrite l x).

Next Obligation.
apply eval_swrite.
exists i.
split.
  eauto.
  exists empty.
  split.
 remove_empty.
   apply splits_refl.
intros.
  remove_empty_in H0; intros H2.
  destruct H2.
  simpl in H2.
  destruct H2.
  auto.
Defined.




(* bind case for write *)

Lemma eval_sbind_swrite : forall
          (A B : Type) (x : loc)
          (v : A) 
          (p2 : unit -> pre) (q2 : unit -> post B) 
          (i : heap) (Q : ans B -> hprop),

      (exists i1, (exists a, exists w:a, (x --> w) i1) /\
         exists i2, splits i (i1::i2::nil) /\
             forall j j1, splits j (j1::i2::nil) -> 
                    (x --> v) j1 ->
                 exists h, (p2 tt # this h) j /\ 
                   forall y m, (q2 tt y ## delta(this h)) j m -> Q y m) -> 
      exists h, 
        (sbind_pre unit (swrite_pre x) (swrite_post A x v) p2 # this h) i /\
         forall y m, (sbind_post unit B (swrite_pre x) (swrite_post A x v) p2 q2 y ## delta(this h)) i m -> Q y m.

intros.
destruct H.
destruct H.
destruct H0.
destruct H0.
exists empty.
split.
 unfold sbind_pre, star1, this in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  split.
   exists x0.
     exists x1.
     unfold swrite_pre, nopre in |- *.
      eauto.
  intros.
    destruct (H2 x0 H x1 H0).
    destruct H3.
    unfold swrite_post in H4.
    destruct H4.
     injection H5.
    intros.
    rewrite H6 in |- *.
    clear H5 H6.
    destruct (H1 h x3 H3 H4).
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H5.
    destruct H7.
    destruct H8.
    exists x5.
    exists x4.
    split.
   auto.
  unfold nopre in |- *.
    auto.
 auto.
intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  remove_empty_in H2; intros H5.
  remove_empty_in H3; intros H6.
  destruct H5.
  simpl in H5.
  destruct H5.
  destruct H6.
  simpl in H5.
  destruct H5.
  clear H2 H3 x3 x2.
  destruct H4.
 destruct H2.
   destruct H3.
   destruct H3.
   destruct H3.
   destruct (H3 x0 H x1 H0).
   destruct H5.
   destruct H6.
   destruct (H1 x3 x4 H5 H6).
   destruct H8.
   apply H9.
   destruct x2.
   clear H7.
   destruct H8.
   destruct H7.
   destruct H7.
   destruct H8.
   destruct H10.
   destruct (H4 x2 H8 x5 H7).
   destruct H10.
   exists x2.
   exists x5.
   split.
  auto.
 exists x6.
   exists x5.
   split.
  auto.
 split.
  auto.
 unfold delta, this in |- *.
   auto.
destruct H2.
  destruct H2.
  destruct (H3 x0 H x1 H0).
  destruct H4.
  destruct H5.
   absurd (Exn x2 = Val tt).
  discriminate.
auto.
Qed.




Program Definition 
  test_eval_sbind_swrite (l : loc) (x : nat) : STsep (l --> 1) nat (fun y i m => (l --> 2*x) m /\ y = Val 20) :=
  sdo (sbind (swrite l (2*x)) (fun _ => sret 20)).

Next Obligation.
apply eval_sbind_swrite.
exists i.
split.
  eauto.
  exists empty.
  split.
 remove_empty.
   apply splits_refl.
intros.
  remove_empty_in H0; intros H2.
  destruct H2.
  simpl in H2.
  destruct H2.
  clear H0 x0.
  apply eval_sret.
  auto.
Defined.



(* try case for write *)

Lemma eval_stry_swrite : forall
         (A B : Type) (x : loc)
         (v : A) 
         (p1 : unit -> pre) (q1 : unit -> post B)
         (p2 : exn -> pre) (q2 : exn -> post B) 
         (i : heap) (Q : ans B -> hprop),

    (exists i1, (exists a, exists w:a, (x --> w) i1) /\
         exists i2, splits i (i1::i2::nil) /\
             forall j j1, splits j (j1::i2::nil) -> 
                    (x --> v) j1 ->
                 exists h, (p1 tt # this h) j /\ 
                   forall y m, (q1 tt y ## delta(this h)) j m -> Q y m) -> 
     exists h : heap,
     (stry_pre unit (swrite_pre x) (swrite_post A x v) p1 p2 # this h) i /\
     (forall y m, (stry_post unit B (swrite_pre x) (swrite_post A x v) p1 q1 p2 q2 y ## delta (this h)) i m -> Q y m).

intros.
destruct H.
destruct H.
destruct H0.
destruct H0.
exists empty.
split.
 unfold stry_pre, star1 in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  split.
   exists x0.
     unfold swrite_pre, nopre in |- *.
      eauto.
    split.
   intros.
     destruct x2.
     destruct (H2 x0 H x1 H0).
     destruct H3.
     destruct H4.
     clear H5.
     destruct (H1 h x2 H3 H4).
     destruct H5.
     destruct H5.
     destruct H5.
     destruct H5.
     destruct H7.
     destruct H8.
     exists x4.
     unfold nopre in |- *.
      eauto.
    intros.
    destruct (H2 x0 H x1 H0).
    destruct H3.
    destruct H4.
     absurd (Exn e = Val tt).
    discriminate.
  auto.
   unfold this in |- *.
   auto.
  intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  remove_empty_in H2; intros H5.
  remove_empty_in H3; intros H6.
  destruct H5.
  destruct H6.
  simpl in H5, H6.
  destruct H5.
  destruct H6.
  clear H2 H3 x3 x5.
  destruct H4.
  destruct H3.
 destruct H3.
   destruct H3.
   destruct H3.
   destruct (H3 x0 H x1 H0).
   destruct H5.
   destruct H6.
   destruct x2.
   clear H7.
   destruct (H1 x3 x4 H5 H6).
   destruct H7.
   apply H8.
   destruct H7.
   destruct H7.
   destruct H7.
   destruct H9.
   destruct H10.
   destruct (H4 x5 H9 x2 H7).
   destruct H10.
   exists x5.
   exists x2.
   split.
  auto.
 exists x6.
   unfold delta, this in |- *.
    eauto.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct (H3 x0 H x1 H0).
  destruct H5.
  destruct H6.
   absurd (Exn x2 = Val tt).
  discriminate.
auto.
Qed.




Program Definition test_eval_stry_swrite (l : loc) (x : nat) : STsep (l --> 1) nat (fun y i m => (l --> 2*x) m /\ y = Val 20) :=
  sdo (stry (swrite l (2*x)) (fun _ => sret 20)
                             (fun _ => sret 30)).

Next Obligation.
apply eval_stry_swrite.
exists i.
split.
  eauto.
  exists empty.
  split.
 remove_empty.
   apply splits_refl.
intros.
  remove_empty_in H0; intros H2.
  destruct H2.
  simpl in H2.
  destruct H2.
  clear H0 x0.
  apply eval_sret.
  auto.
Defined.




(* base case for new *)

Lemma eval_snew : forall
         (A : Type) (v : A) (i : heap) (Q : ans loc -> hprop),
   (forall j x h, (splits j (i::h::nil) -> (x --> v) h -> Q (Val x) j)) ->
    exists h, 
        (snew_pre # this h) i /\
        forall y m, (snew_post A v y ## delta(this h)) i m -> Q y m.

intros.
 econstructor.
split.
 unfold snew_pre, star1, this, emp in |- *.
   exists empty.
   exists i.
   split.
  remove_empty.
    apply splits_refl.
 auto.
  intros.
  destruct y.
 destruct H0.
   destruct H0.
   destruct H0.
   destruct H1.
   destruct H1.
   destruct H1.
   destruct H2.
   destruct H3.
   destruct H3.
   destruct H4.
   apply (H m l x1).
  apply splits_commute.
    auto.
 unfold snew_post in H2.
   destruct H2.
   destruct H2.
    injection H2.
   intros.
   destruct H4.
   auto.
destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct H2.
  destruct H2.
   absurd (Exn e = Val x3).
  discriminate.
auto.
Qed.


Program Definition test_eval_snew (v : nat) : STsep (emp) loc (fun y i m => exists l:loc, y = Val l /\ (l --> (v+v)) m)
 := sdo (snew (2*v)).

Next Obligation.
apply eval_snew.
intros.
unfold emp in H.
rewrite H in H0.
remove_empty_in H0; intros H2.
destruct H2.
simpl in H2.
destruct H2.
 replace (v + v) with (v + (v + 0)).
  eauto.
   omega.
Defined. 


(* bind case for new *)

Lemma eval_sbind_snew : forall
          (A B : Type) 
          (v : A) 
          (p2 : loc -> pre) (q2 : loc -> post B) 
          (i : heap) (Q : ans B -> hprop),

     (forall j x t, (splits j (i::t::nil) -> (x --> v) t -> 
                 exists h, (p2 x # this h) j /\ 
                   forall y m, (q2 x y ## delta(this h)) j m -> Q y m)) -> 
      exists h, 
        (sbind_pre loc (snew_pre) (snew_post A v) p2 # this h) i /\
         forall y m, (sbind_post loc B (snew_pre) (snew_post A v) p2 q2 y ## delta(this h)) i m -> Q y m.

intros.
 econstructor.
split.
 unfold sbind_pre, snew_pre, snew_post, star1, this in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  split.
   exists empty.
     exists i.
     split.
    remove_empty.
      apply splits_refl.
   unfold emp, nopre in |- *.
     auto.
  intros.
    destruct (H0 empty (refl_equal empty) i).
   remove_empty.
     apply splits_refl.
  destruct H1.
    destruct H2.
    destruct H2.
     injection H2.
    intros.
    destruct H4.
    clear H2.
    destruct (H h x x0 (splits_commute H1) H3).
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H2.
    destruct H5.
    destruct H6.
    unfold nopre in |- *.
     eauto.
   auto.
  intros.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H4.
  remove_empty_in H0; intros H3.
  remove_empty_in H1; intros H4.
  destruct H3.
  destruct H4.
  simpl in H3, H4.
  destruct H3.
  destruct H4.
  clear H0 H1 x0 x2.
  destruct H2.
 destruct H0.
   destruct H1.
   destruct H1.
   destruct H1.
   destruct (H1 empty (refl_equal empty) i).
  remove_empty.
    apply splits_refl.
 destruct H3.
   destruct H4.
   destruct H4.
    injection H4.
   intros.
   destruct H6.
   clear H4.
   destruct (H x0 x x1 (splits_commute H3) H5).
   destruct H4.
   destruct H4.
   destruct H4.
   destruct H4.
   destruct H7.
   destruct H8.
   destruct (H2 x3 H7 x2 H4).
   destruct H8.
   apply H6.
   exists x3.
   exists x2.
   unfold delta, this in |- *.
   split.
  auto.
 exists x4.
   exists x2.
    eauto.
destruct H0.
  destruct H0.
  destruct (H1 empty (refl_equal empty) i).
 remove_empty.
   apply splits_refl.
destruct H2.
  destruct H3.
  destruct H3.
   absurd (Exn x = Val x1).
  discriminate.
auto.
Qed.



Program Definition test_eval_sbind_snew (v : nat) : STsep emp loc (fun y i m => exists l, y = Val l /\ (l --> (2*v)) m) :=
   sdo (sbind (snew (v+v)) (fun l => sret l)).

Next Obligation.
apply eval_sbind_snew.
intros.
apply eval_sret.
 replace (v + (v + 0)) with (v + v).
 unfold emp in H.
   rewrite H in H0.
   remove_empty_in H0; intros H2.
   destruct H2.
   simpl in H2.
   destruct H2.
    eauto.
   omega.
Defined.



(* try case for new *)

Lemma eval_stry_snew : forall
         (A B : Type) (v : A)
         (p1 : loc -> pre) (q1 : loc -> post B) 
         (p2 : exn -> pre) (q2 : exn -> post B) 
         (i : heap) (Q : ans B -> hprop), 
  (forall j x t, 
       (splits j (i::t::nil) -> (x --> v) t -> 
        exists h, (p1 x # this h) j /\ forall y m, (q1 x y ## delta(this h)) j m -> Q y m)) -> 
   exists h : heap,
     (stry_pre loc snew_pre (snew_post A v) p1 p2 # this h) i /\
     (forall (y : ans B) (m : heap),
        (stry_post loc B snew_pre (snew_post A v) p1 q1 p2 q2 y ## delta (this h)) i m -> Q y m).

intros.
exists empty.
split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold stry_pre at 1 in |- *.
    split.
   unfold snew_pre, star1, nopre in |- *.
     exists empty.
     exists i.
     split.
    remove_empty.
      apply splits_refl.
   unfold emp in |- *.
     auto.
  split.
   intros.
     destruct (H0 empty (refl_equal empty) i).
    remove_empty.
      apply splits_refl.
   destruct H1.
     destruct H2.
     destruct H2.
      injection H2.
     intros.
     destruct H4.
     clear H2.
     destruct (H h x x0 (splits_commute H1) H3).
     destruct H2.
     destruct H2.
     destruct H2.
     destruct H2.
     destruct H5.
     exists x2.
     unfold nopre in |- *.
      eauto.
    intros.
    destruct (H0 empty (refl_equal empty) i).
   remove_empty.
     apply (splits_refl i).
  destruct H1.
    destruct H2.
    destruct H2.
     absurd (Exn e = Val x0).
    discriminate.
  auto.
   unfold this in |- *.
   auto.
  intros.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H4.
  remove_empty_in H0; intros H3.
  remove_empty_in H1; intros H4.
  destruct H3.
  destruct H4.
  simpl in H3.
  simpl in H4.
  destruct H3.
  destruct H4.
  clear H0 H1 x0 x2.
  destruct H2.
  destruct H1.
 destruct H1.
   destruct H1.
   destruct H1.
   destruct (H1 empty (refl_equal empty) i).
  remove_empty.
    apply splits_refl.
 destruct H3.
   destruct H4.
   destruct H4.
    injection H4.
   intros.
   destruct H6.
   clear H4.
   destruct (H x0 x x1 (splits_commute H3) H5).
   destruct H4.
   apply H6.
   destruct H4.
   destruct H4.
   destruct H4.
   destruct H7.
   destruct H8.
   destruct (H2 x3 H7 x2 H4).
   destruct H8.
   exists x3.
   exists x2.
   split.
  auto.
 exists x4.
   unfold delta, this in |- *.
    eauto.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct (H1 empty (refl_equal empty) i).
 remove_empty.
   apply splits_refl.
destruct H3.
  destruct H4.
  destruct H4.
   absurd (Exn x = Val x2).
  discriminate.
auto.
Qed. 


Program Definition test_eval_stry_snew (v : nat) : STsep emp nat (fun y i m => exists l, (l --> (2*v)) m /\ y = Val 1) :=
   sdo (stry (snew (v+v)) (fun l => sret 1)
                          (fun e => sret 2)).

Next Obligation.
apply eval_stry_snew.
intros.
apply eval_sret.
unfold emp in H.
rewrite H in H0.
remove_empty_in H0; intros H2.
destruct H2.
simpl in H2.
destruct H2.
 replace (v + (v + 0)) with (v + v).
  eauto.
   omega.
Defined.



(* base case for free *)

Lemma eval_sfree : forall
         (x : loc) (i : heap) (Q : ans unit -> hprop),
   (exists j, exists t, (exists a:Type, exists v:a, (x --> v) t) /\
                   splits i (j::t::nil) /\ Q (Val tt) j) ->
   exists h, 
        (sfree_pre x # this h) i /\
        forall y m, (sfree_post x y ## delta(this h)) i m -> Q y m.

intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
 econstructor.
split.
 unfold sfree_pre, star1, this in |- *.
   exists x1.
   exists x0.
   split.
  apply (splits_commute H0).
 split.
   eauto.
   auto.
  intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H4.
  destruct H4.
  unfold emp in H5.
  rewrite H5 in H3.
  remove_empty_in H3; intros H4.
  destruct H4.
  simpl in H4.
  destruct H4.
  apply H1.
Qed.


Program Definition test_eval_sfree (x : loc) : STsep (fun i => exists a, exists v:a, (x --> v) i) unit (fun y i m => emp m /\ y = Val tt) :=
  sdo (sfree x).

Next Obligation.
 eapply eval_sfree.
exists empty.
exists i.
split.
 exists H.
   exists H0.
   auto.
split.
 remove_empty.
   apply splits_refl.
unfold emp in |- *.
  auto.
Defined.


(* bind case for free *)

Lemma eval_sbind_sfree : forall
          (B : Type) (x : loc)
          (p2 : unit -> pre) (q2 : unit -> post B) 
          (i : heap) (Q : ans B -> hprop),
     (exists t, exists j,
          (exists a:Type, exists v:a, (x --> v) t) /\
           splits i (j::t::nil) /\
           exists h, (p2 tt # this h) j /\ 
              forall y m, (q2 tt y ## delta(this h)) j m -> Q y m) -> 
      exists h, 
        (sbind_pre unit (sfree_pre x) (sfree_post x) p2 # this h) i /\
         forall y m, (sbind_post unit B (sfree_pre x) (sfree_post x) p2 q2 y ## delta(this h)) i m -> Q y m.

intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H1.
destruct H1.
destruct H1.
destruct H1.
destruct H3.
destruct H4.
exists empty.
split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold sbind_pre at 1 in |- *.
    split.
   exists x0.
     exists x1.
     split.
    apply (splits_commute H0).
   unfold sfree_pre, nopre in |- *.
      eauto.
    intros.
    assert (sfree_pre x x0).
   unfold sfree_pre in |- *.
      eauto.
    destruct (H4 x0 H5 x1 (splits_commute H0)).
    destruct H6.
    destruct H7.
    unfold emp in H8.
    rewrite H8 in H6.
    remove_empty_in H6; intros H9.
    destruct H9.
    simpl in H9.
    destruct H9.
    clear H6 H7 H8 x8.
    destruct x6.
    exists x5.
    unfold nopre in |- *.
     eauto.
   unfold this in |- *.
   auto.
  intros.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H7.
  destruct H7.
  destruct H8.
  remove_empty_in H4; intros H7.
  remove_empty_in H5; intros H8.
  destruct H7.
  destruct H8.
  simpl in H7, H8.
  destruct H7.
  destruct H8.
  clear H4 H5 x7 x9.
  destruct H6.
 destruct H4.
   destruct H5.
   destruct H5.
   destruct H5.
   assert (sfree_pre x x0).
  unfold sfree_pre in |- *.
     eauto.
   destruct (H5 x0 H7 x1 (splits_commute H0)).
   destruct H8.
   apply H2.
   destruct H9.
   unfold emp in H10.
   rewrite H10 in H8.
   destruct x6.
   clear H9 H10.
   remove_empty_in H8; intros H9.
   destruct H9.
   simpl in H9.
   destruct H9.
   clear H8 x6.
   destruct (H6 x5 H3 x4 H1).
   destruct H8.
   exists x5.
   exists x4.
   split.
  auto.
 exists x1.
   unfold delta, this in |- *.
    eauto.
  destruct H4.
  destruct H4.
  rewrite H4 in |- *.
  assert (sfree_pre x x0).
 unfold sfree_pre in |- *.
    eauto.
  destruct (H5 x0 H6 x1 (splits_commute H0)).
  destruct H7.
  destruct H8.
   absurd (Exn x6 = Val tt).
  discriminate.
auto.
Qed. 



Program Definition test_eval_sbind_sfree (x : loc) : STsep (x --> 3) nat (fun y i m => emp m /\ y = Val 4) :=
  sdo (sbind (sfree x) (fun _ => sret 4)). 

Next Obligation.
apply eval_sbind_sfree.
exists i.
exists empty.
split.
  eauto.
  split.
 remove_empty.
   apply splits_refl.
apply eval_sret.
  unfold emp in |- *.
  auto.
Defined.


(* try case for free *)

Lemma eval_stry_sfree : forall
          (B : Type) (x : loc)
          (p1 : unit -> pre) (q1 : unit -> post B)
          (p2 : exn -> pre) (q2 : exn -> post B) 
          (i : heap) (Q : ans B -> hprop),
   (exists t, exists j,
        (exists a:Type, exists v:a, (x --> v) t) /\
          splits i (j::t::nil) /\
          exists h, (p1 tt # this h) j /\ 
              forall y m, (q1 tt y ## delta(this h)) j m -> Q y m) -> 
   exists h : heap,
     (stry_pre unit (sfree_pre x) (sfree_post x) p1 p2 # this h) i /\
     (forall y m, (stry_post unit B (sfree_pre x) (sfree_post x) p1 q1 p2 q2 y ## delta (this h)) i m -> Q y m).

intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H1.
destruct H1.
destruct H1.
destruct H1.
destruct H1.
destruct H3.
destruct H4.
exists empty.
split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold stry_pre at 1 in |- *.
    split.
   exists x0.
     exists x1.
     split.
    apply (splits_commute H0).
   unfold sfree_pre, nopre in |- *.
      eauto.
    split.
   intros.
     assert (sfree_pre x x0).
    unfold sfree_pre in |- *.
       eauto.
     destruct (H4 x0 H5 x1 (splits_commute H0)).
     destruct H6.
     destruct H7.
     unfold emp in H8.
     rewrite H8 in H6.
     remove_empty_in H6; intros H9.
     destruct H9.
     simpl in H9.
     destruct H9.
     destruct x6.
     exists x5.
     unfold nopre in |- *.
      eauto.
    intros.
    assert (sfree_pre x x0).
   unfold sfree_pre in |- *.
      eauto.
    destruct (H4 x0 H5 x1 (splits_commute H0)).
    destruct H6.
    destruct H7.
     absurd (Exn e = Val tt).
    discriminate.
  auto.
   unfold this in |- *.
   auto.
  intros.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H7.
  destruct H7.
  destruct H8.
  remove_empty_in H4; intros H7.
  remove_empty_in H5; intros H8.
  destruct H7.
  destruct H8.
  simpl in H7, H8.
  destruct H7.
  destruct H8.
  clear H4 H5 x7 x9.
  destruct H6.
  destruct H5.
 destruct H5.
   destruct H5.
   destruct H5.
   assert (sfree_pre x x0).
  unfold sfree_pre in |- *.
     eauto.
   destruct (H5 x0 H7 x1 (splits_commute H0)).
   destruct H8.
   destruct H9.
   unfold emp in H10.
   rewrite H10 in H8.
   destruct x6.
   clear H9 H10.
   remove_empty_in H8; intros H9.
   destruct H9.
   simpl in H9.
   destruct H9.
   clear H8 x6.
   destruct (H6 x5 H3 x4 H1).
   destruct H8.
   apply H2.
   exists x5.
   exists x4.
   split.
  auto.
 unfold delta, this in |- *.
   exists x1.
    eauto.
  destruct H5.
  destruct H5.
  destruct H5.
  assert (sfree_pre x x0).
 unfold sfree_pre in |- *.
    eauto.
  destruct (H5 x0 H7 x1 (splits_commute H0)).
  destruct H8.
  destruct H9.
   absurd (Exn x6 = Val tt).
  discriminate.
auto.
Qed.



Program Definition test_eval_stry_sfree (x : loc) : STsep (x --> 3) nat (fun y i m => emp m /\ y = Val 4) :=
  sdo (stry (sfree x) (fun _ => sret 4) 
                      (fun _ => sret 5)).

Next Obligation.
apply eval_stry_sfree.
exists i.
exists empty.
split.
  eauto.
  split.
 remove_empty.
   apply splits_refl.
apply eval_sret.
  unfold emp in |- *.
  auto.
Defined.



(* base case for throw *)

Lemma eval_sthrow : forall
         (A : Type) (e : exn) (i : heap) (Q : ans A -> hprop),
   Q (Exn e) i -> 
   exists h, 
        (sthrow_pre # this h) i /\
        forall y m, (sthrow_post A e y ## delta(this h)) i m -> Q y m.

intros.
 econstructor.
split.
 unfold sthrow_pre, star1, this, emp in |- *.
   exists empty.
   exists i.
   split.
  remove_empty.
    apply splits_refl.
 auto.
  intros.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H2.
  destruct H2.
  destruct H3.
  rewrite (splits_empty_left H0) in H1.
  remove_empty_in H1; intros H2.
  destruct H2.
  simpl in H2.
  destruct H2.
  auto.
Qed.


Program Definition test_eval_sthrow (e : exn) : STsep emp nat (fun y i m => m = i /\ emp m /\ y = Exn e) :=
  sdo (sthrow nat e).

Next Obligation.
apply eval_sthrow.
auto.
Defined.



(* bind case for throw *)

Lemma eval_sbind_sthrow : forall
          (A B : Type) 
          (e : exn) 
          (p2 : A -> pre) (q2 : A -> post B) 
          (i : heap) (Q : ans B -> hprop),
    Q (Exn e) i -> 
    exists h, 
       (sbind_pre A (sthrow_pre) (sthrow_post A e) p2 # this h) i /\
       forall y m, (sbind_post A B (sthrow_pre) (sthrow_post A e) p2 q2 y ## delta(this h)) i m -> Q y m.

intros.
 econstructor.
split.
 unfold sbind_pre, sthrow_pre, sthrow_post, star1, this, emp, nopre in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  split.
   exists empty.
     exists i.
     split.
    remove_empty.
      apply splits_refl.
   auto.
  intros.
    destruct (H0 empty (refl_equal empty) i).
   remove_empty.
     apply splits_refl.
  destruct H1.
    destruct H2.
     absurd (Val x = Exn e).
    discriminate.
  auto.
 auto.
  intros.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H1.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H2.
 destruct H2.
   destruct H2.
   destruct H2.
   destruct H2.
   destruct H4.
   destruct H4.
   destruct H5.
   destruct H3.
   destruct H3.
   destruct H3.
   destruct (H3 empty (refl_equal empty) x).
  remove_empty.
    apply splits_refl.
 destruct H5.
   destruct H6.
    absurd (Val x3 = Exn e).
   discriminate.
 auto.
destruct H2.
  destruct H2.
  destruct (H3 empty (refl_equal empty) x).
 remove_empty.
   apply splits_refl.
destruct H4.
  destruct H5.
  rewrite H5 in H4.
  remove_empty_in H4; intros H7.
  destruct H7.
  simpl in H7.
  destruct H7.
  destruct H0.
  destruct H1.
   replace x4 with x in H1.
 rewrite <- H1 in H0.
   destruct H0.
    injection H6.
   intros.
   destruct H0.
   destruct H2.
   auto.
apply proof_irrelevance.
Qed.


Program Definition test_eval_sbind_sthrow (e : exn) : STsep emp nat (fun y i m => emp m /\ y = Exn e) :=
  sdo (sbind (sthrow nat e) (fun _ => sret 5)).

Next Obligation.
apply eval_sbind_sthrow.
auto.
Defined.



(* try case for throw *)

Lemma eval_stry_sthrow : forall
          (A B : Type) 
          (e : exn) 
          (p1 : A -> pre) (q1 : A -> post B) 
          (p2 : exn -> pre) (q2 : exn -> post B) 
          (i : heap) (Q : ans B -> hprop),
  (exists h, (p2 e # this h) i /\
      forall y m, (q2 e y ## delta(this h)) i m -> Q y m) ->
   exists h : heap,
     (stry_pre A sthrow_pre (sthrow_post A e) p1 p2 # this h) i /\
     (forall y m, (stry_post A B sthrow_pre (sthrow_post A e) p1 q1 p2 q2 y ## delta (this h)) i m -> Q y m).

intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H2.
exists empty.
split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold stry_pre at 1 in |- *.
    split.
   exists empty.
     exists i.
     split.
    remove_empty.
      apply splits_refl.
   unfold sthrow_pre, emp, nopre in |- *.
      eauto.
  split.
   intros.
     assert (sthrow_pre empty).
    unfold sthrow_pre, emp in |- *.
      auto.
   destruct (H2 empty H3 i).
    remove_empty.
      apply splits_refl.
   destruct H4.
     destruct H5.
      absurd (Val x1 = Exn e).
     discriminate.
   auto.
  intros.
    assert (sthrow_pre empty).
   unfold sthrow_pre, emp in |- *.
     auto.
  destruct (H2 empty H3 i).
   remove_empty.
     apply splits_refl.
  destruct H4.
    destruct H5.
    rewrite H5 in H4.
    remove_empty_in H4; intros H7.
    destruct H7.
    simpl in H7.
    destruct H7.
    clear H5 H4 x2.
     injection H6.
    intros.
    destruct H4.
    clear H6.
    exists x0.
    unfold nopre in |- *.
     eauto.
   unfold this in |- *.
    eauto.
  intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  remove_empty_in H2; intros H5.
  remove_empty_in H3; intros H6.
  destruct H5.
  destruct H6.
  simpl in H5, H6.
  destruct H5.
  destruct H6.
  clear H2 H3 x2 x4.
  destruct H4.
  destruct H3.
 destruct H3.
   destruct H3.
   destruct H3.
   assert (sthrow_pre empty).
  unfold sthrow_pre, emp in |- *.
    auto.
 destruct (H3 empty H5 i).
  remove_empty.
    apply splits_refl.
 destruct H6.
   destruct H7.
    absurd (Val x1 = Exn e).
   discriminate.
 auto.
destruct H3.
  destruct H3.
  destruct H3.
  assert (sthrow_pre empty).
 unfold sthrow_pre, emp in |- *.
   auto.
destruct (H3 empty H5 i).
 remove_empty.
   apply splits_refl.
destruct H6.
  destruct H7.
  rewrite H7 in H6.
  remove_empty_in H6; intros H9.
  injection H8.
  intros.
  destruct H9.
  simpl in H9.
  destruct H9.
  destruct H10.
  clear H7 H8 x4 H6.
  apply H0.
  destruct (H4 x0 H1 x H).
  destruct H6.
  exists x0.
  exists x.
  split.
 auto.
exists x4.
  unfold delta, this in |- *.
   eauto.
Qed.



Program Definition test_eval_stry_sthrow (e : exn) : STsep emp nat (fun y i m => emp m /\ y = Val 6) :=
  sdo (stry (sthrow nat e) (fun _ => sret 5)
                           (fun e => sret 6)).

Next Obligation.
apply eval_stry_sthrow.
apply eval_sret.
auto.
Defined.


(***************************************************************)
(* the following two lemmas are to be used when no other apply *)
(* the first applies when sbinding an abstract term            *)
(* the second applies when strying an abstract term            *)
(* an abstract term is a program whose code is unknown         *)
(* but whose specification has been established before         *)
(***************************************************************)

(*
Definition sbind_pre (A : Type) (p1 : pre) (q1 : post A) (p2 : A -> pre) : pre :=
      (fun i => (p1 # nopre) i /\ forall x h, (p1 --o q1 (Val x)) i h -> (p2 x # nopre) h). 

Definition sbind_post (A B : Type) (p1 : pre) (q1 : post A) (p2 : A -> pre) (q2 : A -> post B) : post B :=
      (fun y i m => (p1 # nopre) i /\ 
           (exists x, exists h, (p1 --o q1 (Val x)) i h /\ (p2 x --o q2 x y) h m) \/
           (exists e, y = Exn e /\ (p1 --o q1 (Exn e)) i m)).
*)

(* bind case for do *)





Lemma eval_sbind_sdo : forall
          (A B : Type)
          (p1 : pre) (q1 : post A) 
          (p2 : A -> pre) (q2 : A -> post B) 
          (i : heap) (Q : ans B -> hprop),
      (exists i1, p1 i1 /\ 
         exists i2, splits i (i1::i2::nil) /\
           forall j j1, splits j (j1::i2::nil) ->

         (forall x, q1 (Val x) i1 j1 -> 
             exists h, (p2 x # this h) j /\ 
                forall y m, (q2 x y ## delta(this h)) j m -> Q y m) /\
           
         (forall e, q1 (Exn e) i1 j1 -> Q (Exn e) j)) -> 

       exists h, 
        (sbind_pre A p1 q1 p2 # this h) i /\
         forall y m, (sbind_post A B p1 q1 p2 q2 y ## delta(this h)) i m -> Q y m.

intros.
destruct H.
destruct H.
destruct H0.
destruct H0.
 econstructor.
split.
 unfold sbind_pre, star1, this in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  split.
   unfold nopre in |- *.
      eauto.
    intros.
    destruct (H2 x H x0 H0).
    destruct H3.
    destruct (H1 h x2 H3).
    destruct (H5 x1 H4).
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H9.
    destruct H10.
    exists x4.
    unfold nopre in |- *.
     eauto.
   auto.
  intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  remove_empty_in H2; intros H5.
  remove_empty_in H3; intros H6.
  destruct H5.
  destruct H6.
  simpl in H5, H6.
  destruct H5.
  destruct H6.
  clear H2 H3 x2 x4.
  destruct H4.
 destruct H2.
   destruct H3.
   destruct H3.
   destruct H3.
   destruct (H3 x H x0 H0).
   destruct H5.
   destruct (H1 x2 x3 H5).
   destruct (H7 x1 H6).
   destruct H9.
   apply H10.
   destruct H9.
   destruct H9.
   destruct H9.
   destruct H11.
   destruct H12.
   destruct (H4 x5 H11 x4 H9).
   destruct H12.
   exists x5.
   exists x4.
   split.
  auto.
 exists x6.
   unfold delta, this in |- *.
    eauto.
  destruct H2.
  destruct H2.
  destruct (H3 x H x0 H0).
  destruct H4.
  destruct (H1 m x2 H4).
  rewrite H2 in |- *.
  apply H7.
  auto.
Qed.





Program Definition test_eval_sbind_sdo (x : nat) : STsep (emp) nat (fun y i m => emp m /\ y = Val (x+2)) :=
  sdo (sbind (test_eval_sret x) (fun t => sret (t+1))).

Next Obligation.
apply eval_sbind_sdo.
exists empty.
split.
 unfold nopre in |- *.
   auto.
exists i.
  split.
 remove_empty.
   apply splits_refl.
intros.
  split.
 intros.
   destruct H1.
   destruct H1.
   remove_empty_in H0; intros H1.
   destruct H1.
   simpl in H1.
   destruct H1.
   clear H0 x1.
   apply eval_sret.
   split.
  auto.
  injection H2.
   intros.
   rewrite H0 in |- *.
   cut (x + 1 + 1 = x + 2).
  auto.
  omega.
intros.
  destruct H1.
  destruct H1.
   absurd (Exn e = Val (x + 1)).
  discriminate.
auto.
Defined.



(* try case for do *)

Lemma eval_stry_sdo : forall
         (A B : Type) 
         (p0 : pre) (q0 : post A) 
         (p1 : A -> pre) (q1 : A -> post B) 
         (p2 : exn -> pre) (q2 : exn -> post B) 
         (i : heap) (Q : ans B -> hprop),

  (exists i1, p0 i1 /\ 
      exists i2, splits i (i1::i2::nil) /\
          forall j j1, splits j (j1::i2::nil) ->

     (forall x, q0 (Val x) i1 j1 -> 
         exists h, (p1 x # this h) j /\ 
           forall y m, (q1 x y ## delta(this h)) j m -> Q y m) /\

     (forall e, q0 (Exn e) i1 j1 -> 
         exists h, (p2 e # this h) j /\ 
           forall y m, (q2 e y ## delta(this h)) j m -> Q y m)) ->  

   exists h : heap,
     (stry_pre A p0 q0 p1 p2 # this h) i /\
     (forall (y : ans B) (m : heap),
      (stry_post A B p0 q0 p1 q1 p2 q2 y ## delta (this h)) i m -> Q y m).

intros.
destruct H.
destruct H.
destruct H0.
destruct H0.
exists empty.
split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold stry_pre in |- *.
    split.
   exists x.
     unfold nopre in |- *.
      eauto.
    split.
   intros.
     destruct (H2 x H x0 H0).
     destruct H3.
     destruct (H1 h x2 H3).
     destruct (H5 x1 H4).
     destruct H7.
     destruct H7.
     destruct H7.
     destruct H7.
     destruct H9.
     destruct H10.
     exists x4.
     unfold nopre in |- *.
      eauto.
    intros.
    destruct (H2 x H x0 H0).
    destruct H3.
    destruct (H1 h x1 H3).
    destruct (H6 e H4).
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H9.
    destruct H10.
    exists x3.
    unfold nopre in |- *.
     eauto.
   unfold this in |- *.
   auto.
  intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H6.
  remove_empty_in H2; intros H5.
  remove_empty_in H3; intros H6.
  destruct H5.
  destruct H6.
  simpl in H5, H6.
  destruct H5.
  destruct H6.
  clear H2 H3 x2 x4.
  destruct H4.
  destruct H3.
 destruct H3.
   destruct H3.
   destruct H3.
   destruct (H3 x H x0 H0).
   destruct H5.
   destruct (H1 x2 x3 H5).
   destruct (H7 x1 H6).
   destruct H9.
   apply H10.
   destruct H9.
   destruct H9.
   destruct H9.
   destruct H11.
   destruct H12.
   destruct (H4 x5 H11 x4 H9).
   destruct H12.
   exists x5.
   exists x4.
   split.
  auto.
 exists x6.
   unfold delta, this in |- *.
    eauto.
  destruct H3.
  destruct H3.
  destruct H3.
  destruct (H3 x H x0 H0).
  destruct H5.
  destruct (H1 x2 x3 H5).
  destruct (H8 x1 H6).
  destruct H9.
  apply H10.
  destruct H9.
  destruct H9.
  destruct H9.
  destruct H11.
  destruct H12.
  destruct (H4 x5 H11 x4 H9).
  destruct H12.
  exists x5.
  exists x4.
  split.
 auto.
unfold delta, this in |- *.
  exists x6.
   eauto.
Qed.




Program Definition test_eval_stry_sdo (x : nat) : STsep (emp) nat (fun y i m => emp m /\ y = Val (x+2)) :=
  sdo (stry (test_eval_sret x) (fun t => sret (t+1))
                               (fun e => sret 3)). 

Next Obligation.
apply eval_stry_sdo.
exists empty.
split.
 unfold nopre in |- *.
   auto.
exists i.
  split.
 remove_empty.
   apply splits_refl.
intros.
  split.
 intros.
   destruct H1.
   destruct H1.
   remove_empty_in H0; intros H1.
   destruct H1.
   simpl in H1.
   destruct H1.
   clear H0 x1.
    injection H2.
   intros.
   rewrite H0 in |- *.
   clear H2 H0.
   apply eval_sret.
   split.
  auto.
  replace (x + 1 + 1) with (x + 2).
  auto.
  omega.
intros.
   absurd (Exn e = Val (x + 1)).
  discriminate.
 tauto.
Defined.


(*****************************************************)
(* associativity lemmas. do not emit any vc's        *)
(* per se, but enable vc generation by exposing      *)
(* commuting conversions between a bind and/or a try *)
(*****************************************************)


(* eval_sbind_sbind shows the equivalence of specs for  *)
(*                                                      *)
(* sbind (sbind c1 (fun x2 => c2 x2)) (fun x3 => c3 x3) *)
(*                                                      *)
(* and                                                  *)
(*                                                      *)
(* sbind c1 (fun x2 => sbind (c2 x2) (fun x3 => c3 x3)) *)

Lemma eval_sbind_sbind : forall
          (A A' B : Type)
          (p1 : pre) (q1 : post A) 
          (p1' : A -> pre) (q1' : A -> post A')
          (p2 : A' -> pre) (q2 : A' -> post B) 
          (i : heap) (Q : ans B -> hprop),
      (exists h, 
        (sbind_pre A p1 q1 (fun x => sbind_pre A' (p1' x) (q1' x) p2) # this h) i /\
        forall y m, (sbind_post A B p1 q1 (fun x => sbind_pre A' (p1' x) (q1' x) p2)
            (fun x => sbind_post A' B (p1' x) (q1' x) p2 q2) y ## delta(this h)) i m -> Q y m) -> 
      exists h, 
        (sbind_pre A' (sbind_pre A p1 q1 p1') (sbind_post A A' p1 q1 p1' q1') p2 # this h) i /\
         forall y m, (sbind_post A' B (sbind_pre A p1 q1 p1') 
            (sbind_post A A' p1 q1 p1' q1') p2 q2 y ## delta(this h)) i m -> Q y m.

intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H1.
destruct H2.
exists empty.
assert (sbind_pre A p1 q1 p1' i).
 unfold sbind_pre in |- *.
   split.
  destruct H1.
    destruct H1.
    destruct H1.
    destruct H2.
    exists x1.
    splits_rewrite_in H1 H.
    splits_join_in H5 (0 :: 1 :: 1 :: nil).
    generalize (splits_commute H6).
     eauto.
   intros.
   destruct (diff1_frame_ex H2 (splits_commute H) H1).
   destruct H4.
   destruct (H3 x1 x2 H5).
   destruct H6.
   destruct H6.
   destruct H7.
   destruct H7.
   destruct H7.
   destruct H7.
   destruct H7.
   destruct H10.
   exists x5.
   splits_rewrite_in H7 H6.
   splits_rewrite_in H12 H4.
   splits_join_in H13 (1 :: 0 :: 1 :: 1 :: nil).
   generalize (splits_commute H14).
    eauto.
  split.
 unfold star1, this in |- *.
   exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold sbind_pre at 1 in |- *.
    split.
   exists i.
     exists empty.
     split.
    remove_empty.
      apply splits_refl.
   unfold nopre in |- *.
     auto.
  intros.
    destruct (H4 i H2 empty).
   remove_empty.
     apply splits_refl.
  destruct H5.
    destruct H6.
   destruct H6.
     destruct H7.
     destruct H7.
     destruct H7.
     remove_empty_in H5; intros H9.
     destruct H9.
     simpl in H9.
     destruct H9.
     clear H5 x5.
     destruct (diff1_frame_ex H7 (splits_commute H) H1).
     destruct H5.
     destruct (H3 x3 x2 H9).
     destruct H10.
     destruct H10.
     destruct H11.
     destruct H11.
     destruct H12.
     splits_rewrite_in H10 H5.
     splits_join_in H12 (1 :: 0 :: 1 :: nil).
     destruct (diff1_frame_ex H8 H14 H11).
     destruct H15.
     destruct (H13 x1 x7 H16).
     destruct H17.
     destruct H17.
     destruct H18.
     destruct H19.
     exists x8.
     splits_flatten_in H15.
     splits_rewrite_in H17 H19.
     splits_join_in H20 (1 :: 1 :: 0 :: 1 :: nil).
     unfold nopre in |- *.
     generalize (splits_commute H21).
      eauto.
    destruct H6.
    destruct H6.
     absurd (Val x1 = Exn x3).
    discriminate.
  auto.
   auto.
  intros.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H7.
  destruct H7.
  destruct H8.
  remove_empty_in H4; intros H7.
  remove_empty_in H5; intros H8.
  destruct H7.
  destruct H8.
  simpl in H7, H8.
  destruct H7.
  destruct H8.
  clear H4 H5 x2 x4.
  destruct H6.
 destruct H4.
   destruct H5.
   destruct H5.
   destruct H5.
   clear H4.
   destruct (H5 i H2 empty).
  remove_empty.
    apply splits_refl.
 destruct H4.
   remove_empty_in H4; intros H8.
   destruct H8.
   simpl in H8.
   destruct H8.
   clear H4 x4.
   destruct H7.
  destruct H4.
    destruct H7.
    destruct H7.
    destruct H7.
    apply H0.
    exists x0.
    exists x.
    split.
   auto.
  destruct (diff1_frame_ex H7 (splits_commute H) H1).
    destruct H9.
    destruct (H3 x3 x5 H10).
    destruct H11.
    destruct H11.
    destruct H12.
    destruct H12.
    destruct H13.
    splits_rewrite_in H11 H9.
    splits_join_in H13 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H8 H15 H12).
    destruct H16.
    generalize (H14 x1 x8 H17).
    intros.
    destruct (diff1_frame_ex H6 H16 H18).
    destruct H19.
    splits_flatten_in H19.
    splits_join_in H21 (0 :: 1 :: 1 :: nil).
    exists (union (x7 :: x9 :: nil) pf1).
    exists x.
    split.
   auto.
  split.
   unfold sbind_post at 1 in |- *.
     left.
     split.
    auto.
   exists x3.
     exists x5.
     split.
    auto.
   unfold diff1 at 1 in |- *.
     intros.
     destruct H23.
     splits_rewrite_in H24 H9.
     splits_join_in H26 (1 :: 0 :: 1 :: nil).
     destruct (diff1_frame_ex H8 H27 H23).
     destruct H28.
     generalize (H25 x1 x10 H29).
     intros.
     destruct (diff1_frame_ex H6 H28 H30).
     destruct H31.
     exists x11.
     split.
    splits_flatten_in H22.
      splits_flatten_in H31.
      destruct H33.
      destruct H34.
      rewrite H33 in H34.
      union_cancel_in H34.
      apply splits_commute.
      exists pf4.
      auto.
   unfold sbind_post in |- *.
     left.
     split.
    auto.
   exists x1.
      eauto.
    unfold delta, this in |- *.
    auto.
   destruct H4.
   destruct H4.
    absurd (Val x1 = Exn x3).
   discriminate.
 auto.
  destruct H4.
  destruct H4.
  rewrite H4 in |- *.
  destruct (H5 i H2 empty).
 remove_empty.
   apply splits_refl.
destruct H6.
  remove_empty_in H6; intros H8.
  destruct H8.
  simpl in H8.
  destruct H8.
  clear H4 H6 x3.
  destruct H7.
 destruct H4.
   destruct H6.
   destruct H6.
   destruct H6.
   apply H0.
   exists x0.
   exists x.
   split.
  auto.
 destruct (diff1_frame_ex H6 (splits_commute H) H1).
   destruct H8.
   destruct (H3 x2 x4 H9).
   destruct H10.
   destruct H10.
   destruct H11.
   destruct H11.
   destruct H12.
   splits_rewrite_in H10 H8.
   splits_join_in H12 (1 :: 0 :: 1 :: nil).
   destruct (diff1_frame_ex H7 H14 H11).
   destruct H15.
   splits_flatten_in H15.
   splits_join_in H17 (0 :: 1 :: 1 :: nil).
   exists (union (x6 :: x7 :: nil) pf1).
   exists x.
   split.
  auto.
 split.
  unfold sbind_post at 1 in |- *.
    left.
    split.
   auto.
  exists x2.
    exists x4.
    split.
   auto.
  unfold diff1 at 1 in |- *.
    intros.
    destruct H19.
    splits_rewrite_in H20 H8.
    splits_join_in H22 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H7 H23 H19).
    destruct H24.
    splits_flatten_in H24.
    elim H17.
    intros.
    destruct H26.
    rewrite H27 in H26.
    union_cancel_in H26.
    exists x8.
    split.
   apply splits_commute.
     exists pf4.
     auto.
  unfold sbind_post in |- *.
    right.
     eauto.
   unfold delta, this in |- *.
   auto.
  destruct H4.
  destruct H4.
  apply H0.
  exists x0.
  exists x.
  split.
 auto.
destruct (diff1_frame_ex H6 (splits_commute H) H1).
  destruct H7.
  exists x3.
  exists x.
  split.
 apply (splits_commute H7).
split.
 unfold sbind_post in |- *.
   right.
    injection H4.
   intros.
   destruct H9.
    eauto.
  unfold delta, this in |- *.
  auto.
Qed.


Program Definition test_eval_sbind_sbind : STsep emp bool (fun y i m => emp m /\ y = Val false) :=
  sdo (sbind (sbind (sret 4) 
                    (fun _ => sret tt)) 
             (fun _ => sret false)).

Next Obligation.
apply eval_sbind_sbind.
apply eval_sbind_sret.
apply eval_sbind_sret.
apply eval_sret.
auto.
Defined.


(* eval_sbind_stry shows the equivalence of specs for  *)
(*                                                     *)
(* sbind (stry c1 (fun x2 => c2 x2) (fun e3 => c3 e3)) *)
(*       (fun y => c4 y)                               *)
(*                                                     *)
(* and                                                 *)
(*                                                     *)
(* stry c1 (fun x2 => sbind (c2 x2) (fun y => c4 y))   *)
(*         (fun e3 => sbind (c3 e3) (fun y => c4 y))   *)

Lemma eval_sbind_stry : forall
       (A B C : Type) 
       (p1 : pre) (q1 : post A) 
       (p2 : A -> pre) (q2 : A -> post B) 
       (p3 : exn -> pre) (q3 : exn -> post B)
       (p4 : B -> pre) (q4 : B -> post C) (i : heap) (Q : ans C -> hprop),
   (exists h : heap,
     (stry_pre A p1 q1 (fun x2 => sbind_pre B (p2 x2) (q2 x2) p4)
                       (fun e3 => sbind_pre B (p3 e3) (q3 e3) p4) # this h) i /\
     (forall y m,
      (stry_post A C p1 q1 (fun x2 => sbind_pre B (p2 x2) (q2 x2) p4)
        (fun x2 => sbind_post B C (p2 x2) (q2 x2) p4 q4) (fun e3 => sbind_pre B (p3 e3) (q3 e3) p4)
        (fun e3 => sbind_post B C (p3 e3) (q3 e3) p4 q4) y  ## delta (this h)) i m -> Q y m)) ->
   exists h : heap,
     (sbind_pre B (stry_pre A p1 q1 p2 p3) (stry_post A B p1 q1 p2 q2 p3 q3) p4 # this h) i /\
     (forall y m, (sbind_post B C (stry_pre A p1 q1 p2 p3) 
                  (stry_post A B p1 q1 p2 q2 p3 q3) p4 q4 y ## delta (this h)) i m -> Q y m).

intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H1.
destruct H3.
destruct H2.
assert (stry_pre A p1 q1 p2 p3 i).
 unfold stry_pre in |- *.
   split.
  destruct H1.
    destruct H1.
    destruct H1.
    destruct H2.
    exists x1.
    splits_rewrite_in H1 H.
    splits_join_in H6 (0 :: 1 :: 1 :: nil).
    generalize (splits_commute H7).
     eauto.
   split.
  intros.
    destruct (diff1_frame_ex H2 (splits_commute H) H1).
    destruct H5.
    destruct (H3 x1 x2 H6).
    destruct H7.
    destruct H7.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H11.
    exists x5.
    splits_rewrite_in H8 H7.
    splits_rewrite_in H13 H5.
    splits_join_in H14 (1 :: 0 :: 1 :: 1 :: nil).
    generalize (splits_commute H15).
     eauto.
   intros.
   destruct (diff1_frame_ex H2 (splits_commute H) H1).
   destruct H5.
   destruct (H4 e x1 H6).
   destruct H7.
   destruct H7.
   destruct H8.
   destruct H8.
   destruct H8.
   destruct H8.
   destruct H8.
   destruct H11.
   exists x4.
   splits_rewrite_in H8 H7.
   splits_rewrite_in H13 H5.
   splits_join_in H14 (1 :: 0 :: 1 :: 1 :: nil).
   generalize (splits_commute H15).
    eauto.
  exists empty.
  split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold sbind_pre in |- *.
    split.
   exists i.
     exists empty.
     split.
    remove_empty.
      apply splits_refl.
   unfold nopre in |- *.
     auto.
  intros.
    destruct (H5 i H2 empty).
   remove_empty.
     apply splits_refl.
  destruct H6.
    remove_empty_in H6; intros H8.
    destruct H8.
    simpl in H8.
    destruct H8.
    clear H6 x3.
    destruct H7.
    destruct H7.
   destruct H7.
     destruct H7.
     destruct H7.
     destruct (diff1_frame_ex H7 (splits_commute H) H1).
     destruct H9.
     destruct (H3 x2 x4 H10).
     destruct H11.
     destruct H11.
     destruct H12.
     destruct H12.
     destruct H13.
     splits_rewrite_in H11 H9.
     splits_join_in H13 (1 :: 0 :: 1 :: nil).
     destruct (diff1_frame_ex H8 H15 H12).
     destruct H16.
     destruct (H14 x1 x7 H17).
     destruct H18.
     destruct H18.
     destruct H19.
     exists x8.
     splits_flatten_in H16.
     splits_rewrite_in H18 H21.
     splits_join_in H22 (1 :: 1 :: 0 :: 1 :: nil).
     generalize (splits_commute H23).
      eauto.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct (diff1_frame_ex H7 (splits_commute H) H1).
    destruct H9.
    destruct (H4 x2 x4 H10).
    destruct H11.
    destruct H11.
    destruct H12.
    destruct H12.
    splits_rewrite_in H11 H9.
    splits_join_in H15 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H8 H16 H12).
    destruct H17.
    destruct (H14 x1 x7 H18).
    destruct H19.
    destruct H19.
    destruct H20.
    exists x8.
    splits_flatten_in H17.
    splits_rewrite_in H19 H22.
    splits_join_in H23 (1 :: 1 :: 0 :: 1 :: nil).
    generalize (splits_commute H24).
     eauto.
   unfold this in |- *.
   auto.
  intros.
  destruct H5.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H6.
  destruct H6.
  destruct H7.
  destruct H8.
  destruct H8.
  destruct H9.
  remove_empty_in H5; intros H8.
  remove_empty_in H6; intros H9.
  destruct H8.
  destruct H9.
  simpl in H8, H9.
  destruct H8.
  destruct H9.
  clear H5 H6 x2 x4.
  apply H0.
  exists x0.
  exists x.
  split.
 auto.
destruct H7.
 destruct H5.
   clear H5.
   destruct H6.
   destruct H5.
   destruct H5.
   destruct (H5 i H2 empty).
  remove_empty.
    apply splits_refl.
 destruct H7.
   remove_empty_in H7; intros H9.
   destruct H9.
   simpl in H9.
   destruct H9.
   clear H7 x4.
   destruct H8.
   destruct H8.
  destruct H8.
    destruct H8.
    destruct H8.
    destruct (diff1_frame_ex H8 (splits_commute H) H1).
    destruct H10.
    destruct (H3 x3 x5 H11).
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    splits_rewrite_in H12 H10.
    splits_join_in H16 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H9 H17 H13).
    destruct H18.
    generalize (H15 x1 x8 H19).
    intros.
    splits_flatten_in H18.
    splits_join_in H21 (1 :: 1 :: 0 :: nil).
    destruct (diff1_frame_ex H6 H22 H20).
    destruct H23.
    splits_flatten_in H23.
    splits_join_in H25 (0 :: 1 :: 1 :: nil).
    exists (union (x7 :: x9 :: nil) pf2).
    exists x.
    split.
   auto.
  split.
   unfold stry_post in |- *.
     split.
    auto.
   left.
     exists x3.
     exists x5.
     split.
    auto.
   unfold diff1 in |- *.
     intros.
     destruct H27.
     splits_rewrite_in H28 H10.
     splits_join_in H30 (1 :: 0 :: 1 :: nil).
     destruct (diff1_frame_ex H9 H31 H27).
     destruct H32.
     generalize (H29 x1 x10 H33).
     intros.
     destruct (diff1_frame_ex H6 H32 H34).
     destruct H35.
     splits_flatten_in H26.
     splits_flatten_in H35.
     destruct H37.
     destruct H38.
     rewrite H37 in H38.
     union_cancel_in H38.
     exists x11.
     split.
    apply splits_commute.
      exists pf5.
      auto.
   unfold sbind_post in |- *.
     left.
     split.
    auto.
    eauto.
    unfold delta, this in |- *.
    auto.
   destruct H8.
   destruct H8.
   destruct H8.
   destruct (diff1_frame_ex H8 (splits_commute H) H1).
   destruct H10.
   destruct (H4 x3 x5 H11).
   destruct H12.
   destruct H12.
   destruct H13.
   destruct H13.
   splits_rewrite_in H12 H10.
   splits_join_in H16 (1 :: 0 :: 1 :: nil).
   destruct (diff1_frame_ex H9 H17 H13).
   destruct H18.
   generalize (H15 x1 x8 H19).
   intros.
   destruct (diff1_frame_ex H6 H18 H20).
   destruct H21.
   splits_flatten_in H21.
   splits_join_in H23 (0 :: 1 :: 1 :: nil).
   exists (union (x7 :: x9 :: nil) pf1).
   exists x.
   split.
  auto.
 split.
  unfold stry_post in |- *.
    split.
   auto.
  right.
    exists x3.
    exists x5.
    split.
   auto.
  unfold diff1 in |- *.
    intros.
    destruct H25.
    splits_rewrite_in H26 H10.
    splits_join_in H28 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H9 H29 H25).
    destruct H30.
    generalize (H27 x1 x10 H31).
    intros.
    destruct (diff1_frame_ex H6 H30 H32).
    destruct H33.
    exists x11.
    splits_flatten_in H33.
    destruct H23.
    destruct H35.
    rewrite H23 in H35.
    union_cancel_in H35.
    split.
   apply splits_commute.
     exists pf4.
     auto.
  unfold sbind_post in |- *.
    left.
    split.
   auto.
   eauto.
   unfold delta, this in |- *.
   auto.
  destruct H5.
  destruct H5.
  rewrite H5 in |- *.
  clear H5.
  destruct (H6 i H2 empty).
 remove_empty.
   apply splits_refl.
destruct H5.
  remove_empty_in H5; intros H8.
  destruct H8.
  simpl in H8.
  destruct H8.
  clear H5 x3.
  destruct H7.
  destruct H7.
 destruct H7.
   destruct H7.
   destruct H7.
   destruct (diff1_frame_ex H7 (splits_commute H) H1).
   destruct H9.
   destruct (H3 x2 x4 H10).
   destruct H11.
   destruct H11.
   destruct H12.
   destruct H12.
   splits_rewrite_in H11 H9.
   splits_join_in H15 (1 :: 0 :: 1 :: nil).
   destruct (diff1_frame_ex H8 H16 H12).
   destruct H17.
   splits_flatten_in H17.
   splits_join_in H19 (0 :: 1 :: 1 :: nil).
   exists (union (x6 :: x7 :: nil) pf1).
   exists x.
   split.
  auto.
 split.
  unfold stry_post in |- *.
    split.
   auto.
  left.
    exists x2.
    exists x4.
    split.
   auto.
  unfold diff1 in |- *.
    intros.
    destruct H21.
    splits_rewrite_in H22 H9.
    splits_join_in H24 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H8 H25 H21).
    destruct H26.
    splits_flatten_in H26.
    destruct H19.
    destruct H28.
    rewrite H19 in H28.
    union_cancel_in H28.
    exists x8.
    split.
   apply splits_commute.
     exists pf4.
     auto.
  unfold sbind_post in |- *.
    right.
     eauto.
   unfold delta, this in |- *.
   auto.
  destruct H7.
  destruct H7.
  destruct H7.
  destruct (diff1_frame_ex H7 (splits_commute H) H1).
  destruct H9.
  destruct (H4 x2 x4 H10).
  destruct H11.
  destruct H11.
  destruct H12.
  destruct H12.
  splits_rewrite_in H11 H9.
  splits_join_in H15 (1 :: 0 :: 1 :: nil).
  destruct (diff1_frame_ex H8 H16 H12).
  destruct H17.
  splits_flatten_in H17.
  splits_join_in H19 (0 :: 1 :: 1 :: nil).
  exists (union (x6 :: x7 :: nil) pf1).
  exists x.
  split.
 auto.
split.
 unfold stry_post in |- *.
   split.
  auto.
 right.
   exists x2.
   exists x4.
   split.
  auto.
 unfold diff1 in |- *.
   intros.
   destruct H21.
   splits_rewrite_in H22 H9.
   splits_join_in H24 (1 :: 0 :: 1 :: nil).
   destruct (diff1_frame_ex H8 H25 H21).
   destruct H26.
   splits_flatten_in H26.
   destruct H19.
   destruct H28.
   rewrite H19 in H28.
   union_cancel_in H28.
   exists x8.
   split.
  apply splits_commute.
    exists pf4.
    auto.
 unfold sbind_post in |- *.
   right.
    eauto.
  unfold delta, this in |- *.
  auto.
Qed.



Program Definition test_eval_sbind_stry : STsep emp unit (fun y i m => emp m /\ y = Val tt) :=
  sdo (sbind (stry (sret 4) 
                   (fun _ => sret false)
                   (fun _ => sret true))
             (fun _ => sret tt)).

Next Obligation.
apply eval_sbind_stry.
apply eval_stry_sret.
apply eval_sbind_sret.
apply eval_sret.
auto.
Defined.


(* eval_stry_sbind shows the equivalence of specs for *)
(*                                                    *)
(* stry (sbind c1 (fun x2 => c2 x2))                  *)
(*      (fun x3 => c3 x3)                             *)
(*      (fun e4 => c4 e4)                             *)
(*                                                    *)
(* and                                                *)
(*                                                    *)
(* stry c1 (fun x2 => stry (c2 x2)                    *)
(*                         (fun x3 => c3 x3)          *)
(*                         (fun e4 => c4 e4))         *)
(*      (fun e4 => c4 e4)                             *)

Lemma eval_stry_sbind : forall
         (A B C : Type) 
         (p1 : pre) (q1 : post A) 
         (p2 : A -> pre) (q2 : A -> post B) 
         (p3 : B -> pre) (q3 : B -> post C) 
         (p4 : exn -> pre) (q4 : exn -> post C) (i : heap) (Q : ans C -> hprop),
    (exists h : heap,
        (stry_pre A p1 q1 (fun x2 => stry_pre B (p2 x2) (q2 x2) p3 p4) p4 # this h) i /\
        (forall y m, (stry_post A C p1 q1 (fun x2 => stry_pre B (p2 x2) (q2 x2) p3 p4)
          (fun x2 => stry_post B C (p2 x2) (q2 x2) p3 q3 p4 q4) p4 q4 y ## delta (this h)) i m -> Q y m)) ->
    exists h : heap,
      (stry_pre B (sbind_pre A p1 q1 p2) (sbind_post A B p1 q1 p2 q2) p3 p4 # this h) i /\
      (forall y m, (stry_post B C (sbind_pre A p1 q1 p2) 
              (sbind_post A B p1 q1 p2 q2) p3 q3 p4 q4 y ## delta (this h)) i m -> Q y m).

intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H1.
destruct H2.
assert (sbind_pre A p1 q1 p2 i).
 unfold sbind_pre in |- *.
   split.
  destruct H1.
    destruct H1.
    destruct H1.
    destruct H2.
    exists x1.
    splits_rewrite_in H1 H.
    splits_join_in H5 (0 :: 1 :: 1 :: nil).
    generalize (splits_commute H6).
     eauto.
   intros.
   destruct (diff1_frame_ex H2 (splits_commute H) H1).
   destruct H4.
   destruct H3.
   destruct (H3 x1 x2 H5).
   destruct H7.
   destruct H7.
   destruct H8.
   destruct H8.
   destruct H8.
   destruct H8.
   destruct H8.
   destruct H11.
   exists x5.
   splits_rewrite_in H8 H7.
   splits_rewrite_in H13 H4.
   splits_join_in H14 (1 :: 0 :: 1 :: 1 :: nil).
   generalize (splits_commute H15).
    eauto.
  exists empty.
  split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold stry_pre in |- *.
    split.
   exists i.
     exists empty.
     split.
    remove_empty.
      apply splits_refl.
   unfold nopre in |- *.
     auto.
  split.
   intros.
     destruct (H4 i H2 empty).
    remove_empty.
      apply splits_refl.
   destruct H5.
     remove_empty_in H5; intros H7.
     destruct H7.
     simpl in H7.
     destruct H7.
     clear H5 x3.
     destruct H6.
    destruct H5.
      destruct H6.
      destruct H6.
      destruct H6.
      destruct H3.
      destruct (diff1_frame_ex H6 (splits_commute H) H1).
      destruct H9.
      destruct (H3 x2 x4 H10).
      destruct H11.
      destruct H11.
      destruct H12.
      destruct H12.
      destruct H14.
      splits_rewrite_in H11 H9.
      splits_join_in H16 (1 :: 0 :: 1 :: nil).
      destruct (diff1_frame_ex H7 H17 H12).
      destruct H18.
      destruct (H14 x1 x7 H19).
      destruct H20.
      destruct H20.
      destruct H21.
      exists x8.
      splits_flatten_in H18.
      splits_rewrite_in H20 H23.
      splits_join_in H24 (1 :: 1 :: 0 :: 1 :: nil).
      generalize (splits_commute H25).
       eauto.
     destruct H5.
     destruct H5.
      absurd (Val x1 = Exn x2).
     discriminate.
   auto.
    intros.
    destruct (H4 i H2 empty).
   remove_empty.
     apply splits_refl.
  destruct H5.
    remove_empty_in H5; intros H7.
    destruct H7.
    simpl in H7.
    destruct H7.
    clear H5 x2.
    destruct H6.
   destruct H5.
     destruct H6.
     destruct H6.
     destruct H6.
     destruct H3.
     destruct (diff1_frame_ex H6 (splits_commute H) H1).
     destruct H9.
     destruct (H3 x1 x3 H10).
     destruct H11.
     destruct H11.
     destruct H12.
     destruct H12.
     destruct H14.
     splits_rewrite_in H11 H9.
     splits_join_in H16 (1 :: 0 :: 1 :: nil).
     destruct (diff1_frame_ex H7 H17 H12).
     destruct H18.
     destruct (H15 e x6 H19).
     destruct H20.
     destruct H20.
     destruct H21.
     exists x7.
     splits_flatten_in H18.
     splits_rewrite_in H20 H23.
     splits_join_in H24 (1 :: 1 :: 0 :: 1 :: nil).
     generalize (splits_commute H25).
      eauto.
    destruct H5.
    destruct H5.
    destruct H3.
     injection H5.
    intros.
    destruct H8.
    clear H5.
    destruct (diff1_frame_ex H6 (splits_commute H) H1).
    destruct H5.
    destruct (H7 e x1 H8).
    destruct H9.
    destruct H9.
    destruct H10.
    exists x2.
    splits_rewrite_in H9 H5.
    splits_join_in H12 (1 :: 0 :: 1 :: nil).
    generalize (splits_commute H13).
     eauto.
   unfold this in |- *.
   auto.
  intros.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct H5.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H7.
  destruct H7.
  destruct H8.
  remove_empty_in H4; intros H7.
  remove_empty_in H5; intros H8.
  destruct H7.
  destruct H8.
  simpl in H7, H8.
  destruct H7.
  destruct H8.
  clear H4 H5 x2 x4.
  destruct H6.
  clear H4.
  destruct H5.
 destruct H4.
   destruct H4.
   destruct H4.
   destruct (H4 i H2 empty).
  remove_empty.
    apply splits_refl.
 destruct H6.
   remove_empty_in H6; intros H8.
   destruct H8.
   simpl in H8.
   destruct H8.
   clear H6 x4.
   destruct H7.
  destruct H6.
    destruct H7.
    destruct H7.
    destruct H7.
    apply H0.
    exists x0.
    exists x.
    split.
   auto.
  destruct (diff1_frame_ex H7 (splits_commute H) H1).
    destruct H9.
    destruct H3.
    destruct (H3 x3 x5 H10).
    destruct H12.
    destruct H12.
    destruct H13.
    destruct H13.
    destruct H15.
    splits_rewrite_in H12 H9.
    splits_join_in H17 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H8 H18 H13).
    destruct H19.
    generalize (H15 x1 x8 H20).
    intros.
    destruct (diff1_frame_ex H5 H19 H21).
    destruct H22.
    splits_flatten_in H22.
    splits_join_in H24 (0 :: 1 :: 1 :: nil).
    exists (union (x7 :: x9 :: nil) pf1).
    exists x.
    split.
   auto.
  split.
   unfold stry_post at 1 in |- *.
     split.
    auto.
   left.
     exists x3.
     exists x5.
     split.
    auto.
   unfold diff1 in |- *.
     intros.
     destruct H26.
     destruct H28.
     splits_rewrite_in H27 H9.
     splits_join_in H30 (1 :: 0 :: 1 :: nil).
     destruct (diff1_frame_ex H8 H31 H26).
     destruct H32.
     generalize (H28 x1 x10 H33).
     intros.
     destruct (diff1_frame_ex H5 H32 H34).
     destruct H35.
     splits_flatten_in H35.
     destruct H24.
     destruct H37.
     rewrite H24 in H37.
     union_cancel_in H37.
     exists x11.
     split.
    apply splits_commute.
      exists pf4.
      auto.
   unfold stry_post in |- *.
     split.
    auto.
   left.
      eauto.
    unfold delta, this in |- *.
    auto.
   destruct H6.
   destruct H6.
    absurd (Val x1 = Exn x3).
   discriminate.
 auto.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct (H4 i H2 empty).
 remove_empty.
   apply splits_refl.
destruct H6.
  remove_empty_in H6; intros H8.
  destruct H8.
  simpl in H8.
  destruct H8.
  clear H6 x4.
  destruct H7.
 destruct H6.
   destruct H7.
   destruct H7.
   destruct H7.
   apply H0.
   exists x0.
   exists x.
   split.
  auto.
 destruct (diff1_frame_ex H7 (splits_commute H) H1).
   destruct H9.
   destruct H3.
   destruct (H3 x3 x5 H10).
   destruct H12.
   destruct H12.
   destruct H13.
   destruct H13.
   destruct H15.
   splits_rewrite_in H12 H9.
   splits_join_in H17 (1 :: 0 :: 1 :: nil).
   destruct (diff1_frame_ex H8 H18 H13).
   destruct H19.
   generalize (H16 x1 x8 H20).
   intros.
   destruct (diff1_frame_ex H5 H19 H21).
   destruct H22.
   splits_flatten_in H22.
   splits_join_in H24 (0 :: 1 :: 1 :: nil).
   exists (union (x7 :: x9 :: nil) pf1).
   exists x.
   split.
  auto.
 split.
  unfold stry_post at 1 in |- *.
    split.
   auto.
  left.
    exists x3.
    exists x5.
    split.
   auto.
  unfold diff1 in |- *.
    intros.
    destruct H26.
    destruct H28.
    splits_rewrite_in H27 H9.
    splits_join_in H30 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H8 H31 H26).
    destruct H32.
    generalize (H29 x1 x10 H33).
    intros.
    destruct (diff1_frame_ex H5 H32 H34).
    destruct H35.
    splits_flatten_in H35.
    destruct H24.
    destruct H37.
    rewrite H24 in H37.
    union_cancel_in H37.
    exists x11.
    split.
   apply splits_commute.
     exists pf4.
     auto.
  unfold stry_post in |- *.
    split.
   auto.
  right.
     eauto.
   unfold delta, this in |- *.
   auto.
  destruct H6.
  destruct H6.
   injection H6.
  intros.
  destruct H8.
  clear H6.
  apply H0.
  exists x0.
  exists x.
  split.
 auto.
destruct (diff1_frame_ex H7 (splits_commute H) H1).
  destruct H6.
  destruct H3.
  generalize (H9 x1 x3 H8).
  intros.
  destruct (diff1_frame_ex H5 H6 H10).
  destruct H11.
  exists x4.
  exists x.
  split.
 apply (splits_commute H11).
split.
 unfold stry_post at 1 in |- *.
   split.
  auto.
 right.
    eauto.
  unfold delta, this in |- *.
  auto.
Qed.


Program Definition test_eval_stry_sbind : STsep emp bool (fun y i m => emp m /\ y = Val false) :=
  sdo (stry (sbind (sret 4) 
                   (fun _ => sret tt))
            (fun _ => sret false)
            (fun _ => sret true)).

Next Obligation.
apply eval_stry_sbind.
apply eval_stry_sret.
apply eval_stry_sret.
apply eval_sret.
auto.
Defined.


(* eval_stry_stry shows the equivalence of specs for *)
(*                                                   *)
(* stry (stry c1 (fun x2 => c2 x2)                   *)
(*               (fun e3 => c3 e3))                  *)
(*      (fun x4 => c4 x4)                            *)
(*      (fun e5 => c5 e5)                            *)
(*                                                   *)
(* and                                               *)
(*                                                   *)
(* stry c1 (fun x2 => stry (c2 x2)                   *) 
(*                         (fun x4 => c4 x4)         *) 
(*                         (fun e5 => c5 e5))        *) 
(*         (fun e3 => stry (c3 e3)                   *)          
(*                         (fun x4 => c4 x4)         *) 
(*                         (fun e5 => c5 e5))        *) 


Lemma eval_stry_stry : forall
         (A B C : Type) 
         (p1 : pre) (q1 : post A) 
         (p2 : A -> pre) (q2 : A -> post B) 
         (p3 : exn -> pre) (q3 : exn -> post B) 
         (p4 : B -> pre) (q4 : B -> post C) 
         (p5 : exn -> pre) (q5 : exn -> post C) (i : heap) (Q : ans C -> hprop), 

  (exists h : heap,
     (stry_pre A p1 q1 (fun x2 => stry_pre B (p2 x2) (q2 x2) p4 p5)
                       (fun e3 => stry_pre B (p3 e3) (q3 e3) p4 p5) # this h) i /\
     (forall y m, 
      (stry_post A C p1 q1 (fun x2 => stry_pre B (p2 x2) (q2 x2) p4 p5)
        (fun x2 => stry_post B C (p2 x2) (q2 x2) p4 q4 p5 q5) (fun e3 => stry_pre B (p3 e3) (q3 e3) p4 p5)
        (fun e3 => stry_post B C (p3 e3) (q3 e3) p4 q4 p5 q5) y ## delta (this h)) i m -> Q y m)) ->
   exists h : heap,
     (stry_pre B (stry_pre A p1 q1 p2 p3) (stry_post A B p1 q1 p2 q2 p3 q3) p4 p5 # this h) i /\
     (forall y m, 
         (stry_post B C (stry_pre A p1 q1 p2 p3) 
         (stry_post A B p1 q1 p2 q2 p3 q3) p4 q4 p5 q5 y ## delta (this h)) i m -> Q y m).

intros.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H.
destruct H1.
destruct H1.
destruct H3.
destruct H2.
assert (stry_pre A p1 q1 p2 p3 i).
 unfold stry_pre in |- *.
   split.
  destruct H1.
    destruct H1.
    destruct H1.
    destruct H2.
    exists x1.
    splits_rewrite_in H1 H.
    splits_join_in H6 (0 :: 1 :: 1 :: nil).
    generalize (splits_commute H7).
     eauto.
   split.
  intros.
    destruct (diff1_frame_ex H2 (splits_commute H) H1).
    destruct H5.
    destruct (H3 x1 x2 H6).
    destruct H7.
    destruct H7.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H8.
    destruct H11.
    exists x5.
    splits_rewrite_in H8 H7.
    splits_rewrite_in H13 H5.
    splits_join_in H14 (1 :: 0 :: 1 :: 1 :: nil).
    generalize (splits_commute H15).
     eauto.
   intros.
   destruct (diff1_frame_ex H2 (splits_commute H) H1).
   destruct H5.
   destruct (H4 e x1 H6).
   destruct H7.
   destruct H7.
   destruct H8.
   destruct H8.
   destruct H8.
   destruct H8.
   destruct H8.
   exists x4.
   splits_rewrite_in H8 H7.
   splits_rewrite_in H12 H5.
   splits_join_in H13 (1 :: 0 :: 1 :: 1 :: nil).
   generalize (splits_commute H14).
    eauto.
  exists empty.
  split.
 exists i.
   exists empty.
   split.
  remove_empty.
    apply splits_refl.
 split.
  unfold stry_pre at 1 in |- *.
    split.
   exists i.
     exists empty.
     split.
    remove_empty.
      apply splits_refl.
   unfold nopre in |- *.
     auto.
  split.
   intros.
     destruct (H5 i H2 empty).
    remove_empty.
      apply splits_refl.
   destruct H6.
     remove_empty_in H6; intros H8.
     destruct H8.
     simpl in H8.
     destruct H8.
     clear H6 x3.
     destruct H7.
     destruct H7.
    destruct H7.
      destruct H7.
      destruct H7.
      destruct (diff1_frame_ex H7 (splits_commute H) H1).
      destruct H9.
      destruct (H3 x2 x4 H10).
      destruct H11.
      destruct H11.
      destruct H12.
      destruct H12.
      destruct H14.
      splits_rewrite_in H11 H9.
      splits_join_in H16 (1 :: 0 :: 1 :: nil).
      destruct (diff1_frame_ex H8 H17 H12).
      destruct H18.
      destruct (H14 x1 x7 H19).
      destruct H20.
      destruct H20.
      destruct H21.
      exists x8.
      splits_flatten_in H18.
      splits_rewrite_in H20 H23.
      splits_join_in H24 (1 :: 1 :: 0 :: 1 :: nil).
      generalize (splits_commute H25).
       eauto.
     destruct H7.
     destruct H7.
     destruct H7.
     destruct (diff1_frame_ex H7 (splits_commute H) H1).
     destruct H9.
     destruct (H4 x2 x4 H10).
     destruct H11.
     destruct H11.
     destruct H12.
     destruct H12.
     destruct H14.
     splits_rewrite_in H11 H9.
     splits_join_in H16 (1 :: 0 :: 1 :: nil).
     destruct (diff1_frame_ex H8 H17 H12).
     destruct H18.
     destruct (H14 x1 x7 H19).
     destruct H20.
     destruct H20.
     destruct H21.
     exists x8.
     splits_flatten_in H18.
     splits_rewrite_in H20 H23.
     splits_join_in H24 (1 :: 1 :: 0 :: 1 :: nil).
     generalize (splits_commute H25).
      eauto.
    intros.
    destruct (H5 i H2 empty).
   remove_empty.
     apply splits_refl.
  destruct H6.
    remove_empty_in H6; intros H8.
    destruct H8.
    simpl in H8.
    destruct H8.
    clear H6 x2.
    destruct H7.
    destruct H7.
   destruct H7.
     destruct H7.
     destruct H7.
     destruct (diff1_frame_ex H7 (splits_commute H) H1).
     destruct H9.
     destruct (H3 x1 x3 H10).
     destruct H11.
     destruct H11.
     destruct H12.
     destruct H12.
     destruct H14.
     splits_rewrite_in H11 H9.
     splits_join_in H16 (1 :: 0 :: 1 :: nil).
     destruct (diff1_frame_ex H8 H17 H12).
     destruct H18.
     destruct (H15 e x6 H19).
     destruct H20.
     destruct H20.
     destruct H21.
     exists x7.
     splits_flatten_in H18.
     splits_rewrite_in H20 H23.
     splits_join_in H24 (1 :: 1 :: 0 :: 1 :: nil).
     generalize (splits_commute H25).
      eauto.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct (diff1_frame_ex H7 (splits_commute H) H1).
    destruct H9.
    destruct (H4 x1 x3 H10).
    destruct H11.
    destruct H11.
    destruct H12.
    destruct H12.
    destruct H14.
    splits_rewrite_in H11 H9.
    splits_join_in H16 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H8 H17 H12).
    destruct H18.
    destruct (H15 e x6 H19).
    destruct H20.
    destruct H20.
    destruct H21.
    exists x7.
    splits_flatten_in H18.
    splits_rewrite_in H20 H23.
    splits_join_in H24 (1 :: 1 :: 0 :: 1 :: nil).
    generalize (splits_commute H25).
     eauto.
   unfold this in |- *.
   auto.
  intros.
  destruct H5.
  destruct H5.
  destruct H5.
  destruct H6.
  destruct H6.
  destruct H6.
  destruct H7.
  destruct H8.
  destruct H8.
  destruct H9.
  remove_empty_in H5; intros H8.
  remove_empty_in H6; intros H9.
  destruct H8.
  destruct H9.
  simpl in H8, H9.
  destruct H8.
  destruct H9.
  clear H5 H6 x2 x4.
  apply H0.
  exists x0.
  exists x.
  split.
 auto.
destruct H7.
  destruct H6.
 destruct H6.
   destruct H6.
   destruct H6.
   destruct (H6 i H2 empty).
  remove_empty.
    apply splits_refl.
 destruct H8.
   destruct H9.
   destruct H10.
  destruct H10.
    destruct H10.
    destruct H10.
    destruct (diff1_frame_ex H10 (splits_commute H) H1).
    destruct H12.
    destruct (H3 x4 x6 H13).
    destruct H14.
    destruct H14.
    destruct H15.
    destruct H15.
    destruct H17.
    splits_rewrite_in H14 H12.
    splits_join_in H19 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H11 H20 H15).
    destruct H21.
    generalize (H17 x1 x9 H22).
    intros.
    splits_flatten_in H21.
    splits_rewrite_in H24 H8.
    remove_empty_in H25; intros H26.
    splits_join_in H26 (1 :: 1 :: 0 :: nil).
    destruct (diff1_frame_ex H7 H27 H23).
    destruct H28.
    splits_flatten_in H28.
    splits_join_in H30 (0 :: 1 :: 1 :: nil).
    exists (union (x8 :: x10 :: nil) pf2).
    exists x.
    split.
   auto.
  split.
   unfold stry_post at 1 in |- *.
     split.
    auto.
   left.
     exists x4.
     exists x6.
     split.
    auto.
   unfold diff1 in |- *.
     intros.
     destruct H32.
     destruct H34.
     splits_rewrite_in H33 H12.
     splits_join_in H36 (1 :: 0 :: 1 :: nil).
     destruct (diff1_frame_ex H11 H37 H32).
     destruct H38.
     generalize (H34 x1 x11 H39).
     intros.
     splits_flatten_in H38.
     splits_rewrite_in H41 H8.
     remove_empty_in H42; intros H43.
     splits_join_in H43 (1 :: 1 :: 0 :: nil).
     destruct (diff1_frame_ex H7 H44 H40).
     destruct H45.
     splits_flatten_in H45.
     destruct H30.
     destruct H47.
     rewrite H30 in H47.
     union_cancel_in H47.
     exists x12.
     split.
    apply splits_commute.
      exists pf6.
      auto.
   unfold stry_post in |- *.
     split.
    auto.
   left.
      eauto.
    unfold delta, this in |- *.
    auto.
   remove_empty_in H8; intros H11.
   destruct H11.
   simpl in H11.
   destruct H11.
   clear H8 x4.
   destruct H10.
   destruct H8.
   destruct H8.
   destruct (diff1_frame_ex H8 (splits_commute H) H1).
   destruct H11.
   destruct (H4 x3 x5 H12).
   destruct H13.
   destruct H13.
   destruct H14.
   destruct H14.
   destruct H16.
   splits_rewrite_in H13 H11.
   splits_join_in H18 (1 :: 0 :: 1 :: nil).
   destruct (diff1_frame_ex H10 H19 H14).
   destruct H20.
   generalize (H16 x1 x8 H21).
   intros.
   destruct (diff1_frame_ex H7 H20 H22).
   destruct H23.
   splits_flatten_in H23.
   splits_join_in H25 (0 :: 1 :: 1 :: nil).
   exists (union (x7 :: x9 :: nil) pf1).
   exists x.
   split.
  auto.
 split.
  unfold stry_post at 1 in |- *.
    split.
   auto.
  right.
    exists x3.
    exists x5.
    split.
   auto.
  unfold diff1 in |- *.
    intros.
    destruct H27.
    destruct H29.
    splits_rewrite_in H28 H11.
    splits_join_in H31 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H10 H32 H27).
    destruct H33.
    generalize (H29 x1 x10 H34).
    intros.
    destruct (diff1_frame_ex H7 H33 H35).
    destruct H36.
    splits_flatten_in H36.
    destruct H25.
    destruct H38.
    rewrite H25 in H38.
    union_cancel_in H38.
    exists x11.
    split.
   apply splits_commute.
     exists pf4.
     auto.
  unfold stry_post in |- *.
    split.
   auto.
  left.
     eauto.
   unfold delta, this in |- *.
   auto.
  destruct H6.
  destruct H6.
  destruct H6.
  destruct (H6 i H2 empty).
 remove_empty.
   apply splits_refl.
destruct H8.
  remove_empty_in H8; intros H10.
  destruct H10.
  simpl in H10.
  destruct H10.
  clear H8 x4.
  destruct H9.
  destruct H9.
 destruct H9.
   destruct H9.
   destruct H9.
   destruct (diff1_frame_ex H9 (splits_commute H) H1).
   destruct H11.
   destruct (H3 x3 x5 H12).
   destruct H13.
   destruct H13.
   destruct H14.
   destruct H14.
   destruct H16.
   splits_rewrite_in H13 H11.
   splits_join_in H18 (1 :: 0 :: 1 :: nil).
   destruct (diff1_frame_ex H10 H19 H14).
   destruct H20.
   generalize (H17 x1 x8 H21).
   intros.
   destruct (diff1_frame_ex H7 H20 H22).
   destruct H23.
   splits_flatten_in H23.
   splits_join_in H25 (0 :: 1 :: 1 :: nil).
   exists (union (x7 :: x9 :: nil) pf1).
   exists x.
   split.
  auto.
 split.
  unfold stry_post at 1 in |- *.
    split.
   auto.
  left.
    exists x3.
    exists x5.
    split.
   auto.
  unfold diff1 in |- *.
    intros.
    destruct H27.
    destruct H29.
    splits_rewrite_in H28 H11.
    splits_join_in H31 (1 :: 0 :: 1 :: nil).
    destruct (diff1_frame_ex H10 H32 H27).
    destruct H33.
    generalize (H30 x1 x10 H34).
    intros.
    destruct (diff1_frame_ex H7 H33 H35).
    destruct H36.
    splits_flatten_in H36.
    destruct H25.
    destruct H38.
    rewrite H25 in H38.
    union_cancel_in H38.
    exists x11.
    split.
   apply splits_commute.
     exists pf4.
     auto.
  unfold stry_post in |- *.
    split.
   auto.
  right.
     eauto.
   unfold delta, this in |- *.
   auto.
  destruct H9.
  destruct H9.
  destruct H9.
  destruct (diff1_frame_ex H9 (splits_commute H) H1).
  destruct H11.
  destruct (H4 x3 x5 H12).
  destruct H13.
  destruct H13.
  destruct H14.
  destruct H14.
  destruct H16.
  splits_rewrite_in H13 H11.
  splits_join_in H18 (1 :: 0 :: 1 :: nil).
  destruct (diff1_frame_ex H10 H19 H14).
  destruct H20.
  generalize (H17 x1 x8 H21).
  intros.
  destruct (diff1_frame_ex H7 H20 H22).
  destruct H23.
  splits_flatten_in H23.
  splits_join_in H25 (0 :: 1 :: 1 :: nil).
  exists (union (x7 :: x9 :: nil) pf1).
  exists x.
  split.
 auto.
split.
 unfold stry_post at 1 in |- *.
   split.
  auto.
 right.
   exists x3.
   exists x5.
   split.
  auto.
 unfold diff1 in |- *.
   intros.
   destruct H27.
   destruct H29.
   splits_rewrite_in H28 H11.
   splits_join_in H31 (1 :: 0 :: 1 :: nil).
   destruct (diff1_frame_ex H10 H32 H27).
   destruct H33.
   generalize (H30 x1 x10 H34).
   intros.
   destruct (diff1_frame_ex H7 H33 H35).
   destruct H36.
   splits_flatten_in H36.
   destruct H25.
   destruct H38.
   rewrite H25 in H38.
   union_cancel_in H38.
   exists x11.
   split.
  apply splits_commute.
    exists pf4.
    auto.
 unfold stry_post in |- *.
   split.
  auto.
 right.
    eauto.
  unfold delta, this in |- *.
  auto.
Qed.


Program Definition test_eval_stry_stry (e : exn) : STsep emp bool (fun y i m => emp m /\ y = Val true) :=
  sdo (stry (stry (sret 4) 
                      (fun _ => sthrow nat e)
                      (fun _ => sret 20))
            (fun _ => sret false)
            (fun _ => sret true)).

Next Obligation.
apply eval_stry_stry.
apply eval_stry_sret.
apply eval_stry_sthrow.
apply eval_sret.
auto.
Defined.


(* The simplification lemma for cases on sums -- life was much improved
 * once I introduced this.
 *)
Lemma eval_case_sum : 
  forall (A:Type)(B:Type)(C:Type)(v : sum A B)(p1 : A->pre)(p2: B -> pre)
         (q1 : A -> post C)(q2 : B -> post C)(i : heap)(Q : ans C -> hprop),
  (forall x:A, v = inl B x -> 
     exists h, 
       (p1 x # this h) i /\ forall z m,((q1 x z) ## delta(this h)) i m -> Q z m)
  ->
  (forall y:B, v = inr A y -> 
     exists h, 
       (p2 y # this h) i /\ forall z m,((q2 y z) ## delta(this h)) i m -> Q z m)
  ->
  exists h, (case_sum_pre v p1 p2 # this h) i /\
            forall z m, (case_sum_post v q1 q2 z ## delta(this h)) i m -> Q z m.
intros.
induction v.
 clear H0.
   assert (inl B a = inl B a).
  auto.
 pose (H _ H0).
   destruct e.
   destruct H1.
   clear H.
   destruct H1.
   destruct H.
   decompose [and] H.
   clear H.
   rewrites.
   exists x.
   split.
  unfold case_sum_pre in |- *.
    unfold star1, this in |- *.
    exists x0.
    exists x.
    simple_splits.
    inversion H. subst.
     auto.
   congruence.
 unfold case_sum_post in |- *.
   unfold star2, delta, this in |- *.
   simple_splits.
   assert ((q1 a z ## delta (this x5)) i m).
    pose (H5 _ H0).
    clear H6.
    unfold star2, this in |- *.
    exists x2.
    exists x5.
    split.
   auto.
  exists x4.
    exists x5.
    unfold delta in |- *.
    simple_splits.
 apply (H2 z m H).
  clear H.
  assert (inr A b = inr A b).
 auto.
pose (H0 _ H).
  destruct e.
  clear H0.
  destruct H1.
  destruct H0.
  destruct H0.
  decompose [and] H0.
  clear H0.
  unfold this in *.
  rewrite <- H5 in *.
  clear H5 x1.
  exists x.
  split.
 unfold case_sum_pre in |- *.
   unfold star1 in |- *.
   exists x0.
   exists x.
   simple_splits.
   congruence.
 assert (b = y).
   congruence.
 rewrite <- H3 in |- *.
   auto.
unfold case_sum_post, star2, delta in |- *.
  intros.
  assert ((q2 b z ## delta (this x)) i m).
   destruct H0.
   destruct H0.
   destruct H0.
   destruct H3.
   destruct H3.
   decompose [and] H3.
   rewrite <- H7 in *.
   clear H7 x2.
   rewrite <- H10 in *.
   clear H10 x4.
   clear H6.
   pose (H9 _ H).
   unfold star2, delta, this in |- *.
   exists x1.
   exists x.
   split.
  auto.
 exists x3.
   exists x.
   simple_splits.
apply (H1 _ _ H3).
Qed.


(****************************************************)
(* A tactic for simplifying verification conditions *) 
(* by applying the various eval_<foo> lemmas        *)
(****************************************************)

Ltac nextvc := 
  match goal with

  (* return *) 

  | [|- exists h, (sret_pre # this h) ?i /\
          forall y m, (sret_post ?A ?v y ## delta(this h)) ?i m -> _] =>
          apply (eval_sret A v i); 
          nextvc 

  | [|- exists h, (sbind_pre ?A sret_pre (sret_post ?A ?v) ?p2 # this h) ?i /\
          forall y m, (sbind_post ?A ?B sret_pre (sret_post ?A ?v) ?p2 ?q2 y
                       ## delta(this h)) ?i m -> _] =>
          apply (eval_sbind_sret A B v p2 q2 i);
          nextvc 

  | [|- exists h, (stry_pre ?A sret_pre (sret_post ?A ?v) ?p1 ?p2 # this h) ?i /\
          forall y m, (stry_post ?A ?B sret_pre (sret_post ?A ?v) ?p1 ?q1 ?p2 ?q2 y
                       ## delta(this h)) ?i m -> _] => 
          apply (eval_stry_sret A B v p1 q1 p2 q2 i); 
          nextvc


  (* read *)
  (* eapplies are not fully instantiated in the case of read *)
  (* this is due to the design of eval lemmas which implicitly *)
  (* quantify over v. this quantification should be made explicit *)
  (* in the future *)

  | [|- exists h, (sread_pre ?A ?x # this h) ?i /\ 
          forall y m, (sread_post ?A ?x y ## delta(this h)) ?i m -> _] =>
          eapply (eval_sread A x); 
          [nextvc | nextvc] 

  | [|- exists h, (sbind_pre ?A (sread_pre ?A ?x) (sread_post ?A ?x) ?p2 # this h) ?i /\
          forall y m, (sbind_post ?A ?B (sread_pre ?A ?x) (sread_post ?A ?x) ?p2 ?q2 y ## delta(this h)) ?i m -> _] =>
          eapply (eval_sbind_sread A B x); 
          [nextvc | nextvc] 

  | [|- exists h, (stry_pre ?A (sread_pre ?A ?x) (sread_post ?A ?x) ?p1 ?p2 # this h) ?i /\
          forall y m, (stry_post ?A ?B (sread_pre ?A ?x) (sread_post ?A ?x) ?p1 ?q1 ?p2 ?q2 y
                ## delta (this h)) ?i m -> _] => 
          eapply (eval_stry_sread A B x);
          [nextvc | nextvc] 

  (* write *)

  | [|- exists h, (swrite_pre ?x # this h) ?i /\
          forall y m, (swrite_post ?A ?x ?v y ## delta(this h)) ?i m -> _] =>
          apply (eval_swrite A x v i);
          nextvc

  | [|- exists h, (sbind_pre unit (swrite_pre ?x) (swrite_post ?A ?x ?v) ?p2 # this h) ?i /\
          forall y m, (sbind_post unit ?B (swrite_pre ?x) (swrite_post ?A ?x ?v) ?p2 ?q2 y ## delta(this h)) ?i m -> _] =>
          apply (eval_sbind_swrite A B x v p2 q2 i);
          nextvc

  | [|- exists h, (stry_pre unit (swrite_pre ?x) (swrite_post ?A ?x ?v) ?p1 ?p2 # this h) ?i /\
          forall y m, (stry_post unit ?B (swrite_pre ?x) (swrite_post ?A ?x ?v) ?p1 ?q1 ?p2 ?q2 y 
               ## delta (this h)) ?i m -> _] => 
          apply (eval_stry_swrite A B x v p1 q1 p2 q2 i);
          nextvc


  (* new *)

  | [|- exists h, (snew_pre # this h) ?i /\
          forall y m, (snew_post ?A ?v y ## delta(this h)) ?i m -> _] =>
          apply (eval_snew A v i);
          nextvc

  | [|- exists h, (sbind_pre loc snew_pre (snew_post ?A ?v) ?p2 # this h) ?i /\
          forall y m, (sbind_post loc ?B snew_pre (snew_post ?A ?v) ?p2 ?q2 y ## delta(this h)) ?i m -> _] =>
          apply (eval_sbind_snew A B v p2 q2 i);
          nextvc

  | [|- exists h, (stry_pre loc snew_pre (snew_post ?A ?v) ?p1 ?p2 # this h) ?i /\
          forall y m, (stry_post loc ?B snew_pre (snew_post ?A ?v) ?p1 ?q1 ?p2 ?q2 y 
               ## delta (this h)) ?i m -> _] => 
          apply (eval_stry_snew A B v p1 q1 p2 q2 i);
          nextvc


  (* free *)

  | [|- exists h, (sfree_pre ?x # this h) ?i /\
          forall y m, (sfree_post ?x y ## delta(this h)) ?i m -> _] =>
          apply (eval_sfree x i); 
          nextvc

  | [|- exists h, (sbind_pre unit (sfree_pre ?x) (sfree_post ?x) ?p2 # this h) ?i /\
          forall y m, (sbind_post unit ?B (sfree_pre ?x) (sfree_post ?x) ?p2 ?q2 y ## delta(this h)) ?i m -> _] =>
          apply (eval_sbind_sfree B x p2 q2 i);
          nextvc

  | [|- exists h, (stry_pre unit (sfree_pre ?x) (sfree_post ?x) ?p1 ?p2 # this h) ?i /\
          forall y m, (stry_post unit ?B (sfree_pre ?x) (sfree_post ?x) ?p1 ?q1 ?p2 ?q2 y 
            ## delta (this h)) ?i m -> _] =>
          apply (eval_stry_sfree B x p1 q1 p2 q2 i);
          nextvc

  (* throw *)

  | [|- exists h, (sthrow_pre # this h) ?i /\
          forall y m, (sthrow_post ?A ?e y ## delta(this h)) ?i m -> _] =>
          apply (eval_sthrow A e i);
          nextvc

  | [|- exists h, (sbind_pre ?A sthrow_pre (sthrow_post ?A ?e) ?p2 # this h) ?i /\
          forall y m, (sbind_post ?A ?B sthrow_pre (sthrow_post ?A ?e) ?p2 ?q2 y ## delta(this h)) ?i m -> _] =>
          apply (eval_sbind_sthrow A B e p2 q2 i);
          nextvc

  | [|- exists h, (stry_pre ?A sthrow_pre (sthrow_post ?A ?e) ?p1 ?p2 # this h) ?i /\
          forall y m, (stry_post ?A ?B sthrow_pre (sthrow_post ?A ?e) ?p1 ?q1 ?p2 ?q2 y 
            ## delta (this h)) ?i m -> _] =>
          apply (eval_stry_sthrow A B e p1 q1 p2 q2 i);
          nextvc


  (* case *)
  
  | [|- exists h, (case_sum_pre ?v ?p1 ?p2 # this h) ?i /\
          forall z m, (case_sum_post ?v ?q1 ?q2 z ## delta(this h)) ?i m -> _] =>
          eapply (eval_case_sum _ _ _ v p1 p2 q1 q2); 
          [nextvc | nextvc]
   
       (* other cases missing *)


  (** commuting conversions **)

  | [|- exists h, (sbind_pre ?A' (sbind_pre ?A ?p1 ?q1 ?p1') (sbind_post ?A ?A' ?p1 ?q1 ?p1' ?q1') ?p2 # this h) ?i /\
          forall y m, (sbind_post ?A' ?B (sbind_pre ?A ?p1 ?q1 ?p1')
            (sbind_post ?A ?A' ?p1 ?q1 ?p1' ?q1') ?p2 ?q2 y ## delta(this h)) ?i m -> _] =>
          apply (eval_sbind_sbind A A' B p1 q1 p1' q1' p2 q2 i);
          nextvc

  | [|- exists h, (sbind_pre ?B (stry_pre ?A ?p1 ?q1 ?p2 ?p3) (stry_post ?A ?B
                      ?p1 ?q1 ?p2 ?q2 ?p3 ?q3) ?p4 # this h) ?i /\
          forall y m, (sbind_post ?B ?C (stry_pre ?A ?p1 ?q1 ?p2 ?p3)
                  (stry_post ?A ?B ?p1 ?q1 ?p2 ?q2 ?p3 ?q3) ?p4 ?q4 y 
               ## delta (this h)) ?i m -> _] =>
          apply (eval_sbind_stry A B C p1 q1 p2 q2 p3 q3 p4 q4 i);
          nextvc

  | [|- exists h, (stry_pre ?B (sbind_pre ?A ?p1 ?q1 ?p2) (sbind_post ?A ?B ?p1 ?q1 ?p2 ?q2) ?p3 ?p4 # this h) ?i /\
          forall y m, (stry_post ?B ?C (sbind_pre ?A ?p1 ?q1 ?p2)
              (sbind_post ?A ?B ?p1 ?q1 ?p2 ?q2) ?p3 ?q3 ?p4 ?q4 y ## delta (this h)) ?i m -> _] =>
          apply (eval_stry_sbind A B C p1 q1 p2 q2 p3 q3 p4 q4 i);
          nextvc
 
  | [|- exists h, (stry_pre ?B (stry_pre ?A ?p1 ?q1 ?p2 ?p3) (stry_post ?A ?B ?p1 ?q1 ?p2 ?q2 ?p3 ?q3) ?p4 ?p5 # this h) ?i /\
          forall y m, (stry_post ?B ?C (stry_pre ?A ?p1 ?q1 ?p2 ?p3)
                      (stry_post ?A ?B ?p1 ?q1 ?p2 ?q2 ?p3 ?q3) ?p4 ?q4 ?p5 ?q5 y ## delta (this h)) ?i m -> _] => 
          apply (eval_stry_stry A B C p1 q1 p2 q2 p3 q3 p4 q4 p5 q5 i);
          nextvc

  (* if all else fails, apply the "do" lemmas *)

  | [|- exists h, (sbind_pre ?A ?p1 ?q1 ?p2 # this h) ?i /\
          forall y m, (sbind_post ?A ?B ?p1 ?q1 ?p2 ?q2 y ## delta(this h)) ?i m -> _] => 
        apply (eval_sbind_sdo A B p1 q1 p2 q2 i);
        nextvc
  
  | [|- exists h, (stry_pre ?A ?p0 ?q0 ?p1 ?p2 # this h) ?i /\
          forall y m, (stry_post ?A ?B ?p0 ?q0 ?p1 ?q1 ?p2 ?q2 y ## delta (this h)) ?i m -> _] =>
        apply (eval_stry_sdo A B p0 q0 p1 q1 p2 q2 i);
        nextvc

  | _ => simple_splits
  end.




(**************************)
(** Some simple examples **)
(**************************)

Definition read_inc (x : loc) := 
   sbind (sread x) (fun xv => 
        sret (xv+1)).

Program Definition prec_read_inc (x : loc) :
     STsep (fun i => exists v : nat, (x --> v) i) 
         nat
         (fun y i m => forall v : nat, ((x --> v) i) -> ((x --> v) m) /\ y = Val(v+1)) :=
     sdo (read_inc x). 

Next Obligation.
nextvc.
generalize (points_to_same H0 H1).
intros.
destruct H2.
auto.
Defined.


Definition swap (A B : Type) (x y : loc) :=
            sbind (sread x) (fun xv => 
                sbind (sread y) (fun yv => 
                   sbind (swrite x (yv:B)) (fun t1 => 
		      sbind (swrite y (xv:A)) (fun t2 => 
                         sret tt)))).


Hint Unfold nopre.
Program Definition 
  swap_precise (A B : Type)(x y : loc) :
        STsep (fun i => exists vx : A, exists vy : B, 
		      ((x --> vx) # (y --> vy)) i)
               unit
              (fun r i m => forall (vx:A)(vy:B), 
                          ((x --> vx) # (y --> vy)) i -> ((x --> vy) # (y --> vx)) m /\ r = Val tt) :=
   sdo (swap A B x y).

Next Obligation.

destruct H1 as [h1 [h2 [splits1 [pt1 pt2]]]].
nextvc.
   exists h2.
   exists h1.
   split.
  apply (splits_commute splits1).
    eauto.
  nextvc.
  exists h1.
  split.
  eauto.
  exists h2.
  split.
  eauto.
intros m h1' splits2 pt3.
  nextvc.
  exists h2.
  split.
  eauto. eapply ex_intro. split. apply splits_commute. eauto.
intros m' h2'' splits3 pt4.
  nextvc.
  destruct H1 as [j1 [j2 [splits4 [pt5 pt6]]]].
  destruct (points_to_same_subheap pt1 pt5 splits1 splits4) as [eq1 eq2].
  subst.
  destruct
   (points_to_same_subheap pt6 pt2 (splits_commute splits4) (splits_commute splits1)) as [eq1 eq2].
  subst.
  exists h1'.
  exists h2''.
  split.
 apply (splits_commute splits3).
auto.
Defined.



Program Definition 
    swap_swap (A B : Type) (x y : loc) :
           STsep (fun i => exists xv:A, exists yv:B, ((x --> xv) # (y --> yv)) i)
                  unit 
                 (fun r i m => i = m /\ r = Val tt) :=
   
    sdo (sbind (swap_precise A B x y) (fun _ => swap_precise B A x y)).

Next Obligation.
nextvc.
exists i.
split.
  eauto.
  exists empty.
  split.
 remove_empty.
   apply splits_refl.
intros.
  remove_empty_in H2; intros H3.
  destruct H3.
  simpl in H3.
  destruct H3.
  clear H2 x0.
  split.
 intros.
   destruct (H2 H H0 H1).
   destruct x0.
   clear H4.
   exists empty.
   split.
  exists j.
    exists empty.
    split.
   remove_empty.
     apply splits_refl.
  split.
    eauto.
    unfold this in |- *.
    auto.
   intros.
   destruct H4.
   destruct H4.
   destruct H4.
   destruct H5.
   destruct H5.
   destruct H5.
   destruct H6.
   destruct H7.
   destruct H7.
   destruct H8.
   remove_empty_in H4; intros H7.
   remove_empty_in H5; intros H8.
   destruct H7.
   destruct H8.
   simpl in H7, H8.
   destruct H7.
   destruct H8.
   clear H4 H5 x1 x3.
   destruct (H6 H0 H H3).
   split.
  destruct H1.
    destruct H1.
    destruct H1.
    destruct H7.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H9.
    unfold points_to in H7, H8, H9, H10.
    rewrite <- H7 in H9.
    rewrite <- H8 in H10.
    destruct H9.
    destruct H10.
    destruct H1.
    destruct H4.
    rewrite H1 in |- *.
    rewrite H4 in |- *.
    auto.
 auto.
  intros.
  destruct (H2 H H0 H1).
   absurd (Exn e = Val tt).
  discriminate.
auto.
Defined.


(** local state example **)

Record counter_object : Type :=
  build {inv : nat -> hprop;
         method : STsep (fun i => exists v:nat, inv v i) 
                       nat
                      (fun y i h => forall v, inv v i -> inv (v+1) h /\ y = Val v)}.
  

Program
Definition new_counter : STsep (emp) counter_object (fun y i h => exists v, y = Val v /\ ((inv v) 0) h) :=
   sdo (x <-- snew 0 ; 
        sret (build (fun v h => (x --> v) h)
                    (sdo (y <-- !! x ;
                          x ::= y + 1 ;; 
                          sret y)))).
                  
Next Obligation.
nextvc.  exists i.  split.  eauto.  exists empty.  split.
remove_empty.  apply splits_refl.  intros.  remove_empty_in H1; intros
H3.  destruct H3.  simpl in H3.  destruct H3.  clear H1 x0.  nextvc.
generalize (points_to_same H0 H1); intros H3.  destruct H3.  auto.
generalize (points_to_same H0 H1); intros H3.  destruct H3.  auto.
Defined.

Next Obligation.  
nextvc.  nextvc.  econstructor.  split.  eauto.
simpl.  auto.  
Defined.

Program 
Definition use_counter : STsep (emp) nat (fun y i h => y = Val 2) :=
   sdo (c <-- new_counter;
        x0 <-- method c;
        x1 <-- method c;
        x2 <-- method c;
        sret x2).  
Next Obligation.  
nextvc.  exists empty.  split.  split.  nextvc.  exists empty.  split.
remove_empty.  apply splits_refl.  intros.  remove_empty_in H.  intros
H2.  destruct H2.  simpl in H0.  destruct H0.  clear H x.  split.
intros.  destruct H.  destruct H.  injection H; intros H1.  destruct
H1.  clear H.  nextvc.  exists j.  split.  eauto.  exists empty.
split.  remove_empty.  apply splits_refl.  intros.  remove_empty_in H.
intros H1.  destruct H1.  simpl in H1.  destruct H1.  clear H x0.
split.  intros.  destruct (H 0).  auto.  simpl in H1.  injection H2;
intros H3.  symmetry in H3; destruct H3.  clear H H2.  nextvc.  exists
j0.  split.  eauto.  exists empty.  split.  remove_empty.  apply
splits_refl.  intros.  remove_empty_in H; intros H2.  destruct H2.
simpl in H2.  destruct H2.  clear H x0.  split.  intros.  destruct (H
1 H1).  injection H3; intros H4.  symmetry in H4. destruct H4.  simpl
in H2.  clear H H3.  nextvc.  exists j1.  split.  eauto.  exists
empty.  split.  remove_empty.  apply splits_refl.  intros.
remove_empty_in H.  intros H3.  destruct H3.  simpl in H3.  destruct
H3.  clear H x0.  split.  intros.  destruct (H 2 H2).  injection H4;
intros H5.  symmetry in H5.  destruct H5.  simpl in H3.  clear H H4.
nextvc.  intros; destruct (H 2); tauto.  intros; destruct (H 1); try
discriminate; auto.  intros; destruct (H 0); try discriminate; auto.
intros. destruct H as [H0 [H1 H2]]. discriminate.
Qed.


(*** scratch space; remove eventually 

Record type1 : Type :=
    build {i1 : nat -> hprop;
           i2 : nat -> hprop; 
           body : SIO (fun i => exists v : nat, i1 v i)
                       unit
                      (fun _ i m => forall v :nat, i1 v i -> i2 v m)}.


Program Definition 
   e1 := fun (p : pre) (q : post unit) 
      =>
     fun (g : (unit -> type1) -> (SIO p unit q)) => 
          bind (new_ref 0) (fun x =>
             bind (new_ref 0) (fun y =>
                 bind (g (fun k => 
                              (build
                                 (fun (v:nat) (i:heap) => exists w:nat, ((y --> v) # (x --> w)) i)
                                 (fun (v:nat) (i:heap) => (v = 0 -> ((y --> v) # (x --> 1)) i) /\ (v <> 0 -> False))
                               
                                  (do (bind (read nat y)
                                         (fun t => cond (beq_nat t 0)
                                                           (write x 1)
                                                           (diverge unit)))  
                                                       _ (* proof of coercion *)
                                                ))))
                        (fun _ => 
                      bind (read nat x) 
                          (fun t => cond (beq_nat t 1) (diverge unit) (write y 1))))).

Next Obligation.

destruct H.
destruct H.
destruct H.
destruct H0.
 eapply evals_bind_read.
   unfold star in |- *.
   exists x2.
   exists x3.
   split.
  auto.
 split.
  apply H0.
   unfold nopre in |- *; auto.
   eapply evals_cond.
 intros.
    eapply evals_write.
  exists nat.
    exists x1.
    unfold star in |- *.
    unfold nopre in |- *.
    exists x3.
    exists x2.
    split.
   apply splits_commute; auto.
  auto.
 intros.
   unfold write_pre in H3.
   unfold write_post in H3.
   unfold diff in H3.
   generalize (H3 x2); intros.
   assert
    (((fun i : heap => exists b : Type, exists y : b, (x --> y) i) # this x2)
       i).
  unfold star in |- *.
    exists x3.
    exists x2.
    split.
   apply splits_commute.
     auto.
  split.
   exists nat.
     exists x1.
     auto.
  unfold this in |- *.
    auto.
 destruct (H5 H6).
   destruct H7.
   destruct H7.
   destruct H7.
   destruct H8.
   destruct H9.
   unfold this in H10.
   rewrite H10 in H7.
   rewrite H10 in H8.
   clear x6 H10.
   split.
  destruct H4.
    destruct H4.
    destruct H4.
    destruct H4.
    destruct H10.
    assert (v = x0).
    eapply heap_func.
      unfold star in |- *.
      exists x7.
      exists x8.
      split.
     apply H4.
      split.
     apply H10.
      unfold nopre in |- *; auto.
     unfold star in |- *.
     exists x2.
     exists x3.
     unfold nopre in |- *;  eauto.
    intros.
    rewrite H12 in |- *.
    unfold star in |- *.
    exists x2.
    exists x5.
    split.
   apply splits_commute.
     auto.
   eauto.
   intros.
    absurd (v = 0).
  auto.
 destruct H4.
   destruct H4.
   destruct H4.
   destruct H4.
   destruct H11.
   assert (v = x0).
   eapply heap_func.
     unfold star in |- *.
     exists x7.
     exists x8.
     split.
    apply H4.
     split.
    apply H11.
     unfold nopre in |- *; auto.
    unfold star in |- *.
    exists x2.
    exists x3.
    unfold nopre in |- *;  eauto.
   generalize H2.
   induction x0.
  auto.
 unfold beq_nat in |- *.
   intros.
    absurd (false = true).
   discriminate.
 auto.
  induction x0.
 simpl in |- *.
   intro.
    absurd (true = false).
   discriminate.
 auto.
clear IHx0.
  intros.
  clear H2.
  exists i.
  split.
 unfold star in |- *.
   unfold emp in |- *.
   exists heap_empty.
   exists i.
   split.
  apply splits_commute; auto.
    apply splits_empty.
 unfold this in |- *; auto.
intros.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H2.
  destruct H4.
  destruct H5.
   absurd False.
 auto.
auto.       
Defined.              

*)
