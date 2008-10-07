(***********************************************)
(* Definitions of separation logic connectives *)
(* andassociated lemmas                       *)
(***********************************************)

Require Import Assumptions.
Require Import ProofIrrelevance.
Require Import BasicTactics.
Require Import MemModel.
Require Import List.
Require Import DisjointUnion.
Require Import ST.

(* unary and heap predicates *)
Require Export HeapProp.

Open Local Scope hprop_scope.

(* binary heap predicates *)
Definition hhprop := heap -> heap -> Prop.

(* separation logic connectives *)

Definition emp : hprop := 
   fun h => h = empty.

Definition splits (h : heap) (hs : list heap) : Prop := 
   exists pf : disjoint hs, h = union hs pf.

Definition star1 (p1 p2 : hprop) : hprop :=
   fun h => exists h1, exists h2, splits h (h1::h2::nil) /\ p1 h1 /\ p2 h2.

Definition star2 (q1 q2 : hhprop) : hhprop :=
   fun i h => exists i1, exists i2, splits i (i1::i2::nil) /\
                exists h1, exists h2, splits h (h1::h2::nil) /\ 
                   q1 i1 h1 /\ q2 i2 h2.

Definition wand (p1 p2 : hprop) : hprop :=
   fun h => forall h1, p1 h1 -> 
              forall h2, splits h2 (h1::h::nil) -> p2 h2.

Definition diff1 (p : hprop) (q : hhprop) : hhprop :=
   fun i h => forall i1, p i1 -> 
                  forall m, splits i (i1::m::nil) -> 
                      exists h1, splits h (h1::m::nil) /\ q i1 h1. 
                
Definition delta (p : hprop) : hhprop := 
   fun i h => p i /\ p h.

Definition nabla (p : hprop) : hhprop :=
   fun i h => p h.               

Definition this (m : heap) : hprop :=
   fun h => m = h.

Definition points_to (l : loc) (A : Type) (v : A) : hprop :=
   fun h => h = update_loc empty l v.

Implicit Arguments points_to [A].
   

Notation "p1 '#' p2"   := (star1 p1 p2)               (at level 50).
Notation "p1 '--#' p2" := (wand p1 p2)                (at level 80).
Notation "q1 '##' q2"  := (star2 q1 q2)               (at level 50).
Notation "l '-->' v"   := (points_to l v)             (at level 50).
Notation "p '--o' q"   := (diff1 p q)                 (at level 75).


(*****************************************)
(* Lemmas and tactics about this and emp *)
(*****************************************)
Lemma this_eq (m : heap)(h:heap) : this m h -> h = m.
  unfold this. symmetry. trivial.
Qed.

Implicit Arguments this_eq [m h].

Lemma emp_eq (h:heap) : emp h -> h = empty.
  unfold emp. trivial.
Qed.

Implicit Arguments emp_eq [h].

Lemma this_refl (h : heap) : this h h.
  unfold this. trivial.
Qed.

Lemma emp_refl : emp empty.
  unfold emp. trivial.
Qed.

Lemma this_sym (h1 : heap) (h2 : heap) : this h1 h2 -> this h2 h1.
  unfold this. intros. symmetry. trivial.
Qed.

Implicit Arguments this_sym [h1 h2].

Hint Resolve this_refl emp_refl.

(* rewrites in a specific hypothesis *)
Ltac rewrite_this_in H :=
   match (type of H) with 
     this _ _ => rewrite -> (this_eq H) in * ; clear H
     | emp _ => rewrite -> (emp_eq H) in * ; clear H
     | _ => fail H "is not a this (or emp) predicate"
   end.

(* finds a single useful hypothesis and rewrites with it *)
Ltac rewrite_this_once :=
   match goal  with 
       [H : this _ _ |- _ ]=> rewrite -> (this_eq H) in * ; clear H
     | [H : emp _ |- _ ] => rewrite -> (emp_eq H) in * ; clear H
     | _ => fail "no this (or emp) predicate found"
   end.

Ltac rewrite_this := repeat rewrite_this_once.
(* testing the tactic *)

Lemma test_rewrite_this :  
   forall (h h1 h2 : heap),
     this h h2 -> emp h2 -> emp h.
intros.
rewrite_this. trivial.
Qed.


(***************************************)
(* Lemmas and tactics about heap lists *)
(***************************************)

Lemma splits_permute : 
   forall (h : heap) (hs1 : list heap), splits h hs1 -> 
        forall (hs2 : list heap), Permutation hs1 hs2 -> splits h hs2.

unfold splits in |- *.
intros.
destruct H.
assert (disjoint hs2).
  eapply disjoint_permute.
    apply x.
   auto.
  exists H1.
  rewrite H in |- *.
  apply union_permute.
  auto.
Qed.

Implicit Arguments splits_permute [h hs1 hs2].


(*****************************************)
(* tactic for removing empty from unions *)
(* given splits h (... :: empty :: ...)  *)
(* produce splits h (... ...)            *)
(*****************************************)

(* removal in a goal *)

Lemma splits_empty_goal :
   forall (h : heap) (hs1 hs2 : list heap),
       splits h (hs1 ++ hs2) -> splits h (hs1 ++ empty :: hs2).

unfold splits in |- *.
intros.
destruct H.
destruct (disjoint_app_elim x).
destruct H1.
assert (disjoint (hs1 ++ empty :: hs2)).
 apply disjoint_app_intro.
  auto.
 simpl in |- *.
   split.
  auto.
 apply disjoint_heap_list_empty.
 apply disjoint_list_list_cons_intro_right.
  apply disjoint_heap_list_empty.
 auto.
exists H3.
  rewrite H in |- *.
  symmetry  in |- *.
  apply union_empty.
Qed.

Implicit Arguments splits_empty_goal [h hs1 hs2].



Ltac remove_empty :=
   match goal with 
     [ |- splits ?h1 ?hs1 ] =>
        match hs1 with 
           context F [empty :: ?X] =>
              let h := fresh "H" with
                  l1 := context F [nil (A:=heap)] with
                  l2 := X in
                  assert (h : splits h1 (l1++empty :: l2)); 
                  [ (apply splits_empty_goal; simpl) |               
                    (simpl in h; apply h) ]
          | _ => idtac "no empty to remove in the goal"; fail 2
        end
     | _ => idtac "goal is not a splits predicate"; fail
   end.    


(* test the tactic *)

Lemma test_remove_empty : 
   forall (h h1 h2 : heap),
      splits h (h1::h2::nil) -> splits h (h1::empty::h2::empty::empty::nil).

intros.
remove_empty.
remove_empty.
remove_empty.
auto.
Qed.

(*****************************************)
(* tactic for removing empty from unions *)
(* in a hypothesis                       *)
(*****************************************)

Lemma splits_empty_hyp :
   forall (h : heap) (hs1 hs2 : list heap), 
       splits h (hs1 ++ empty :: hs2) -> splits h (hs1 ++ hs2).

unfold splits in |- *.
intros.
destruct H.
destruct (disjoint_app_elim x).
destruct H1.
destruct (disjoint_list_list_cons_elim_right H2).
simpl in H1.
destruct H1.
assert (disjoint (hs1 ++ hs2)).
 apply disjoint_app_intro.
  auto.
 auto.
 auto.
exists H6.
  rewrite H in |- *.
  apply union_empty.
Qed.

Implicit Arguments splits_empty_hyp [h hs1 hs2].


Ltac remove_empty_in H :=
   match (type of H) with 
      splits ?h1 ?hs1 => 
         match hs1 with 
            context F [empty :: ?X] =>
               let h := fresh "H" in
               let l1 := context F [nil (A:=heap)] in
               let l2 := X in
                   assert (h : splits h1 (l1++l2));
                   [(apply splits_empty_hyp; simpl; apply H) |
                     simpl in h; revert h]
            | _ => idtac "nothing to rewrite in" H; fail 2
         end
      | _ => idtac H "is not a splits predicate"; fail
   end.


(* testing the tactic *)

Lemma test_remove_empty_in :  
   forall (h h1 h2 h3 : heap),
        splits h (h1::h2::empty::h3::nil) -> 
          splits h (h1::h2::h3::nil).

intros.
remove_empty_in H.
auto.
Qed.


(*****************************************)
(* tactic for replacing a heap with      *)
(* its splitting in a goal               *)
(* if H : splits h1 hs1, reduce proving  *)
(* splits h2 (... h1 ...)                *)
(* intro proving splits h2 (... hs1 ...) *)
(*****************************************)

Lemma splits_subst_goal : 
   forall (h1 h2 : heap) (hs0 hs1 hs2 : list heap), 
      splits h1 hs1 ->  splits h2 (hs0 ++ hs1 ++ hs2) ->
         splits h2 (hs0 ++ h1 :: hs2).

unfold splits in |- *.
intros.
destruct H.
destruct H0.
destruct (disjoint_app_elim x0).
destruct H2.
destruct (disjoint_app_elim H2).
destruct H5.
destruct (disjoint_list_list_app_elim_right H3).
assert (disjoint (hs0 ++ h1 :: hs2)).
 apply disjoint_app_intro.
  auto.
 simpl in |- *.
   split.
  auto.
 rewrite H in |- *.
   apply disjoint_heap_list_union_intro.
   auto.
 apply disjoint_list_list_cons_intro_right.
  rewrite H in |- *.
    apply disjoint_heap_list_union_intro.
    apply disjoint_list_list_commute.
    auto.
 auto.
exists H9.
  rewrite H0 in |- *.
  assert (disjoint (hs1 ++ hs2)).
 auto.
assert (disjoint (h1 :: hs2)).
 rewrite H in |- *.
   simpl in |- *.
   split.
  auto.
 apply disjoint_heap_list_union_intro.
   auto.
apply
 (union_app_intro (hs:=hs0) (hs1:=hs1 ++ hs2) (hs2:=
    h1 :: hs2) (pf1:=H10) (pf2:=H11)).
 auto.
apply disjoint_list_list_cons_intro_right.
 rewrite H in |- *.
   apply disjoint_heap_list_union_intro.
   apply disjoint_list_list_commute.
   auto.
auto.
generalize H11.
  rewrite H in |- *.
  intros.
  symmetry  in |- *.
  apply union_assoc.
Qed.

Implicit Arguments splits_subst_goal [h1 h2 hs0 hs1 hs2].


Ltac splits_rewrite H :=
   match (type of H) with 
       splits ?h1 ?hs1 => 
           match goal with
              [ |- splits ?h2 ?hs2 ] => 
                  match hs2 with 
                      context F [h1 :: ?X] =>
                         let h := fresh "H" with
                             d := fresh "D" with
                             l1 := context F [nil (A:=heap)] with
                             l2 := X in
                             assert (h : splits h2 (l1++h1::l2));
                             [(apply (@splits_subst_goal h1 h2 l1 hs1 l2 H); simpl) |
                              (simpl in h; apply h)]
                      | _ => idtac "nothing to rewrite in the goal"; fail 3
                  end
              | _ => idtac "goal is not a splits predicate"; fail 2
           end
       | _ => idtac H "is not a splits predicate"; fail
   end.

(* testing *)

Lemma splits_subst_goal_test : 
   forall (h1 h2 t1 t2 t3 t4: heap),
       splits h1 (t2::t3::nil) -> splits h2 (t1::t2::t3::t4::nil) -> 
           splits h2 (t1::h1::t4::nil).

intros.
splits_rewrite H.
auto.
Qed.


(*****************************************)
(* tactic for replacing a heap with      *)
(* its splitting in a hypothesis         *)
(* if H : splits h1 hs1, and             *)
(* G : splits h2 (... h1 ...), then      *)
(* assume splits h2 (... hs1 ...)        *)
(*****************************************)

Lemma splits_subst_hyp : 
   forall (h1 h2 : heap) (hs0 hs1 hs2 : list heap), 
      splits h1 hs1 -> splits h2 (hs0 ++ h1 :: hs2) -> 
          splits h2 (hs0 ++ hs1 ++ hs2).

unfold splits in |- *.
intros.
destruct H.
rewrite H in H0.
destruct H0.
destruct (disjoint_app_elim x0).
destruct H2.
simpl in H2.
destruct H2.
generalize (disjoint_heap_list_union_elim H4).
intros.
generalize (disjoint_list_list_cons_elim_right H3).
intros.
destruct H6.
generalize (disjoint_heap_list_union_elim H6).
generalize (disjoint_heap_list_union_elim H6).
intros.
assert (disjoint (hs0 ++ hs1 ++ hs2)).
 apply disjoint_app_intro.
  auto.
 apply disjoint_app_intro.
  auto.
 auto.
 auto.
 apply disjoint_list_list_app_intro_right.
  apply disjoint_list_list_commute.
    auto.
 auto.
auto.
  exists H10.
  rewrite H0 in |- *.
  assert (disjoint (union hs1 x :: hs2)).
 simpl in |- *.
    tauto.
assert (disjoint (hs1 ++ hs2)).
 apply disjoint_app_intro.
  auto.
 auto.
 auto.
apply (union_app_intro (hs:=hs0) (pf1:=H11) (pf2:=H12)).
 auto.
apply disjoint_list_list_app_intro_right.
 apply disjoint_list_list_commute.
   auto.
auto.
apply union_assoc.
Qed.

Implicit Arguments splits_subst_hyp [h1 h2 hs0 hs1 hs2]. 



Ltac splits_rewrite_in H G :=
   match (type of H) with 
       splits ?h1 ?hs1 => 
           match (type of G) with
              splits ?h2 ?hs2 => 
                  match hs2 with 
                      context F [h1 :: ?X] =>
                         let h := fresh "H" with
                             d := fresh "D" with
                             l1 := context F [nil (A:=heap)] with
                             l2 := X in
                             assert (h : splits h2 (l1++hs1++l2));
                             [(apply (@splits_subst_hyp h1 h2 l1 hs1 l2 H) ; simpl; apply G) |
                             simpl in h]
                      | _ => idtac "nothing to rewrite in" G; fail 3
                  end
              | _ => idtac G "is not a splits predicate"; fail 2
           end
       | _ => idtac H "is not a splits predicate"; fail
   end.
 

(* testing the tactic *)

Lemma splits_subst_goal_test1 : forall h h1 h2 t t1 t2 t3 t4, 
        splits h (h1::h2::nil) -> splits t (t1::t2::h::t3::t4::nil) -> 
            splits t (t1::t2::h1::h2::t3::t4::nil).

intros.
splits_rewrite_in H H0.
auto.
Qed.

Lemma splits_subst_goal_test2 : 
       forall h t t1 t2, splits h nil -> splits t (t1::h::t2::nil) -> 
                            splits t (t1::t2::nil).
intros.
splits_rewrite_in H H0.
auto.
Qed.

(****************************************************************)
(* question: can we generalize splits_rewrite so that           *)
(* G is C(... splits h2 (... h1 ...) ...)                       *)
(* for arbitrary context C                                      *)
(*                                                              *)
(* it seems that generalization would require lemmas like       *)
(*                                                              *)
(* Lemma Leibniz1 : forall (p1 p2 : Prop) (P : Prop -> Prop),   *)
(*     (p1 <-> p2) -> P(p1) -> P(p2).                           *)
(*                                                              *)
(* and                                                          *)
(*                                                              *)
(* Lemma splits_subst_eq :		                        *)
(*   forall (h1 h2 : heap) (hs0 hs1 hs2 : list heap),           *)
(*      splits h1 hs1 ->                                        *)
(*            splits h2 (hs0 ++ h1 :: hs2) =                    *)
(*            splits h2 (hs0 ++ hs1 ++ hs2).                    *)
(*                                                              *)
(****************************************************************)


(***************************************************)
(* tactic for removing empty from unions in a goal *)
(***************************************************)

Ltac subst_emp H :=
   rewrite H; remove_empty. 

(* testing *)

Lemma subst_emp_test : 
    forall (h h1 h2 t : heap),
       emp h -> splits t (h1::h2::nil) -> 
         splits t (h1::h::h2::nil).

intros.
subst_emp H.
auto.
Qed.


(*********************************************************)
(* tactic for removing empty from unions in a hypothesis *)
(*********************************************************)

(* annoying that coq is not letting me *)
(* name the result of rewriting *)

Ltac subst_emp_in H G :=
    let h := fresh "H" in 
       generalize G; intro h;
       rewrite H in h; 
       remove_empty_in h; 
       clear h.

(* testing the tactic *) 

Lemma subst_emp_in_test : 
   forall (h h1 h2 h3 : heap), 
      emp h2 -> 
          splits h (h1 :: h2 :: h3 :: nil) -> 
             splits h (h1 :: h3 :: nil).

intros.
subst_emp_in H H0.
auto.
Qed.



(***************************************************)
(* tactic for proving permutations on closed lists *)
(* adapted from the reference manual               *)
(***************************************************)

Lemma list_shuffle : 
   forall (A : Type) (x : A) (xs : list A), 
        Permutation (x :: xs) (xs ++ x :: nil).

intros A x.
induction xs.
 simpl in |- *.
   apply perm_skip.
   apply perm_nil.
simpl in |- *.
   eapply perm_trans.
   apply perm_swap.
  apply perm_skip.
  auto.
Qed.

Implicit Arguments list_shuffle [A].



Ltac Permut n := 
  match goal with
  | |- (Permutation nil nil) => apply perm_nil
  | |- (Permutation (?a :: ?l1) (?a :: ?l2)) => 
      let newn := eval compute in (length l1) in 
      (apply perm_skip; Permut newn) 
  | |- (Permutation (?a :: ?l1) ?l2) => 
       match eval compute in n with 
       | 1 => fail 
       | _ => 
           let l1' := constr:(l1 ++ a :: nil) in 
           (apply (perm_trans (l := a :: l1) (l' := l1') (l'' := l2)); 
           [ apply list_shuffle | compute; Permut (pred n) ])
       end 
  end. 


Ltac PermutProve := 
  match goal with
  | |- (Permutation ?l1 ?l2) => 
      match eval compute in (length l1 = length l2) with 
      | (?n = ?n) => Permut n 
      end
  end.

Lemma permut_prove_test : 
    Permutation (1::2::3::nil) (3::2::1::nil).

PermutProve.
Qed.


(************************************************)
(* tactic for joining a heap list into a union  *)
(* in a goal about disjointness                 *)
(************************************************)

Ltac disjoint_join' hs bs hs_union1 hs_union2 H :=
  match hs with
  | nil => assert (H : exists pf, disjoint ((union hs_union2 pf)::hs_union1))
  | (?h::?hs') =>
      match bs with
      | nil => fail "list mismatch"
      | (0::?bs') => disjoint_join' hs' bs' (h::hs_union1) (hs_union2) H
      | (_::?bs') => disjoint_join' hs' bs' (hs_union1) (h::hs_union2) H
      end
  end.

Lemma disjoint_join_lemma : 
   forall (hs1 hs2 : list heap) pf,
     disjoint ((union hs1 pf) :: hs2) -> 
        disjoint (hs1 ++ hs2).

intros.
simpl in H.
apply disjoint_app_intro.
 auto.
 tauto.
destruct H.
  apply (disjoint_heap_list_union_elim H0).
Qed.

Implicit Arguments disjoint_join_lemma [hs1 hs2 pf].

(* new definition of list reverse which does not use ++          *)
(* the existing definition rev uses ++ and is thus               *)
(* not quite good for use in tactics                             *)
(* oftentimes ++ needs to be rewritten in simplifications,       *)
(* but then rewriting cannot be localized only to the occurences *)
(* generated by rev.                                             *)
(* hence the need for a primitive definition which does not      *)
(* depend on ++                                                  *)

Fixpoint lr' (A : Type) (hs : list A) (ts : list A) {struct hs} : list A :=
   match hs with
   | nil => ts
   | cons h' hs' => lr' A hs' (h'::ts)
   end.

Definition lr (A : Type) (hs : list A) : list A := 
     lr' A hs nil.
   
Implicit Arguments lr [A].

Ltac disjoint_join bs := 
  match goal with
  | [ |- disjoint ?hs ] =>
    let hs' := (eval cbv beta iota delta [lr lr'] in (lr hs)) with
        bs' := (eval cbv beta iota delta [lr lr'] in (lr bs)) with
        H := fresh "H" with
        pf := fresh "pf" in
     disjoint_join' hs' bs' (@nil heap) (@nil heap) H;
     [idtac | 
      destruct H as [pf]; 
      generalize (disjoint_join_lemma H); 
      let H1 := fresh "H" in 
      intros H1;
      apply (disjoint_permute H1 (hs2 := hs)); 
      simpl; PermutProve ]
  | _ => idtac "goal is not a disjoint predicate"; fail
  end.


Lemma disjoint_join_test : 
   forall (h1 h2 h3 h4 h5 : heap), 
      (exists pf : disjoint (h2 :: h3 :: nil),
         disjoint (union (h2 :: h3 :: nil) pf :: h1 :: h4 :: h5 :: nil)) -> disjoint (h1::h2::h3::h4::h5::nil).

intros.
disjoint_join (0 :: 1 :: 1 :: 0 :: 0 :: nil).
auto.
Qed.

(************************************************)
(* tactic for joining a heap list into a union  *)
(* in a hypothesis about disjointness           *)
(************************************************)

Lemma disjoint_join_in_lemma : 
   forall (hs1 hs2 hs3 : list heap),
       disjoint hs1 -> Permutation hs1 (hs2 ++ hs3) ->
          exists pf, disjoint ((union hs2 pf) :: hs3).

intros.
assert (disjoint (hs2 ++ hs3)).
  eapply disjoint_permute.
    apply H.
   auto.
  destruct (disjoint_app_elim H1).
  destruct H3.
  exists H2.
  apply disjoint_cons_intro.
 auto.
apply disjoint_heap_list_union_intro.
  auto.
Qed.

Implicit Arguments disjoint_join_in_lemma [hs1 hs2 hs3].


Ltac disjoint_join_in H bs :=
   match (type of H) with
   | (disjoint ?hs) =>
     let hs' := (eval cbv beta iota delta [lr lr'] in (lr hs)) with
         bs' := (eval cbv beta iota delta [lr lr'] in (lr bs)) with
         H1 := fresh "H" with
         pf := fresh "pf" in
       disjoint_join' hs' bs' (@nil heap) (@nil heap) H1;
       [ apply (fun (hs2 hs3 : list heap) => disjoint_join_in_lemma (hs2:=hs2) (hs3:=hs3) H);
         simpl; 
         PermutProve 
       | let pf1 := fresh "pf" in destruct H1 as [pf1] ]
   | _ => idtac H "is not a disjointness predicate"; fail
   end.


Lemma disjoint_join_in_test : 
   forall (h1 h2 h3 h4 h5 : heap), 
     disjoint (h1::h2::h3::h4::h5::nil) ->
      exists pf : disjoint (h2 :: h3 :: nil),
         disjoint (union (h2 :: h3 :: nil) pf :: h1 :: h4 :: h5 :: nil).

intros.
disjoint_join_in H (0 :: 1 :: 1 :: 0 :: 0 :: nil).
exists pf0.
auto.
Qed.


(************************************************)
(* tactic for joining a heap list into a union  *)
(* in a goal about splitting                    *)
(************************************************)

Ltac splits_join' t hs bs hs_union1 hs_union2 H :=
  match hs with
   | nil => assert (H : exists pf, splits t ((union hs_union2 pf)::hs_union1))
   | (?h::?hs') =>
       match bs with 
        | nil => fail "list mismatch"
        | (0 :: ?bs') => splits_join' t hs' bs' (h::hs_union1) (hs_union2) H
        | (_ :: ?bs') => splits_join' t hs' bs' (hs_union1) (h::hs_union2) H
       end
  end.


Lemma union_join_lemma : 
   forall (hs1 hs2 hs3 : list heap) pf1 pf2 pf3,
    Permutation hs3 (hs1 ++ hs2) -> 
       union ((union hs1 pf1) :: hs2) pf2 = union hs3 pf3.

intros.
assert (disjoint (hs1 ++ hs2)).
  eapply disjoint_permute.
    apply pf3.
   auto.
  transitivity (union (hs1 ++ hs2) H0).
 apply union_assoc.
symmetry  in |- *.
  apply union_permute.
  auto.
Qed.

Implicit Arguments union_join_lemma [hs1 hs2 hs3 pf1 pf2 pf3].



Ltac splits_join bs := 
  match goal with
  | [ |- splits ?h ?hs ] =>
    let hs' := (eval cbv beta iota delta [lr lr'] in (lr hs)) with
        bs' := (eval cbv beta iota delta [lr lr'] in (lr bs)) with
        H := fresh "H" with
        pf := fresh "pf" in
     splits_join' h hs' bs' (@nil heap) (@nil heap) H; 
     [idtac | 
      destruct H as [pf]; 
      let pf1 := fresh "pf" in 
      destruct H as [pf1];
      let pf2 := fresh "pf" in
      assert (pf2 : disjoint hs); 
          [ disjoint_join bs; exists pf; apply pf1 | 
            exists pf2; 
            rewrite H;
            apply union_join_lemma;
            simpl;
            PermutProve ]
     ]
  | _ => idtac "goal is not a splits predicate"; fail
  end.
      

(* testing *)

Lemma splits_join_test : 
   forall (h1 h2 h3 h4 h5 : heap), 
     (exists pf : disjoint (h3 :: h4 :: nil),
        splits h1 (union (h3 :: h4 :: nil) pf :: h2 :: h5 :: nil)) ->
     splits h1 (h2::h3::h4::h5::nil).

intros.
splits_join (0 :: 1 :: 1 :: 0 :: nil).
auto.
Qed.


(************************************************)
(* tactic for joining a heap list into a union  *)
(* in a hypothesis about splitting              *)
(************************************************)

Lemma splits_join_in_lemma : 
   forall (h : heap) (hs1 hs2 hs3 : list heap),
       splits h hs1 -> Permutation hs1 (hs2 ++ hs3) ->
          exists pf, splits h ((union hs2 pf) :: hs3).

intros.
destruct H.
assert (disjoint (hs2 ++ hs3)).
  eapply disjoint_permute.
    apply x.
   auto.
  destruct (disjoint_app_elim H1).
  destruct H3.
  exists H2.
  unfold splits in |- *.
  assert (disjoint (union hs2 H2 :: hs3)).
 simpl in |- *.
   split.
  auto.
 apply disjoint_heap_list_union_intro.
   auto.
exists H5.
  rewrite H in |- *.
  symmetry  in |- *.
  apply union_join_lemma.
  auto.
Qed.

Implicit Arguments splits_join_in_lemma [h hs1 hs2 hs3].




Ltac splits_join_in H bs :=
   match (type of H) with
   | (splits ?h ?hs) =>
     let hs' := (eval cbv beta iota delta [lr lr'] in (lr hs)) with
         bs' := (eval cbv beta iota delta [lr lr'] in (lr bs)) with
         H1 := fresh "H" with
         pf := fresh "pf" in
       splits_join' h hs' bs' (@nil heap) (@nil heap) H1;
       [ apply (fun (hs2 hs3 : list heap) => splits_join_in_lemma (hs2:=hs2) (hs3:=hs3) H);
         simpl;
         PermutProve | let pf1 := fresh "pf" in destruct H1 as [pf1] ]
   | _ => idtac H "is not a splits predicate"; fail
   end.


Lemma splits_join_in_test : 
   forall (h h1 h2 h3 h4 h5 : heap), 
     splits h (h1::h2::h3::h4::h5::nil) ->
      exists pf : disjoint (h2 :: h3 :: nil),
         splits h (union (h2 :: h3 :: nil) pf :: h1 :: h4 :: h5 :: nil).

intros.
splits_join_in H (0 :: 1 :: 1 :: 0 :: 0 :: nil).
exists pf0.
auto.
Qed.


(*************************************************)
(* tactic for flattening unions from a heap list *)
(* in a goal about disjointness                  *)
(*************************************************)

(* removes the first union *)

Ltac disjoint_flatten' :=
  match goal with
  | [ |- disjoint ?hs1 ] =>
      match hs1 with 
         context F [union ?hs2 ?pf :: ?X] =>
           let h := fresh "H" with
              l1 := context F [nil (A:=heap)] with
              l2 := X in
              let l3 := (eval cbv beta iota delta [app] in (l1++hs2++l2)) in
              assert (h : exists pf, disjoint ((union hs2 pf)::(l1++l2))); 
              [ idtac | 
                destruct h;
                apply (fun hs2 => disjoint_permute (hs2:=hs2) h);
                simpl; PermutProve ];
              assert (h : disjoint (l3)); 
              [ idtac | 
                apply (fun hs2 hs3 => disjoint_join_in_lemma (hs2:=hs2) (hs3:=hs3) h);
                simpl; 
                PermutProve ]
      | _ => fail 1 "nothing to flatten in the goal"
      end
  | _ => fail "goal is not a disjointness predicate"
  end.

(* loop until all unions removed *)
Ltac disjoint_flatten := repeat (progress disjoint_flatten').

Lemma disjoint_flatten_test : 
    forall (h1 h2 h3 h4 h5 : heap) pf1 pf2,
       disjoint (h1::h2::h3::h4::h5::nil) -> 
           disjoint ((union (h1::h2::nil) pf1)::(union (h3::h4::nil) pf2)::h5::nil).

intros.
disjoint_flatten.
auto.
Qed.


(*************************************************)
(* tactic for flattening unions from a heap list *)
(* in a hypothesis about disjointness            *)
(*************************************************)

(* replace H by a copy without the first union *)
(* repeat until all unions removed *)

Ltac disjoint_flatten_in' H :=
  match (type of H) with
  | disjoint ?hs1 =>
      match hs1 with 
         context F [union ?hs2 ?pf :: ?X] =>
           let h := fresh "H" with
               l1 := context F [nil (A:=heap)] with
               l2 := X in
               let l3 := (eval cbv beta iota delta [app] in (l1++hs2++l2)) in
              assert (h : disjoint ((union hs2 pf)::(l1++l2))); 
              [ apply (fun hs2 => disjoint_permute (hs2:=hs2) H);
                simpl; PermutProve |
                idtac ];
              clear H;
              assert (H : disjoint l3); 
              [ generalize (disjoint_join_lemma h); 
                let h2 := fresh "H" in 
                 intros h2;
                 apply (fun hs2 => disjoint_permute (hs2:=hs2) h2);
                 simpl;
                 PermutProve | clear h ]; 
              disjoint_flatten_in' H
      | _ => idtac
      end
  | _ => fail "hypothesis is not a disjointness predicate"
  end.


(* duplicate H and call disjoint_flatten_in' *)

Ltac disjoint_flatten_in H :=
   generalize H; 
   let h := fresh "H" in
   intros h;
   disjoint_flatten_in' h.


Lemma disjoint_flatten_in_test : 
    forall (h1 h2 h3 h4 h5 : heap) pf1 pf2,
       disjoint ((union(h1::h2::nil) pf1)::(union (h3::h4::nil) pf2)::h5::nil) -> 
            disjoint (h1::h2::h3::h4::h5::nil).

intros.
disjoint_flatten_in H.
auto.
Qed.


(*************************************************)
(* tactic for flattening unions from a heap list *)
(* in a goal about splitting                     *)
(*************************************************)

(* removes the first union *)

Ltac splits_flatten' :=
  match goal with
  | [ |- splits ?h ?hs1 ] =>
      match hs1 with 
         context F [union ?hs2 ?pf :: ?X] =>
           let H := fresh "H" with
              l1 := context F [nil (A:=heap)] with
              l2 := X in
              let l3 := (eval cbv beta iota delta [app] in (l1++hs2++l2)) in
              assert (H : exists pf, splits h ((union hs2 pf)::(l1++l2))); 
              [ idtac | 
                destruct H;
                apply (fun hs2 => splits_permute (hs2:=hs2) H);
                simpl; PermutProve ];
              assert (H : splits h l3); 
              [ idtac | 
                apply (fun hs2 hs3 => splits_join_in_lemma (hs2:=hs2) (hs3:=hs3) H);
                simpl; 
                PermutProve ]
      | _ => fail 1 "nothing to flatten in the goal"
      end
  | _ => fail "goal is not a splitting predicate"
  end.

(* loop until all unions removed *)
Ltac splits_flatten := repeat (progress splits_flatten').

Lemma splits_flatten_test : 
    forall (h h1 h2 h3 h4 h5 : heap) pf1 pf2,
       splits h (h1::h2::h3::h4::h5::nil) -> 
           splits h ((union (h1::h2::nil) pf1)::(union (h3::h4::nil) pf2)::h5::nil).

intros.
splits_flatten.
auto.
Qed.


(*************************************************)
(* tactic for flattening unions from a heap list *)
(* in a hypothesis about splitting               *)
(*************************************************)

Lemma splits_join_lemma :
   forall (h : heap) (hs1 hs2 hs3 : list heap) pf, 
      splits h ((union hs1 pf)::hs2) ->  
            Permutation hs3 (hs1++hs2) -> splits h hs3.

unfold splits in |- *.
intros.
destruct H as (pf2).
destruct (disjoint_cons_elim pf2).
generalize (disjoint_heap_list_union_elim H2); intros.
assert (disjoint hs3).
  eapply disjoint_permute.
    assert (disjoint (hs1 ++ hs2)).
   apply disjoint_app_intro.
    auto.
   auto.
   auto.
  apply H4.
   apply Permutation_sym.
   auto.
  exists H4.
  rewrite H in |- *.
  apply union_join_lemma.
  auto.
Qed.

Implicit Arguments splits_join_lemma [h hs1 pf hs2 hs3].



(* replace H by a copy without the first union *)
(* repeat until all unions removed *)

Ltac splits_flatten_in' H :=
  match (type of H) with
  | splits ?h ?hs1 =>
      match hs1 with 
         context F [union ?hs2 ?pf :: ?X] =>
           let G := fresh "H" with
               l1 := context F [nil (A:=heap)] with
               l2 := X in
               let l3 := (eval cbv beta iota delta [app] in (l1++hs2++l2)) in
              assert (G : splits h ((union hs2 pf)::(l1++l2))); 
              [ apply (fun hs2 => splits_permute (hs2:=hs2) H);
                simpl; PermutProve | idtac ];
              clear H;
              assert (H : splits h l3); 
              [ apply (fun hs3 => splits_join_lemma (hs3:=hs3) G);
                simpl; PermutProve | clear G ];
              splits_flatten_in' H 
      | _ => idtac
      end
  | _ => fail "hypothesis is not a splitting predicate"
  end.


(* duplicate H and call splits_flatten_in' *)

Ltac splits_flatten_in H :=
   generalize H; 
   let h := fresh "H" in
   intros h;
   splits_flatten_in' h.


Lemma splits_flatten_in_test : 
    forall (h h1 h2 h3 h4 h5 : heap) pf1 pf2,
       splits h ((union(h1::h2::nil) pf1)::(union (h3::h4::nil) pf2)::h5::nil) -> 
            splits h (h1::h2::h3::h4::h5::nil).

intros.
splits_flatten_in H.
auto.
Qed.



(********************************************)
(* cancellation tactics over heap equations *)
(* in hypothesis                            *)
(*                                          *)
(* should eventually be generalized         *)
(* to a procedure for solving a system      *)
(* of linear equations over heap variables  *)
(* where the coefficients are 0,1,-1        *)
(********************************************)

(* compute common heaps from two heap lists *)

Lemma union_cancel_in_lemma :
   forall (h : heap) (hs1 hs2 : list heap),
       (exists pf1, exists pf2, union (h :: hs1) pf1 = union (h :: hs2) pf2) -> 
           exists pf1, exists pf2, union hs1 pf1 = union hs2 pf2.

intros.
destruct H.
destruct H.
simpl in x.
simpl in x0.
exists (proj1 x).
exists (proj1 x0).
 eapply union_cons_cancel2.
apply H.
Qed.

Implicit Arguments union_cancel_in_lemma [h hs1 hs2].



Ltac union_cancel_heap_in' h H :=
  match (type of H) with
  | (exists pf1, exists pf2, union ?hs1 pf1 = union ?hs2 pf2) =>
    match hs1 with
      context F1 [h :: ?X1] =>
        match hs2 with
          context F2 [h :: ?X2] => 
           let l1 := context F1 [X1] in
           let l2 := context F2 [X2] in
           let H1 := fresh "H" in
           let H2 := fresh "H" in
           let H3 := fresh "H" in
           let pf1 := fresh "pf1" in
           let pf2 := fresh "pf2" in
           let ppf1 := fresh "pf" in
           elim H; intros pf1 H1; 
           elim H1; intros pf2 H2; 
           assert (H3 : exists pf1, exists pf2, 
              (union (h::l1) pf1) = (union (h::l2) pf2)); 
           [ assert (ppf1 : disjoint (h::l1) /\ disjoint (h::l2)); 
               [ split; [ apply (fun hs2 => disjoint_permute (hs2:=hs2) pf1);
                          PermutProve | 
                          apply (fun hs2 => disjoint_permute (hs2:=hs2) pf2);
                          PermutProve ] |
                 exists (proj1 ppf1); exists (proj2 ppf1);
                 transitivity (union hs1 pf1);
                 [ apply union_permute; PermutProve |
                   rewrite H2; apply union_permute; PermutProve ]
               ]
              | generalize (union_cancel_in_lemma H3);
                clear H pf1 pf2 H1 H2 H3; 
                intro H ]
          | _ => idtac
        end
      | _ => idtac
    end
  | _ => fail
  end.


(* removing all common heaps from the unions *)

Ltac union_cancel_in' hs H :=
  match hs with
   | nil => idtac
   | cons ?h ?hs' => 
       union_cancel_heap_in' h H;
       union_cancel_in' hs' H
  end.


(* wrappers to call union_cancel_heap_in' and union_cancel_in' *)

Ltac union_cancel_heap_in h H :=
  match (type of H) with
   | (union ?hs1 ?pf1 = union ?hs2 ?pf2) => 
       let H1 := fresh "H" in
       assert (H1 : exists pf1, exists pf2, union hs1 pf1 = union hs2 pf2); 
        [ exists pf1; exists pf2; apply H | idtac ];
        union_cancel_heap_in' h H1;
        let pf1 := fresh "pf1" in
        let pf2 := fresh "pf2" in 
        destruct H1 as [pf1 H1];
        destruct H1 as [pf2 H1]
   | _ => fail
   end.


Ltac union_cancel_in H :=
  match (type of H) with
   | (union ?hs1 ?pf1 = union ?hs2 ?pf2) => 
       let H1 := fresh "H" in
       assert (H1 : exists pf1, exists pf2, union hs1 pf1 = union hs2 pf2); 
        [ exists pf1; exists pf2; apply H | idtac ];
        union_cancel_in' hs1 H1;
        let pf1 := fresh "pf1" in
        let pf2 := fresh "pf2" in 
        destruct H1 as [pf1 H1];
        destruct H1 as [pf2 H1]
   | _ => fail
   end.


Lemma union_cancel_in_test : 
    forall (h1 h2 h3 h4 h5 : heap) pf1 pf2,
      (union (h1::h2::h3::nil) pf1 = 
       union (h3::h2::h5::nil) pf2) -> h1 = h5.

intros.
union_cancel_in H.
auto.
Qed.


(********************************************)
(* cancellation tactics over heap equations *)
(* in goals                                 *)
(********************************************)

Parameter union_cancel_lemma :
   forall (h : heap) (hs1 hs2 : list heap),
       (forall pf1, forall pf2, union hs1 pf1 = union hs2 pf2) -> 
          (forall pf1, forall pf2, union (h :: hs1) pf1 = union (h :: hs2) pf2).
   

Ltac union_cancel_heap' h :=
  match goal with
  | [ |- (forall pf1, forall pf2, union ?hs1 pf1 = union ?hs2 pf2) ] =>
    match hs1 with
      context F1 [h :: ?X1] =>
        match hs2 with
          context F2 [h :: ?X2] => 
            let l1 := context F1 [X1] in
            let l2 := context F2 [X2] in
            let H := fresh "H" in
           assert (H : forall pf1, forall pf2, (union (h::l1) pf1) = (union (h::l2) pf2)); 
           [ idtac |
             let pf1 := fresh "pf1" in 
             let pf2 := fresh "pf2" in
             let ppf1 := fresh "pf1" in
             let ppf2 := fresh "pf2" in
             intros pf1 pf2;
             assert (ppf1 : disjoint (h::l1)); 
               [ apply (fun hs2 => disjoint_permute (hs2:=hs2) pf1);
                 PermutProve | idtac ];
             assert (ppf2 : disjoint (h::l2)); 
               [ apply (fun hs2 => disjoint_permute (hs2:=hs2) pf2);
                 PermutProve | idtac ];
             transitivity (union (h::l1) ppf1);
              [ apply union_permute; PermutProve | 
                rewrite (H ppf1 ppf2); apply union_permute; PermutProve ] 
           ];
           apply union_cancel_lemma
          | _ => idtac
        end
      | _ => idtac
    end
  | _ => fail
  end.


(* removing all common heaps from the unions *)

Ltac union_cancel' hs :=
  match hs with
   | nil => idtac
   | cons ?h ?hs' => 
       union_cancel_heap' h;
       union_cancel' hs'
  end.



(* wrappers to call union_cancel_heap' and union_cancel' *)

Ltac union_cancel_heap h :=
  match goal with
   | [ |- (union ?hs1 ?pf1 = union ?hs2 ?pf2) ] => 
       let H1 := fresh "H" in
       assert (H1 : forall pf1, forall pf2, union hs1 pf1 = union hs2 pf2);
       [ idtac | apply H1 ];
       union_cancel_heap' h; intros
   | _ => fail
   end.  


Ltac union_cancel :=
  match goal with 
   | [ |- (union ?hs1 ?pf1 = union ?hs2 ?pf2) ] =>
       let H1 := fresh "H" in
       assert (H1 : forall pf1, forall pf2, union hs1 pf1 = union hs2 pf2);
       [ idtac | apply H1 ];
       union_cancel' hs1;
       intros
   | _ => fail
  end.


Lemma union_cancel_test : 
    forall (h1 h2 h3 h4 h5 : heap) pf1 pf2,
      (exists pf1, exists pf2, union (h1::h4::nil) pf1 = union (h5::nil) pf2) -> 
         union (h1::h2::h3::h4::nil) pf1 = union (h3::h2::h5::nil) pf2.

intros.
union_cancel.
destruct H.
destruct H.
apply H.
Qed.


(**********************************************)
(* Useful lemmas about separation connectives *)
(**********************************************)

Lemma diff1_frame :
   forall (i m h i1 m1 : heap) (p : hprop) (q : hhprop),
        (p --o q) i m ->  splits i (h::i1::nil) -> 
            splits m (h::m1::nil) -> (p --o q) i1 m1. 

unfold diff1 in |- *.
intros.
splits_rewrite_in H3 H0.
splits_join_in H4 (1 :: 0 :: 1 :: nil).
destruct (H i0 H2 (union (h :: m0 :: nil) pf0)).
 apply (splits_permute H5).
   PermutProve.
destruct H6.
  exists x.
  split.
 destruct H1.
   splits_flatten_in H6.
   destruct H8.
   rewrite H1 in H8.
   union_cancel_in H8.
   unfold splits in |- *.
   exists pf2.
   auto.
auto.
Qed.

Implicit Arguments diff1_frame [i m h i1 m1 p q].



Lemma diff1_frame_ex : 
   forall (i m h i1 : heap) (p : hprop) (q : hhprop),
          (p --o q) i m -> splits i (h::i1::nil) -> (p # nopre) i1 ->
                exists m1, splits m (h::m1::nil) /\ (p --o q) i1 m1.

intros.
destruct H1.
destruct H1.
destruct H1.
destruct H2.
clear H3.
splits_rewrite_in H1 H0.
unfold diff1 in H.
splits_join_in H3 (1 :: 0 :: 1 :: nil).
destruct (H x H2 (union (h :: x0 :: nil) pf0)).
 apply (splits_permute H4).
   PermutProve.
destruct H5.
  splits_flatten_in H5.
  splits_join_in H7 (1 :: 0 :: 1 :: nil).
  exists (union (x1 :: x0 :: nil) pf1).
  split.
 apply (splits_permute H8).
   PermutProve.
apply (diff1_frame (i:=i) (m:=m) (h:=h)).
 auto.
auto.
apply (splits_permute H8).
  PermutProve.
Qed.

Implicit Arguments diff1_frame_ex [i m h i1 p q]. 


Lemma splits_refl : 
   forall h : heap, splits h (h :: nil).

intros.
unfold splits in |- *.
simpl in |- *.
assert (True /\ True).
 auto.
exists H.
  auto.
Qed.


Lemma splits_commute : 
   forall (i i1 i2 : heap), 
      splits i (i1::i2::nil) -> splits i (i2::i1::nil).

intros.
apply (splits_permute H).
PermutProve.
Qed.

Implicit Arguments splits_commute [i i1 i2].


Lemma splits_empty_right : 
   forall (i h : heap), 
     splits i (i::h::nil) -> h = empty.

intros.
destruct H.
disjoint_join_in x (1 :: 0 :: nil).
assert (union (i :: nil) pf0 = union (i :: h :: nil) x).
 assert (i = union (i :: nil) pf0).
  destruct (splits_refl i).
     tauto.
 rewrite <- H1 in |- *.
   auto.
union_cancel_in H1.
  generalize (splits_refl empty).
  intros.
  remove_empty_in H3; intros H4.
  destruct H4.
  rewrite H4 in |- *.
  destruct (splits_refl h).
  rewrite H5 in |- *.
   replace x1 with pf2.
  replace x0 with pf1.
  symmetry  in |- *.
    auto.
 apply proof_irrelevance.
apply proof_irrelevance.
Qed.

Implicit Arguments splits_empty_right [i h].

Lemma splits_empty_left : 
   forall (i h : heap), 
     splits i (h::i::nil) -> h = empty.

intros.
 eapply splits_empty_right.
apply splits_commute.
 eexact H.
Qed.

Implicit Arguments splits_empty_left [i h].



Lemma splits_selects_intro : 
   forall (l : loc) (A : Type) (v : A) (h : heap) (hs : list heap),
        splits h hs ->
           (exists h' : heap, In h' hs /\ selects l v h') -> 
              selects l v h.

intros.
destruct H.
rewrite H in |- *.
apply selects_union_intro.
auto.
Qed.

Implicit Arguments splits_selects_intro [l A v h hs].



Lemma splits_selects_elim : 
   forall (l : loc) (A : Type) (v : A) (h : heap) (hs : list heap),
        splits h hs ->
           selects l v h -> 
              exists h' : heap, In h' hs /\ selects l v h'. 

intros.
destruct H.
rewrite H in H0.
apply (selects_union_elim H0).
Qed.

Implicit Arguments splits_selects_elim [l A v h hs].



Lemma splits_update_loc_intro : 
   forall (l : loc) (A : Type) (v : A) (h1 h2 : heap), 
     h1 = update_loc h2 l v ->
        unused_loc l h2 ->
           splits h1 (update_loc empty l v :: h2 :: nil).

unfold splits in |- *.
intros.
assert (disjoint (update_loc empty l v :: h2 :: nil)).
 simpl in |- *.
   split.
  auto.
 split.
  apply disjoint2_update_loc_intro.
     apply disjoint_empty_right.
  auto.
 auto.
exists H1.
  rewrite H in |- *.
  assert
   (exists pf : _, update_loc h2 l v = update_loc (union (h2 :: nil) pf) l v).
 simpl in |- *.
   assert (True /\ True).
  auto.
 exists H2.
   auto.
destruct H2.
  rewrite H2 in |- *.
  apply update_loc_union_empty.
  simpl in |- *.
  auto.
Qed.

Implicit Arguments splits_update_loc_intro [l A v h1 h2].


Lemma splits_update_loc_elim : 
   forall (l : loc) (A : Type) (v : A) (h1 h2 : heap), 
     splits h1 (update_loc empty l v :: h2 :: nil) ->
        h1 = update_loc h2 l v /\ unused_loc l h2.

intros.
destruct H.
split.
 rewrite H in |- *.
   symmetry  in |- *.
   assert (disjoint (h2 :: nil)).
  simpl in |- *.
    auto.
 transitivity (update_loc (union (h2 :: nil) H0) l v).
  simpl in |- *.
    auto.
 apply update_loc_union_empty.
   simpl in |- *.
   apply (disjoint_update_loc_elim x).
   simpl in |- *.
   auto.
apply (disjoint_update_loc_elim x).
  simpl in |- *.
  auto.
Qed.

Implicit Arguments splits_update_loc_elim [l A v h1 h2].


Lemma splits_singleton(h1 h2:heap) : splits h1 (h2::nil) -> h1 = h2.
intros.
unfold splits in H.
destruct H.
unfold union in H.
simpl in H.
auto.
Qed.

Implicit Arguments splits_singleton [h1 h2].

Lemma points_to_same : 
   forall (l : loc) (A : Type) (x0 x1 : A) (h : heap),
    (l --> x0) h -> (l --> x1) h -> x0 = x1.

unfold points_to in |- *.
intros.
assert (selects l x0 h).
 rewrite H in |- *.
   apply sel_eq.
assert (selects l x1 h).
 rewrite H0 in |- *.
   apply sel_eq.
apply (same_selects H1 H2).
Qed.

Implicit Arguments points_to_same [l A x0 x1 h].


Lemma points_to_same_subheap : 
   forall (l : loc) (A : Type) (x1 x2 : A) (i h1 h2 : heap) (hs1 hs2 : list heap),
     (l --> x1) h1 -> (l --> x2) h2 -> 
        splits i (h1::hs1) -> splits i (h2::hs2) ->
            h1 = h2 /\ x1 = x2.

unfold points_to in |- *.
intros.
assert (selects l x1 h1).
 rewrite H in |- *.
   apply sel_eq.
assert (selects l x2 h2).
 rewrite H0 in |- *.
   apply sel_eq.
assert (selects l x1 i).
  eapply splits_selects_intro.
    apply H1.
   exists h1.
   simpl in |- *.
   auto.
  assert (selects l x2 i).
  eapply splits_selects_intro.
    apply H2.
   exists h2.
   simpl in |- *.
   auto.
  generalize (same_selects H5 H6).
  intros.
  destruct H7.
  split.
 rewrite H in |- *.
   rewrite H0 in |- *.
   auto.
auto.
Qed.

Implicit Arguments points_to_same_subheap [l A x1 x2 i h1 h2 hs1 hs2].


Lemma points_to_same_subheap_type : 
   forall (l : loc) (A1 : Type) (x1 : A1) (A2 : Type) (x2 : A2) (i h1 h2 : heap) (hs1 hs2 : list heap),
     (l --> x1) h1 -> (l --> x2) h2 -> 
        splits i (h1::hs1) -> splits i (h2::hs2) ->
            h1 = h2 /\ dyn A1 x1 = dyn A2 x2.

unfold points_to in |- *.
intros.
assert (selects l x1 h1).
 rewrite H in |- *.
   apply sel_eq.
assert (selects l x2 h2).
 rewrite H0 in |- *.
   apply sel_eq.
assert (selects l x1 i).
  eapply splits_selects_intro.
    apply H1.
   exists h1.
   simpl in |- *.
   auto.
  assert (selects l x2 i).
  eapply splits_selects_intro.
    apply H2.
   exists h2.
   simpl in |- *.
   auto.
  generalize (same_selects_type H5 H6).
  intros.
  split.
    injection H7.
   intros.
   destruct H9.
   destruct (points_to_same_subheap H H0 H1 H2).
   auto.
auto.
Qed.

Implicit Arguments points_to_same_subheap_type [l A1 x1 A2 x2 i h1 h2 hs1 hs2].

(* Should be in Separation.v *)
Lemma splits_same_head : forall (i h1 h2:heap) (hs : list heap),
  (splits i (h1::hs)) -> (splits i (h2::hs)) -> h1 = h2.
intros. destruct H. destruct H0. rewrite H in H0.
eapply union_cons_cancel1. apply H0.
Defined.

Implicit Arguments splits_same_head [i h1 h2 hs].

Lemma splits_same_tail : forall (i h:heap) (h1s h2s : list heap),
  (splits i (h::h1s)) -> (splits i (h::h2s)) -> 
    exists pf1, exists pf2, (union h1s pf1) = (union h2s pf2).
intros. generalize H. intro. destruct H1. clear H1. simpl in x. destruct x.
exists H1. generalize H0. intro. destruct H3. clear H3. simpl in x.
destruct x. exists H3. destruct H. destruct H0.  eapply union_cons_cancel2.
rewrite H in H0. apply H0.
Qed.

Implicit Arguments splits_same_tail [i h h1s h2s].

Lemma star1_commute : forall (P1 P2:hprop) (h:heap), (P1 # P2) h -> (P2 # P1) h.
Proof.
  intros P1 P2 h [h1 [h2 [sp [p1 p2]]]]. 
  exists h2. exists h1. split. apply splits_commute.
  trivial. auto.
Qed.

Implicit Arguments star1_commute [P1 P2 h].

(* some lemmas for eliminating emp *)
Lemma elim_emp_left : forall (P:hprop)(h:heap), P h -> (emp # P) h.
Proof.
intros. unfold star1 in |- *. exists empty. exists h. unfold emp in |- *.
cvcsimps. remove_empty. apply splits_refl.
Defined.

Lemma elim_emp_right : forall (P:hprop)(h:heap), P h -> (P # emp) h.
Proof.
intros. unfold star1 in |- *. exists h. exists empty. unfold emp in |- *.
cvcsimps. remove_empty. apply splits_refl.
Defined.

(* some lemmas for eliminating emp from the hypothesis *)
Lemma elim_emp_left_hyp : forall (P:hprop)(h:heap), (emp # P) h -> P h.
Proof.
intros P h [h1 [h2 [sp [empp P1]]]]. unfold emp in empp. subst.
remove_empty_in sp. clear sp. intros sp. 
rewrite (splits_singleton sp). trivial.
Defined.

Implicit Arguments elim_emp_left_hyp [P h].

Lemma elim_emp_right_hyp : forall (P:hprop)(h:heap), (P # emp) h -> P h.
Proof.
  intros. apply elim_emp_left_hyp. apply star1_commute. trivial.
Defined.

Implicit Arguments elim_emp_right_hyp [P h].

(* a lemma about splitting an empty heap *)
Lemma splits_empty_nil : splits empty nil.
unfold splits in |- *. assert (disjoint nil). unfold disjoint in |- *.
auto. exists H. unfold union in |- *. auto.
Defined.

(* a lemma for eliminating nopre when the predicate is satisfied by h *)
Lemma ptsto_star_nopre(P:heap->Prop)(h:heap) : 
  P h -> (P # nopre) h.
intros. exists h. exists empty. split. remove_empty. apply splits_refl.
split. auto. unfold nopre in |- *. auto.
Defined.

(* similar but when h splits *)
Lemma ptsto_star_nopre2(P:heap->Prop)(h h1 h2:heap) : 
  splits h (h1::h2::nil) -> P h1 -> (P # nopre) h.
intros. exists h1. exists h2. unfold nopre. tauto.
Defined.

Lemma splits_empty_emptys (h1:heap) (hs:list heap):
  splits empty (h1::hs) -> emp h1 /\ splits empty hs.
Proof.
  intros. destruct H. destruct (union_empty_emptys H). 
  split; auto.
Qed.

Implicit Arguments splits_empty_emptys [h1 hs].

Lemma splits_empty_empty (h1 h2:heap) :
  splits empty (h1::h2::nil) -> emp h1 /\ emp h2.
Proof.
  intros. destruct H. pose (union_empty_empty H). trivial.
Qed.

Implicit Arguments splits_empty_empty [h1 h2].

Lemma splits_same : forall (i1 i2:heap) (hs : list heap),
  (splits i1 hs) -> (splits i2 hs) -> i1 = i2.
Proof.
intros. destruct H. destruct H0. replace x with x0 in H.
  congruence.
  apply proof_irrelevance.
Qed.

Implicit Arguments splits_same [i1 i2 hs].

Lemma splits_nil_empty (h:heap) :splits h nil -> h = empty.
  intros. destruct H. simpl in H. trivial.
Qed.

Implicit Arguments splits_nil_empty [h].

(* finds useful hypothesis and rewrites with them *)
Ltac rewrites_once :=
   match goal  with 
       [H : this _ _ |- _ ]=> pose (eqa := this_eq H) ; clearbody eqa; clear H; rewrite -> eqa in * ; clear eqa
     | [H : emp _ |- _ ] => pose (eqa := emp_eq H) ; clearbody eqa; clear H; rewrite -> eqa in * ; clear eqa
     | [H : splits empty (?h1) |- _ ] => match (h1) with 
                                  (nil) => clear H
                                  | ( ?h3 :: ?hs ) => 
                                    let emp1 := fresh "emphead" in
                                      let emp2 := fresh "emptail" in
                                        destruct (splits_empty_emptys H) as [emp1 emp2]; clear H
                                      end
     | [H1 : splits ?h1 ?h2 |- _ ] => match goal with 
                                          [H2 : splits h1 h2 |- _ ] => fail 0
                                        | [H2 : splits _ h2 |- _ ] => let eqa := fresh "eqa" in 
                                                              pose (eqa := splits_same H1 H2); clearbody eqa;
                                                                clear H2; rewrite -> eqa in * ; clear eqa
                                      end
                                    ||
                                      match h2 with 
                                         nil => pose (eqa := splits_nil_empty H1) ; 
                                           clearbody eqa; clear H1; rewrite -> eqa in * ; clear eqa
                                       | _ :: nil => pose (eqa := splits_singleton H1) ; 
                                           clearbody eqa; clear H1; rewrite -> eqa in * ; clear eqa
                                       | ?h3 :: ?hs => match goal with
                                                       [H2 : splits h1 h2 |- _ ] => fail 0
                                                       | [H2 : splits h1 ?hh2 |- _ ] => 
                                                          match hh2 with
                                                            ?h4 :: hs => let eqa := fresh "eqa" in 
                                                              pose (eqa := splits_same_head H1 H2); clearbody eqa;
                                                                clear H2; rewrite -> eqa in * ; clear eqa
                                                            | h3 :: ?hhs => 
                                                              match hhs with
                                                                _ :: nil => 
                                                                let eqa := fresh "eqa" in 
                                                                  pose (eqa := splits_same_head (splits_commute H1) (splits_commute H2)); 
                                                                    clearbody eqa; clear H2; rewrite -> eqa in * ; clear eqa
                                                              end
                                                          end
                                                       end
                                     end 

     | _ => fail "nothing to rewrite"
   end.

Ltac rewrites := repeat rewrites_once.
(* testing the tactic *) 

Ltac rewrites_same_tail H1 H2 := 
  let pf1 := fresh "pf1" in 
    let pf2 := fresh "pf2" in   
      let equ := fresh "equ" in  
        destruct (splits_same_tail H1 H2) as [pf1 equ];
          destruct equ as [pf2 equ]; rewrites.


Lemma test_rewrites :  
   forall (h h1 h2 : heap),
     splits h1 (h2::nil) -> this h h2 -> this h1 h.
intros.
rewrites.
trivial.
Qed.

Lemma test_rewrite_same :  
   forall (h1 h2 h3 h5 h6 h7 h8 h9 h10 h11 h12 h13: heap),
     splits h1 (h3::nil) -> splits h2 (h3::nil) -> 
     splits h1 (h5 :: h7 :: nil) -> splits h2 (h6 :: h7 :: nil) ->
     splits h8 (h5::(h9::nil)) -> splits h8 (h6::(h10::nil)) ->
     h9 = h10.
intros.
rewrites. trivial.
Qed.





