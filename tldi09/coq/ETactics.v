(* Extended tactics for Coq 8.1svn.
 *
 * Based on work of Arthur Chargueraud, extended by Avi Shinnar and
 * Chris Jeris.  April 2007.
 *)

(********************** Immediate Extensions ***********************)

(* TACTIC sets H E
 * Add the term E to the context, named H, then forget the definitional
 * equality H := E. *)
Ltac sets H E := 
  set (H := E); clearbody H.

(* TACTIC asserts H E
 * Assert the term E as an intermediate subgoal, named H. *)
Ltac asserts H E :=
  assert (H : E).

(* TACTIC splits
 * split (which is equivalent to intros; apply <constructor> for any
 * inductive datatype that has only one constructor, most commonly /\)
 * until nothing happens. *)
Ltac splits :=
  repeat split.

(* TACTIC destructs H
 * Recursively destruct an inductive term until it no longer generates two
 * variables. *)
Ltac destructs H :=
  let H1 := fresh "H" in let H2 := fresh "H" in first 
  [ destruct H as [H1 H2]; destructs H1 ; destructs H2 | idtac ].

(* TACTIC inversions H
 * Inversion always generates a bunch of equations; subst afterward. *)
Ltac inversions H :=
  inversion H; subst.

(* TACTIC injections H
 * Apply the injectivity of constructors to reduce equations between
 * inductively defined terms; then forget the original equation and carry
 * out the substitution of the reduced equation. *)
Ltac injections H :=
  injection H; clear H; intros; subst.

(* TACTIC contradictions
 * Discharge a goal with contradictory hypotheses by replacing by False. *)
Ltac contradictions :=
  assert False; [ idtac | contradiction ].

(************************** Added Tactics **************************)

(* TACTIC decide_equality
 * Apply the decidability of equality where it is applicable. *)
Ltac decide_equality := 
  match goal with |- {?X = ?Y} + {?X <> ?Y} 
  => decide equality X Y end.

(* TACTIC func_equal
 * Apply f_equal[n], that is, f args = f args' <= args = args', with anywhere
 * from one to four arguments. *)
Ltac func_equal := match goal with
  | [ |- (?F _ = ?F _ ) ] => apply (f_equal F)
  | [ |- (?F _ _ = ?F _ _) ] => apply (f_equal2 F)
  | [ |- (?F _ _ _ = ?F _ _ _) ] => apply (f_equal3 F)
  | [ |- (?F _ _ _ _ = ?F _ _ _ _) ] => apply (f_equal4 F)
  | _ => idtac
  end.

(* TACTIC generalize_equality expr name
 * Add a hypothesis of the form forall name, name = expr -> *)
Ltac generalize_equality expr name := let equa := fresh in
  (set (name := expr); assert (equa : name = expr); 
  [ trivial | generalize name equa; clear name equa ]).

(* These tactics help deal with the conjugated lemmas that result from
 * mutual induction, *)

(* TACTIC split_nor
 * Convert ~(A \/ B \/ C ...) in the context into ~A and ~B and ~C and... . *)
Ltac split_nor H :=
  let H1 := fresh "NL" in let H2 := fresh "NR" in
    match type of H with
      | (~ (?x \/ ?y)) =>
        assert (H1 : ~ x); [intro; apply H; left; assumption |
          assert (H2 : ~ y); [intro; apply H; right; assumption |
            try split_nor H2]];
        clear H
    end.

(* TACTIC apply_conj_branch
 * Apply one branch of a conjunction (A -> B) /\ (A' -> B') /\ ...
 * and clear all unapplied branches. *)
Ltac apply_conj_branch H :=
  let N := fresh "HU" in 
    let N1 := fresh "HU" in
      let N2 := fresh "HU" in sets N H; 
        match type of N with 
          | (_ /\ _) => destruct N as [N1 N2]; 
             ((apply_conj_branch N1) 
                   || (apply_conj_branch N2)); clear N1 N2
          | _ => apply N
        end.
(* TACTIC applys
 * Try regular application, and if it fails, try conjunction application. *)
Ltac applys H := apply H || apply_conj_branch H.

(* TACTIC eapply_conj_branch
 * TACTIC eapplys
 * Replace apply by eapply in the above two tactics. *)
Ltac eapply_conj_branch H :=
  let N := fresh "HU" in 
    let N1 := fresh "HU" in
      let N2 := fresh "HU" in sets N H; 
        match type of N with 
          | (_ /\ _) => destruct N as [N1 N2]; 
             ((eapply_conj_branch N1) 
                   || (eapply_conj_branch N2)); clear N1 N2
          | _ => eapply N
        end.
Ltac eapplys H := eapply H || eapply_conj_branch H.

(* TACTIC poses
 * Add the specified term to the context, decomposing all conjunctions that
 * appear at top level in it. *)
Ltac poses H :=
  let N := fresh "HU" in sets N H; 
        match type of N with 
          | (_ /\ _) => (let N1 := fresh "HUT" in
                           let N2 := fresh "HUT" in 
                             destruct N as [N1 N2]; 
                               ((try poses N1) 
                                 ; (try poses N2)); clear N1 N2)
          | _ => idtac
        end.

(********************** Maths Manipulations ************************)

Require Import Omega.

(* TACTIC change_maths exp1 with exp2
 * Attempt to destructure and rewrite H1 as H2, then discharge the rewriting
 * using omega. *)
Tactic Notation "change_maths" constr(H1) "with" constr(H2) :=
  replace H1 with H2; [ idtac | omega ].

(* TACTIC absurd_maths
 * Discharge a goal with contradictory arithmetic hypotheses by replacing
 * by False, then try to discharge False using omega. *)
Tactic Notation "absurd_maths" :=
  assert False; [ omega | contradiction ].

(* TACTIC sne
 * Given (i <> j), assert that (S i <> S j). *)
Ltac sne H := 
  let H1 := fresh "SNE" in
    match type of H with
      | (?x <> ?y) => assert (H1 : S x <> S y); [omega | idtac]
    end.

(********************** Aggressive Automation **********************)

(* Suffix * uniformly means "follow by auto*". *)
Tactic Notation "auto" "*" := 
  try solve [ auto | intuition (eauto 7) ]. 
Tactic Notation "asserts" "*" ident(H) constr(E) :=
  assert (H : E); [ auto* | idtac ].
Tactic Notation "apply" "*" constr(H) := 
  first [ apply H | eapply H ]; auto* .
Tactic Notation "applys" "*" constr(H) := 
  first [ applys H | eapplys H ]; auto* .
Tactic Notation "splits" "*" := 
  splits; auto* .
Tactic Notation "inversion" "*" constr(H) := 
  inversion H; auto* .
Tactic Notation "induction" "*" constr(H) := 
  induction H; auto* .
Tactic Notation "inversions" "*" constr(H) := 
  inversions H; auto* .
Tactic Notation "contradictions" "*" := 
   contradictions; auto* .
Tactic Notation "rewrite" "*" constr(H) := 
  rewrite -> H; auto* .
Tactic Notation "rewrite" "*" "<-" constr(H) := 
  rewrite <- H; auto* .
Tactic Notation "simpl" "*" := 
  simpl; auto* .
Tactic Notation "destruct" "*" constr(H) := 
  destruct H; auto* .
Tactic Notation "func_equal" "*" := 
  func_equal; auto* .

(* TACTIC use E, use2 E E', use3 E E' E''
 * Add the argument expressions to the context using poses, then
 * proof-search by auto*. *)
Ltac use expr :=
  poses expr; auto* .
Ltac use2 expr1 expr2 :=
  poses expr1; use expr2.
Ltac use3 expr1 expr2 expr3 :=
  poses expr1; poses expr2; use expr3.
