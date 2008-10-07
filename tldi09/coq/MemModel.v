(**********************************)
(* Memory Model.                  *)
(*                                *)
(* array(n) = set of n locations  *)
(* not necessarily consecutive    *)
(**********************************)

Require Import Assumptions.
Require Import Omega.
Require Import Compare.
Require Import ProofIrrelevance.
Require Import UsefulMisc.

Record dynamic : Type := 
   dyn {type_of : Type;  
        val_of  : type_of}.

Theorem dyn_inj : forall (A : Type) (x y : A),
                          (dyn A x = dyn A y) -> x = y. 
intros.
inversion H.
apply (inj_pairT2 Type (fun t => t) A x y H1).
Defined.

Implicit Arguments dyn_inj [A].



(* To use dependent elimination of pairs we must establish         *)
(* that terms are invariant under substitution of equality proofs. *)
(* This is much weaker than proof irrelevance, and so we obtain    *)
(* the exact statement from proof irrelevance here.                *)

Theorem eq_rect_eq_witness :
    forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p), 
         x = eq_rect p Q x p h.

intros.
assert (h = refl_equal p).
apply (proof_irrelevance (p=p) h (refl_equal p)).
rewrite H.
unfold eq_rect.
reflexivity.
Defined.


Theorem dyn_eta : 
   forall d : dynamic, d = dyn (type_of d) (val_of d).
Proof. intros; case d; auto. Qed.


(*****************************************)
(* Definition of the model.              *)
(* Ideally, definitions should be        *)
(* abstracted, to hide the internals     *)
(*****************************************)

Parameter loc : Set.
Parameter loc_eq : forall (l1 l2 : loc), {l1 = l2} + {l1 <> l2}.

Lemma loc_eq_refl : 
   forall (l : loc), 
      loc_eq l l = left (l <> l) (refl_equal l).

intros.
case (loc_eq l l).
 intros.
   assert (e = refl_equal l).
  apply proof_irrelevance.
 rewrite H in |- *.
   auto.
intros.
   absurd (l = l).
 auto.
auto.
Qed.


Lemma loc_eq_nrefl : 
   forall (l1 l2 : loc),
     forall (pf : l1 <> l2), loc_eq l1 l2 = right (l1 = l2) pf.

intros.
case (loc_eq l1 l2).
 intros.
    absurd (l1 = l2).
  auto.
 auto.
intros.
  assert (n = pf).
 apply proof_irrelevance.
rewrite H in |- *.
  auto.
Qed.



(* The heap is just a map from locations to maybe dynamics. *)
Definition heap := loc -> option dynamic.
Definition empty : heap := fun _ => None.


(** array(n) is a set of n locations **)
(** do we want the type array(0)? **)

Record array (len : nat) : Type :=
   build_array {get    : forall (i : nat), i < len -> loc;
                inj_pf : forall (i j : nat) (pfi : i < len) (pfj : j < len),
                              get i pfi = get j pfj -> i = j}.

Implicit Arguments get [len].
Implicit Arguments inj_pf [len].



(***********************************)
(* Exported methods and properties *)
(***********************************)

Definition lookup_loc (h : heap) (l : loc) : option dynamic :=  h l.

Definition modify_loc (h : heap) (l : loc) (v : option dynamic) :=
   fun (n : loc) => 
     match loc_eq n l with
      | left eq => v
      | right neq => h n
     end.

Lemma lookup_loc_empty (l : loc) : lookup_loc empty l = None.
Proof. auto. Qed.


Lemma heap_extensional : 
        forall (h1 h2 : heap),
               (forall l, lookup_loc h1 l = lookup_loc h2 l) -> h1 = h2.
Proof.
unfold lookup_loc; intros h1 h2 H.
apply (extensional loc (fun l => option dynamic)); auto.
Qed.

Implicit Arguments heap_extensional [h1 h2].



Definition lookup_array (n : nat) (a : array n)
                        (i : nat) (pf : i < n) : loc :=
  get a i pf.

Implicit Arguments lookup_array [n].


Program Fixpoint 
  modify_array_upto (h : heap) (n : nat) (a : array n)
                    (v : option dynamic) (i : nat) (pf : i < n) {struct i} : heap :=
 
  let t := modify_loc h (lookup_array a i pf) v in
    match i with
      | 0 => t
      | S j => modify_array_upto t n a v j _
    end.

Implicit Arguments modify_array_upto [n].


Program Definition 
  modify_array (h : heap) (n : nat) 
               (a : array n) (v : option dynamic) : heap :=

  if (nat_cmp n 0) then h 
  else modify_array_upto h a v (n - 1) _.

Implicit Arguments modify_array [n].


Theorem inj_array : forall (n : nat) (a : array n)
                           (i j : nat) (pfi : i < n) (pfj : j < n), 
                      lookup_array a i pfi = lookup_array a j pfj -> i = j.
intros.
unfold lookup_array in *.
apply (inj_pf a i j pfi pfj H).
Defined.

Implicit Arguments inj_array [n].


Definition update_loc (h : heap) (l : loc) (A : Type) (v : A) : heap :=
   modify_loc h l (Some (dyn A v)).

Implicit Arguments update_loc [A].


Definition update_array (h : heap) (n : nat) (a : array n)
                        (A : Type) (v : A) : heap :=
   modify_array h a (Some (dyn A v)).

Implicit Arguments update_array [A n].


Definition free_loc (h : heap) (l : loc) : heap := 
   modify_loc h l None.


Definition free_array (h : heap) (n : nat) (a : array n) : heap :=
  modify_array h a None.

Implicit Arguments free_array [n].


Definition selects (l : loc) (A : Type) (val : A) (h : heap) : Prop :=
   h l = Some (dyn A val).               

Implicit Arguments selects [A].


(* heap injectivity *)

Lemma same_selects : 
   forall (l : loc) (A : Type) (v1 v2 : A) (h : heap),
      selects l v1 h -> selects l v2 h -> v1 = v2.

unfold selects in |- *.
intros.
apply dyn_inj.
 congruence.
Qed.

Implicit Arguments same_selects [l A v1 v2 h].


Lemma same_selects_type : 
   forall (l : loc) (A1 A2 : Type) (v1 : A1) (v2 : A2) (h : heap),
      selects l v1 h -> selects l v2 h -> dyn A1 v1 = dyn A2 v2.

intros.
elim H.
elim H.
generalize H H0.
intros.
unfold selects in H1.
unfold selects in H2.
rewrite H1 in H2.
injection H2.
intros.
destruct H4.
clear H1 H2 H3.
 replace v1 with v2.
 auto.
 eapply same_selects.
   apply H0.
  apply H.
Qed.

Implicit Arguments same_selects_type [l A1 A2 v1 v2 h].



(* McCarthy's axioms *)

Lemma sel_eq : 
  forall (l : loc) (A : Type) (v : A) (h : heap),
      selects l v (update_loc h l v).

intros.
unfold selects in |- *.
unfold update_loc in |- *.
unfold modify_loc in |- *.
case (loc_eq l l).
 auto.
intros.
   absurd (l = l).
 auto.
auto.
Qed.

Implicit Arguments sel_eq [A].



Lemma sel_eq1 :
  forall (l1 : loc) (A : Type) (v : A) (h : heap), 
      selects l1 v h -> 
        forall (l2 : loc), (l1 = l2) -> selects l1 v (update_loc h l2 v).

intros.
unfold selects, update_loc in |- *.
unfold modify_loc in |- *.
elim (loc_eq l1 l2).
  tauto.
 tauto.
Qed.

Implicit Arguments sel_eq1 [A].


Lemma sel_neq :
   forall (l1 : loc) (A1 : Type) (v1 : A1) (h : heap),
        selects l1 v1 h -> 
          forall (l2 : loc) (A2 : Type) (v2 : A2), 
             (l1 <> l2) -> selects l1 v1 (update_loc h l2 v2).

unfold selects in |- *.
intros.
unfold update_loc in |- *.
unfold modify_loc in |- *.
elim (loc_eq l1 l2).
  tauto.
 tauto.
Qed.

Implicit Arguments sel_neq [A1 A2].



Definition unused_loc (l : loc) (h : heap) : Prop :=  
   lookup_loc h l = None.


Definition valid_loc (l : loc) (h : heap) : Prop :=
   exists A : Type, exists v : A, selects l v h.


Lemma selects_valid :
   forall (l : loc) (A : Type) (v : A) (h : heap), 
      selects l v h -> valid_loc l h.

unfold valid_loc in |- *.
 eauto.
Qed.

Implicit Arguments selects_valid [A].



(* unused_loc/valid_loc are mutualy exclusive *)

Lemma loc_ex : 
   forall (l : loc) (h : heap), 
       valid_loc l h -> unused_loc l h -> False.

unfold valid_loc in |- *.
unfold unused_loc in |- *.
unfold selects in |- *.
unfold lookup_loc in |- *.
intros.
destruct H.
destruct H.
rewrite H in H0.
 discriminate.
Qed.

Implicit Arguments loc_ex [h l].


(* unused_loc/valid_loc excluded middle *)

Lemma loc_em : 
    forall (l : loc) (h : heap), 
       unused_loc l h \/ valid_loc l h.
intros.
unfold unused_loc in |- *.
unfold valid_loc in |- *.
unfold lookup_loc in |- *.
unfold selects in |- *.
case (h l).
 intros.
   right.
   exists (type_of d).
   exists (val_of d).
   rewrite <- (dyn_eta d) in |- *.
   auto.
auto.
Qed.


Lemma unused_loc_empty : 
   forall (l : loc), unused_loc l empty.

unfold unused_loc in |- *.
apply lookup_loc_empty.
Qed.

Lemma selects_update_loc : 
   forall (l1 l2 : loc) (A1 A2 : Type) (v1 : A1) (v2 : A2) (h : heap),
     selects l1 v1 (update_loc h l2 v2) ->
        (l1 = l2 /\ dyn A1 v1 = dyn A2 v2) \/ (l1 <> l2 /\ selects l1 v1 h).

intros.
unfold selects in H.
unfold update_loc in H.
unfold modify_loc in H.
case (loc_eq l1 l2).
 intros.
   rewrite e in H.
   rewrite (loc_eq_refl l2) in H.
   left.
   split.
  auto.
 assert (forall (A : Type) (t1 t2 : A), Some t1 = Some t2 -> t1 = t2).
  intros.
     injection H0.
    auto.
 apply H0.
   auto.
intros.
  rewrite (loc_eq_nrefl l1 l2 n) in H.
  right.
  split.
 auto.
unfold selects in |- *.
  auto.
Qed.

Implicit Arguments selects_update_loc [l1 l2 A1 A2 v1 v2 h].



Lemma valid_loc_update_loc : 
   forall (l1 l2 : loc) (A : Type) (v : A) (h : heap),
       valid_loc l1 (update_loc h l2 v) -> 
          l1 = l2 \/ (l1 <> l2 /\ valid_loc l1 h).

intros.
unfold valid_loc in H.
destruct H as (A0).
destruct H as (v0).
destruct (selects_update_loc H).
 destruct H0.
   left.
   auto.
destruct H0.
  right.
  unfold valid_loc in |- *.
  split.
 auto.
exists A0.
  exists v0.
  auto.
Qed.

Implicit Arguments valid_loc_update_loc [l1 l2 A v h].



Lemma free_loc_update_loc : 
   forall (l : loc) (A : Type) (v : A) (h : heap),
       unused_loc l h -> 
         free_loc (update_loc h l v) l = h.

unfold free_loc in |- *.
unfold unused_loc in |- *.
unfold update_loc in |- *.
unfold modify_loc in |- *.
unfold lookup_loc in |- *.
intros.
apply heap_extensional.
intros.
unfold lookup_loc in |- *.
case (loc_eq l0 l).
 intros.
   rewrite e in |- *.
   auto.
auto.
Qed.

Implicit Arguments free_loc_update_loc [l A v h].


Lemma update_loc_update_loc :
   forall (l : loc) (A1 : Type) (A2 : Type) (v1 : A1) (v2 : A2) (h : heap),
     update_loc (update_loc h l v1) l v2 = update_loc h l v2.

intros.
unfold update_loc in |- *.
unfold modify_loc in |- *.
apply heap_extensional.
intros.
unfold lookup_loc in |- *.
case (loc_eq l0 l).
 auto.
auto.
Qed.

Implicit Arguments update_loc_update_loc [l A1 A2 v1 v2 h].


(* rewrite the arrays unused/valid functions as fixpoints *)
(* then a lot of proving can be done by simplification *)

Definition unused_array (n : nat) (a : array n) (h : heap) : Prop := 
   forall (i : nat) (pf : i < n), unused_loc (lookup_array a i pf) h.

Implicit Arguments unused_array [n].


Definition valid_array (n : nat) (a : array n) (h : heap) := 
   forall (i : nat) (pf : i < n), valid_loc (lookup_array a i pf) h.

Implicit Arguments valid_array [n].


(***********)
(* Tactics *)
(***********)

(* a simple tactic for splitting a points-to goal into the two *)
(* cases when x and y are equal/not-equal. *)

Ltac heap_split :=
  match goal with
  | [ |- selects ?l1 _ (update_loc _ ?l2 _) ] => eapply sel_eq1
  | [ |- selects ?l1 _ (update_loc _ ?l2 _) ] => eapply sel_neq
  | _ => idtac
  end.


