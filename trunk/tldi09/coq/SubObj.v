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
Set Printing Universes.

Parameter null : loc.



Check STsep.
Print Universes.

Definition alpha := prod loc loc.
Check nat -> hprop.
Check post.
(* Parameter f : STsep emp unit (fun i y m => True). *)

Record T : Type :=
  TC { o : nat -> hprop;
       f : forall (n : nat),
             STsep (fun i => exists n' : nat, o n' i) unit
                   (fun y i m => y = Val tt /\ o n m) }.
Check T.

Check dynamic.
Check points_to.
Check star1.
Check hprop -> hprop -> hprop.
Check nat -> Prop.
Check nat -> hprop.
Check hprop.
Check heap.
Check dynamic.
Check nat -> T.

Parameter l : loc.

Ltac splits_refl_empty := solve[repeat(remove_empty); apply splits_refl].

Ltac splits_eqto_subheap H :=
  let n1 := fresh "tmpH" in
  let n2 := fresh "tmpPF" in
  let n3 := fresh "tmpH" in
    generalize H; intros n1; repeat(remove_empty_in n1; clear n1; intros n1);
    destruct n1 as [ n2 n3 ]; simpl in n3; clear n2 H; generalize n3; 
    clear n3; intros H.

Program Definition tmp' (n : nat) : 
  STsep (fun i => exists n' : nat, (l --> n') i) unit
        (fun y i m => y = Val tt /\ (l --> n) m) :=
  sdo (swrite l n).
Next Obligation.
nextvc.
exists i.
split.
exists nat.
exists H.
assumption.
exists empty.
split.
splits_refl_empty.
intros.
split.
trivial.
splits_eqto_subheap H1.
rewrite H1.
assumption.
Defined.

Program Definition T' : T := TC tmp'.
Check T.

(* Tt : Type(STsep.3) *)
Definition Tt := STsep emp T (fun y i m => emp m /\ y = Val T').

Program Definition tmp : Tt :=
  sdo (sret T').
Next Obligation.
nextvc.
Qed.

Check sdo.

Program Definition tmp'' (l' : loc) : STsep (fun i => exists v : nat, (l' --> v) i) unit (fun y i m => (l' --> tmp) m) := 
  sdo (swrite l' tmp).
Next Obligation.
nextvc.
exists i.
split.
exists nat.
exists H.
assumption.
exists empty.
split.
splits_refl_empty.
intros.
assert(j = j1).
remove_empty_in H1.
intros.
destruct H3.
simpl in H3.
assumption.
rewrite H3.
assumption.
Defined.

(*
Inductive LL (y : loc) (a : T) : hprop -> Prop :=
  | tmp'''' : LL y a (fun i => (y --> a) i).
*)
(*
Inductive LL (y : loc) (a : T) (i : heap) : Prop :=
  | consLL : (y --> a) i -> LL y a i.
*)
Program Definition tmp''' (l' : loc) : STsep (fun i => exists v : nat, 
  (l' --> v) i) unit (fun y i m => (l' --> T') m) := 
  sdo (swrite l' T').
Next Obligation.
nextvc.
exists i.
split.
exists nat.
exists H.
assumption.
exists empty.
split.
splits_refl_empty.
intros.
assert(j = j1).
remove_empty_in H1.
intros.
destruct H3.
simpl in H3.
assumption.
rewrite H3.
assumption.
Defined.


Parameter t : (nat -> hprop).
Parameter h : heap.
Check heap.
Check dynamic.
Check nat -> hprop.
Check points_to.
Print dynamic.
Check hprop.

Check ((l --> tmp) h).
Check ((l --> T') h).
Check ((l --> t) h).

Fixpoint LL (y : loc) (l : list nat) (i : heap) : Prop :=
  match l with
  | nil => i = empty /\ y = null
  | cons h t => exists y' : loc, (y --> (h, y') # LL y' t) i
  end.

Inductive LL (y : loc) (l : list T) (i : heap) : Prop :=
  | empLL : l = nil /\ y = null /\ emp i -> LL y l i
  | consLL : (exists a : T, exists l' : list T, l = a::l' /\
                 (exists s' : loc, ((y --> (a, s')) # LL s' l') i)) ->
                      LL y l i.
 
Check T.
Check list.
Check list T.
Check LL.
Check points_to.
Definition sub (a : alpha) (n : nat) (l : list T) : hprop :=
  fun (h : heap) => exists l' : loc, 
    (((fst a) --> n) # ((snd a) --> l') # LL l' l) h.



(* 
*** Local Variables: *** 
*** coq-prog-args: ("-emacs-U" "-verbose") *** 
*** End: *** 
*) 

(* "-impredicative-set") *)
