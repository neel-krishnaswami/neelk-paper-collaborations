Require Import Assumptions.
Require Import MemModel.
Require Import HeapProp.
Require Import ST.
Require Import Separation.
Require Import STsep.
Require Import List.
Require Import DisjointUnion.
Require Import ETactics.

Open Local Scope hprop_scope.

Definition precise (P:hprop) := forall (h:heap),
  forall (h1 h2:heap), splits h (h1::h2::nil) -> P h1 ->
    forall (h3 h4:heap), splits h (h3::h4::nil) -> P h3 ->
      (h1 = h3 /\ h2 = h4).
