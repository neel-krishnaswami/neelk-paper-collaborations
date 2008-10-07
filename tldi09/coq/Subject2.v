Require Import DisjointUnion.
Require Import List.
Require Import MemModel.
Require Import ST.
Require Import Separation.
Require Import STsep.
Require Import Assumptions.
Require Import Tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Open Local Scope stsep_scope.

Record T : Type :=
  TC { o : nat -> hprop;
          f : forall (n : nat),
             STsep (fun i => exists n' : nat, o n' i) unit
                   (fun y i m => y = Val tt /\ forall n' : nat, o n' i -> o n m) }.

Definition sub (l : loc) (n : nat) :=
  (l --> n).

Program Definition new (n : nat) :
  STsep (fun i => emp i) loc (fun y i m => 
    exists l : loc, y = Val l /\ (emp i -> sub l n m)) :=
  sdo(snew n).
Next Obligation.
nextvc.
exists x.
intuition.
Qed.

Fixpoint obs (l : list T) (h : heap) : Prop :=
  match l with
    | nil  => emp h
    | hd::tail => ((fun h => exists i : nat, o hd i h) # obs tail) h
  end.

Fixpoint obs_at (l : list T) (n : nat) (h : heap) {struct l} : Prop :=
  match l with
    | nil => emp h
    | hd::tail => (o hd n # obs_at tail n) h
  end.

Definition bspec (sub : loc -> nat -> hprop) (l : loc) (ll : list T) :=
  forall n, STsep (fun i => exists k, (sub l k # obs ll) i ) 
            unit 
            (fun y i m => y = Val tt /\ forall k, (sub l k # obs ll) i -> 
                                              (sub l n # obs_at ll n) m).

Program Definition broadcast (l : loc) : bspec sub l nil :=
  (fun n => sdo (swrite l n)).
Next Obligation.
destruct H0 as [ i1 [ i2 [ I1 [ I2 I3 ] ] ] ].
splits_rewrite.
unfold sub in I2.
nextvc.
exists i1.
split.
eauto.
exists empty.
intuition.
remove_empty.
apply splits_refl.
splits_rewrite.
destruct H2 as [ k1 [ k2 [ K1 [ K2 K3 ] ] ] ].
splits_rewrite.
exists j1; exists empty.
intuition.
remove_empty.
apply splits_refl.
Qed.

Program Definition register 
  (l : loc) (ll : list T) (t : T) (broad : bspec sub l ll) : bspec sub l (t::ll) :=
  (fun n => sdo(broad n;; f t n)).
Next Obligation.
destruct H0 as [ i1 [ i2 [ I1 [ I2 I3 ] ] ] ].
destruct I3 as [ i3 [ i4 [ I4 [ I5 I6 ] ] ] ].
destruct I5 as [ m I5 ].
splits_rewrite_in I4 I1; clear I1 I4.
exists empty.
split.
unfold sbind_pre.
exists i; exists empty.
split.
remove_empty.
apply splits_refl.
split.
splits_join_in H0 (1::0::1::nil).
assert((fun i : heap => exists k : nat, (sub l k # obs ll) i) (union (i1::i4::nil) pf0)).
exists H; exists i1; exists i4.
intuition.
exists pf0; trivial.
split.
exists (union (i1::i4::nil) pf0); exists i3.
intuition.
intros.
generalize(H3 (union (i1::i4::nil) pf0) H2); clear H2 H3; intros.
generalize(H2 i3 H1); clear H2; intros.
destruct H2 as [ h' [ H10 [ H11 H12 ] ] ].
exists i3; exists h'.
intuition eauto.
apply splits_commute; assumption.
auto.
intros.
destruct H1 as [ k1 [ k2 [ K1 [ k3 [ k4 [ K2 [ K3 [ K4 K5 ] ] ] ] ] ] ] ].
unfold this in K4, K5.
rewrite <- K4 in *; clear K4 k2.
rewrite <- K5 in *; clear K5 k4.
destruct K3.
destruct H1 as [ K3 [ x [ h [ K4 K5 ] ] ] ].
splits_rewrite.
splits_join_in H0 (1::0::1::nil).
assert((fun i : heap => exists k : nat, (sub l k # obs ll) i) (union (i1::i4::nil) pf0)).
exists H; exists i1; exists i4.
intuition.
exists pf0; trivial.
generalize(K4 (union (i1::i4::nil) pf0) H2); clear H2; intros K6.
generalize(K6 i3 H1); clear K6; intros K6.
destruct K6 as [ h' [ K6 [ K7 K8 ] ] ].
assert((fun i : heap => exists n' : nat, o t n' i) i3).
eauto.
generalize(K5 i3 H2); clear H2; intros K9.
apply splits_commute in K6.
generalize(K9 h' K6); clear K9; intros K9.
destruct K9 as [ h1' [ K9 [ K10 K11 ] ] ].
split.
assumption.
intros.
destruct H2 as [ u1 [ u2 [ U1 [ U2 U3 ] ] ] ].
destruct U3 as [ u3 [ u4 [ U4 [ U5 U6 ] ] ] ].
destruct U5 as [ i U5 ].
splits_rewrite_in U4 U1; clear U1 U4.
splits_join_in H2 (1::0::1::nil).
assert((fun i : heap => exists k : nat, (sub l k # obs ll) i) (union (u1::u4::nil) pf1)).
exists k; exists u1; exists u4.
intuition.
exists pf1; trivial.
generalize(K4 (union (u1::u4::nil) pf1) H4 u3 H3); clear H4; intros U7.
destruct U7 as [ u1' [ U8 [ U9 U10 ] ] ].
assert((fun i : heap => exists n' : nat, o t n' i) u3).
eauto.
apply splits_commute in U8.
generalize(K5 u3 H4 u1' U8); clear H4; intros U11.
destruct U11 as [ u2' [ U11 [ U12 U13 ] ] ].
assert((sub l k # obs ll) (union (u1 :: u4 :: nil) pf1)).
exists u1; exists u4.
intuition.
exists pf1; trivial.
generalize(U10 k H4); clear H4; intros U14.
destruct U14 as [ r1 [ r2 [ R1 [ R2 R3 ] ] ] ].
splits_rewrite_in R1 U11; clear R1 U11.
splits_join_in H4 (1::0::1::nil).
exists r1; exists (union (u2'::r2::nil) pf2).
intuition.
apply splits_commute; trivial.
exists u2'; exists r2.
intuition.
exists pf2; trivial.
splits_rewrite.
eapply U13.
apply U5.
destruct H1 as [ e [ H1 H2 ] ].
splits_join_in H0 (1::0::1::nil).
assert((fun i : heap => exists k : nat, (sub l k # obs ll) i) (union (i1::i4::nil) pf0)).
exists H; exists i1; exists i4.
intuition.
exists pf0; trivial.
splits_rewrite.
generalize(H2 (union (i1::i4::nil) pf0) H4 i3 H3); clear H4; intros H4.
destruct H4 as [ h1' [ H4 [ H5 H6 ] ] ].
inversion H5.
Qed.

Record SubObj : Type :=
  SubObjCon {
    Sub : loc -> nat -> heap -> Prop;
    SNew : forall (n : nat), STsep (fun i => emp i) loc (fun y i m => exists l, y = Val l /\ (emp i -> Sub l n m));
    SBroad : forall (l : loc), bspec Sub l nil;
    SReg : forall (l : loc) (ll : list T) (t : T) (broad : bspec Sub l ll), bspec Sub l (t::ll)
 }.

Definition SubImpl : SubObj := SubObjCon new broadcast register.

Print bspec.

Section Example.

Variable c : loc.
Definition c_O (l : loc) (n : nat) := (l --> n).
Program Definition c_notify (n : nat) : STsep (fun i => exists k, c_O c k i) unit (fun y i m => y = Val tt /\ forall k, c_O c k i -> c_O c n m)
  := sdo(swrite c n).
Next Obligation.
nextvc.
exists i.
split.
unfold c_O in H0.
exists nat; exists H; assumption.
exists empty.
split.
remove_empty.
apply splits_refl.
intros.
splits_rewrite.
intuition.
Qed.

Definition client := TC c_notify.

Program Definition example (S : SubObj) :
  STsep (fun i => exists k, o client k i) unit 
            (fun y i m => y = Val tt /\ exists l : loc, (Sub S l 42 # obs_at (client::nil) 42) m) :=
  sdo(l <-- SNew S 2; SReg client (SBroad S l) 42).
Next Obligation.
intros.
nextvc.
exists empty.
split.
auto.
exists i.
split.
remove_empty.
apply splits_refl.
intros.
split.
intros.
destruct H2 as [ l [ H2 H3 ] ].
assert(Sub S l 2 j1).
apply H3.
auto.
inversion H2.
rewrite H6 in *; clear H6 x H2.
exists empty.
split.
exists j; exists empty.
split.
remove_empty.
apply splits_refl.
intuition.
exists 2.
exists j1; exists i.
intuition.
exists i; exists empty.
intuition eauto.
remove_empty.
apply splits_refl.
intros.
destruct H2 as [ b1 [ b2 [ B1 [ b3 [ b4 [ B2 [ B3 [ B4 B5 ] ] ] ] ] ] ] ].
unfold this in B4, B5.
rewrite <- B4 in *; clear B4 b2.
rewrite <- B5 in *; clear B5 b4.
splits_rewrite.
destruct B3.
split.
assumption.
exists l.
generalize(H5 2); clear H5; intros H5.
assert((Sub S l 2
      # (fun h : heap =>
         ((fun h0 : heap => exists i : nat, c_O c i h0)
          # (fun h0 : heap => emp h0)) h)) b1).
exists j1; exists i.
intuition.
exists i; exists empty.
intuition eauto.
remove_empty.
apply splits_refl.
generalize(H5 H6); clear H6; intros.
assumption.
intros.
destruct H2 as [ l [ H2 H3 ] ].
inversion H2.
Qed.