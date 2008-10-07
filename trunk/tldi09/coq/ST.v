(** * The ST monad *)
(* Yet another version of ST, but this time with various 
 * declarations (read_pre, write_pre, read_post, write_post, etc.)
 * used for specifications of primitives and combinators so that
 * we can try to simplify them using tactics.  When compared to
 * STMonad2, the proofs are somewhat simpler. 
 *)

Require Export BasicTactics.
Require Export MemModel.
Require Export Exn. 


(** The answer type.
    All computations return answers -- either a value or an exception
*)
Inductive ans(A:Type) : Type :=
| Val : A -> ans A
| Exn : exn -> ans A.
Implicit Arguments Val [A].
Implicit Arguments Exn [A].

(** pre-conditions classify heaps *)
Definition pre := heap -> Prop.
(** empty pre-condition *)
Definition nopre : pre := fun h => True.
(** post-conditions relate an answer, an initial heap, and a final heap *)
Definition post (A : Type) := ans A -> heap -> heap -> Prop.

Hint Resolve ex_intro.

(** the ST monad type constructor -- classified by the answer type, and
    a pre and post-condition.  Semantically, when given a heap satisfying
    the pre-condition, will either (a) diverge, (b) terminate with an answer
    and final state related to the initial state by the post-condition.
*)
Set Printing Universes.
Parameter ST : forall (A: Type), pre -> post A -> Type.
Check ST.
Check pre.
Print Universes.
Implicit Arguments ST [A].

(** return -- lift a pure value into the monad *)
Definition ret_post(A:Type)(x:A) : post A := 
  fun y i m => m = i /\ y = Val x.
Implicit Arguments ret_post[A].

Parameter ret : 
  forall (A : Type) (x : A), ST nopre (ret_post x).
Implicit Arguments ret [A].

(** throw -- lift an exception into the monad *)
Definition throw_post(A:Type)(x:exn) : post A :=
  fun y i m => m = i /\ y = Exn x.

Parameter throw :
  forall (A : Type)(x : exn), ST nopre (throw_post A x).

(** bind -- sequencing for the monad.  The pre-condition of the compound
    bind c1 c2 includes the pre-condition of c1, plus a requirement that
    any Val and heap that satisfies c1's post-condition implies the pre-
    condition of c2.  The post-condition of the compound command tells
    us that either (a) there exists an intermediate heap h and Val x,
     that satisified c1's post-condition, and the final answer and heap are 
    determined by x, the intermediate heap, and c2's post-condition, or
    else (b) there exists an exception e thrown by c1 that is the answer
    of the computation.
*)
Definition bind_pre(A:Type)(p1:pre)(q1 : post A)(p2 : A -> pre) := 
  fun i => (p1 i) /\ (forall x m, (q1 (Val x) i m) -> (p2 x m)).
Implicit Arguments bind_pre[A].

Definition bind_noexn(A B:Type)(p1:pre)(q1:post A)(q2:A->post B) := 
  fun y i m => exists x, exists h, q1 (Val x) i h /\ q2 x y h m.
Implicit Arguments bind_noexn[A B].

Definition bind_exn(A B:Type)(p1:pre)(q1:post A) : post B := 
  fun y i m => exists e, y = Exn e /\ q1 (Exn e) i m.
Implicit Arguments bind_exn[A B].

Definition bind_post(A B:Type)(p1:pre)(q1:post A)(q2:A->post B) := 
  fun y i m => (p1 i) /\ (bind_noexn p1 q1 q2 y i m \/ bind_exn p1 q1 y i m).
Implicit Arguments bind_post[A B].

Parameter bind : 
  forall (A B : Type) 
         (p1 : pre) (q1 : post A) (c1 : ST p1 q1)
         (p2 : A -> pre) (q2 : A -> post B) 
         (c2 : forall x: A, ST (p2 x) (q2 x)),
  ST (bind_pre p1 q1 p2) (bind_post p1 q1 q2).
Implicit Arguments bind [A B p1 q1 p2 q2].



(** associative try, in the style of Benton and Kennedy *)

Definition try_pre (A : Type) (p1 : pre) (q1 : post A) (p2 : A -> pre) (p3 : exn -> pre) : pre := 
  fun i => (p1 i) /\ (forall x m, (q1 (Val x) i m -> p2 x m)) 
                  /\ (forall e m, (q1 (Exn e) i m -> p3 e m)).

Implicit Arguments try_pre [A].


Definition try_post 
        (A B : Type) 
        (p1 : pre) (q1 : post A)
        (q2 : A -> post B) 
        (q3 : exn -> post B) : post B :=
  fun y i m => (p1 i) /\ 
         ((exists x, exists h, q1 (Val x) i h /\ q2 x y h m) \/ 
          (exists e, exists h, q1 (Exn e) i h /\ q3 e y h m)).

Implicit Arguments try_post [A B]. 


Parameter try : 
  forall (A B : Type)
         (p1 : pre) (q1 : post A) (c1 : ST p1 q1)
         (p2 : A -> pre) (q2 : A -> post B) (c2 : forall x:A, ST (p2 x) (q2 x))
         (p3 : exn -> pre) (q3 : exn -> post B) (c3 : forall e:exn, ST (p3 e) (q3 e)),
  ST  (try_pre p1 q1 p2 p3)
      (try_post p1 q1 q2 q3).

Implicit Arguments try [A B p1 q1 p2 q2 p3 q3].

(* a call-by-value fixpoint.  Issues to consider:  why not CBN?
 * Do we need a monotonicity requirement on f?
 *)

Parameter ffix :
  forall (A : Type)
         (B : A -> Type)
         (p : A -> pre)
         (q : forall x : A, post (B x))
         (f : forall (b : forall x:A, ST (p x) (q x)) (x : A), ST (p x) (q x)),
    forall (x: A), ST (p x) (q x).

Implicit Arguments ffix [A B p q].



(*
(* Call-by-name fixpoint.

   Monotonicity not required, since no equations over code can be
   proved. Postpones solving for the pre and post of the recursive
   call by recording the obligation in the pre and post of the result.
  
   p and q should be irrelevant variables, if Coq could only support
   that. 

   The soundness of this spec is arguable. Just from knowing that p
   and q exist, there is no guarantee that I can extract the actual p
   and q, and plug them into the body of the fix constructor. Matching
   against a proof of (exists p q, ...) will give me some p' and q',
   but these can only be used in proofs, not in terms.

   Thus, if we interpreted ST in the usual state monad, this rule
   would not be sound. In the continuation monad, it would, because
   there we are trying to prove False, so the whole model is built out
   of proofs, and hence p' and q' are usable. What about the predicate
   transformer model?

   On the other hand, one may argue that we will not plug p' and q'
   into the body of the fixpoint. Rather, we will plug in the lfp of
   the system of equations generated from P and Q. Then p' and q'
   should just be approximations to this lfp. But in order for this
   lfp to exist, we need to guarantee that P and Q derive a monotone
   system of equations, else the lfp may not exist. How to argue that
   P and Q are always monotone? I don't think they need to be, since
   they can misuse q in many different ways.

   So, the tradeof is, we get to postpone giving the invariant, but
   that comes with a price, as we now need to prove the
   monotonicity.
*)

Definition fix_pre (A : Type) (P : pre -> post A -> pre) 
                   (Q : pre -> post A -> post A) : pre :=
   fun i => exists p, exists q, P p q i /\ 
                forall y i j, (P p q i -> p i) /\ 
                              (q y i j -> Q p q y i j).

Implicit Arguments fix_pre [A].

Definition fix_post (A : Type) (P : pre -> post A -> pre)
                    (Q : pre -> post A -> post A) : post A :=
   fun y i h => 
       forall p q, P p q i ->
          (forall y i j, (P p q i -> p i) /\ (q y i j -> Q p q y i j)) -> 
              Q p q y i h.

Implicit Arguments fix_post [A].

Parameter ffix : 
  forall (A : Type)
         (P : pre -> post A -> pre) (Q : pre -> post A -> post A) 
         (f : forall (p:pre)(q:post A), ST p q -> ST (P p q) (Q p q)), 
           ST (fix_pre P Q) (fix_post P Q).

Implicit Arguments ffix [A P Q].
*)


(** do -- in essence, the rule of consequence for ST commands.  Allows
   one to strengthen the pre-condition and weaken the post-condition.
*)
Parameter do : 
  forall (A : Type)
         (p1 p2 : pre) (q1 q2 : post A) (c : ST p1 q1) 
         (pf : (forall i, (p2 i) -> (p1 i)) /\
               (forall x i m, p2 i -> q1 x i m -> q2 x i m)),
  ST p2 q2.
Implicit Arguments do [A p1 q1 p2 q2].

(** new -- create a new reference cell and initialize it with the value v.
    The result is a location guaranteed not to have been allocated before,
    and the resulting heap is the same as the initial heap, except that
    the returned location now points to v.
*)
Definition new_post(A:Type)(v:A) := 
  fun y i m => exists r:loc, y = Val r /\ unused_loc r i /\ 
                             m = update_loc i r v. 
Implicit Arguments new_post[A].

Parameter new : forall (A : Type) (v : A), ST nopre (new_post v).
Implicit Arguments new [A].

(** free -- deallocate the location r.  Demands that the location points
    to something (is allocated).
*)
Definition free_post(r:loc) := 
  fun y i m => y=Val tt /\ m = free_loc i r.

Parameter free : forall (r : loc), ST (valid_loc r) (free_post r).

(** read -- returns the A-value that is the contents of a location.  Requires 
    that the location point to a value of type A and ensures memory is 
    unchanged.
*)
Definition read_pre(A:Type)(r:loc) := 
  fun i => exists v:A, selects r v i.

Definition read_post(A:Type)(r:loc) := 
  fun y i m => m = i /\ forall v:A, selects r v i -> y=Val v.

Parameter read : 
  forall (A : Type) (r : loc), ST (read_pre A r) (read_post A r).
Implicit Arguments read [A].

(** write -- updates the location r's contents with the value v.  Requires
   that the location is allocated and thus points to something before
   doing the update.
*)
Definition write_post(A:Type)(r:loc)(v:A) :=
  fun y i m => y = Val tt /\ m = update_loc i r v.
Implicit Arguments write_post[A].

Parameter write : 
  forall (A : Type) (r : loc) (v : A), ST (valid_loc r) (write_post r v).
Implicit Arguments write [A].


Parameter cond : 
  forall (A : Type) (b : bool)
         (p1 : pre) (q1 : post A) (e1 : ST p1 q1)
         (p2 : pre) (q2 : post A) (e2 : ST p2 q2),
        ST (fun i => (b=true -> p1 i) /\
                     (b=false -> p2 i))
           (fun x i m =>
                     (b=true -> q1 x i m) /\
                     (b=false -> q2 x i m)).

Implicit Arguments cond [A p1 q1 p2 q2].


Parameter diverge : 
  forall (A : Type), ST nopre (fun (y:ans A) i m => False).

Delimit Scope st_scope with st. 

Notation "x '<--' c1 ';' c2" := (bind c1 (fun x => c2))
  (at level 80, right associativity) : st_scope.

Notation "c1 ';;' c2" := (bind c1 (fun _ => c2))
  (at level 80, right associativity) : st_scope.

Notation "'!!' x" := (read x)
  (at level 50) : st_scope.

Notation "e1 '::=' e2" := (write e1 e2)
  (at level 60) : st_scope.

Open Local Scope st_scope.

(************************************************************************)
(** ** Some useful lemmas                                               *)
(************************************************************************)

(* if P -> Exn e = Val v, then P implies anything -- useful for
 * discharging cases where an exception cannot have been thrown. *)
Theorem ValExnFalse : 
  forall (A:Type)(e:exn)(v:A)(P:Prop),(P -> Exn e = Val v)->(forall Q, P->Q).
intros.
assert (Exn e = Val v).
 apply (H H0).
 congruence.
Defined.
Implicit Arguments ValExnFalse [A e P].

Lemma bind_bind_pre(A B:Type)(p1:pre)(q1 : post A)(p2: A -> pre)
                   (q2 : A -> post B)(p3 : B -> pre)(i:heap) :
  bind_pre p1 q1 
           (fun y m => q1 (Val y) i m -> bind_pre (p2 y) (q2 y) p3 m) i
  -> (bind_pre (bind_pre p1 q1 p2) (bind_post p1 q1 q2) p3) i.
Proof.
 unfold bind_pre, bind_post
 ; unfold bind_noexn, bind_exn
 ; simplifier.
 pose (H1 x m H0 H0).
   tauto.
 pose (H2 x0 x1 H1 H1).
  destruct a.
   eapply H4.
  assumption.
 discriminate H1.
Qed.

Lemma bind_read_pre(A:Type)(r:loc)(p2 : A -> pre)(i:heap) :
  (exists v:A, selects r v i /\ p2 v i) ->
  bind_pre (read_pre A r) (read_post A r) p2 i.
Proof.
 unfold bind_pre, read_pre, read_post
 ; simplifier.
 pose (H1 x0 H).
 inversion e.
  subst.
 assumption.
Qed.


Lemma simp_bind_read_pre(A:Type)(r:loc)(p2:A->pre)(i:heap) :
  bind_pre (read_pre A r) (read_post A r) p2 i -> 
  exists v:A, selects r v i /\ p2 v i.
Proof.
unfold bind_pre. unfold read_pre. unfold read_post. intros.
destruct H. destruct H. exists x. split. auto. eapply H0.
split. auto. intro. intro. assert (x = v). eapply same_selects.
eauto. eauto. rewrite H2. auto.
Defined.

Lemma bind_new_pre(A:Type)(v:A)(p2 : loc -> pre)(i:heap) :
  (forall r:loc, unused_loc r i -> p2 r (update_loc i r v)) ->
  (bind_pre nopre (new_post v) p2) i.
Proof.
 unfold bind_pre, new_post.
 simplifier.
 inversion H0.
  subst.
 apply (H x0 H1).
Qed.

Lemma bind_write_pre(A:Type)(r:loc)(v:A)(p2 : unit->pre)(i:heap) :
  (valid_loc r i /\ p2 tt (update_loc i r v)) ->
  (bind_pre (valid_loc r) (write_post r v) p2) i.
Proof.
 unfold bind_pre, write_post.
 simplifier.
 inversion H0.
  subst.
 assumption.
Qed.

Lemma bind_new_post(A B:Type)(v:A)(q2:loc->post B)(y:ans B)(i m:heap) :
  (bind_post nopre (new_post v) q2 y i m) ->
  (exists r:loc, unused_loc r i /\ q2 r y (update_loc i r v) m).
Proof.
 unfold bind_post, new_post
 ; unfold bind_noexn, bind_exn.
 simplifier.
 exists x1.
  inversion H0.
   subst.
  auto.
 discriminate H1.
Qed.
Implicit Arguments bind_new_post [A B].


Lemma bind_read_post(A B:Type)(r:loc)(q2:A->post B)(y:ans B)(i m:heap) :
  (bind_post (read_pre A r) (read_post A r) q2 y i m) ->
  (exists v:A, selects r v i /\ q2 v y i m).
Proof.
 unfold read_pre, read_post, bind_post
 ; unfold bind_noexn, bind_exn.
 simplifier.
 exists x.
    pose (H2 x H).
   inversion e;  subst.
   auto.
 pose (H2 x H).
   discriminate e.
Qed.
Implicit Arguments bind_read_post [A B].


Lemma bind_write_post(A B:Type)(r:loc)(v:A)(q2:unit->post B)(y:ans B)(i m:heap) :
  (bind_post (valid_loc r) (write_post r v) q2 y i m) ->
  (valid_loc r i /\ q2 tt y (update_loc i r v) m).
Proof.
 unfold bind_post, write_post
 ; unfold bind_noexn, bind_exn.
 simplifier. 
 inversion H0; subst; assumption.
 inversion H1.
Qed.


(* Still need to figure out how to re-associate post-conditions for bind's
Lemma bind_bind_post
  (bind_post (bind_pre p1 q1 p2) (bind_post p1 q1 q2) q3) ->
  bind_post p1 q1 ???.
*)


(************************************************************************)
(** ** Tactics                                                          *)
(************************************************************************)

(* a tactic for getting rid of cases that don't throw an exception *)
Ltac val_exn_false h := eapply ValExnFalse ; [ apply h; eauto | eauto ].

(* a tactic for simplifying goals -- tries to simplify assumptions
 * and get rid of boring cases.  Some of this is speculative and
 * shouldn't be... A lot of it is specific to the sort of VCs that
 * I ran into in the code below. *)
Ltac csimp := 
  match goal with
  | [ |- (exists x, _) -> _ ] => 
      (* (exists x, P) -> G ==> forall x, P -> G *)
      let h := fresh "H" in intro h; elim h; clear h
  | [ |- (_ /\ _) -> _] => 
      (* (P1 /\ P2) -> G ==> P1 -> P2 -> G *)
      let h := fresh "H" in intro h; elim h; clear h
  | [ |- (_ \/ _) -> _] =>
      (* (P1 \/ P2) -> G ==> (P1 -> G) \/ (P2 -> G) *)
      let h := fresh "H" in intro h; elim h; 
      [clear h | clear h ]
  | [ |- (Val _ = Exn _) -> _] =>
      (* (Exn _ = Val _) -> G ==> True *)
      let h := fresh "H" in intro h; congruence
  | [ |- (Exn _ = Val _) -> _] =>
      (* (Val _ = Exn _) -> G ==> True *)
      let h := fresh "H" in intro h; congruence
  | [ |- (Val ?x = Val ?y) -> _] =>
      (* (Val x = Val y) -> G ==> (x = y) -> G *)
      let h := fresh "H" in intro h; cut (x = y); 
      [clear h | congruence]
  | [ |- (_ = _) -> _ ] => 
      (* (x = y) -> G ==>  x=y |- G[x/y] *)
      let h := fresh "H" in intro h; rewrite h
  | [ H:selects ?x ?v1 ?i |- selects ?x ?v2 ?i -> _] =>
      (* selects x v1 i |- selects x v2 i -> P ==>
             selects x v1 i |- v2 = v1 -> P *)
      let h := fresh "H" in intro h; 
      cut (v2 = v1); [ idtac | apply (same_selects x v2 v1 i h H) ]
  | [ |- (forall v, _ -> Exn _ = Val _) -> _ ] =>
      (* (forall v, _ -> Exn _ = Val _) -> _ ==> False *)
      let h := fresh "H" in intro h; val_exn_false h
  | [H:selects ?r ?w ?i |- (forall v, selects ?r v ?i -> Val ?x = Val v) -> _]
    => 
       (* selects r w i |- (forall v, selects r v i -> Val x = Val v) -> P
          ==>
          selects r w i, forall v, selects r v i |- -> (Val x = Val w)-> P
       *)
       let h := fresh "H" in intro h;
       cut (Val x = Val w); [ idtac | apply (h w H) ]
  | [ |- forall x, _ ] => 
      (* P -> G ==> P |- G *)
       intro
  | [ H:valid_loc ?x ?i |- valid_loc ?x ?i ] => auto
  | [ |- valid_loc ?x ?i] => eapply (selects_valid x i); eauto
      (* valid_loc x i -- try to prove x points to something in i *)
  | [ |- (_ /\ _) ] => 
      (* G1 /\ G2 ==> |- G1 and |- G2 *)
      split ; [ idtac | idtac ]
  | [ |- selects ?y ?v (update_loc ?h ?x ?w) ] => 
      (* break this into the two cases where y=x and y<>x *)
      unfold update_loc at 1; idtac "UNFOLD"; unfold update_loc; unfold selects at 1;
      elim (loc_eq x y) ; [ auto | auto ]
  | [ |- selects _ _ (update_loc _ _ _) ] => 
      (* if that failed, invoke the heap-split tactic *)
      heap_split
  | [ |- eq (A:=heap) ?h1 ?h2 ] =>
      (* when the goal asks to prove two heaps equivalent, go ahead
       * and eta-expand them. *)
      apply (heap_extensional h1 h2); intro
  | [ |- nopre _ ] => 
      (* nopre is "True" *)
      unfold nopre; auto
  | _ => auto
  end. 

(* aggressive simplifier -- instantiates existentials when we have
 * a single assumption of the appropriate type *)
Ltac asimp := 
  match goal with
  | [ a:?T, b:?T |- exists x:?T, _] => 
      (* this rule is used to override the next one when there's more
       * than one choice in context to instantiate a variable *)
      idtac
  | [ a:?T |- exists x:?T, _ ] => exists a
      (* here we have one term in context and instantiate the quantifier
       * with it.  But this is not always right... *)
  | _ => csimp
  end.

(* repeat csimp until there's no progress *)
Ltac csimps := repeat (progress csimp).
Ltac asimps := repeat (progress asimp).



(* tries to simplify goals that are pre-conditions by using some
 * of the lemmas above. *)
Ltac simp_pre := 
  match goal with
  | [ H:read_pre _ _ _ |- _] =>
    elim H ; clear H ; intro ; intro 
  | [ H:nopre _ |- _] =>
    clear H
  | [ |- bind_pre nopre _ _ _ ] => unfold bind_pre at 1
  | [ |- bind_pre (read_pre _ _) (read_post _ _) _ _ ] =>
    eapply bind_read_pre
  | [ |- bind_pre nopre (new_post _) _ _ ] =>
    eapply bind_new_pre
  | [ |- bind_pre (valid_loc _) (write_post _ _) _ _ ] =>
    eapply bind_write_pre
  | [ |- bind_pre (bind_pre _ _ _) (bind_post _ _ _) _ _] =>
    eapply bind_bind_pre
  | [ |- (bind_pre (read_pre ?A ?r) (read_post ?A ?r) ?p2 ?i) -> _] => 
    let H := fresh "H" in
    intro H;
    cut (exists v:A, selects r v i /\ p2 v i);
    [clear H | apply (simp_bind_read_pre A r p2 i H) ]
  | [ |- (bind_pre nopre _ _ _) -> _ ] => unfold bind_pre at 1
  | _ => idtac
  end.

(* tries to simplify goals that involve post-conditions using some
 * of the lemmas above. *)
Ltac simp_post := 
  match goal with
  | [ |- bind_post (read_pre ?A ?r) (read_post ?A ?r) ?q ?y ?i ?m -> _ ] =>
    let H := fresh "H" in
    intro H;
    cut (exists v:A, selects r v i /\ q v y i m) ;
      [ clear H | apply (bind_read_post r q y i m H)]
  | [ |- bind_post (valid_loc ?r) (write_post ?r ?v) ?q ?y ?i ?m -> _ ] =>
    let H := fresh "H" in
    intro H;
    cut (valid_loc r i /\ q tt y (update_loc i r v) m) ;
      [ clear H | apply (bind_write_post r v q y i m H) ]
  | [ |- bind_post nopre (new_post ?v) ?q ?y ?i ?m -> _ ] =>
    let H := fresh "H" in
    intro H;
    cut (exists r:loc, unused_loc i r /\ q r y (update_loc i r v) m) ;
      [ clear H | apply (bind_new_post v q y i m H) ]
  | [ |- read_post _ _ _ _ _ -> _ ] => unfold read_post at 1
  | [ |- write_post _ _ _ _ _ -> _ ] => unfold write_post at 1
  | [ |- new_post _ _ _ _ -> _] => unfold new_post at 1
  | [ |- bind_post _ _ _ _ _ _ -> _] => unfold bind_post at 1
  | [ |- ret_post _ _ _ _ -> _] => unfold ret_post at 1
  | [ |- bind_noexn _ _ _ _ _ _ -> _] => unfold bind_noexn at 1
  | [ |- bind_exn _ _ _ _ _ -> _] => unfold bind_exn at 1
  | _ => idtac
  end.

(* simlify post- and pre-conditions, and then do aggressive simplifier *)
Ltac avcsimp := (simp_post ; simp_pre ; asimp).
(* simlify post- and pre-conditions, and then do conservative simplifier *)
Ltac cvcsimp := (simp_post ; simp_pre ; csimp).

(* same as above but repeat while there's progress *)
Ltac avcsimps := repeat (progress avcsimp). 
Ltac cvcsimps := repeat (progress cvcsimp). 
