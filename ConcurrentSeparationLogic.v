(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 14: Concurrent Separation Logic
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap Setoid Classes.Morphisms SepCancel.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Shared notations and definitions; main material starts afterward. *)

Notation heap := (fmap nat nat).
Notation locks := (set nat).

Hint Extern 1 (_ <= _) => linear_arithmetic.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try linear_arithmetic.


(** * A shared-memory concurrent language with loops *)

(* Let's work with a variant of the imperative language from last time. *)

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

Inductive cmd : Set -> Type :=
| Return {result : Set} (r : result) : cmd result
| Fail {result} : cmd result
| Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc

| Read (a : nat) : cmd nat
| Write (a v : nat) : cmd unit
| Lock (a : nat) : cmd unit
| Unlock (a : nat) : cmd unit
| Alloc (numWords : nat) : cmd nat
| Free (base numWords : nat) : cmd unit

| Par (c1 c2 : cmd unit) : cmd unit.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).
Infix "||" := Par.

Fixpoint initialize (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => initialize h base numWords' $+ (base + numWords', 0)
  end.

Fixpoint deallocate (h : heap) (base numWords : nat) : heap :=
  match numWords with
  | O => h
  | S numWords' => deallocate (h $- base) (base+1) numWords'
  end.

Inductive step : forall A, heap * locks * cmd A -> heap * locks * cmd A -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) h l h' l',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Bind c1 c2) (h', l', Bind c1' c2)
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) h l,
  step (h, l, Bind (Return v) c2) (h, l, c2 v)

| StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h l,
  step (h, l, Loop init body) (h, l, o <- body init; match o with
                                                     | Done a => Return a
                                                     | Again a => Loop a body
                                                     end)

| StepRead : forall h l a v,
  h $? a = Some v
  -> step (h, l, Read a) (h, l, Return v)
| StepWrite : forall h l a v v',
  h $? a = Some v
  -> step (h, l, Write a v') (h $+ (a, v'), l, Return tt)
| StepAlloc : forall h l numWords a,
  (forall i, i < numWords -> h $? (a + i) = None)
  -> step (h, l, Alloc numWords) (initialize h a numWords, l, Return a)
| StepFree : forall h l a numWords,
  step (h, l, Free a numWords) (deallocate h a numWords, l, Return tt)

| StepLock : forall h l a,
  ~a \in l
  -> step (h, l, Lock a) (h, l \cup {a}, Return tt)
| StepUnlock : forall h l a,
  a \in l
  -> step (h, l, Unlock a) (h, l \setminus {a}, Return tt)

| StepPar1 : forall h l c1 c2 h' l' c1',
  step (h, l, c1) (h', l', c1')
  -> step (h, l, Par c1 c2) (h', l', Par c1' c2)
| StepPar2 : forall h l c1 c2 h' l' c2',
  step (h, l, c2) (h', l', c2')
  -> step (h, l, Par c1 c2) (h', l', Par c1 c2').
    
Definition trsys_of (h : heap) (l : locks) {result} (c : cmd result) := {|
  Initial := {(h, l, c)};
  Step := step (A := result)
|}.

(* Next, we define our notion of assertion and instantiate the generic
 * separation-logic cancelation automation, in exactly the same way as
 * before. *)
Module Import S <: SEP.
  Definition hprop := heap -> Prop.
  (* We add the locks to the mix. *)

  Definition himp (p q : hprop) := forall h, p h -> q h.
  Definition heq (p q : hprop) := forall h, p h <-> q h.

  (* Lifting a pure proposition: it must hold, and the heap must be empty. *)
  Definition lift (P : Prop) : hprop :=
    fun h => P /\ h = $0.

  (* Separating conjunction, one of the two big ideas of separation logic.
   * When does [star p q] apply to [h]?  When [h] can be partitioned into two
   * subheaps [h1] and [h2], respectively compatible with [p] and [q].  See book
   * module [Map] for definitions of [split] and [disjoint]. *)
  Definition star (p q : hprop) : hprop :=
    fun h => exists h1 h2, split h h1 h2 /\ disjoint h1 h2 /\ p h1 /\ q h2.

  (* Existential quantification *)
  Definition exis A (p : A -> hprop) : hprop :=
    fun h => exists x, p x h.

  (* Convenient notations *)
  Notation "[| P |]" := (lift P) : sep_scope.
  Infix "*" := star : sep_scope.
  Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
  Delimit Scope sep_scope with sep.
  Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
  Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).

  Local Open Scope sep_scope.

  (* And now we prove some key algebraic properties, whose details aren't so
   * important.  The library automation uses these properties. *)

  Lemma iff_two : forall A (P Q : A -> Prop),
    (forall x, P x <-> Q x)
    -> (forall x, P x -> Q x) /\ (forall x, Q x -> P x).
  Proof.
    firstorder.
  Qed.

  Local Ltac t := (unfold himp, heq, lift, star, exis; propositional; subst);
                 repeat (match goal with
                         | [ H : forall x, _ <-> _ |- _  ] =>
                           apply iff_two in H
                         | [ H : ex _ |- _ ] => destruct H
                         | [ H : split _ _ $0 |- _ ] => apply split_empty_fwd in H
                         end; propositional; subst); eauto 15.

  Theorem himp_heq : forall p q, p === q
    <-> (p ===> q /\ q ===> p).
  Proof.
    t.
  Qed.

  Theorem himp_refl : forall p, p ===> p.
  Proof.
    t.
  Qed.

  Theorem himp_trans : forall p q r, p ===> q -> q ===> r -> p ===> r.
  Proof.
    t.
  Qed.

  Theorem lift_left : forall p (Q : Prop) r,
    (Q -> p ===> r)
    -> p * [| Q |] ===> r.
  Proof.
    t.
  Qed.

  Theorem lift_right : forall p q (R : Prop),
    R
    -> p ===> q
    -> p ===> q * [| R |].
  Proof.
    t.
  Qed.

  Hint Resolve split_empty_bwd'.

  Theorem extra_lift : forall (P : Prop) p,
    P
    -> p === [| P |] * p.
  Proof.
    t.
    apply split_empty_fwd' in H1; subst; auto.
  Qed.    

  Theorem star_comm : forall p q, p * q === q * p.
  Proof.
    t.
  Qed.

  Theorem star_assoc : forall p q r, p * (q * r) === (p * q) * r.
  Proof.
    t.
  Qed.

  Theorem star_cancel : forall p1 p2 q1 q2, p1 ===> p2
    -> q1 ===> q2
    -> p1 * q1 ===> p2 * q2.
  Proof.
    t.
  Qed.

  Theorem exis_gulp : forall A p (q : A -> _),
    p * exis q === exis (fun x => p * q x).
  Proof.
    t.
  Qed.

  Theorem exis_left : forall A (p : A -> _) q,
    (forall x, p x ===> q)
    -> exis p ===> q.
  Proof.
    t.
  Qed.

  Theorem exis_right : forall A p (q : A -> _) x,
    p ===> q x
    -> p ===> exis q.
  Proof.
    t.
  Qed.
End S.

Export S.
(* Instantiate our big automation engine to these definitions. *)
Module Import Se := SepCancel.Make(S).


(* ** Some extra predicates outside the set that the engine knows about *)

(* Capturing single-mapping heaps *)
Definition heap1 (a v : nat) : heap := $0 $+ (a, v).
Definition ptsto (a v : nat) : hprop :=
  fun h => h = heap1 a v.

(* Helpful notations, some the same as above *)
Notation "[| P |]" := (lift P) : sep_scope.
Notation emp := (lift True).
Infix "*" := star : sep_scope.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
Delimit Scope sep_scope with sep.
Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).
Infix "|->" := ptsto (at level 30) : sep_scope.

Fixpoint multi_ptsto (a : nat) (vs : list nat) : hprop :=
  match vs with
  | nil => emp
  | v :: vs' => a |-> v * multi_ptsto (a + 1) vs'
  end%sep.

Infix "|-->" := multi_ptsto (at level 30) : sep_scope.

Fixpoint zeroes (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => zeroes n' ++ 0 :: nil
  end.

Fixpoint allocated (a n : nat) : hprop :=
  match n with
  | O => emp
  | S n' => (exists v, a |-> v) * allocated (a+1) n'
  end%sep.

Infix "|->?" := allocated (at level 30) : sep_scope.


(** * Finally, the Hoare logic *)

(* The whole thing is parameterized on a map from locks to invariants on their
 * owned state.  The map is a list, with lock [i] getting the [i]th invariant in
 * the list.  Lock numbers at or beyond the list length are forbidden. *)

Inductive hoare_triple (linvs : list hprop) : forall {result}, hprop -> cmd result -> (result -> hprop) -> Prop :=
(* First, we have the basic separation-logic rules from before. *)
| HtReturn : forall P {result : Set} (v : result),
    hoare_triple linvs P (Return v) (fun r => P * [| r = v |])%sep
| HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
    hoare_triple linvs P c1 Q
    -> (forall r, hoare_triple linvs (Q r) (c2 r) R)
    -> hoare_triple linvs P (Bind c1 c2) R
| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I,
    (forall acc, hoare_triple linvs (I (Again acc)) (body acc) I)
    -> hoare_triple linvs (I (Again init)) (Loop init body) (fun r => I (Done r))
| HtFail : forall {result},
    hoare_triple linvs [| False |]%sep (Fail (result := result)) (fun _ => [| False |])%sep
| HtRead : forall a R,
    hoare_triple linvs (exists v, a |-> v * R v)%sep (Read a) (fun r => a |-> r * R r)%sep
| HtWrite : forall a v',
    hoare_triple linvs (exists v, a |-> v)%sep (Write a v') (fun _ => a |-> v')%sep
| HtAlloc : forall numWords,
    hoare_triple linvs emp%sep (Alloc numWords) (fun r => r |--> zeroes numWords)%sep
| HtFree : forall a numWords,
    hoare_triple linvs (a |->? numWords)%sep (Free a numWords) (fun _ => emp)%sep

(* Next, how to handle locking: the thread takes ownership of a memory chunk
 * satisfying the lock's invariant. *)
| HtLock : forall a I,
    nth_error linvs a = Some I
    -> hoare_triple linvs emp%sep (Lock a) (fun _ => I)

(* When unlocking, the thread relinquishes ownership of a memory chunk
 * satisfying the lock's invariant. *)
| HtUnlock : forall a I,
    nth_error linvs a = Some I
    -> hoare_triple linvs I (Unlock a) (fun _ => emp)%sep

(* When forking into two threads, divide the (local) heap among them. *)
| HtPar : forall P1 c1 Q1 P2 c2 Q2,
    hoare_triple linvs P1 c1 Q1
    -> hoare_triple linvs P2 c2 Q2
    -> hoare_triple linvs (P1 * P2)%sep (Par c1 c2) (fun _ => Q1 tt * Q2 tt)%sep

(* Now we repeat these two structural rules from before. *)
| HtConsequence : forall {result} (c : cmd result) P Q (P' : hprop) (Q' : _ -> hprop),
    hoare_triple linvs P c Q
    -> P' ===> P
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple linvs P' c Q'
| HtFrame : forall {result} (c : cmd result) P Q R,
    hoare_triple linvs P c Q
    -> hoare_triple linvs (P * R)%sep c (fun r => Q r * R)%sep.


Notation "linvs ||- {{ P }} c {{ r ~> Q }}" :=
  (hoare_triple linvs P%sep c (fun r => Q%sep)) (at level 90, c at next level).

Lemma HtStrengthen : forall linvs {result} (c : cmd result) P Q (Q' : _ -> hprop),
    hoare_triple linvs P c Q
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple linvs P c Q'.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

Lemma HtWeaken : forall linvs {result} (c : cmd result) P Q (P' : hprop),
    hoare_triple linvs P c Q
    -> P' ===> P
    -> hoare_triple linvs P' c Q.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

Hint Resolve himp_refl.

Lemma invert_Return : forall linvs {result : Set} (r : result) P Q,
  hoare_triple linvs P (Return r) Q
  -> P ===> Q r.
Proof.
  induct 1; propositional; eauto.

  cancel.

  eauto using himp_trans.

  rewrite IHhoare_triple; eauto.
Qed.

Hint Constructors hoare_triple.

Lemma invert_Bind : forall linvs {result' result} (c1 : cmd result') (c2 : result' -> cmd result) P Q,
  hoare_triple linvs P (Bind c1 c2) Q
  -> exists R, hoare_triple linvs P c1 R
               /\ forall r, hoare_triple linvs (R r) (c2 r) Q.
Proof.
  induct 1; propositional; eauto.

  invert IHhoare_triple; propositional.
  eexists; propositional.
  eapply HtWeaken.
  eassumption.
  auto.
  eapply HtStrengthen.
  apply H4.
  auto.

  simp.
  exists (fun r => x r * R)%sep.
  propositional.
  eapply HtFrame; eauto.
  eapply HtFrame; eauto.
Qed.

Lemma invert_Loop : forall linvs {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) P Q,
    hoare_triple linvs P (Loop init body) Q
    -> exists I, (forall acc, hoare_triple linvs (I (Again acc)) (body acc) I)
                 /\ P ===> I (Again init)
                 /\ (forall r, I (Done r) ===> Q r).
Proof.
  induct 1; propositional; eauto.

  invert IHhoare_triple; propositional.
  exists x; propositional; eauto.
  unfold himp in *; eauto.

  eauto using himp_trans.

  simp.
  exists (fun o => x o * R)%sep; propositional; eauto.
  rewrite H0; eauto.
  rewrite H3; eauto.
Qed.

(* Now that we proved enough basic facts, let's hide the definitions of all
 * these predicates, so that we reason about them only through automation. *)
Opaque heq himp lift star exis ptsto.

Lemma unit_not_nat : unit = nat -> False.
Proof.
  simplify.
  assert (exists x : unit, forall y : unit, x = y).
  exists tt; simplify.
  cases y; reflexivity.
  rewrite H in H0.
  invert H0.
  specialize (H1 (S x)).
  linear_arithmetic.
Qed.

Lemma invert_Read : forall linvs a P Q,
  hoare_triple linvs P (Read a) Q
  -> exists R, (P ===> exists v, a |-> v * R v)%sep
               /\ forall r, a |-> r * R r ===> Q r.
Proof.
  induct 1; simp; eauto.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  eauto 7 using himp_trans.

  exists (fun n => x n * R)%sep; simp.
  rewrite H1.
  cancel.

  rewrite <- H2.
  cancel.
Qed.

Lemma invert_Write : forall linvs a v' P Q,
  hoare_triple linvs P (Write a v') Q
  -> exists R, (P ===> (exists v, a |-> v) * R)%sep
               /\ a |-> v' * R ===> Q tt.
Proof.
  induct 1; simp; eauto.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  exists emp; simp.
  cancel; auto.
  cancel; auto.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  eauto 7 using himp_trans.

  exists (x * R)%sep; simp.
  rewrite H1.
  cancel.

  cancel.
  rewrite <- H2.
  cancel.
Qed.

Lemma invert_Alloc : forall linvs numWords P Q,
  hoare_triple linvs P (Alloc numWords) Q
  -> forall r, P * r |--> zeroes numWords ===> Q r.
Proof.
  induct 1; simp; eauto.

  apply unit_not_nat in x0; simp.

  cancel.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  rewrite H0; eauto.
  eauto 7 using himp_trans.

  rewrite <- IHhoare_triple.
  cancel.
Qed.

(* Temporarily transparent again! *)
Transparent heq himp lift star exis ptsto.

Lemma zeroes_initialize' : forall h a v,
    h $? a = None
    -> (fun h' : heap => h' = h $+ (a, v)) ===> (fun h' => h' = h) * a |-> v.
Proof.
  unfold himp, star, split, ptsto, disjoint; simp.
  exists h, (heap1 a v).
  propositional.
  maps_equal.
  unfold heap1.
  rewrite lookup_join2.
  simp.
  simp.
  apply lookup_None_dom in H.
  propositional.
  cases (h $? k).
  rewrite lookup_join1; auto.
  eauto using lookup_Some_dom.
  rewrite lookup_join2; auto.
  unfold heap1; simp.
  eauto using lookup_None_dom.
  unfold heap1 in *.
  cases (a ==n a0); simp.
Qed.

(* Opaque again! *)
Opaque heq himp lift star exis ptsto.

Lemma multi_ptsto_app : forall ls2 ls1 a,
     a |--> ls1 * (a + length ls1) |--> ls2 ===> a |--> (ls1 ++ ls2).
Proof.
  induct ls1; simp; cancel; auto.

  replace (a + 0) with a by linear_arithmetic.
  cancel.

  rewrite <- IHls1.
  cancel.
  replace (a0 + 1 + length ls1) with (a0 + S (length ls1)) by linear_arithmetic.
  cancel.
Qed.

Lemma length_zeroes : forall n,
    length (zeroes n) = n.
Proof.
  induct n; simplify; auto.
  rewrite app_length; simplify.
  linear_arithmetic.
Qed.

Lemma initialize_fresh : forall a' h a numWords,
    a' >= a + numWords
    -> initialize h a numWords $? a' = h $? a'.
Proof.
  induct numWords; simp; auto.
Qed.

Lemma zeroes_initialize : forall numWords a h,
    (forall i, i < numWords -> h $? (a + i) = None)
    -> (fun h' => h' = initialize h a numWords) ===> (fun h' => h' = h) * a |--> zeroes numWords.
Proof.
  induct numWords; simp.

  cancel; auto.
  rewrite <- multi_ptsto_app.
  rewrite zeroes_initialize'.
  erewrite IHnumWords.
  simp.
  rewrite length_zeroes.
  cancel; auto.
  auto.
  rewrite initialize_fresh; auto.
Qed.

Lemma invert_Free : forall linvs a numWords P Q,
  hoare_triple linvs P (Free a numWords) Q
  -> P ===> a |->? numWords * Q tt.
Proof.
  induct 1; simp; eauto.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  cancel; auto.

  rewrite H0.
  rewrite IHhoare_triple.
  cancel; auto.

  rewrite IHhoare_triple.
  cancel; auto.
Qed.

(* Temporarily transparent again! *)
Transparent heq himp lift star exis ptsto.

Lemma do_deallocate' : forall a Q h,
    ((exists v, a |-> v) * Q)%sep h
    -> Q (h $- a).
Proof.
  unfold ptsto, star, split, heap1; simp.
  invert H1.
  replace ($0 $+ (a, x1) $++ x0 $- a) with x0; auto.
  maps_equal.
  cases (k ==n a); simp.
  specialize (H a).
  simp.
  cases (x0 $? a); auto.
  exfalso; apply H; equality.
  rewrite lookup_join2; auto.
  apply lookup_None_dom.
  simp.
Qed.

Lemma do_deallocate : forall Q numWords a h,
    (a |->? numWords * Q)%sep h
    -> Q (deallocate h a numWords).
Proof.
  induct numWords; simp.

  unfold star, exis, lift in H; simp.
  apply split_empty_fwd' in H0; simp.

  apply IHnumWords.
  clear IHnumWords.
  
  apply do_deallocate'.
  Opaque heq himp lift star exis ptsto.
  match goal with
  | [ H : ?P h |- ?Q h ] => assert (P ===> Q) by cancel
  end.
  Transparent himp.
  apply H0; auto.
  Opaque himp.
Qed.

Lemma HtReturn' : forall linvs P {result : Set} (v : result) Q,
    P ===> Q v
    -> hoare_triple linvs P (Return v) Q.
Proof.
  simp.
  eapply HtStrengthen.
  constructor.
  simp.
  cancel.
Qed.

Opaque heq himp lift star exis ptsto.

Lemma invert_Lock : forall linvs a P Q,
  hoare_triple linvs P (Lock a) Q
  -> exists I, nth_error linvs a = Some I
               /\ P * I ===> Q tt.
Proof.
  induct 1; simp; eauto 10.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  eexists; simp.
  eauto.
  cancel.

  eexists; simp.
  eauto.
  rewrite H0; eauto using himp_trans.

  eexists; simp.
  eauto.
  rewrite <- H2.
  cancel.
Qed.

Lemma invert_Unlock : forall linvs a P Q,
  hoare_triple linvs P (Unlock a) Q
  -> exists I, nth_error linvs a = Some I
               /\ P ===> Q tt * I.
Proof.
  induct 1; simp; eauto 10.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  eexists; simp.
  eauto.
  cancel.

  eexists; simp.
  eauto.
  rewrite <- H1; eauto using himp_trans.

  eexists; simp.
  eauto.
  rewrite H2.
  cancel.
Qed.

Lemma invert_Par : forall linvs c1 c2 P Q,
  hoare_triple linvs P (Par c1 c2) Q
  -> exists P1 P2 Q1 Q2,
      hoare_triple linvs P1 c1 Q1
      /\ hoare_triple linvs P2 c2 Q2
      /\ P ===> P1 * P2
      /\ Q1 tt * Q2 tt ===> Q tt.
Proof.
  induct 1; simp; eauto 10.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  symmetry in x0.
  apply unit_not_nat in x0; simp.

  eauto 10 using himp_trans.

  exists (x * R)%sep, x0, (fun r => x1 r * R)%sep, x2; simp; eauto.
  rewrite H2; cancel.
  rewrite <- H4; cancel.
Qed.

(* Temporarily transparent again! *)
Transparent heq himp lift star exis ptsto.

(* Guarded predicates *)
Definition guarded (P : Prop) (p : hprop) : hprop :=
  fun h => IF P then p h else emp%sep h.

Infix "===>" := guarded : sep_scope.

Theorem guarded_true : forall (P : Prop) p, P
  -> (P ===> p) === p.
Proof.
  unfold heq, guarded, IF_then_else; simp.
Qed.

Theorem guarded_false : forall (P : Prop) p, ~P
  -> (P ===> p) === emp.
Proof.
  unfold heq, guarded, IF_then_else; simp.
Qed.

(* Iterated separating conjunction *)
Fixpoint bigstar A (P : nat -> A -> hprop) (ls : list A) : hprop :=
  match ls with
  | nil => emp
  | x :: ls' => P 0 x * bigstar (fun n => P (S n)) ls'
  end%sep.

Definition lockChunks (l : locks) (ls : list hprop) :=
  bigstar (fun i I => (~i \in l) ===> I)%sep ls.

Lemma use_himp : forall P Q, P ===> Q
  -> forall h, P h -> Q h.
Proof.
  auto.
Qed.

Lemma ptsto_out : forall h a v p,
    h $? a = Some v
    -> (exists v', a |-> v' * p v')%sep h
    -> (a |-> v * p v)%sep h
       /\ forall v', (a |-> v' * p v)%sep (h $+ (a, v')).
Proof.
  invert 2.
  invert H1.
  simp.

  invert H2.
  unfold split in H0; subst.
  rewrite lookup_join1 in H.
  unfold heap1 in H.
  simplify.
  invert H.
  exists (heap1 a v), x1; simp.
  eauto.
  unfold ptsto.
  eauto.
  unfold heap1; simplify.
  sets.

  invert H2.
  unfold split in H0; subst.
  rewrite lookup_join1 in H.
  unfold heap1 in H.
  simplify.
  invert H.
  exists (heap1 a v'), x1; simp.
  unfold split.
  maps_equal.
  rewrite lookup_join1.
  unfold heap1; simplify; auto.
  unfold heap1; simplify; sets.
  repeat rewrite lookup_join2; auto.
  unfold heap1; simplify; sets.
  unfold heap1; simplify; sets.
  unfold disjoint in *; simp.
  apply (H1 a0); eauto.
  cases (a ==n a0); simp.
  unfold heap1 in *; simplify; equality.
  unfold heap1 in *; simplify; equality.
  unfold ptsto.
  eauto.
  unfold heap1; simplify; sets.
Qed.

Lemma specialize_hprop : forall (p : hprop) h,
    p h
    -> (fun h' => h' = h) ===> p.
Proof.
  unfold himp; equality.
Qed.

Opaque heq himp lift star exis ptsto.

Lemma bigstar_impl : forall A ls (p q : nat -> A -> hprop),
    (forall i x, p i x ===> q i x)
    -> bigstar p ls ===> bigstar q ls.
Proof.
  induct ls; simplify; auto.
  rewrite H.
  rewrite IHls.
  cancel.
  simp.
  eauto.
Qed.

Lemma guarded_impl : forall P Q p,
    P <-> Q
    -> (P ===> p) ===> (Q ===> p).
Proof.
  simp.
  excluded_middle P.
  repeat rewrite guarded_true by propositional.
  auto.
  repeat rewrite guarded_false by propositional.
  auto.
Qed.

Lemma lockChunks_lock' : forall l I linvs (f : nat -> nat) a,
    ~f a \in l
    -> nth_error linvs a = Some I
    -> (forall x y, f x = f y -> x = y)
    -> bigstar (fun i I => (~f i \in l) ===> I)%sep linvs ===> I * bigstar (fun i I => (~(f i \in l \cup {f a})) ===> I)%sep linvs.
Proof.
  induct linvs; simplify.

  cases a; simplify; equality.

  cases a0; simplify.
  invert H0.
  rewrite guarded_true by sets.
  rewrite guarded_false by sets.
  cancel.
  apply bigstar_impl.
  simp.
  apply guarded_impl.
  sets.
  apply H1 in H2.
  equality.

  apply (IHlinvs (fun n => f (S n))) in H0; auto.
  rewrite H0.
  cancel.
  apply guarded_impl.
  sets.
  apply H1 in H3.
  equality.
  simp.
  apply H1 in H2.
  equality.
Qed.

Lemma lockChunks_lock : forall a l I linvs,
    ~a \in l
    -> nth_error linvs a = Some I
    -> lockChunks l linvs ===> I * lockChunks (l \cup {a}) linvs.
Proof.
  simp.
  apply lockChunks_lock' with (f := fun n => n); auto.
Qed.

Lemma lockChunks_unlock' : forall l I linvs (f : nat -> nat) a,
    f a \in l
    -> nth_error linvs a = Some I
    -> (forall x y, f x = f y -> x = y)
    -> I * bigstar (fun i I => (~f i \in l) ===> I)%sep linvs ===> bigstar (fun i I => (~(f i \in l \setminus {f a})) ===> I)%sep linvs.
Proof.
  induct linvs; simplify.

  cases a; simplify; equality.

  cases a0; simplify.
  invert H0.
  rewrite guarded_false by sets.
  rewrite guarded_true by sets.
  cancel.
  apply bigstar_impl.
  simp.
  apply guarded_impl.
  sets.
  apply H0; propositional.
  apply H1 in H4.
  equality.

  apply (IHlinvs (fun n => f (S n))) in H0; auto.
  rewrite <- H0.
  cancel.
  apply guarded_impl.
  sets.
  apply H2; propositional.
  apply H1 in H5.
  equality.
  simp.
  apply H1 in H2.
  equality.
Qed.

Lemma lockChunks_unlock : forall a l I linvs,
    a \in l
    -> nth_error linvs a = Some I
    -> I * lockChunks l linvs ===> lockChunks (l \setminus {a}) linvs.
Proof.
  simp.
  apply lockChunks_unlock' with (f := fun n => n); auto.
Qed.

Lemma preservation : forall linvs {result} (c : cmd result) h l c' h' l',
    step (h, l, c) (h', l', c')
    -> forall P Q R, hoare_triple linvs P c Q
                     -> (P * R * lockChunks l linvs)%sep h
                     -> exists P', hoare_triple linvs P' c' Q
                                   /\ (P' * R * lockChunks l' linvs)%sep h'.
Proof.
  induct 1; simplify.

  apply invert_Bind in H0; simp.
  eapply IHstep in H0; eauto.
  simp.
  eauto.
  
  apply invert_Bind in H; simp.
  specialize (invert_Return H); eauto using HtWeaken.

  apply invert_Loop in H; simp.
  eexists; simp.
  econstructor.
  eauto.
  simp.
  cases r.
  apply HtReturn'.
  auto.
  eapply HtStrengthen.
  eauto.
  eauto.
  eapply use_himp; try eassumption.
  rewrite H1.
  eauto.

  apply invert_Read in H0; simp.
  assert ((exists v, a |-> v * (x v * R * lockChunks l' linvs))%sep h').
  eapply use_himp; try eassumption.
  rewrite H0.
  cancel.
  eapply ptsto_out in H2; eauto.
  eexists; simp.
  apply HtReturn'.
  eauto.
  eapply use_himp; try eassumption.
  cancel.

  apply invert_Write in H0; simp.
  assert ((exists v, a |-> v * (x * R * lockChunks l' linvs))%sep h).
  eapply use_himp; try eassumption.
  rewrite H0.
  cancel.
  eapply ptsto_out in H2; eauto.
  propositional.
  eexists; simp.
  apply HtReturn'.
  eauto.
  eapply use_himp; try apply H5.
  cancel.

  apply invert_Alloc with (r := a) in H0.
  eexists; propositional.
  apply HtReturn'.
  eassumption.
  apply use_himp with ((P * R * lockChunks l' linvs) * a |--> zeroes numWords)%sep.
  cancel.
  apply use_himp with ((fun h' => h' = h) * a |--> zeroes numWords)%sep.
  cancel.
  eauto using specialize_hprop.
  eapply use_himp.
  apply zeroes_initialize; auto.
  simp.

  apply invert_Free in H.
  eexists; propositional.
  instantiate (1 := Q tt).
  apply HtReturn'.
  auto.
  apply do_deallocate; simplify.
  change (fun f => (Q tt * lockChunks l' linvs) f)%sep with (Q tt * lockChunks l' linvs)%sep.
  eapply use_himp; try eassumption.
  rewrite H.
  cancel.

  apply invert_Lock in H0.
  simp.
  eexists; propositional.
  apply HtReturn'; auto.
  eapply use_himp; try eassumption.
  rewrite <- H3.
  cancel.
  apply lockChunks_lock; auto.

  apply invert_Unlock in H0.
  simp.
  eexists; propositional.
  apply HtReturn'; auto.
  eapply use_himp; try eassumption.
  rewrite H3.
  cancel.
  rewrite <- lockChunks_unlock; eauto.
  cancel.

  apply invert_Par in H0.
  simp.
  eapply IHstep in H2.
  simp.
  eexists; propositional.
  eapply HtStrengthen.
  econstructor.
  eassumption.
  eassumption.
  simp.
  cases r; auto.
  eapply use_himp; try eassumption.
  cancel.
  eapply use_himp; try eassumption.
  cancel.
  
  apply invert_Par in H0.
  simp.
  eapply IHstep in H0.
  simp.
  eexists; propositional.
  eapply HtStrengthen.
  econstructor.
  eassumption.
  eassumption.
  simp.
  cases r; auto.
  eapply use_himp; try eassumption.
  cancel.
  eapply use_himp; try eassumption.
  rewrite H3.
  cancel.
Qed.

Definition allLockChunks (linvs : list hprop) := bigstar (fun _ I => I) linvs.

Lemma allLockChunks_lockChunks' : forall linvs (f : nat -> nat),
   bigstar (fun _ I => I) linvs ===> bigstar (fun i I => (~f i \in {}) ===> I) linvs.
Proof.
  induct linvs; simp; auto.

  rewrite guarded_true by sets.
  rewrite IHlinvs.
  cancel.
Qed.

Lemma allLockChunks_lockChunks : forall linvs,
    allLockChunks linvs ===> lockChunks {} linvs.
Proof.
  simp.
  apply allLockChunks_lockChunks' with (f := fun n => n).
Qed.

Lemma hoare_triple_sound' : forall linvs P {result} (c : cmd result) Q,
    hoare_triple linvs P c Q
    -> forall h, (P * allLockChunks linvs)%sep h
    -> invariantFor (trsys_of h {} c)
                    (fun p =>
                       let '(h, l, c) := p in
                       exists P', hoare_triple linvs P' c Q
                                  /\ (P' * lockChunks l linvs)%sep h).
Proof.
  simplify.

  apply invariant_induction; simplify.

  propositional; subst; simplify.
  eexists; propositional.
  eauto.
  eapply use_himp; try eassumption.
  rewrite allLockChunks_lockChunks.
  auto.

  cases s.
  cases p.
  cases s'.
  cases p.
  simp.
  eapply preservation with (R := emp%sep) in H1; eauto.
  simp.
  eexists; propositional; eauto.
  eapply use_himp; try eassumption.
  cancel.
  eapply use_himp; try eassumption.
  cancel.
Qed.

Fixpoint notAboutToFail {result} (c : cmd result) :=
  match c with
  | Fail _ => false
  | Bind _ _ c1 _ => notAboutToFail c1
  | Par c1 c2 => notAboutToFail c1 && notAboutToFail c2
  | _ => true
  end.

Lemma hoare_triple_notAboutToFail : forall linvs P result (c : cmd result) Q,
    hoare_triple linvs P c Q
    -> notAboutToFail c = false
    -> P ===> [| False |].
Proof.
  induct 1; simp; try equality; eauto using himp_trans.

  apply andb_false_iff in H1; propositional.
  rewrite H1; cancel.
  rewrite H1; cancel.

  rewrite H1; cancel.
Qed.

Lemma False_star : forall p,
    [| False |] * p ===> [| False |].
Proof.
  cancel.
Qed.

Theorem hoare_triple_sound : forall linvs P {result} (c : cmd result) Q,
    hoare_triple linvs P c Q
    -> forall h, (P * allLockChunks linvs)%sep h
    -> invariantFor (trsys_of h {} c)
                    (fun p => let '(_, _, c) := p in
                              notAboutToFail c = true).
Proof.
  simplify.

  eapply invariant_weaken.
  eapply hoare_triple_sound'; eauto.
  simp.
  cases s.
  cases p.
  simp.
  cases (notAboutToFail c0); auto.
  eapply hoare_triple_notAboutToFail in Heq; eauto.
  apply use_himp with (Q := [| False |]%sep) in H3.
  invert H3; propositional.
  rewrite Heq.
  cancel.
Qed.
