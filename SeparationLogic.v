(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 14: Separation Logic
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap Setoid Classes.Morphisms SepCancel.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Shared notations and definitions; main material starts afterward. *)

Definition heap := fmap nat nat.

Hint Extern 1 (_ <= _) => linear_arithmetic : core.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic : core.

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try linear_arithmetic.


(** * Encore of last mixed-embedding language from last time *)

(* Let's work with a variant of the imperative language from last time. *)

Inductive loop_outcome acc :=
| Done (a : acc)
| Again (a : acc).

Inductive cmd : Set -> Type :=
| Return {result : Set} (r : result) : cmd result
| Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
| Read (a : nat) : cmd nat
| Write (a v : nat) : cmd unit
| Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc
| Fail {result} : cmd result

(* But let's also add memory allocation and deallocation. *)
| Alloc (numWords : nat) : cmd nat
| Free (base numWords : nat) : cmd unit.

Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).

(* These helper functions respectively initialize a new span of memory and
 * remove a span of memory that the program is done with. *)

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

(* Let's do the semantics a bit differently this time, falling back on classic
 * small-step operational semantics. *)
Inductive step : forall A, heap * cmd A -> heap * cmd A -> Prop :=
| StepBindRecur : forall result result' (c1 c1' : cmd result') (c2 : result' -> cmd result) h h',
  step (h, c1) (h', c1')
  -> step (h, Bind c1 c2) (h', Bind c1' c2)
| StepBindProceed : forall (result result' : Set) (v : result') (c2 : result' -> cmd result) h,
  step (h, Bind (Return v) c2) (h, c2 v)

| StepLoop : forall (acc : Set) (init : acc) (body : acc -> cmd (loop_outcome acc)) h,
  step (h, Loop init body) (h, o <- body init; match o with
                                               | Done a => Return a
                                               | Again a => Loop a body
                                               end)

| StepRead : forall h a v,
  h $? a = Some v
  -> step (h, Read a) (h, Return v)
| StepWrite : forall h a v v',
  h $? a = Some v
  -> step (h, Write a v') (h $+ (a, v'), Return tt)
| StepAlloc : forall h numWords a,
  (forall i, i < numWords -> h $? (a + i) = None)
  -> step (h, Alloc numWords) (initialize h a numWords, Return a)
| StepFree : forall h a numWords,
  step (h, Free a numWords) (deallocate h a numWords, Return tt).


Definition trsys_of (h : heap) {result} (c : cmd result) := {|
  Initial := {(h, c)};
  Step := step (A := result)
|}.

(* Now let's get into the first distinctive feature of separation logic: an
 * assertion language that takes advantage of *partiality* of heaps.  We give our
 * definitions inside a module, which will shortly be used as a parameter to
 * another module (from the book library), to get some free automation for
 * implications between these assertions. *)
Module Import S <: SEP.
  Definition hprop := heap -> Prop.
  (* A [hprop] is a regular old assertion over heaps. *)

  (* Implication *)
  Definition himp (p q : hprop) := forall h, p h -> q h.

  (* Equivalence *)
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
    p ===> q
    -> R
    -> p ===> q * [| R |].
  Proof.
    t.
  Qed.

  Hint Resolve split_empty_bwd' : core.

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

(* For describing a "struct" in memory at consecutive addresses *)
Fixpoint multi_ptsto (a : nat) (vs : list nat) : hprop :=
  match vs with
  | nil => emp
  | v :: vs' => a |-> v * multi_ptsto (a + 1) vs'
  end%sep.

Infix "|-->" := multi_ptsto (at level 30) : sep_scope.

(* We'll use this one to describe the struct returned by [Alloc]. *)
Fixpoint zeroes (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => zeroes n' ++ 0 :: nil
  end.

(* For recording merely that a range of cells is mapped into our memory space *)
Fixpoint allocated (a n : nat) : hprop :=
  match n with
  | O => emp
  | S n' => (exists v, a |-> v) * allocated (a+1) n'
  end%sep.

Infix "|->?" := allocated (at level 30) : sep_scope.


(** * Finally, the Hoare logic *)

Inductive hoare_triple : forall {result}, hprop -> cmd result -> (result -> hprop) -> Prop :=
(* First, four basic rules that look exactly the same as before *)
| HtReturn : forall P {result : Set} (v : result),
    hoare_triple P (Return v) (fun r => P * [| r = v |])%sep
| HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
    hoare_triple P c1 Q
    -> (forall r, hoare_triple (Q r) (c2 r) R)
    -> hoare_triple P (Bind c1 c2) R
| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I,
    (forall acc, hoare_triple (I (Again acc)) (body acc) I)
    -> hoare_triple (I (Again init)) (Loop init body) (fun r => I (Done r))
| HtFail : forall {result},
    hoare_triple (fun _ => False) (Fail (result := result)) (fun _ _ => False)

(* Now the new rules for primitive heap operations: *)

| HtRead : forall a R,
    hoare_triple (exists v, a |-> v * R v)%sep (Read a) (fun r => a |-> r * R r)%sep
(* To read from an address, it must be mapped into the address space with some
 * value.  Afterward, that address is known to point to the result value [r].
 * An additional *frame* predicate [R] is along for the ride. *)

| HtWrite : forall a v',
    hoare_triple (exists v, a |-> v)%sep (Write a v') (fun _ => a |-> v')%sep
(* To write to an address, just show that it's mapped into the address space.
 * Afterward, that address points to the value we've written.  Note that this
 * rule is in the *small-footprint* style, with no frame predicate baked in. *)

| HtAlloc : forall numWords,
    hoare_triple emp%sep (Alloc numWords) (fun r => r |--> zeroes numWords)%sep
(* Allocation works in any memory, transitioning to a state where the result
 * value points to a sequence of zeroes. *)

| HtFree : forall a numWords,
    hoare_triple (a |->? numWords)%sep (Free a numWords) (fun _ => emp)%sep
(* Deallocation requires an argument pointing to the appropriate number of
 * words, taking us to a state where those addresses are unmapped. *)

| HtConsequence : forall {result} (c : cmd result) P Q (P' : hprop) (Q' : _ -> hprop),
    hoare_triple P c Q
    -> P' ===> P
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple P' c Q'
(* This is essentially the same rule of consequence from before. *)

| HtFrame : forall {result} (c : cmd result) P Q R,
    hoare_triple P c Q
    -> hoare_triple (P * R)%sep c (fun r => Q r * R)%sep.
(* The *frame rule* is the other big idea of separation logic.  We can extend
 * any Hoare triple by starring an arbitrary assertion [R] into both
 * precondition and postcondition.  Note that rule [HtRead] built in a variant
 * of the frame rule, where the frame predicate [R] may depend on the value [v]
 * being read.  The other operations can use this generic frame rule instead. *)


Notation "{{ P }} c {{ r ~> Q }}" :=
  (hoare_triple P%sep c (fun r => Q%sep)) (at level 90, c at next level).

Lemma HtStrengthen : forall {result} (c : cmd result) P Q (Q' : _ -> hprop),
    hoare_triple P c Q
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple P c Q'.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

Lemma HtWeaken : forall {result} (c : cmd result) P Q (P' : hprop),
    hoare_triple P c Q
    -> P' ===> P
    -> hoare_triple P' c Q.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

(* Now, we carry out a moderately laborious soundness proof!  It's safe to skip
 * ahead to the text "Examples", but a few representative lemma highlights
 * include [invert_Read], [preservation], [progress], and the main theorem
 * [hoare_triple_sound]. *)

Lemma invert_Return : forall {result : Set} (r : result) P Q,
  hoare_triple P (Return r) Q
  -> forall h, P h -> Q r h.
Proof.
  induct 1; propositional; eauto.

  exists h, $0; propositional; eauto.
  unfold lift; propositional.

  unfold himp in *; eauto.

  unfold star, himp in *; simp; eauto 7.
Qed.

Hint Constructors hoare_triple : core.

Lemma invert_Bind : forall {result' result} (c1 : cmd result') (c2 : result' -> cmd result) P Q,
  hoare_triple P (Bind c1 c2) Q
  -> exists R, hoare_triple P c1 R
               /\ forall r, hoare_triple (R r) (c2 r) Q.
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

Lemma invert_Loop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) P Q,
    hoare_triple P (Loop init body) Q
    -> exists I, (forall acc, hoare_triple (I (Again acc)) (body acc) I)
                 /\ (forall h, P h -> I (Again init) h)
                 /\ (forall r h, I (Done r) h -> Q r h).
Proof.
  induct 1; propositional; eauto.

  invert IHhoare_triple; propositional.
  exists x; propositional; eauto.
  unfold himp in *; eauto.

  simp.
  exists (fun o => x o * R)%sep; propositional; eauto.
  unfold star in *; simp; eauto 7.
  unfold star in *; simp; eauto 7.
Qed.

Lemma invert_Fail : forall result P Q,
  hoare_triple P (Fail (result := result)) Q
  -> forall h, P h -> False.
Proof.
  induct 1; propositional; eauto.

  unfold star in *; simp; eauto.
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

Lemma invert_Read : forall a P Q,
  hoare_triple P (Read a) Q
  -> exists R, (P ===> exists v, a |-> v * R v)%sep
               /\ forall r, a |-> r * R r ===> Q r.
Proof.
  induct 1; simp; eauto.

  exists R; simp.
  cancel; auto.
  cancel; auto.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  eauto 7 using himp_trans.

  exists (fun n => x n * R)%sep; simp.
  rewrite H1.
  cancel.

  rewrite <- H2.
  cancel.
Qed.

Lemma invert_Write : forall a v' P Q,
  hoare_triple P (Write a v') Q
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

Lemma invert_Alloc : forall numWords P Q,
  hoare_triple P (Alloc numWords) Q
  -> forall r, P * r |--> zeroes numWords ===> Q r.
Proof.
  induct 1; simp; eauto.

  apply unit_not_nat in x0; simp.

  cancel.

  apply unit_not_nat in x0; simp.

  rewrite H0.
  eauto using himp_trans.

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

Lemma invert_Free : forall a numWords P Q,
  hoare_triple P (Free a numWords) Q
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

Lemma HtReturn' : forall P {result : Set} (v : result) Q,
    P ===> Q v
    -> hoare_triple P (Return v) Q.
Proof.
  simp.
  eapply HtStrengthen.
  constructor.
  simp.
  cancel.
Qed.

(* Temporarily transparent again! *)
Transparent heq himp lift star exis ptsto.

Lemma preservation : forall {result} (c : cmd result) h c' h',
    step (h, c) (h', c')
    -> forall Q, hoare_triple (fun h' => h' = h) c Q
                 -> hoare_triple (fun h'' => h'' = h') c' Q.
Proof.
  induct 1; simplify.

  apply invert_Bind in H0; simp.
  eauto.

  apply invert_Bind in H; simp.
  specialize (invert_Return H); eauto using HtWeaken.

  apply invert_Loop in H; simp.
  econstructor.
  eapply HtWeaken.
  eauto.
  assumption.
  simp.
  cases r.
  apply HtReturn'.
  unfold himp; simp; eauto.
  eapply HtStrengthen.
  eauto.
  unfold himp; simp; eauto.

  apply invert_Read in H0; simp.
  apply HtReturn'.
  assert ((exists v, a |-> v * x v)%sep h') by auto.
  unfold exis, star in H1; simp.
  unfold ptsto in H4; subst.
  unfold split in H1; subst.
  unfold heap1 in H.
  rewrite lookup_join1 in H by (simp; sets).
  unfold himp; simp.
  invert H.
  apply H2.
  unfold star.
  exists (heap1 a v), x2; propositional.
  unfold split; reflexivity.
  unfold ptsto; reflexivity.

  apply invert_Write in H0; simp.
  apply HtReturn'.
  simp.
  assert (((exists v : nat, a |-> v) * x)%sep h) by auto.
  unfold star in H1; simp.
  invert H4.
  unfold ptsto in H5; subst.
  unfold split in H3; subst.
  unfold heap1 in H.
  rewrite lookup_join1 in H by (simp; sets).
  unfold himp; simp.
  invert H.
  apply H2.
  unfold star.
  exists ($0 $+ (a, v')), x1; propositional.
  unfold split.
  unfold heap1.
  maps_equal.
  rewrite lookup_join1 by (simp; sets).
  simp.
  repeat rewrite lookup_join2 by (simp; sets); reflexivity.
  unfold disjoint in *; simp.
  cases (a0 ==n a); simp.
  apply H1 with (a0 := a).
  unfold heap1; simp.
  equality.
  assumption.
  unfold ptsto; reflexivity.

  apply invert_Alloc with (r := a) in H0.
  apply HtReturn'.
  unfold himp; simp.
  eapply himp_trans in H0; try apply zeroes_initialize.
  auto.
  assumption.

  apply invert_Free in H.
  assert ((a |->? numWords * Q tt)%sep h) by auto.
  apply HtReturn'.
  unfold himp; simp.
  eapply do_deallocate.
  eauto.
Qed.

Lemma deallocate_None : forall a' numWords h a,
    h $? a' = None
    -> deallocate h a numWords $? a' = None.
Proof.
  induct numWords; simp.
  rewrite IHnumWords; simp.
  cases (a ==n a'); simp.
Qed.

Lemma preservation_finite : forall {result} (c : cmd result) h c' h' bound,
    step (h, c) (h', c')
    -> (forall a, a >= bound -> h $? a = None)
    -> exists bound', forall a, a >= bound' -> h' $? a = None.
Proof.
  induct 1; simplify; eauto.

  exists bound; simp.
  cases (a ==n a0); simp.
  rewrite H0 in H; equality.
  auto.

  exists (max bound (a + numWords)); simp.
  rewrite initialize_fresh; auto.

  exists bound; simp.
  eauto using deallocate_None.
Qed.

Hint Constructors step : core.

Lemma progress : forall {result} (c : cmd result) P Q,
    hoare_triple P c Q
    -> forall h h1 h2, split h h1 h2
                       -> disjoint h1 h2
                       -> P h1
                       -> (exists bound, forall a, a >= bound -> h $? a = None)
                       -> (exists r, c = Return r)
                          \/ (exists h' c', step (h, c) (h', c')).
Proof.
  induct 1; simp;
  repeat match goal with
           | [ H : forall _ h1 _, _ -> _ -> ?P h1 -> _, H' : ?P _ |- _ ] => eapply H in H'; clear H; try eassumption; simp
         end; eauto.

  invert H1.
  right; exists h, (Return x0).
  constructor.
  unfold split, ptsto, heap1 in *; simp.
  unfold star in H2; simp.
  unfold split in H; simp.
  rewrite lookup_join1; simp.
  rewrite lookup_join1; simp.
  sets.
  eapply lookup_Some_dom.
  rewrite lookup_join1; simp.
  sets.

  right; exists (h $+ (a, v')), (Return tt).
  unfold split, exis, ptsto, heap1 in *; simp.
  econstructor.
  rewrite lookup_join1; simp.
  sets.

  unfold lift in H1; simp.
  apply split_empty_fwd' in H; simp.
  right; exists (initialize h2 x numWords), (Return x).
  constructor.
  simp; auto.

  unfold star in H2; simp.
  apply IHhoare_triple with (h := h) (h1 := x0) (h2 := h2 $++ x1); eauto.
  unfold split in *; simp.
  rewrite (@join_comm _ _ h2 x1).
  apply join_assoc.
  sets.
  cases (h2 $? x2).
  cases (x1 $? x2).
  specialize (H2 x2).
  specialize (H1 x2).
  rewrite lookup_join2 in H1.
  apply H1; equality.
  unfold not.
  simplify.
  cases (x0 $? x2).
  exfalso; apply H2; equality.
  apply lookup_None_dom in Heq1; propositional.
  apply lookup_None_dom in Heq0; propositional.
  apply lookup_None_dom in Heq; propositional.

  unfold split, disjoint in *; simp.
  cases (h2 $? a).
  rewrite lookup_join1 in H8.
  apply H1 with (a := a); auto.
  rewrite lookup_join1; auto.
  cases (x0 $? a); try equality.
  eauto using lookup_Some_dom.
  eauto using lookup_Some_dom.
  rewrite lookup_join2 in H8.
  eapply H2; eassumption.
  eauto using lookup_None_dom.
Qed.

Lemma hoare_triple_sound' : forall P {result} (c : cmd result) Q,
    hoare_triple P c Q
    -> P $0
    -> invariantFor (trsys_of $0 c)
                    (fun p =>
                       (exists bound, forall a, a >= bound -> fst p $? a = None)
                       /\ hoare_triple (fun h' => h' = fst p)
                                       (snd p)
                                       Q).
Proof.
  simplify.

  apply invariant_induction; simplify.

  propositional; subst; simplify.
  exists 0; simp.
  eapply HtWeaken; eauto.
  unfold himp; simplify; equality.

  cases s.
  cases s'.
  simp.
  eauto using preservation_finite.
  eauto using preservation.
Qed.

Theorem hoare_triple_sound : forall P {result} (c : cmd result) Q,
    hoare_triple P c Q
    -> P $0
    -> invariantFor (trsys_of $0 c)
                    (fun p => (exists r, snd p = Return r)
                              \/ (exists p', step p p')).
Proof.
  simplify.

  eapply invariant_weaken.
  eapply hoare_triple_sound'; eauto.
  simp.
  specialize (progress H3); simplify.
  specialize (H2 (fst s) (fst s) $0).
  assert (split (fst s) (fst s) $0) by auto.
  assert (disjoint (fst s) $0) by auto.
  assert (exists bound, forall a, a >= bound -> fst s $? a = None) by eauto.
  cases s; simp; eauto.
Qed.

(* Fancy theorem to help us rewrite within preconditions and postconditions *)
Instance hoare_triple_morphism : forall A,
  Proper (heq ==> eq ==> (eq ==> heq) ==> iff) (@hoare_triple A).
Proof.
  Transparent himp.
  repeat (hnf; intros).
  unfold pointwise_relation in *; intuition subst.

  eapply HtConsequence; eauto.
  rewrite H; reflexivity.
  intros.
  hnf in H1.
  specialize (H1 r _ eq_refl).
  rewrite H1; reflexivity.

  eapply HtConsequence; eauto.
  rewrite H; reflexivity.
  intros.
  hnf in H1.
  specialize (H1 r _ eq_refl).
  rewrite H1; reflexivity.
  Opaque himp.
Qed.


(** * Examples *)

Opaque heq himp lift star exis ptsto.

(* Here comes some automation that we won't explain in detail, instead opting to
 * use examples. *)

Theorem use_lemma : forall result P' (c : cmd result) (Q : result -> hprop) P R,
  hoare_triple P' c Q
  -> P ===> P' * R
  -> hoare_triple P c (fun r => Q r * R)%sep.
Proof.
  simp.
  eapply HtWeaken.
  eapply HtFrame.
  eassumption.
  eauto.
Qed.

Theorem HtRead' : forall a v,
  hoare_triple (a |-> v)%sep (Read a) (fun r => a |-> v * [| r = v |])%sep.
Proof.
  simp.
  apply HtWeaken with (exists r, a |-> r * [| r = v |])%sep.
  eapply HtStrengthen.
  apply HtRead.
  simp.
  cancel; auto.
  subst; cancel.
  cancel; auto.
Qed.

Theorem HtRead'' : forall p P R,
  P ===> (exists v, p |-> v * R v)
  -> hoare_triple P (Read p) (fun r => p |-> r * R r)%sep.
Proof.
  simp.
  eapply HtWeaken.
  apply HtRead.
  assumption.
Qed.

Ltac basic := apply HtReturn' || eapply HtWrite || eapply HtAlloc || eapply HtFree.

Ltac step0 := basic || eapply HtBind || (eapply use_lemma; [ basic | cancel; auto ])
              || (eapply use_lemma; [ eapply HtRead' | solve [ cancel; auto ] ])
              || (eapply HtRead''; solve [ cancel ])
              || (eapply HtStrengthen; [ eapply use_lemma; [ basic | cancel; auto ] | ])
              || (eapply HtConsequence; [ apply HtFail | .. ]).
Ltac step := step0; simp.
Ltac ht := simp; repeat step.
Ltac conseq := simplify; eapply HtConsequence.
Ltac use_IH H := conseq; [ apply H | .. ]; ht.
Ltac loop_inv0 Inv := (eapply HtWeaken; [ apply HtLoop with (I := Inv) | .. ])
                      || (eapply HtConsequence; [ apply HtLoop with (I := Inv) | .. ]).
Ltac loop_inv Inv := loop_inv0 Inv; ht.
Ltac use H := (eapply use_lemma; [ eapply H | cancel; auto ])
              || (eapply HtStrengthen; [ eapply use_lemma; [ eapply H | cancel; auto ] | ]).

Ltac heq := intros; apply himp_heq; split.

(* That's the end of the largely unexplained automation.  Let's prove some
 * programs! *)


(** ** Swapping with two pointers *)

Definition swap p q :=
  tmpp <- Read p;
  tmpq <- Read q;
  _ <- Write p tmpq;
  Write q tmpp.

(* Looking at the precondition here, note how we no longer work with explicit
 * functions over heaps.  All that is hidden within the assertion language.
 * Also note that the definition of [*] gives us nonaliasing of [p] and [q] for
 * free! *)
Theorem swap_ok : forall p q a b,
  {{p |-> a * q |-> b}}
    swap p q
  {{_ ~> p |-> b * q |-> a}}.
Proof.
  unfold swap.
  (* [simp] is our generic simplifier for this file. *)
  simp.
  (* We generally just keep calling [step] to advance forward by one atomic
   * statement. *)
  step.
  step.
  (* We do often want to use [simp] to clean up the goal after [step] infers an
   * intermediate assertion. *)
  simp.
  step.
  step.
  simp.
  step.
  step.
  simp.
  step.
  (* The [cancel] procedure repeatedly finds matching subformulas on the two
   * sides of [===>], removing them and recurring, possibly learning the values
   * of some unification variables each time. *)
  cancel.
  subst.
  cancel.
Qed.

Opaque swap.
(* This command prevents later proofs from peeking inside the implementation of
 * [swap].  Instead, we only reason about it through [swap_ok]. *)

(* Two swaps in a row provide a kind of rotation across three addresses. *)
Definition rotate p q r :=
  _ <- swap p q;
  swap q r.

Theorem rotate_ok : forall p q r a b c,
  {{p |-> a * q |-> b * r |-> c}}
    rotate p q r
  {{_ ~> p |-> b * q |-> c * r |-> a}}.
Proof.
  unfold rotate.
  simp.
  step.
  (* Now we invoke our earlier theorem by name.  Note that its precondition only
   * matches a subset of our current precondition.  The rest of state is left
   * alone, which we can prove "for free" by the frame rule. *)
  use swap_ok.
  simp.
  use swap_ok.
  simp.
  cancel.
Qed.

Opaque rotate.

(** ** Initializing a fresh object *)

Definition init :=
  p <- Alloc 2;
  _ <- Write p 7;
  _ <- Write (p+1) 8;
  Return p.

Theorem init_ok :
  {{emp}}
    init
  {{p ~> p |--> [7; 8]}}.
Proof.
  unfold init.
  simp.
  step.
  step.
  simp.
  step.
  step.
  simp.
  step.
  step.
  simp.
  step.
  cancel.
Qed.

Opaque init.

Theorem the_circle_of_life_ok :
  {{emp}}
    p <- init;
    Free p 2
  {{_ ~> emp}}.
Proof.
  step.
  use init_ok.
  simp.
  step.
  cancel.
Qed.

Theorem ultra_combo_ok :
  {{emp}}
    p <- init;
    _ <- swap p (p+1);
    Return p
  {{p ~> p |--> [8; 7]}}.
Proof.
  step.
  use init_ok.
  simp.
  step.
  use swap_ok.
  simp.
  step.
  cancel.
Qed.

(** ** In-place reversal of a singly linked list *)

(* Let's give a recursive definition of how a linked list should be laid out in
 * memory. *)
Fixpoint linkedList (p : nat) (ls : list nat) :=
  match ls with
    | nil => [| p = 0 |]
      (* An empty list is associated with a null pointer and no memory
       * contents. *)
    | x :: ls' => [| p <> 0 |]
                  * exists p', p |--> [x; p'] * linkedList p' ls'
      (* A nonempty list is associated with a nonnull pointer and a two-cell
       * struct, which points to a further list. *)
  end%sep.

(* The definition of [linkedList] is recursive in the list.  Let's also prove
 * lemmas for simplifying [linkedList] invocations based on values of [p]. *)

Theorem linkedList_null : forall ls,
  linkedList 0 ls === [| ls = nil |].
Proof.
  (* Tactic [heq] breaks an equivalence into two implications. *)
  heq; cases ls; cancel.
Qed.

Theorem linkedList_nonnull : forall {p ls},
  p <> 0
  -> linkedList p ls === exists x ls' p', [| ls = x :: ls' |] * p |--> [x; p'] * linkedList p' ls'.
Proof.
  heq; cases ls; cancel; match goal with
                         | [ H : _ = _ :: _ |- _ ] => invert H
                         end; cancel.
Qed.

Hint Rewrite <- rev_alt.
Hint Rewrite rev_involutive.

(* Let's hide the definition of [linkedList], so that we *only* reason about it
 * via the two lemmas we just proved. *)
Opaque linkedList.

(* In-place linked-list reverse, the "hello world" of separation logic! *)
Definition reverse p :=
  pr <- for pr := (p, 0) loop
    let (p, r) := pr in
    if p ==n 0 then
      Return (Done pr)
    else
      tmp <- Read (p + 1);
      _ <- Write (p+1) r;
      Return (Again (tmp, p))
  done;
  Return (snd pr).

(* Helper function to peel away the [Done]/[Again] status of a [loop_outcome] *)
Definition valueOf {A} (o : loop_outcome A) :=
  match o with
  | Done v => v
  | Again v => v
  end.

Theorem reverse_ok : forall p ls,
  {{linkedList p ls}}
    reverse p
  {{r ~> linkedList r (rev ls)}}.
Proof.
  unfold reverse.
  simp.
  step.
  (* When we reach a loop, we give the invariant with a special tactic. *)
  loop_inv (fun o => exists ls1 ls2, [| ls = rev_append ls1 ls2 |]
                                     * linkedList (fst (valueOf o)) ls2
                                     * linkedList (snd (valueOf o)) ls1
                                     * [| match o with
                                          | Done (p, _) => p = 0
                                          | _ => True
                                          end |])%sep.
  cases (a ==n 0); simp.
  step.
  cancel.
  step.
  (* We use [setoid_rewrite] for rewriting under binders ([exists], in this
   * case).  Note that we also specify hypothesis [n] explicitly, since
   * [setoid_rewrite] isn't smart enough to infer parameters otherwise. *)
  setoid_rewrite (linkedList_nonnull n).
  step.
  simp.
  step.
  step.
  simp.
  step.
  setoid_rewrite (linkedList_nonnull n).
  cancel.
  simp.
  setoid_rewrite linkedList_null.
  cancel.
  equality.
  simp.
  step.
  cancel.
  simp.
  setoid_rewrite linkedList_null.
  cancel.
  simp.
  cancel.
Qed.

Opaque reverse.

(* ** Calling [reverse] twice, to illustrate the *frame rule* *)

Theorem reverse_two_ok : forall p1 ls1 p2 ls2,
  {{linkedList p1 ls1 * linkedList p2 ls2}}
    p1 <- reverse p1;
    p2 <- reverse p2;
    Return (p1, p2)
  {{ps ~> linkedList (fst ps) (rev ls1) * linkedList (snd ps) (rev ls2)}}.
Proof.
  simp.
  step.
  use reverse_ok.
  simp.
  step.
  use reverse_ok.
  simp.
  step.
  cancel.
Qed.
(* Note that the intuitive correctness theorem would be *false* for lists
 * sharing any cells in common!  The inherent disjointness of [*] saves us from
 * worrying about those cases. *)


(* ** Computing the length of a linked list *)

(* To state a good loop invariant, it will be helpful to define
 * *list segments* that end with some pointer beside null. *)
Fixpoint linkedListSegment (p : nat) (ls : list nat) (q : nat) :=
  match ls with
    | nil => [| p = q |]
    | x :: ls' => [| p <> 0 |] * exists p', p |--> [x; p'] * linkedListSegment p' ls' q
  end%sep.

(* Next, two [linkedListSegment] lemmas analogous to those for [linkedList]
 * above *)

Lemma linkedListSegment_empty : forall p ls,
  linkedList p ls ===> linkedList p ls * linkedListSegment p nil p.
Proof.
  cancel.
Qed.

Lemma linkedListSegment_append : forall q r x ls p,
  q <> 0
  -> linkedListSegment p ls q * q |--> [x; r] ===> linkedListSegment p (ls ++ x :: nil) r.
Proof.
  induct ls; cancel; auto.
  subst; cancel.
  rewrite <- IHls; cancel; auto.
Qed.

(* One more [linkedList] lemma will be helpful.  We'll re-reveal the predicate's
 * definition to prove the lemma. *)

Transparent linkedList.

Lemma linkedListSegment_null : forall ls p,
  linkedListSegment p ls 0 ===> linkedList p ls.
Proof.
  induct ls; cancel; auto.
Qed.

Opaque linkedList linkedListSegment.

(* A few algebraic properties of list operations: *)
Hint Rewrite <- app_assoc.
Hint Rewrite app_length app_nil_r.

(* We tie a few of them together into this lemma. *)
Lemma move_along : forall A (ls : list A) x2 x1 x0 x,
  ls = x2 ++ x1
  -> x1 = x0 :: x
  -> ls = (x2 ++ [x0]) ++ x.
Proof.
  simp.
Qed.

Hint Resolve move_along : core.

Theorem length_ok : forall p ls,
  {{linkedList p ls}}
    q_len <- for q_len := (p, 0) loop
      let (q, len) := q_len in
      if q ==n 0 then
        Return (Done q_len)
      else
        tmp <- Read (q + 1);
        Return (Again (tmp, len+1))
    done;
    Return (snd q_len)
  {{len ~> linkedList p ls * [| len = length ls |]}}.
Proof.
  simp.
  step.
  loop_inv (fun o => exists ls1 ls2, [| ls = ls1 ++ ls2 |]
                                     * linkedListSegment p ls1 (fst (valueOf o))
                                     * linkedList (fst (valueOf o)) ls2
                                     * [| snd (valueOf o) = length ls1 |]
                                     * [| match o with
                                          | Done (q, _) => q = 0 /\ ls2 = nil
                                          | _ => True
                                          end |])%sep.
  cases (a ==n 0); simp.
  step.
  setoid_rewrite linkedList_null.
  cancel.
  simp.
  step.
  setoid_rewrite (linkedList_nonnull n).
  step.
  simp.
  step.
  cancel.
  simp.
  setoid_rewrite <- linkedListSegment_append.
  cancel.
  auto.
  simp.
  simp.
  rewrite linkedListSegment_empty.
  cancel.
  simp.
  step.
  cancel.
  simp.
  rewrite linkedListSegment_null.
  rewrite linkedList_null.
  cancel.
  simp.
Qed.
