(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 12: Separation Logic
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap Setoid Classes.Morphisms.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Shared notations and definitions; main material starts afterward. *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Definition heap := fmap nat nat.
Definition assertion := heap -> Prop.

Hint Extern 1 (_ <= _) => linear_arithmetic.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try linear_arithmetic.


(** * Encore of last mixed-embedding language from last time *)

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
  | S numWords' => deallocate (h $- (base + numWords')) base numWords'
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


(* CODE TO BE MOVED TO A LIBRARY MODULE SOON *)
Module Type SEP.
  Parameter hprop : Type.
  Parameter lift : Prop -> hprop.
  Parameter star : hprop -> hprop -> hprop.
  Parameter exis : forall A, (A -> hprop) -> hprop.

  Notation "[| P |]" := (lift P).
  Infix "*" := star.
  Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)).

  Parameters himp heq : hprop -> hprop -> Prop.

  Infix "===" := heq (no associativity, at level 70).
  Infix "===>" := himp (no associativity, at level 70).

  Axiom himp_heq : forall p q, p === q
                               <-> (p ===> q /\ q ===> p).
  Axiom himp_refl : forall p, p ===> p.
  Axiom himp_trans : forall p q r, p ===> q -> q ===> r -> p ===> r.

  Axiom lift_left : forall p (Q : Prop) r,
    (Q -> p ===> r)
    -> p * [| Q |] ===> r.
  Axiom lift_right : forall p q (R : Prop),
    R
    -> p ===> q
    -> p ===> q * [| R |].
  Axiom extra_lift : forall (P : Prop) p,
    P
    -> p === [| P |] * p.

  Axiom star_comm : forall p q, p * q === q * p.
  Axiom star_assoc : forall p q r, p * (q * r) === (p * q) * r.
  Axiom star_cancel : forall p1 p2 q1 q2, p1 ===> p2
    -> q1 ===> q2
    -> p1 * q1 ===> p2 * q2.

  Axiom exis_gulp : forall A p (q : A -> _),
    p * exis q === exis (fun x => p * q x).
  Axiom exis_left : forall A (p : A -> _) q,
    (forall x, p x ===> q)
    -> exis p ===> q.
  Axiom exis_right : forall A p (q : A -> _) x,
    p ===> q x
    -> p ===> exis q.
End SEP.

Module Sep(Import S : SEP).
  Add Parametric Relation : hprop himp
    reflexivity proved by himp_refl
    transitivity proved by himp_trans
    as himp_rel.

  Lemma heq_refl : forall p, p === p.
  Proof.
    intros; apply himp_heq; intuition (apply himp_refl).
  Qed.

  Lemma heq_sym : forall p q, p === q -> q === p.
  Proof.
    intros; apply himp_heq; apply himp_heq in H; intuition.
  Qed.

  Lemma heq_trans : forall p q r, p === q -> q === r -> p === r.
  Proof.
    intros; apply himp_heq; apply himp_heq in H; apply himp_heq in H0;
    intuition (eauto using himp_trans).
  Qed.

  Add Parametric Relation : hprop heq
    reflexivity proved by heq_refl
    symmetry proved by heq_sym
    transitivity proved by heq_trans
    as heq_rel.

  Instance himp_heq_mor : Proper (heq ==> heq ==> iff) himp.
  Proof.
    hnf; intros; hnf; intros.
    apply himp_heq in H; apply himp_heq in H0.
    intuition eauto using himp_trans.
  Qed.

  Add Parametric Morphism : star
  with signature heq ==> heq ==> heq
  as star_mor.
  Proof.
    intros; apply himp_heq; apply himp_heq in H; apply himp_heq in H0;
    intuition (auto using star_cancel).
  Qed.

  Add Parametric Morphism : star
  with signature himp ==> himp ==> himp
  as star_mor'.
  Proof.
    auto using star_cancel.
  Qed.

  Instance exis_iff_morphism (A : Type) :
    Proper (pointwise_relation A heq ==> heq) (@exis A).
  Proof.
    hnf; intros; apply himp_heq; intuition.
    hnf in H.
    apply exis_left; intro.
    eapply exis_right.
    assert (x x0 === y x0) by eauto.
    apply himp_heq in H0; intuition eauto.
    hnf in H.
    apply exis_left; intro.
    eapply exis_right.
    assert (x x0 === y x0) by eauto.
    apply himp_heq in H0; intuition eauto.
  Qed.

  Lemma star_comm_lift : forall P q, [| P |] * q === q * [| P |].
  Proof.
    intros; apply star_comm.
  Qed.

  Lemma star_assoc_lift : forall p Q r,
    (p * [| Q |]) * r === p * r * [| Q |].
  Proof.
    intros.
    rewrite <- star_assoc.
    rewrite (star_comm [| Q |]).
    apply star_assoc.
  Qed.

  Lemma star_comm_exis : forall A (p : A -> _) q, exis p * q === q * exis p.
  Proof.
    intros; apply star_comm.
  Qed.

  Ltac lift :=
    intros; apply himp_heq; split;
    repeat (apply lift_left; intro);
    repeat (apply lift_right; intuition).

  Lemma lift_combine : forall p Q R,
    p * [| Q |] * [| R |] === p * [| Q /\ R |].
  Proof.
    intros; apply himp_heq; split;
    repeat (apply lift_left; intro);
    repeat (apply lift_right; intuition).
  Qed.

  Lemma lift1_left : forall (P : Prop) q,
    (P -> [| True |] ===> q)
    -> [| P |] ===> q.
  Proof.
    intros.
    rewrite (@extra_lift True [| P |]); auto.
    apply lift_left; auto.
  Qed.

  Lemma lift1_right : forall p (Q : Prop),
    Q
    -> p ===> [| True |]
    -> p ===> [| Q |].
  Proof.
    intros.
    rewrite (@extra_lift True [| Q |]); auto.
    apply lift_right; auto.
  Qed.

  Ltac normalize0 :=
    setoid_rewrite exis_gulp
    || setoid_rewrite lift_combine
    || setoid_rewrite star_assoc
    || setoid_rewrite star_comm_lift
    || setoid_rewrite star_assoc_lift
    || setoid_rewrite star_comm_exis.

  Ltac normalizeL :=
    (apply exis_left || apply lift_left; intro; try congruence)
    || match goal with
         | [ |- [?P] ===> _ ] =>
           match P with
             | True => fail 1
             | _ => apply lift1_left; intro; try congruence
           end
       end.

  Ltac normalizeR :=
    eapply exis_right || apply lift_right
    || match goal with
         | [ |- _ ===> [?Q] ] =>
           match Q with
             | True => fail 1
             | _ => apply lift1_right
           end
       end.

  Ltac normalize1 := normalize0 || normalizeL || normalizeR.

  Lemma lift_uncombine : forall p P Q,
    p * [| P /\ Q |] === p * [| P |] * [| Q |].
  Proof.
    lift.
  Qed.
  
  Ltac normalize2 := setoid_rewrite lift_uncombine
    || setoid_rewrite star_assoc.

  Ltac normalizeLeft :=
    let s := fresh "s" in intro s;
    let rhs := fresh "rhs" in
    match goal with
      | [ |- _ ===> ?Q ] => set (rhs := Q)
    end;
    simpl; intros; repeat (normalize0 || normalizeL);
    repeat match goal with
             | [ H : ex _ |- _ ===> _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : _ = _ |- _ ] => rewrite H
           end; subst; subst rhs.
                                                      
  Ltac normalize :=
    simpl; intros; repeat normalize1; repeat normalize2;
    repeat (match goal with
              | [ H : ex _ |- _ ===> _ ] => destruct H
            end; intuition subst); subst.

  Ltac forAllAtoms p k :=
    match p with
      | ?q * ?r => (forAllAtoms q k || forAllAtoms r k) || fail 2
      | _ => k p
    end.

  Lemma stb1 : forall p q r,
    (q * p) * r === q * r * p.
  Proof.
    intros; rewrite <- star_assoc; rewrite (star_comm p r); apply star_assoc.
  Qed.

  Ltac sendToBack part :=
    repeat match goal with
             | [ |- context[(?p * part) * ?q] ] => setoid_rewrite (stb1 part p q)
             | [ |- context[part * ?p] ] => setoid_rewrite (star_comm part p)
           end.

  Theorem star_cancel' : forall p1 p2 q, p1 ===> p2
    -> p1 * q ===> p2 * q.
  Proof.
    intros; apply star_cancel; auto using himp_refl.
  Qed.

  Ltac cancel1 :=
    match goal with
      | _ => apply himp_refl
      | _ => apply star_cancel'
      | [ |- ?p ===> ?q ] =>
        forAllAtoms p ltac:(fun p0 =>
          sendToBack p0;
          forAllAtoms q ltac:(fun q0 =>
            sendToBack q0;
            apply star_cancel'))
      | _ => progress autorewrite with core
    end.

  Ltac cancel := normalize; repeat cancel1;
                 try match goal with
                       | [ |- _ ===> _ ] => intuition (try congruence)
                     end.
End Sep.


(* Now we instantiate the generic signature of separation-logic assertions and
 * connectives. *)
Module Import S <: SEP.
  Definition hprop := heap -> Prop.

  (* Implication *)
  Definition himp (p q : hprop) := forall h, p h -> q h.

  (* Equivalence *)
  Definition heq (p q : hprop) := forall h, p h <-> q h.

  (* Lifting a pure proposition *)
  Definition lift (P : Prop) : hprop :=
    fun h => P /\ h = $0.

  (* Separating conjunction, one of the two big ideas of separation logic *)
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

  (* And now we prove some key algebraic properties.  I'll skip explaining the
   * details. *)

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

  Theorem emp_heap : forall h, lift True h -> h = $0.
  Proof.
    t.
  Qed.
End S.

Export S.
(* Instantiate our big automation engine to these definitions. *)
Module Import Se := Sep(S).
Export Se.


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


(** * Finally, the Hoare logic *)

Inductive hoare_triple : assertion -> forall {result}, cmd result -> (result -> assertion) -> Prop :=
(* First, four basic rules that look exactly the same as before *)
| HtReturn : forall P {result : Set} (v : result),
    hoare_triple P (Return v) (fun r h => P h /\ r = v)
| HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
    hoare_triple P c1 Q
    -> (forall r, hoare_triple (Q r) (c2 r) R)
    -> hoare_triple P (Bind c1 c2) R
| HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I,
    (forall acc, hoare_triple (I (Again acc)) (body acc) I)
    -> hoare_triple (I (Again init)) (Loop init body) (fun r h => I (Done r) h)
| HtFail : forall {result},
    hoare_triple (fun _ => False) (Fail (result := result)) (fun _ _ => False)

| HtRead : forall a v,
    hoare_triple (a |-> v)%sep (Read a) (fun r => a |-> v * [| r = v |])%sep
| HtWrite : forall a v',
    hoare_triple (exists v, a |-> v)%sep (Write a v') (fun _ => a |-> v')%sep
| HtAlloc : forall numWords,
    hoare_triple emp%sep (Alloc numWords) (fun r => r |--> zeroes numWords)%sep
| HtFree : forall a numWords,
    hoare_triple (exists vs, a |--> vs * [| length vs = numWords |])%sep (Free a numWords) (fun _ => emp)%sep

| HtConsequence : forall {result} (c : cmd result) P Q (P' : assertion) (Q' : _ -> assertion),
    hoare_triple P c Q
    -> P' ===> P
    -> (forall r, Q r ===> Q' r)
    -> hoare_triple P' c Q'
| HtFrame : forall {result} (c : cmd result) P Q R,
    hoare_triple P c Q
    -> hoare_triple (P * R)%sep c (fun r => Q r * R)%sep.

Notation "{{ P }} c {{ r ~> Q }}" :=
  (hoare_triple P%sep c (fun r => Q%sep)) (at level 90, c at next level).

Lemma HtStrengthen : forall {result} (c : cmd result) P Q (Q' : _ -> assertion),
    hoare_triple P c Q
    -> (forall r h, Q r h -> Q' r h)
    -> hoare_triple P c Q'.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

Lemma HtWeaken : forall {result} (c : cmd result) P Q (P' : assertion),
    hoare_triple P c Q
    -> (forall h, P' h -> P h)
    -> hoare_triple P' c Q.
Proof.
  simplify.
  eapply HtConsequence; eauto.
  reflexivity.
Qed.

Lemma invert_Return : forall {result : Set} (r : result) P Q,
  hoare_triple P (Return r) Q
  -> forall h, P h -> Q r h.
Proof.
  induct 1; propositional; eauto.

  unfold himp in *; eauto.

  unfold star, himp in *; simp; eauto 7.
Qed.

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

Hint Constructors hoare_triple.

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
  -> exists v R, (P ===> a |-> v * R)%sep
               /\ a |-> v * R ===> Q v.
Proof.
  induct 1; simp; eauto.

  exists v, emp; simp.
  cancel; auto.
  cancel; auto.

  apply unit_not_nat in x0; simp.

  apply unit_not_nat in x0; simp.

  eauto 7 using himp_trans.

  exists x, (x0 * R)%sep; simp.
  cancel.

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
  -> P ===> (exists vs, a |--> vs * [| length vs = numWords |]) * Q tt.
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

Lemma grab_last' : forall n2 n1 a,
    (exists vs, a |--> vs * [|length vs = n1 + n2|])
     ===> (exists vs, a |--> vs * [| length vs = n1 |])
    * (exists vs, (a + n1) |--> vs * [| length vs = n2 |]).
Proof.
  induct n1; simp.

  cancel.
  instantiate (1 := nil); simp.
  replace (a + 0) with a by linear_arithmetic.
  cancel; auto.

  apply himp_trans with ((exists v, a |-> v)
                         * (exists vs : list nat,
                               (a+1) |--> vs * [|length vs = n1 + n2|]))%sep.
  cancel.
  instantiate (1 := tl x).
  cases x; simp.
  instantiate (1 := hd 0 x).
  cases x; simp.
  cancel.

  rewrite IHn1.
  clear IHn1.
  replace (a + S n1) with (a + 1 + n1) by linear_arithmetic.
  cancel.
  instantiate (1 := x1 :: x0); simp.
  cancel.
Qed.  

Lemma grab_last : forall n a,
    (exists vs, a |--> vs * [|length vs = S n|])
    ===> (exists vs, a |--> vs * [|length vs = n|])
    * (exists v, (a + n) |-> v).
Proof.
  simplify.
  replace (S n) with (n + 1) by linear_arithmetic.
  rewrite grab_last'.
  cancel; auto.
  instantiate (1 := hd 0 x).
  cases x; simp.
  cases x; simp.
  cancel.
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

Lemma do_deallocate : forall Q a numWords h,
    ((exists vs, a |--> vs * [|length vs = numWords|]) * Q)%sep h
    -> Q (deallocate h a numWords).
Proof.
  induct numWords; simp.

  unfold star, exis, lift in H; simp.
  cases x1; simp.
  unfold emp in *; simp.
  replace h with x0.
  equality.
  apply split_empty_fwd in H1; simp.
  apply split_empty_fwd' in H0; equality.

  apply IHnumWords.
  clear IHnumWords.
  Opaque heq himp lift star exis ptsto.
  assert ((exists vs : list nat,
              a |--> vs * [|Datatypes.length vs = S numWords|]) * Q
          ===> (exists vs, a |--> vs * [|length vs = numWords|])
          * (exists v, (a + numWords) |-> v) * Q) by (rewrite grab_last; cancel; auto).
  apply H0 in H; clear H0.
  assert ((exists vs, a |--> vs * [|length vs = numWords|])
          * (exists v : nat, (a + numWords) |-> v) * Q
          ===> (exists v : nat, (a + numWords) |-> v) *
          ((exists vs, a |--> vs * [|length vs = numWords|]) * Q)) by (cancel; auto).
  apply H0 in H; clear H0.
  apply do_deallocate'.
  assumption.
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
  eapply HtStrengthen.
  eauto.
  simp; eauto.
  eapply HtStrengthen.
  eauto.
  simp; eauto.

  apply invert_Read in H0; simp.
  eapply HtStrengthen.
  econstructor.
  simp.
  assert ((a |-> x * x0)%sep h') by auto.
  unfold star in H0; simp.
  unfold ptsto in H4; subst.
  unfold split in H3; subst.
  unfold heap1 in H.
  rewrite lookup_join1 in H by (simp; sets).
  simp.
  invert H.
  apply H2.
  unfold star.
  exists (heap1 a v), x2; propositional.
  unfold split; reflexivity.
  unfold ptsto; reflexivity.

  apply invert_Write in H0; simp.
  eapply HtStrengthen.
  econstructor.
  simp.
  assert (((exists v : nat, a |-> v) * x)%sep h) by auto.
  unfold star in H1; simp.
  invert H4.
  unfold ptsto in H5; subst.
  unfold split in H3; subst.
  unfold heap1 in H.
  rewrite lookup_join1 in H by (simp; sets).
  simp.
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
  eapply HtStrengthen.
  econstructor.
  simp.
  eapply himp_trans in H0; try apply zeroes_initialize.
  auto.
  assumption.

  apply invert_Free in H.
  assert (((exists vs : list nat, a |--> vs * [|Datatypes.length vs = numWords|]) * Q tt)%sep h) by auto.
  eapply HtStrengthen.
  econstructor.
  simp.
  eapply do_deallocate.
  eauto.
Qed.

Lemma deallocate_None : forall a' numWords h a,
    h $? a' = None
    -> deallocate h a numWords $? a' = None.
Proof.
  induct numWords; simp.
  rewrite IHnumWords; simp.
  cases (a + numWords ==n a'); simp.
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

Hint Constructors step.

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

  right; exists h, (Return v).
  constructor.
  unfold split, ptsto, heap1 in *; simp.
  rewrite lookup_join1; simp.
  sets.

  right; exists (h $+ (a, v')), (Return tt).
  unfold split, exis, ptsto, heap1 in *; simp.
  econstructor.
  rewrite lookup_join1; simp.
  sets.

  unfold emp in H1; simp.
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
  rewrite lookup_join2 in H8; eauto.
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
