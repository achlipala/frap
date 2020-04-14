(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 15: Connecting to Real-World Programming Languages and Platforms
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap SepCancel ModelCheck Classes.Morphisms.
Require Import Arith.Div2 Eqdep.

(** * Some odds and ends from past chapters *)

Ltac simp := repeat (simplify; subst; propositional;
                     try match goal with
                         | [ H : ex _ |- _ ] => invert H
                         end); try linear_arithmetic.


(** * Orientation *)

(* We've now done plenty of Coq proofs that apply to idealizations of real-world
 * programming languages.  What happens when we want to connect to real
 * development ecosystems?  The corresponding book chapter works through several
 * dimensions of variation across approaches.  The whole subject is an active
 * area of research, and there aren't standard solutions that everyone agrees
 * on.  The rest of this code file develops one avant-garde approach. *)


(** * Bitvectors of known length *)

(* One way we can increase realism is ditching the natural numbers for
 * bitvectors of fixed size, as we find in, e.g., registers of most computer
 * processors.  A simple dependent type definition gets the job done. *)

Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall {n}, word n -> word (S n).

(* The index of a [word] tells us how many bits it takes up. *)

(* Next come a set of operation definitions, whose details we will gloss
 * over. *)

Fixpoint wordToNat {sz} (w : word sz) : nat :=
  match w with
    | WO => O
    | WS false w => 2 * wordToNat w
    | WS true w => S (2 * wordToNat w)
  end.

Fixpoint mod2 (n : nat) : bool :=
  match n with
    | 0 => false
    | 1 => true
    | S (S n') => mod2 n'
  end.

Fixpoint natToWord (sz n : nat) : word sz :=
  match sz with
    | O => WO
    | S sz' => WS (mod2 n) (natToWord sz' (div2 n))
  end.

Definition wzero {sz} := natToWord sz 0.
Definition wone {sz} := natToWord sz 1.
Notation "^" := (natToWord _) (at level 0).
(* Note this notation that we do use later, for "casting" a natural number into
 * a word.  (We might "lose" bits if the input number is too large!) *)

Definition wplus {sz} (w1 w2 : word sz) : word sz :=
  natToWord sz (wordToNat w1 + wordToNat w2).

Infix "^+" := wplus (at level 50, left associativity).
(* And we will also use this notation in the main development, as a binary
 * addition operator.  The remaining definitions are safe to gloss over. *)

Definition whd {sz} (w : word (S sz)) : bool :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S _ => bool
                             end with
    | WO => tt
    | WS b _ => b
  end.

Definition wtl {sz} (w : word (S sz)) : word sz :=
  match w in word sz' return match sz' with
                               | O => unit
                               | S sz'' => word sz''
                             end with
    | WO => tt
    | WS _ w' => w'
  end.

Lemma shatter_word : forall {n} (a : word n),
  match n return word n -> Prop with
    | O => fun a => a = WO
    | S _ => fun a => a = WS (whd a) (wtl a)
  end a.
Proof.
  destruct a; eauto.
Qed.

Lemma shatter_word_S : forall {n} (a : word (S n)),
  exists b, exists c, a = WS b c.
Proof.
  intros; repeat eexists; apply (shatter_word a).
Qed.
Lemma shatter_word_0 : forall a : word 0,
  a = WO.
Proof.
  intros; apply (shatter_word a).
Qed.

Hint Resolve shatter_word_0 : core.

Require Import Coq.Logic.Eqdep_dec.

Definition weq : forall {sz} (x y : word sz), sumbool (x = y) (x <> y).
  refine (fix weq sz (x : word sz) : forall y : word sz, sumbool (x = y) (x <> y) :=
    match x in word sz return forall y : word sz, sumbool (x = y) (x <> y) with
      | WO => fun _ => left _ _
      | WS b x' => fun y => if bool_dec b (whd y)
        then if weq _ x' (wtl y) then left _ _ else right _ _
        else right _ _
    end); clear weq.

  symmetry; apply shatter_word_0.

  subst; symmetry; apply (shatter_word y).

  rewrite (shatter_word y); simpl; intro; injection H; intros;
    apply n0; apply inj_pair2_eq_dec in H0; [ auto | apply eq_nat_dec ].

  abstract (rewrite (shatter_word y); simpl; intro; apply n0; injection H; auto).
Defined.

Lemma mod2_2times : forall n,
    mod2 (2 * n) = false.
Proof.
  induct n; simplify; auto.
  replace (n + S (n + 0)) with (S (2 * n)) by linear_arithmetic.
  assumption.
Qed.

Lemma mod2_plus1_2times : forall n,
    mod2 (1 + 2 * n) = true.
Proof.
  induct n; simplify; auto.
  replace (n + S (n + 0)) with (S (2 * n)) by linear_arithmetic.
  assumption.
Qed.

Theorem adding_one_changes : forall sz (w : word sz),
    sz > 0
    -> w ^+ ^1 <> w.
Proof.
  propositional.
  cases sz; try linear_arithmetic.
  pose proof (shatter_word_S w); first_order; subst.
  unfold wplus in H0.
  simplify.
  invert H0.
  clear H3.
  cases x.
  replace (S (wordToNat x0 + (wordToNat x0 + 0)) + S (wordToNat (^ 0) + (wordToNat (^ 0) + 0)))
          with (2 * (1 + wordToNat x0 + @wordToNat sz (^0))) in H2 by linear_arithmetic.
  rewrite mod2_2times in H2; equality.
  replace (wordToNat x0 + (wordToNat x0 + 0) + S (wordToNat (^ 0) + (wordToNat (^ 0) + 0)))
          with (1 + 2 * (wordToNat x0 + @wordToNat sz (^0))) in H2 by linear_arithmetic.
  rewrite mod2_plus1_2times in H2.
  equality.
Qed.

(* Oh, but pay attention to this one: much of our development will be
 * paramterized over what word size to consider.  Any module implementing this
 * type explains one particular choice. *)
Module Type BIT_WIDTH.
  Parameter bit_width : nat.
  Axiom bit_width_nonzero : bit_width > 0.
End BIT_WIDTH.


(** * A modification of last chapter's language, to use words instead of naturals *)

(* There actually isn't much to say about this language and its separation
 * logic.  We are almost just copying and pasting word operations for [nat]
 * operations.  Also, we drop failure and dynamic memory allocation, since they
 * would just distract from the main point. *)

Module MixedEmbedded(Import BW : BIT_WIDTH).
  Definition wrd := word bit_width.
  Definition heap := fmap wrd wrd.

  Ltac simp := repeat (simplify; subst; propositional;
                       try match goal with
                           | [ H : ex _ |- _ ] => invert H
                           end).


  Inductive loop_outcome {acc} :=
  | Done (a : acc)
  | Again (a : acc).

  Arguments loop_outcome : clear implicits.

  Inductive cmd : Set -> Type :=
  | Return {result : Set} (r : result) : cmd result
  | Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
  | Read (a : wrd) : cmd wrd
  | Write (a v : wrd) : cmd unit
  | Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc.

  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).
  Notation "'for' x := i 'loop' c1 'done'" := (Loop i (fun x => c1)) (right associativity, at level 80).

  Inductive step : forall {A}, heap * cmd A -> heap * cmd A -> Prop :=
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
    -> step (h, Write a v') (h $+ (a, v'), Return tt).


  Definition trsys_of (h : heap) {result} (c : cmd result) := {|
    Initial := {(h, c)};
    Step := step (A := result)
  |}.

  Definition multistep_trsys_of (h : heap) {result} (c : cmd result) := {|
    Initial := {(h, c)};
    Step := (step (A := result))^*
  |}.

  Module Import S <: SEP.
    Definition hprop := heap -> Prop.

    Definition himp (p q : hprop) := forall h, p h -> q h.

    Definition heq (p q : hprop) := forall h, p h <-> q h.

    Definition lift (P : Prop) : hprop :=
      fun h => P /\ h = $0.

    Definition star (p q : hprop) : hprop :=
      fun h => exists h1 h2, split h h1 h2 /\ disjoint h1 h2 /\ p h1 /\ q h2.

    Definition exis {A} (p : A -> hprop) : hprop :=
      fun h => exists x, p x h.

    Notation "[| P |]" := (lift P) : sep_scope.
    Infix "*" := star : sep_scope.
    Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
    Delimit Scope sep_scope with sep.
    Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
    Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).

    Local Open Scope sep_scope.

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
  Module Import Se := SepCancel.Make(S).
  Export Se.


  (* ** Predicates *)

  Definition heap1 (a v : wrd) : heap := $0 $+ (a, v).
  Definition ptsto (a v : wrd) : hprop :=
    fun h => h = heap1 a v.

  Notation "[| P |]" := (lift P) : sep_scope.
  Notation emp := (lift True).
  Infix "*" := star : sep_scope.
  Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : sep_scope.
  Delimit Scope sep_scope with sep.
  Notation "p === q" := (heq p%sep q%sep) (no associativity, at level 70).
  Notation "p ===> q" := (himp p%sep q%sep) (no associativity, at level 70).
  Infix "|->" := ptsto (at level 30) : sep_scope.

  Fixpoint multi_ptsto (a : wrd) (vs : list wrd) : hprop :=
    match vs with
    | nil => emp
    | v :: vs' => a |-> v * multi_ptsto (a ^+ ^1) vs'
    end%sep.

  Infix "|-->" := multi_ptsto (at level 30) : sep_scope.


  (** * Finally, the Hoare logic *)

  Inductive hoare_triple : forall {result}, hprop -> cmd result -> (result -> hprop) -> Prop :=
  | HtReturn : forall P {result : Set} (v : result),
      hoare_triple P (Return v) (fun r => P * [| r = v |])%sep
  | HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
      hoare_triple P c1 Q
      -> (forall r, hoare_triple (Q r) (c2 r) R)
      -> hoare_triple P (Bind c1 c2) R
  | HtLoop : forall {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) I,
      (forall acc, hoare_triple (I (Again acc)) (body acc) I)
      -> hoare_triple (I (Again init)) (Loop init body) (fun r => I (Done r))

  | HtRead : forall a R,
      hoare_triple (exists v, a |-> v * R v)%sep (Read a) (fun r => a |-> r * R r)%sep
  | HtWrite : forall a v',
      hoare_triple (exists v, a |-> v)%sep (Write a v') (fun _ => a |-> v')%sep

  | HtConsequence : forall {result} (c : cmd result) P Q (P' : hprop) (Q' : _ -> hprop),
      hoare_triple P c Q
      -> P' ===> P
      -> (forall r, Q r ===> Q' r)
      -> hoare_triple P' c Q'

  | HtFrame : forall {result} (c : cmd result) P Q R,
      hoare_triple P c Q
      -> hoare_triple (P * R)%sep c (fun r => Q r * R)%sep.


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

  (* Now that we proved enough basic facts, let's hide the definitions of all
   * these predicates, so that we reason about them only through automation. *)
  Opaque heq himp lift star exis ptsto.

  Lemma unit_not_wrd : unit = wrd -> False.
  Proof.
    simplify.
    assert (exists x : unit, forall y : unit, x = y).
    exists tt; simplify.
    cases y; reflexivity.
    rewrite H in H0.
    invert H0.
    specialize (H1 (x ^+ ^1)).
    eapply adding_one_changes.
    apply bit_width_nonzero.
    symmetry; eassumption.
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

    apply unit_not_wrd in x0; simp.

    specialize (IHhoare_triple _ _ eq_refl JMeq.JMeq_refl JMeq.JMeq_refl); first_order.
    exists x.
    propositional.
    etransitivity; eauto.
    etransitivity; eauto.

    specialize (IHhoare_triple _ _ eq_refl JMeq.JMeq_refl JMeq.JMeq_refl); first_order.
    exists (fun n => x n * R)%sep; simp.
    rewrite H0.
    cancel.

    rewrite <- H1.
    cancel.
  Qed.

  Lemma invert_Write : forall a v' P Q,
    hoare_triple P (Write a v') Q
    -> exists R, (P ===> (exists v, a |-> v) * R)%sep
                 /\ a |-> v' * R ===> Q tt.
  Proof.
    induct 1; simp; eauto.

    symmetry in x0.
    apply unit_not_wrd in x0; simp.

    exists emp; simp.
    cancel; auto.
    cancel; auto.

    eexists; split.
    etransitivity; eauto.
    etransitivity; eauto.

    exists (x * R)%sep; simp.
    rewrite H1.
    cancel.

    cancel.
    rewrite <- H2.
    cancel.
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
    specialize (invert_Return _ _ _ H); eauto using HtWeaken.

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
    assert (((exists v : wrd, a |-> v) * x)%sep h) by auto.
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
    cases (weq a0 a); simp.
    apply H1 with (a0 := a).
    unfold heap1; simp.
    equality.
    assumption.
    unfold ptsto; reflexivity.
  Qed.

  Hint Constructors step : core.

  Lemma progress : forall {result} (c : cmd result) P Q,
      hoare_triple P c Q
      -> forall h h1 h2, split h h1 h2
                         -> disjoint h1 h2
                         -> P h1
                         -> (exists r, c = Return r)
                            \/ (exists h' c', step (h, c) (h', c')).
  Proof.
    induct 1; simp;
    repeat match goal with
             | [ H : forall _ h1 _, _ -> _ -> ?P h1 -> _, H' : ?P _ |- _ ] => eapply H in H'; clear H; try eassumption; simp
           end; eauto.

    invert H1.
    right; exists h, (Return x).
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

    unfold star in H2; simp.
    apply IHhoare_triple with (h := h) (h1 := x) (h2 := h2 $++ x0); eauto.
    unfold split in *; simp.
    rewrite (@join_comm _ _ h2 x0).
    apply join_assoc.
    sets.
    cases (h2 $? x1).
    cases (x0 $? x1).
    specialize (H2 x1).
    specialize (H1 x1).
    rewrite lookup_join2 in H1.
    apply H1; equality.
    unfold not.
    simplify.
    cases (x $? x1).
    exfalso; apply H2; equality.
    apply lookup_None_dom in Heq1; propositional.
    apply lookup_None_dom in Heq0; propositional.
    apply lookup_None_dom in Heq; propositional.

    unfold split, disjoint in *; simp.
    cases (h2 $? a).
    rewrite lookup_join1 in H7.
    apply H1 with (a := a); auto.
    rewrite lookup_join1; auto.
    cases (x $? a); try equality.
    eauto using lookup_Some_dom.
    eauto using lookup_Some_dom.
    rewrite lookup_join2 in H7.
    eapply H2; eassumption.
    eauto using lookup_None_dom.
  Qed.

  Lemma hoare_triple_sound' : forall P {result} (c : cmd result) Q,
      hoare_triple P c Q
      -> forall h, P h
      -> invariantFor (trsys_of h c)
                      (fun p =>
                         hoare_triple (fun h' => h' = fst p)
                                      (snd p)
                                      Q).
  Proof.
    simplify.

    apply invariant_induction; simplify.

    propositional; subst; simplify.
    eapply HtWeaken; eauto.
    unfold himp; simplify; equality.

    cases s.
    cases s'.
    simp.
    eauto using preservation.
  Qed.

  Theorem hoare_triple_sound : forall P {result} (c : cmd result) Q,
      hoare_triple P c Q
      -> forall h, P h
      -> invariantFor (trsys_of h c)
                      (fun p => (exists r, snd p = Return r)
                                \/ (exists p', step p p')).
  Proof.
    simplify.

    eapply invariant_weaken.
    eapply hoare_triple_sound'; eauto.
    simp.
    specialize (progress _ _ _ H1); simplify.
    specialize (H2 (fst s) (fst s) $0).
    assert (split (fst s) (fst s) $0) by auto.
    assert (disjoint (fst s) $0) by auto.
    cases s; simp; eauto.
  Qed.

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


  (** * Examples, starting with reusable tactics *)

  Global Opaque heq himp lift star exis ptsto.

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

  Ltac basic := apply HtReturn' || eapply HtWrite.

  Ltac step0 := basic || eapply HtBind || (eapply use_lemma; [ basic | cancel; auto ])
                || (eapply use_lemma; [ eapply HtRead' | solve [ cancel; auto ] ])
                || (eapply HtRead''; solve [ cancel ])
                || (eapply HtStrengthen; [ eapply use_lemma; [ basic | cancel; auto ] | ]).
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


  (** * List-reverse example *)

  Fixpoint linkedList (p : wrd) (ls : list wrd) :=
    match ls with
      | nil => [| p = ^0 |]
      | x :: ls' => [| p <> ^0 |]
                    * exists p', p |--> [x; p'] * linkedList p' ls'
    end%sep.

  Theorem linkedList_null : forall ls,
    linkedList (^0) ls === [| ls = nil |].
  Proof.
    heq; cases ls; cancel.
  Qed.

  Theorem linkedList_nonnull : forall p ls,
    p <> ^0
    -> linkedList p ls === exists x ls' p', [| ls = x :: ls' |] * p |--> [x; p'] * linkedList p' ls'.
  Proof.
    heq; cases ls; cancel; match goal with
                           | [ H : _ = _ :: _ |- _ ] => invert H
                           end; cancel.
  Qed.

  Hint Rewrite <- rev_alt.
  Hint Rewrite rev_involutive.

  Opaque linkedList.

  Definition reverse p :=
    pr <- for pr := (p, ^0) loop
      let (p, r) := pr in
      if weq p (^0) then
        Return (Done pr)
      else
        tmp <- Read (p ^+ ^1);
        _ <- Write (p ^+ ^1) r;
        Return (Again (tmp, p))
    done;
    Return (snd pr).

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
    loop_inv (fun o => exists ls1 ls2, [| ls = rev_append ls1 ls2 |]
                                       * linkedList (fst (valueOf o)) ls2
                                       * linkedList (snd (valueOf o)) ls1
                                       * [| match o with
                                            | Done (p, _) => p = ^0
                                            | _ => True
                                            end |])%sep.
    cases (weq a (^0)); simp.
    step.
    cancel.
    step.
    setoid_rewrite (linkedList_nonnull _ _ n).
    step.
    simp.
    step.
    step.
    simp.
    step.
    setoid_rewrite (linkedList_nonnull _ _ n).
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
End MixedEmbedded.


(** * A simple C-like language, embedded deeply *)

(* In [DeepAndShallowEmbeddings], we saw how to extract programs from the last
 * language to OCaml and run them with an interpreter.  That interpreter needs
 * to be trusted, and its performance isn't so great.  It could be better to
 * generate C-like syntax trees in Coq and output them directly.  We will use
 * this next language to that end. *)

Module DeeplyEmbedded(Import BW : BIT_WIDTH).
  Definition wrd := word bit_width.

  Inductive exp :=
  | Var (x : var)
  | Const (n : wrd)
  | Add (e1 e2 : exp)
  | Read (e : exp).

  Inductive stmt :=
  | Skip
  | Assign (x : var) (e : exp)
  | Write (ae ve : exp)
  | Seq (s1 s2 : stmt)
  | IfThenElse (e : exp) (s1 s2 : stmt)
  | WhileLoop (e : exp) (s1 : stmt).

  Definition heap := fmap wrd wrd.
  Definition valuation := fmap var wrd.

  Inductive eval : heap -> valuation -> exp -> wrd -> Prop :=
  | VVar : forall H V x v,
      V $? x = Some v
      -> eval H V (Var x) v
  | VConst : forall H V n,
      eval H V (Const n) n
  | VAdd : forall H V e1 e2 n1 n2,
      eval H V e1 n1
      -> eval H V e2 n2
      -> eval H V (Add e1 e2) (n1 ^+ n2)
  | VRead : forall H V e1 p v,
      eval H V e1 p
      -> H $? p = Some v
      -> eval H V (Read e1) v.

  Inductive step : heap * valuation * stmt -> heap * valuation * stmt -> Prop :=
  | StAssign : forall H V x e v,
      eval H V e v
      -> step (H, V, Assign x e) (H, V $+ (x, v), Skip)
  | StWrite : forall H V ae ve a v hv,
      eval H V ae a
      -> eval H V ve v
      -> H $? a = Some hv
      -> step (H, V, Write ae ve) (H $+ (a, v), V, Skip)
  | StSeq1 : forall H V s2,
      step (H, V, Seq Skip s2) (H, V, s2)
  | StSeq2 : forall H V s1 s2 H' V' s1',
      step (H, V, s1) (H', V', s1')
      -> step (H, V, Seq s1 s2) (H', V', Seq s1' s2)
  | StIfThen : forall H V e s1 s2 n,
      eval H V e n
      -> n <> ^0
      -> step (H, V, IfThenElse e s1 s2) (H, V, s1)
  | StIfElse : forall H V e s1 s2,
      eval H V e (^0)
      -> step (H, V, IfThenElse e s1 s2) (H, V, s2)
  | StWhileTrue : forall H V e s1 n,
      eval H V e n
      -> n <> ^0
      -> step (H, V, WhileLoop e s1) (H, V, Seq s1 (WhileLoop e s1))
  | StWhileFalse : forall H V e s1,
      eval H V e (^0)
      -> step (H, V, WhileLoop e s1) (H, V, Skip).

  Definition trsys_of (H : heap) (V : valuation) (s : stmt) := {|
    Initial := {(H, V, s)};
    Step := step
  |}.


  (** ** Printing as C code *)

  (* Here we have the pay-off: even within Coq, it is easy to print these syntax
   * trees as normal C (concrete) syntax.  The functions speak for
   * themselves! *)

  Fixpoint wordS {sz} (w : word sz) : string :=
    match w with
    | WO => ""
    | WS false w' => wordS w' ++ "0"
    | WS true w' => wordS w' ++ "1"
    end.

  Definition binS {sz} (w : word sz) : string :=
    "0b" ++ wordS w.

  Fixpoint expS (e : exp) : string :=
    match e with
    | Var x => x
    | Const n => binS n
    | Add e1 e2 => expS e1 ++ " + " ++ expS e2
    | Read e1 => "*(" ++ expS e1 ++ ")"
    end.

  Definition newline := String (Ascii.ascii_of_nat 10) "".

  Fixpoint stmtS' (indent : string) (s : stmt) : string :=
    match s with
    | Skip => ""
    | Assign x e => indent ++ x ++ " = " ++ expS e ++ ";"
    | Write ae ve => indent ++ "*(" ++ expS ae ++ ") = " ++ expS ve ++ ";"
    | Seq s1 s2 => stmtS' indent s1 ++ newline ++ stmtS' indent s2

    | IfThenElse e s1 s2 => indent ++ "if (" ++ expS e ++ ") {" ++ newline
                                   ++ stmtS' ("  " ++ indent) s1 ++ newline
                                   ++ indent ++ "} else {" ++ newline
                                   ++ stmtS' ("  " ++ indent) s2 ++ newline
                                   ++ indent ++ "}"
    | WhileLoop e s1 => indent ++ "while (" ++ expS e ++ ") {" ++ newline
                               ++ stmtS' ("  " ++ indent) s1 ++ newline
                               ++ indent ++ "}"
    end.

  Definition stmtS := stmtS' "".
End DeeplyEmbedded.


(** * Connecting the two *)

(* Reasoning about the mixed-embedding language is much more pleasant than for
 * the deep-embedding language.  Let's implement a verified translation from the
 * former to the latter.  The translation will be an inductive judgment. *)

Module MixedToDeep(Import BW : BIT_WIDTH).
  Module Import DE := DeeplyEmbedded(BW).
  Module Import ME := MixedEmbedded(BW).

  (* Key insight: we translate with respect to a valuation [V], telling us the
   * values of the variables in the deep-embedding world.  When we hit a value
   * of the mixed-embedding world, one translation option is to find a variable
   * known to hold that value, outputting that variable as the translation! *)

  Inductive translate_exp (V : valuation) : forall {A}, A -> exp -> Prop :=
  | TrAdd : forall (v1 v2 : wrd) e1 e2,
      translate_exp V v1 e1
      -> translate_exp V v2 e2
      -> translate_exp V (v1 ^+ v2) (Add e1 e2)
  | TrVar : forall x v,
      V $? x = Some v
      -> translate_exp V v (Var x)
  | TrConst : forall v,
      translate_exp V v (Const v).
  (* Something subtle happens in this last case.  We can turn any value into a
   * constant of the deep embedding?  Sounds like a cop-out!  See a note below
   * on why the cop-out doesn't apply. *)

  (* Things get pretty intricate from here on, including with a weird sort of
   * polymorphism over relations.  We will only comment on the main points. *)

  Inductive translate_result (V : valuation) (v : wrd) : stmt -> Prop :=
  | TrReturn : forall e,
      translate_exp V v e
      -> translate_result V v (Assign "result" e)
  | TrReturned :
      V $? "result" = Some v
      -> translate_result V v Skip.

  Inductive translate_loop_body (V : valuation) (v1_v2 : wrd * wrd) : stmt -> Prop :=
  | TrlReturn : forall e1 e2,
      translate_exp V (fst v1_v2) e1
      -> translate_exp (V $+ ("i", fst v1_v2)) (snd v1_v2) e2
      -> translate_loop_body V v1_v2 (Seq (Assign "i" e1) (Assign "acc" e2))
  | TrlReturned1 : forall e2,
      V $? "i" = Some (fst v1_v2)
      -> translate_exp V (snd v1_v2) e2
      -> translate_loop_body V v1_v2 (Seq Skip (Assign "acc" e2))
  | TrlReturned2 : forall e2,
      V $? "i" = Some (fst v1_v2)
      -> translate_exp V (snd v1_v2) e2
      -> translate_loop_body V v1_v2 (Assign "acc" e2)
  | TrlReturned3 :
      V $? "i" = Some (fst v1_v2)
      -> V $? "acc" = Some (snd v1_v2)
      -> translate_loop_body V v1_v2 Skip.

  Inductive return_type := OneWord | TwoWords.

  Definition rtt (rt : return_type) :=
    match rt with
    | OneWord => wrd
    | TwoWords => wrd * wrd
    end%type.

  (* This is the main relation for translating commands. *)
  Inductive translate 
    : forall {rt}, (valuation -> rtt rt -> stmt -> Prop)
                 -> valuation -> forall {A}, cmd A -> stmt -> Prop :=
  | TrDone : forall {rt} (translate_return : valuation -> rtt rt -> stmt -> Prop) V (v : rtt rt) s,
      translate_return V v s
      -> translate translate_return V (Return v) s
  | TrAssign : forall {rt} (translate_return : valuation -> rtt rt -> stmt -> Prop) V B (v : wrd) (c : wrd -> cmd B) e x s1,
      V $? x = None
      -> x <> "i"
      -> x <> "acc"
      -> translate_exp V v e
      -> (forall w, translate translate_return (V $+ (x, w)) (c w) s1)
         (* ^-- Note this crucial case for translating [Bind].  We require that
          * the translation of the body be correct for any possible value of the
          * mixed-embedding variable, so long as we guarantee that the value is
          * also stashed in deep-embedding variable [x] before proceeding! *)
      -> translate translate_return V (Bind (Return v) c) (Seq (Assign x e) s1)
  | TrAssigned : forall rt (translate_return : valuation -> rtt rt -> stmt -> Prop) V B (v : wrd) (c : wrd -> cmd B) x s1,
      V $? x = Some v
      -> translate translate_return V (c v) s1
      -> translate translate_return V (Bind (Return v) c) (Seq Skip s1)
  (* ^-- Note also "extra" rules like this one, which won't be used in
   * translating a command in the first place.  Instead, they are only used to
   * "strengthen the induction hypothesis" in the simulation proof we use to
   * show soundness of translation.  In other words, execution of
   * mixed-embedding programs generates intermediate states (e.g., with "extra"
   * [Skip]s) that we still need to relate to the deep embedding. *)
  | TrRead : forall rt (translate_return : valuation -> rtt rt -> stmt -> Prop) V B (a : wrd) (c : wrd -> cmd B) e x s1,
      V $? x = None
      -> x <> "i"
      -> x <> "acc"
      -> translate_exp V a e
      -> (forall w, translate translate_return (V $+ (x, w)) (c w) s1)
      -> translate translate_return V (Bind (Read a) c) (Seq (Assign x (DE.Read e)) s1)
  | TrWrite : forall rt (translate_return : valuation -> rtt rt -> stmt -> Prop) V B a v (c : unit -> cmd B) ae ve s1,
      translate_exp V a ae
      -> translate_exp V v ve
      -> translate translate_return V (c tt) s1
      -> translate translate_return V (Bind (Write a v) c) (Seq (DE.Write ae ve) s1)
  | TrAssignedUnit : forall rt (translate_return : valuation -> rtt rt -> stmt -> Prop) V B (c : unit -> cmd B) s1,
      translate translate_return V (c tt) s1
      -> translate translate_return V (Bind (Return tt) c) (Seq Skip s1)

  (* Next, note that the [Loop] rules only apply to a restricted pattern, to
   * simplify the formalism.  The next rule is the one used in compilation,
   * while the rest are only used internally in the soundness proof. *)
  | TrLoop : forall V (initA initB : wrd) body {A} (c : wrd * wrd -> cmd A) ea s1 s2,
      V $? "i" = None
      -> V $? "acc" = None
      -> translate_exp V initA ea
      -> (forall w1 w2, translate (rt := TwoWords) translate_loop_body (V $+ ("i", w1) $+ ("acc", w2)) (body w1 w2) s1)
      -> (forall w1 w2, translate (rt := OneWord) translate_result (V $+ ("i", w1) $+ ("acc", w2)) (c (w1, w2)) s2)
      -> translate (rt := OneWord) translate_result V
                   (Bind (Loop (initA, initB)
                               (fun pr =>
                                  let (p, r) := pr in
                                  if weq p (^0) then
                                    Return (Done pr)
                                  else
                                    p' <- body p r;
                                    Return (Again p'))) c)
                   (Seq (Assign "i" ea)
                        (Seq (Assign "acc" (Const initB))
                             (Seq (WhileLoop (Var "i") s1)
                                  s2)))
  | TrLoop1 : forall V (initA initB : wrd) body {A} (c : wrd * wrd -> cmd A) s1 s2,
      V $? "i" = None
      -> V $? "acc" = None
      -> (forall w1 w2, translate (rt := TwoWords) translate_loop_body (V $+ ("i", w1) $+ ("acc", w2)) (body w1 w2) s1)
      -> (forall w1 w2, translate (rt := OneWord) translate_result (V $+ ("i", w1) $+ ("acc", w2)) (c (w1, w2)) s2)
      -> translate (rt := OneWord) translate_result (V $+ ("i", initA))
                   (Bind (Loop (initA, initB)
                               (fun pr =>
                                  let (p, r) := pr in
                                  if weq p (^0) then
                                    Return (Done pr)
                                  else
                                    p' <- body p r;
                                    Return (Again p'))) c)
                   (Seq Skip
                        (Seq (Assign "acc" (Const initB))
                             (Seq (WhileLoop (Var "i") s1)
                                  s2)))
  | TrLoop2 : forall V (initA initB : wrd) body {A} (c : wrd * wrd -> cmd A) s1 s2,
      V $? "i" = None
      -> V $? "acc" = None
      -> (forall w1 w2, translate (rt := TwoWords) translate_loop_body (V $+ ("i", w1) $+ ("acc", w2)) (body w1 w2) s1)
      -> (forall w1 w2, translate (rt := OneWord) translate_result (V $+ ("i", w1) $+ ("acc", w2)) (c (w1, w2)) s2)
      -> translate (rt := OneWord) translate_result (V $+ ("i", initA))
                   (Bind (Loop (initA, initB)
                               (fun pr =>
                                  let (p, r) := pr in
                                  if weq p (^0) then
                                    Return (Done pr)
                                  else
                                    p' <- body p r;
                                    Return (Again p'))) c)
                   (Seq (Assign "acc" (Const initB))
                        (Seq (WhileLoop (Var "i") s1)
                             s2))
  | TrLoop3 : forall V (initA initB : wrd) body {A} (c : wrd * wrd -> cmd A) s1 s2,
      V $? "i" = None
      -> V $? "acc" = None
      -> (forall w1 w2, translate (rt := TwoWords) translate_loop_body (V $+ ("i", w1) $+ ("acc", w2)) (body w1 w2) s1)
      -> (forall w1 w2, translate (rt := OneWord) translate_result (V $+ ("i", w1) $+ ("acc", w2)) (c (w1, w2)) s2)
      -> translate (rt := OneWord) translate_result (V $+ ("i", initA) $+ ("acc", initB))
                   (Bind (Loop (initA, initB)
                               (fun pr =>
                                  let (p, r) := pr in
                                  if weq p (^0) then
                                    Return (Done pr)
                                  else
                                    p' <- body p r;
                                    Return (Again p'))) c)
                   (Seq Skip
                        (Seq (WhileLoop (Var "i") s1)
                             s2))
  | TrLoop4 : forall V V' (initA initB : wrd) body {A} (c : wrd * wrd -> cmd A) s1 s2,
      V $? "i" = None
      -> V $? "acc" = None
      -> V' $? "i" = Some initA
      -> V' $? "acc" = Some initB
      -> (forall w1 w2, translate (rt := TwoWords) translate_loop_body (V $+ ("i", w1) $+ ("acc", w2)) (body w1 w2) s1)
      -> (forall w1 w2, translate (rt := OneWord) translate_result (V $+ ("i", w1) $+ ("acc", w2)) (c (w1, w2)) s2)
      -> translate (rt := OneWord) translate_result (V $++ V')
                   (Bind (Loop (initA, initB)
                               (fun pr =>
                                  let (p, r) := pr in
                                  if weq p (^0) then
                                    Return (Done pr)
                                  else
                                    p' <- body p r;
                                    Return (Again p'))) c)
                   (Seq (WhileLoop (Var "i") s1)
                        s2)
  | TrLoop5 : forall V V' (initA initB : wrd) {A} (c : wrd * wrd -> cmd A) s2,
      V $? "i" = None
      -> V $? "acc" = None
      -> V' $? "i" = Some initA
      -> V' $? "acc" = Some initB
      -> (forall w1 w2, translate (rt := OneWord) translate_result (V $+ ("i", w1) $+ ("acc", w2)) (c (w1, w2)) s2)
      -> translate (rt := OneWord) translate_result (V $++ V')
                   (Bind (Return (initA, initB)) c)
                   (Seq Skip s2)
  | TrLoop6 : forall V V' V'' body' body {A} (c : wrd * wrd -> cmd A) s' s1 s2,
      V $? "i" = None
      -> V $? "acc" = None
      -> translate (rt := TwoWords) translate_loop_body (V $++ V') body' s'
      -> (forall w1 w2, translate (rt := TwoWords) translate_loop_body (V $+ ("i", w1) $+ ("acc", w2)) (body w1 w2) s1)
      -> (forall w1 w2, translate (rt := OneWord) translate_result (V $+ ("i", w1) $+ ("acc", w2)) (c (w1, w2)) s2)
      -> translate (rt := OneWord) translate_result (V $++ V' $++ V'')
                   (Bind (Bind (Bind body' (fun p' => Return (Again p')))
                               (fun o =>
                                  match o with
                                  | Done a => Return a
                                  | Again a =>
                                    Loop a
                                         (fun pr : wrd * wrd =>
                                            let (p, r) := pr in
                                            if weq p (^0) then
                                              Return (Done pr)
                                            else
                                              p' <- body p r;
                                              Return (Again p'))
                                  end))
                         c)
                   (Seq (Seq s' (WhileLoop (Var "i") s1)) s2).

  (* Here are tactics to compile programs automatically. *)

  Ltac freshFor vm k :=
    let rec keepTrying x :=
        let H := fresh in
        (assert (H : vm $? x = None) by (simplify; equality);
         clear H; k x)
        || let x' := eval simpl in (x ++ "_")%string in keepTrying x' in
    keepTrying "tmp".

  Ltac translate := simpl;
    match goal with
    | [ |- translate_exp _ (_ ^+ _) _ ] => eapply TrAdd
    | [ |- translate_exp ?V ?v _ ] =>
      match V with
      | context[add _ ?y v] => apply TrVar with (x := y); simplify; equality
      end
    | [ |- translate_exp _ _ _ ] => eapply TrConst

    | [ |- translate _ _ (Return _) _ ] => (apply (@TrDone OneWord); apply TrReturn)
                                           || (apply (@TrDone TwoWords); apply TrlReturn)
    | [ |- translate _ ?V (Bind (Return _) _) _ ] =>
      freshFor V ltac:(fun y =>
                         eapply TrAssign with (x := y); [ simplify; equality | equality | equality | | intro ])
    | [ |- translate _ ?V (Bind (Read _) _) _ ] =>
      freshFor V ltac:(fun y =>
                         eapply TrRead with (x := y); [ simplify; equality | equality | equality | | intro ])
    | [ |- translate _ ?V (Bind (Write _ _) _) _ ] =>
      eapply TrWrite
    | [ |- translate _ ?V (Bind (Loop _ _) _) _ ] =>
      eapply TrLoop; [ simplify; equality | simplify; equality | | intros | intros ]
    end.

  (** ** Some examples of compiling programs *)

  Example adder (a b c : wrd) :=
    Bind (Return (a ^+ b)) (fun ab => Return (ab ^+ c)).

  Lemma translate_adder : sig (fun s =>
        forall a b c, translate (rt := OneWord) translate_result ($0 $+ ("a", a) $+ ("b", b) $+ ("c", c)) (adder a b c) s).
  Proof.
    eexists; simplify.
    unfold adder.
    repeat translate.
  Defined.

  Definition adder_compiled := Eval simpl in proj1_sig translate_adder.

  Example reader (p1 p2 : wrd) :=
    Bind (Read p1) (fun v1 => Bind (Read p2) (fun v2 => Return (v1 ^+ v2))).

  Lemma translate_reader : sig (fun s =>
        forall p1 p2, translate (rt := OneWord) translate_result ($0 $+ ("p1", p1) $+ ("p2", p2)) (reader p1 p2) s).
  Proof.
    eexists; simplify.
    unfold reader.
    repeat translate.
  Defined.

  Definition reader_compiled := Eval simpl in proj1_sig translate_reader.

  Example incrementer (p : wrd) :=
    Bind (Read p) (fun v => Bind (Write p (v ^+ ^1)) (fun _ => Return v)).

  Lemma translate_incrementer : sig (fun s =>
        forall p, translate (rt := OneWord) translate_result ($0 $+ ("p", p)) (incrementer p) s).
  Proof.
    eexists; simplify.
    unfold incrementer.
    repeat translate.
  Defined.

  Definition incrementer_compiled := Eval simpl in proj1_sig translate_incrementer.

  Example summer (p : wrd) :=
    Bind (Loop (p, ^0) (fun pr => let (p, r) := pr in
                                  if weq p (^0) then
                                    Return (Done pr)
                                  else
                                    next_data <-
                                              (data <- Read p;
                                               next <- Read (p ^+ ^1);
                                               Return (next, r ^+ data));
                                    Return (Again next_data)))
         (fun pr => Return (snd pr)).

  Lemma translate_summer : sig (fun s =>
        forall p, translate (rt := OneWord) translate_result ($0 $+ ("p", p)) (summer p) s).
  Proof.
    eexists; simplify.
    unfold summer.
    repeat translate.
  Defined.

  Definition summer_compiled := Eval simpl in proj1_sig translate_summer.

  (* We restate our original example program to accommodate limitations
   * in the tactics! *)
  Definition reverse_alt p :=
    pr <- for pr := (p, ^0) loop
      let (p, r) := pr in
      if weq p (^0) then
        Return (Done pr)
      else
        pr' <- (tmp <- Read (p ^+ ^1);
                _ <- Write (p ^+ ^1) r;
                copy <- Return p;
                Return (tmp, copy));
        Return (Again pr')
    done;
    Return (snd pr).

  Lemma translate_reverse_alt : sig (fun s =>
        forall p, translate (rt := OneWord) translate_result ($0 $+ ("p", p)) (reverse_alt p) s).
  Proof.
    eexists; simplify.
    unfold reverse_alt.
    repeat translate.
  Defined.

  Definition reverse_alt_compiled := Eval simpl in proj1_sig translate_reverse_alt.


  (** ** Soundness proof *)

  (* We omit explanation of most of these details, which get rather hairy.
   * Also, these proof scripts are not exactly modeling best practices in
   * automation.  Maybe some day the author will be motivated to clean them
   * up. *)

  (* We do point out here that one recurring motif throughout the lemmas is
   * taking a translation run and applying it in a *larger* valuation than was
   * used as input.  Intuitively, it is OK to run with extra variables around,
   * if we don't actually read them.  This opportunity is important for
   * translated loop bodies, which, after the first loop iteration, get run with
   * their own past variable settings still in place, even though the body
   * provably never reads its own past settings of temporary variables. *)

  Lemma eval_translate : forall H V V' e v,
      eval H (V $++ V') e v
      -> forall (v' : wrd), translate_exp V v' e
      -> v = v'.
  Proof.
    induct 1; invert 1; simplify.

    apply inj_pair2 in H2; subst.
    rewrite lookup_join1 in H0 by (eapply lookup_Some_dom; eauto).
    equality.

    apply inj_pair2 in H1; subst.
    equality.

    apply inj_pair2 in H1; subst.
    erewrite IHeval1 by eauto.
    erewrite IHeval2 by eauto.
    equality.
  Qed.

  Lemma multistep_bind : forall A h (c1 : cmd A) h' c1',
      step^* (h, c1) (h', c1')
      -> forall B (c2 : A -> cmd B), step^* (h, Bind c1 c2) (h', Bind c1' c2).
  Proof.
    induct 1; eauto.
    cases y; simplify.
    specialize (IHtrc _ _ _ _ _ eq_refl JMeq.JMeq_refl JMeq.JMeq_refl JMeq.JMeq_refl _ c2).
    eauto.
  Qed.

  Lemma eq_merge_zero : forall A B (m : fmap A B),
      m $++ $0 = m.
  Proof.
    simplify.
    maps_equal.
    cases (m $? k).
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    assumption.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
  Qed.

  (* Complex statement here, really dealing mostly with the whole idea of
   * ignoring parts of valuations! *)
  Lemma step_translate_loop : forall V (c : cmd (wrd * wrd)) s,
      translate (rt := TwoWords) translate_loop_body V c s
      -> forall H H' V' V'' s',
        DE.step (H, V $++ V', s) (H', V'', s')
        -> exists c', ME.step^* (H, c) (H', c')
                      /\ ((V'' = V $++ V'
                           /\ translate (rt := TwoWords) translate_loop_body V c' s')
                          \/ exists x v, V'' = V $++ V' $+ (x, v)
                               /\ (x = "i" \/ x = "acc" \/ V $? x = None)
                               /\ translate (rt := TwoWords) translate_loop_body (V $+ (x, v)) c' s').
  Proof.
    induct 1.

    cases v; invert H; invert 1; simplify.

    invert H5.
    eapply eval_translate in H4; eauto; subst.
    eexists; split.
    eauto.
    right; do 2 eexists; split.
    eauto.
    propositional.
    apply (@TrDone TwoWords); apply TrlReturned1; simplify; auto.

    eexists; propositional.
    eauto.
    left; propositional.
    apply (@TrDone TwoWords); apply TrlReturned2; simplify; eauto.
    invert H5.

    eapply eval_translate in H5; eauto; subst.
    eexists; propositional.
    eauto.
    right; do 2 eexists; split.
    eauto.
    propositional.
    apply (@TrDone TwoWords); apply TrlReturned3; simplify; auto.

    invert 1; simplify.
    invert H9.
    eapply eval_translate in H8; eauto; subst.
    eexists; propositional.
    eauto.
    right; do 2 eexists; propositional.
    econstructor.
    instantiate (1 := x).
    simplify; equality.
    eauto.

    invert 1; simplify.
    eauto 10.
    invert H5.

    invert 1.
    invert H9.
    invert H8.
    eapply eval_translate in H7; eauto; subst.
    eexists; propositional.
    eapply TrcFront.
    eauto.
    eauto.
    right; do 2 eexists; propositional.
    econstructor.
    instantiate (1 := x); simplify; equality.
    eauto.

    invert 1.
    invert H6.
    eapply eval_translate in H8; eauto; subst.
    eapply eval_translate in H13; eauto; subst.
    do 2 eexists; propositional.
    eapply TrcFront.
    eauto.
    eauto.
    left; propositional.
    eapply TrAssignedUnit.
    assumption.
    
    invert 1.
    eauto 7.
    invert H4.
  Qed.

  Lemma translate_Skip : forall rt (translate_return : valuation -> rtt rt -> stmt -> Prop)
                                (V : valuation) (c : cmd (rtt rt)),
      translate translate_return V c Skip
      -> exists v, c = Return v /\ translate_return V v Skip.
  Proof.
    invert 1.
    apply inj_pair2 in H0; subst.
    apply inj_pair2 in H2; subst.
    eauto.
  Qed.

  Lemma step_translate : forall V (c : cmd wrd) s,
      translate (rt := OneWord) translate_result V c s
      -> forall H H' V' V'' s',
        DE.step (H, V $++ V', s) (H', V'', s')
        -> exists c', ME.step^* (H, c) (H', c')
                           /\ ((V'' = V $++ V'
                                /\ exists V''' V'''', V'' = V''' $++ V''''
                                /\ translate (rt := OneWord) translate_result V''' c' s')
                               \/ exists x v, V'' = V $++ V' $+ (x, v)
                                 /\ translate (rt := OneWord) translate_result (V $+ (x, v)) c' s').
  Proof.
    induct 1.

    invert H; invert 1; simplify.

    eapply eval_translate in H4; eauto; subst.
    eexists; propositional.
    eauto.
    right; do 2 eexists; propositional.
    apply (@TrDone OneWord); apply TrReturned; simplify; auto.

    invert 1; simplify.
    invert H9.
    eapply eval_translate in H8; eauto; subst.
    eexists; propositional.
    eauto.
    right; do 2 eexists; propositional.
    econstructor.
    instantiate (1 := x); simplify; reflexivity.
    eauto.

    invert 1; simplify.
    eexists; propositional.
    eapply TrcFront.
    eauto.
    eauto.
    eauto 6.
    invert H5.

    invert 1.
    invert H9.
    invert H8.
    eapply eval_translate in H7; eauto; subst.
    eexists; propositional.
    eapply TrcFront.
    eauto.
    eauto.
    right; do 2 eexists; propositional.
    econstructor.
    instantiate (1 := x); simplify; reflexivity.
    eauto.

    invert 1.
    invert H6.
    eapply eval_translate in H8; eauto; subst.
    eapply eval_translate in H13; eauto; subst.
    eexists; propositional.
    eapply TrcFront.
    eauto.
    eauto.
    left; propositional.
    do 2 eexists; propositional.
    eapply TrAssignedUnit.
    assumption.
    
    invert 1.
    eauto 9.
    invert H4.

    invert 1.
    invert H10.
    eapply eval_translate in H9; eauto; subst.
    eexists; propositional.
    eauto.
    right; do 2 eexists; propositional.
    eapply TrLoop1; eauto.

    invert 1.
    eexists; propositional.
    eauto.
    left; propositional.
    do 2 eexists; propositional.
    eapply TrLoop2; eauto.
    invert H9.

    invert 1.
    invert H9.
    invert H8.
    eexists; propositional.
    eauto.
    right; do 2 eexists; propositional.
    eapply TrLoop3; eauto.

    invert 1.

    eexists; propositional.
    eauto.
    left; propositional.
    do 2 eexists; propositional.
    replace (V $+ ("i", initA) $+ ("acc", initB)) with (V $++ ($0 $+ ("i", initA) $+ ("acc", initB))).
    eapply TrLoop4; eauto.
    simplify; equality.
    simplify; equality.
    maps_equal.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    cases (V $? k).
    repeat rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    equality.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    invert H9.

    invert 1.
    inversion_clear H11; subst.
    invert H9.
    rewrite lookup_join1 in H14.
    rewrite lookup_join2 in H14 by (eapply lookup_None_dom; simplify; eauto).
    match goal with
    | [ H1 : _ $? "i" = _, H2 : _ $? "i" = _ |- _ ] =>
      match type of H1 with
      | ?E1 = _ =>
        match type of H2 with
        | ?E2 = _ =>
          replace E2 with E1 in * by reflexivity
        end
      end
    end.
    rewrite H1 in H14; invert H14.
    eexists; propositional.
    eapply TrcFront.
    eauto.
    simplify.
    cases (weq n (^0 : wrd)).
    equality.
    eauto.
    left; propositional.
    do 2 eexists; propositional.
    replace (V $++ V') with (V $++ ($0 $+ ("i", n) $+ ("acc", initB)) $++ V').
    apply TrLoop6; eauto.
    replace (V $++ ($0 $+ ("i", n) $+ ("acc", initB))) with (V $+ ("i", n) $+ ("acc", initB)).
    eauto.
    maps_equal.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    cases (V $? k).
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    equality.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    maps_equal.
    cases (V $? k).
    rewrite lookup_join1.
    repeat rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    repeat rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (k ==v "i"); subst.
    rewrite lookup_join1.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify.
    etransitivity; [ | symmetry; eassumption ].
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    cases (k ==v "acc"); subst.
    rewrite lookup_join1.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify.
    etransitivity; [ | symmetry; eassumption ].
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    rewrite lookup_join2.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    apply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).    
    eassumption.
    
    invert H9.
    rewrite lookup_join1 in H13.
    rewrite lookup_join2 in H13 by (eapply lookup_None_dom; simplify; eauto).
    match goal with
    | [ H1 : _ $? "i" = _, H2 : _ $? "i" = _ |- _ ] =>
      match type of H1 with
      | ?E1 = _ =>
        match type of H2 with
        | ?E2 = _ =>
          replace E2 with E1 in * by reflexivity
        end
      end
    end.
    rewrite H1 in H13; invert H13.
    eexists; propositional.
    eapply TrcFront.
    eauto.
    simplify.
    cases (weq (^0 : wrd) (^0 : wrd)).
    eapply TrcFront.
    eauto.
    eauto.
    exfalso; apply n; reflexivity.
    left; propositional.
    do 2 eexists; propositional.
    apply TrLoop5; auto.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.

    clear H4.
    invert 1.
    eexists; propositional.
    eapply TrcFront.
    eauto.
    eauto.
    left; propositional.
    do 2 eexists; split.
    2: eauto.
    instantiate (1 := V' $++ V'0).
    maps_equal.
    cases (V $? k).
    rewrite lookup_join1.
    repeat rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom; simplify; eauto.
    repeat rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (k ==v "i"); subst.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom; simplify; eauto.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (k ==v "acc"); subst.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom; simplify; eauto.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom; simplify; eauto.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_None_dom; simplify; eauto.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    assumption.
    invert H8.

    clear H3 H5 IHtranslate.
    invert 1.
    invert H8.

    apply translate_Skip in H1.
    invert H1.
    invert H3.
    invert H5.
    cases x; simplify.
    rewrite lookup_join2 in H1 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join2 in H3 by (eapply lookup_None_dom; simplify; eauto).
    eexists; split.
    eapply TrcFront.
    eapply StepBindRecur.
    eapply StepBindRecur.
    eauto.
    eapply TrcFront.
    eauto.
    eauto.
    left; propositional.
    exists (V $++ ($0 $+ ("i", w) $+ ("acc", w0))), (V' $++ V'' $++ V'0).
    split.
    2: eapply TrLoop4; eauto.
    2: simplify; equality.
    2: simplify; equality.
    maps_equal.
    cases (V $? k).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (k ==v "i"); subst.
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; assumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (k ==v "acc"); subst.
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; assumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join2.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).    
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    repeat rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    assumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    assumption.

    replace (V $++ V' $++ V'' $++ V'0) with ((V $++ V') $++ (V'' $++ V'0)) in H7.
    eapply step_translate_loop in H7; eauto.
    simp.
    eexists; split.
    eapply multistep_bind.
    eapply multistep_bind.
    eapply multistep_bind.
    eassumption.
    left; propositional.
    maps_equal.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join2.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    do 2 eexists; split.
    2: eapply TrLoop6; eauto.
    instantiate (2 := V'').
    instantiate (1 := V'0).
    maps_equal.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join2.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.

    eexists; split.
    eapply multistep_bind.
    eapply multistep_bind.
    eapply multistep_bind.
    eassumption.
    right; do 2 eexists; split.
    instantiate (2 := "i").
    instantiate (1 := x1).
    maps_equal.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join2.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    replace (V $++ V' $++ V'' $+ ("i", x1)) with (V $++ (V' $+ ("i", x1)) $++ V'').
    eapply TrLoop6; eauto.
    replace (V $++ (V' $+ ("i", x1))) with (V $++ V' $+ ("i", x1)).
    assumption.
    maps_equal.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    maps_equal.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eauto.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; eassumption.
    repeat rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; assumption.
    eexists; split.
    eapply multistep_bind.
    eapply multistep_bind.
    eapply multistep_bind.
    eassumption.
    right; do 2 eexists; split.
    instantiate (2 := "acc").
    instantiate (1 := x1).
    maps_equal.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join2.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    replace (V $++ V' $++ V'' $+ ("acc", x1)) with (V $++ (V' $+ ("acc", x1)) $++ V'').
    eapply TrLoop6; eauto.
    replace (V $++ (V' $+ ("acc", x1))) with (V $++ V' $+ ("acc", x1)).
    assumption.
    maps_equal.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    maps_equal.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).    
    simplify; equality.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; eassumption.
    repeat rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; assumption.

    eexists; split.
    eapply multistep_bind.
    eapply multistep_bind.
    eapply multistep_bind.
    eassumption.
    right; do 2 eexists; split.
    instantiate (2 := x0).
    instantiate (1 := x1).
    maps_equal.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join2.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    replace (V $++ V' $++ V'' $+ (x0, x1)) with (V $++ (V' $+ (x0, x1)) $++ V'').
    eapply TrLoop6; eauto.
    replace (V $++ (V' $+ (x0, x1))) with (V $++ V' $+ (x0, x1)).
    assumption.
    maps_equal.
    rewrite lookup_join2.
    simplify.
    equality.
    eapply lookup_None_dom.
    cases (V $? k); auto.
    rewrite lookup_join1 in H5.
    equality.
    eapply lookup_Some_dom; eassumption.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    maps_equal.
    rewrite lookup_join1.
    rewrite lookup_join2.
    simplify.
    equality.
    eapply lookup_None_dom.
    cases (V $? k); auto.
    rewrite lookup_join1 in H5.
    equality.
    eapply lookup_Some_dom; eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    simplify; equality.
    eapply lookup_None_dom.
    cases (V $? k); auto.
    rewrite lookup_join1 in H5.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; eassumption.
    repeat rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    simplify; eassumption.
    maps_equal.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join2.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.

    Grab Existential Variables.
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
  Qed.

  (* This is the invariant for simulation!  Note the crucial addition of extra
   * variables in the valuation.  We carefully chose the two languages to treat
   * the heap identically, so we can require heap equality. *)
  Inductive translated : forall {A}, DE.heap * valuation * stmt -> ME.heap * cmd A -> Prop :=
  | Translated : forall A H V V' s (c : cmd A),
      translate (rt := OneWord) translate_result V c s
      -> translated (H, V $++ V', s) (H, c).

  Theorem translated_simulates : forall H V c s,
      translate (rt := OneWord) translate_result V c s
      -> simulates (translated (A := wrd)) (DE.trsys_of H V s) (ME.multistep_trsys_of H c).
  Proof.
    constructor; simplify.

    propositional; subst.
    eexists; split.
    replace V with (V $++ $0) by apply eq_merge_zero.
    econstructor.
    eassumption.
    auto.

    invert H1.
    apply inj_pair2 in H4; subst.
    cases st1'.
    cases p.
    eapply step_translate in H7; eauto.
    simp.

    eexists; split; [ | eassumption ].
    rewrite H1.
    econstructor.
    assumption.

    eexists; split; [ | eassumption ].
    replace (V0 $++ V' $+ (x0, x1)) with ((V0 $+ (x0, x1)) $++ V').
    econstructor.
    assumption.
    maps_equal.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    simplify; equality.
    cases (V0 $? k).
    repeat rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    simplify; equality.
    repeat rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
  Qed.

  Hint Constructors eval DE.step : core.

  Lemma translate_exp_sound' : forall V v e,
      translate_exp V v e
      -> forall H V', eval H (V $++ V') e v.
  Proof.
    induct 1; simplify; eauto.
    constructor.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    assumption.
  Qed.

  Lemma translate_exp_sound : forall V v e,
      translate_exp V v e
      -> forall H, eval H V e v.
  Proof.
    induct 1; simplify; eauto.
  Qed.

  Hint Resolve translate_exp_sound translate_exp_sound' : core.

  Lemma not_stuck_loop : forall V (c : cmd (wrd * wrd)) s,
      translate (rt := TwoWords) translate_loop_body V c s
      -> forall H H' c',
        step (H, c) (H', c')
        -> forall V', exists p', DE.step (H, V $++ V', s) p'.
  Proof.
    induct 1; invert 1; simplify.

    eexists.
    econstructor.
    econstructor.
    eauto.

    eexists.
    econstructor.
    econstructor.
    eauto.

    eexists.
    econstructor.
    econstructor.
    eauto.

    apply inj_pair2 in H11; subst.
    invert H9.
    eexists.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.

    apply inj_pair2 in H8; subst.
    invert H6.
    eexists.
    econstructor.
    econstructor.
    eauto.
    eauto.
    eauto.

    apply inj_pair2 in H6; subst.
    invert H4.

    eauto.
  Qed.

  Lemma invert_Return : forall {rt} (translate_return : valuation -> rtt rt -> stmt -> Prop) V (v : rtt rt) s,
      translate translate_return V (Return v) s
      -> translate_return V v s.
  Proof.
    invert 1.
    apply inj_pair2 in H0; subst.
    apply inj_pair2 in H2; subst.
    assumption.
  Qed.

  Lemma not_stuck : forall V (c : cmd wrd) s,
      translate (rt := OneWord) translate_result V c s
      -> forall H H' c',
        step (H, c) (H', c')
        -> forall V', exists p', DE.step (H, V $++ V', s) p'.
  Proof.
    induct 1; invert 1; simplify.

    eexists.
    econstructor.
    econstructor.
    eauto.

    eexists.
    econstructor.
    econstructor.
    eauto.

    eexists.
    econstructor.
    econstructor.
    eauto.

    apply inj_pair2 in H11; subst.
    invert H9.
    eexists.
    econstructor.
    econstructor.
    econstructor.
    eauto.
    eauto.

    apply inj_pair2 in H8; subst.
    invert H6.
    eexists.
    econstructor.
    econstructor.
    eauto.
    eauto.
    eauto.

    apply inj_pair2 in H6; subst.
    invert H4.

    eauto.

    apply inj_pair2 in H12; subst.
    invert H10.
    eexists.
    econstructor.
    econstructor.
    eauto.

    apply inj_pair2 in H11; subst.
    invert H9.
    eexists.
    econstructor.

    apply inj_pair2 in H11; subst.
    invert H9.
    eexists.
    econstructor.
    econstructor.
    eauto.

    eauto.

    apply inj_pair2 in H13; subst.
    invert H11.
    cases (weq initA (^0)); subst.
    eexists.
    econstructor.
    apply StWhileFalse.
    econstructor.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    assumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eexists.
    econstructor.
    eapply StWhileTrue.
    econstructor.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    assumption.

    apply inj_pair2 in H11; subst.
    invert H9.

    eauto.

    apply inj_pair2 in H12; subst.
    invert H10.
    apply inj_pair2 in H12; subst.
    invert H9.
    apply inj_pair2 in H12; subst.
    eapply not_stuck_loop in H1; eauto.
    simp.
    cases x.
    cases p.
    eexists.
    econstructor.
    econstructor.
    replace (V $++ V' $++ V'' $++ V'0) with (V $++ V' $++ (V'' $++ V'0)).
    eassumption.
    maps_equal.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join2.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.

    apply inj_pair2 in H12; subst.
    specialize (invert_Return _ _ _ _ H1); invert 1.
    eexists.
    repeat econstructor.
    replace (V $++ V' $++ V'' $++ V'0) with (V $++ V' $++ (V'' $++ V'0)).
    eauto.
    maps_equal.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join2.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eexists.
    repeat econstructor.
    eexists.
    repeat econstructor.
    replace (V $++ V' $++ V'' $++ V'0) with (V $++ V' $++ (V'' $++ V'0)).
    eauto.
    maps_equal.
    cases (V $? k).
    repeat rewrite lookup_join1.
    equality.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    eassumption.
    cases (V' $? k).
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    equality.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join1.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    cases (V'' $? k).
    rewrite lookup_join2.
    rewrite lookup_join1 by (eapply lookup_Some_dom; simplify; eauto).
    rewrite lookup_join1.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_Some_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    rewrite lookup_join2.
    rewrite lookup_join2.
    rewrite lookup_join2.
    equality.
    eapply lookup_None_dom.
    rewrite lookup_join2.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eapply lookup_None_dom.
    eassumption.
    eapply lookup_None_dom.
    rewrite lookup_join2 by (eapply lookup_None_dom; simplify; eauto).
    eassumption.
    eexists.
    repeat econstructor.

    Grab Existential Variables.
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
    exact (^0) || exact (Return (^0)).
  Qed.

  (* The main theorem!  Prove a Hoare triple in the high-level language;
   * conclude safe execution in the low-level language. *)
  Theorem hoare_triple_sound : forall P (c : cmd wrd) Q V s H,
      hoare_triple P c Q
      -> P H
      -> translate (rt := OneWord) translate_result V c s
      -> V $? "result" = None
      -> invariantFor (DE.trsys_of H V s)
                      (fun p => snd p = Skip
                                \/ exists p', DE.step p p').
  Proof.
    simplify.
    eapply invariant_weaken.
    eapply invariant_simulates.
    apply translated_simulates.
    eassumption.
    apply invariant_multistepify with (sys := trsys_of H c).
    eauto using hoare_triple_sound.
    invert 1; simp.

    cases st2; simplify; subst.
    invert H5; simplify.
    apply inj_pair2 in H10; subst.
    specialize (invert_Return _ _ _ _ H9); invert 1.
    right; eexists.
    econstructor; eauto.
    auto.

    invert H5; simp.
    apply inj_pair2 in H7; subst; simplify.
    cases x.
    eapply not_stuck in H10.
    simp.
    eauto.
    eauto.
  Qed.


  (** ** Applying the main theorem to the earlier examples *)

  Theorem adder_ok : forall a b c,
      {{emp}}
        adder a b c
      {{r ~> [| r = a ^+ b ^+ c |]}}.
  Proof.
    unfold adder.
    simplify.
    step.
    step.
    instantiate (1 := (fun r => [| r = a ^+ b |])%sep).
    cancel.
    simp.
    step.
    cancel.
    equality.
  Qed.

  Theorem adder_compiled_ok : forall a b c,
      invariantFor (DE.trsys_of $0 ($0 $+ ("a", a) $+ ("b", b) $+ ("c", c)) adder_compiled)
                      (fun p => snd p = Skip
                                \/ exists p', DE.step p p').
  Proof.
    simplify.
    eapply hoare_triple_sound.
    apply adder_ok.
    constructor; auto.
    apply (proj2_sig translate_adder).
    simplify; equality.
  Qed.

  Theorem reader_ok : forall p1 p2 v1 v2,
      {{p1 |-> v1 * p2 |-> v2}}
        reader p1 p2
      {{r ~> [| r = v1 ^+ v2 |] * p1 |-> v1 * p2 |-> v2}}.
  Proof.
    unfold reader.
    simplify.
    step.
    step.
    simp.
    step.
    step.
    simp.
    step.
    cancel.
    equality.
  Qed.

  Theorem reader_compiled_ok : forall p1 p2 v1 v2,
      p1 <> p2
      -> invariantFor (DE.trsys_of ($0 $+ (p1, v1) $+ (p2, v2)) ($0 $+ ("p1", p1) $+ ("p2", p2)) reader_compiled)
                      (fun p => snd p = Skip
                                \/ exists p', DE.step p p').
  Proof.
    simplify.
    eapply hoare_triple_sound.
    apply reader_ok.
    exists ($0 $+ (p1, v1)), ($0 $+ (p2, v2)); propositional.
    unfold split.
    maps_equal.
    rewrite lookup_join2; simplify; auto; sets.
    rewrite lookup_join1; simplify; auto; sets.
    rewrite lookup_join2; simplify; auto; sets.
    unfold disjoint; simplify.
    cases (weq a p1); simplify; propositional.
    constructor.
    constructor.
    apply (proj2_sig translate_reader).
    simplify; equality.
  Qed.

  Theorem incrementer_ok : forall p v,
      {{p |-> v}}
        incrementer p
      {{r ~> [| r = v |] * p |-> (v ^+ ^1)}}.
  Proof.
    unfold incrementer.
    simplify.
    step.
    step.
    simp.
    step.
    step.
    simp.
    step.
    cancel.
    subst.
    cancel.
  Qed.

  Theorem incrementer_compiled_ok : forall p v,
      invariantFor (DE.trsys_of ($0 $+ (p, v)) ($0 $+ ("p", p)) incrementer_compiled)
                      (fun p => snd p = Skip
                                \/ exists p', DE.step p p').
  Proof.
    simplify.
    eapply hoare_triple_sound.
    apply incrementer_ok.
    constructor.
    apply (proj2_sig translate_incrementer).
    simplify; equality.
  Qed.
End MixedToDeep.


(** * Getting concrete *)

(* Let's generate C code for the concrete bitwidth of 32. *)

Module Bw32.
  Definition bit_width := 32.
  Theorem bit_width_nonzero : bit_width > 0.
  Proof.
    unfold bit_width; linear_arithmetic.
  Qed.
End Bw32.

Module MixedEmbedded32.
  Module Import ME := MixedToDeep(Bw32).

  Definition adder_exported := Eval compute in DE.stmtS adder_compiled.
  Definition reader_exported := Eval compute in DE.stmtS reader_compiled.
  Definition incrementer_exported := Eval compute in DE.stmtS incrementer_compiled.
  Definition summer_exported := Eval compute in DE.stmtS summer_compiled.
  Definition reverse_alt_exported := Eval compute in DE.stmtS reverse_alt_compiled.
End MixedEmbedded32.
