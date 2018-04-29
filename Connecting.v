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


(** * Bitvectors of known length *)

Inductive word : nat -> Set :=
| WO : word O
| WS : bool -> forall {n}, word n -> word (S n).

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

Definition wplus {sz} (w1 w2 : word sz) : word sz :=
  natToWord sz (wordToNat w1 + wordToNat w2).

Infix "^+" := wplus (at level 50, left associativity).

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

Hint Resolve shatter_word_0.

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

Module Type BIT_WIDTH.
  Parameter bit_width : nat.
  Axiom bit_width_nonzero : bit_width > 0.
End BIT_WIDTH.


(** * A modification of last chapter's language, to use words instead of naturals *)


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
  | Loop {acc : Set} (init : acc) (body : acc -> cmd (loop_outcome acc)) : cmd acc
  | Fail {result} : cmd result.

  (* We're leaving out allocation and deallocation, to avoid distraction from
   * the main point of the examples to follow. *)

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
    Definition exis {A} (p : A -> hprop) : hprop :=
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
  | HtFail : forall {result},
      hoare_triple (fun _ => False) (Fail (result := result)) (fun _ _ => False)

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

  Hint Constructors hoare_triple.

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

  Hint Constructors step.

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


(** * A simple C-like language with just two data types *)

Module DeeplyEmbedded(Import BW : BIT_WIDTH).
  Definition wrd := word bit_width.

  Inductive exp :=
  | Var (x : var)
  | Const (n : wrd)
  | Add (e1 e2 : exp)
  | Head (e : exp)
  | Tail (e : exp)
  | NotNull (e : exp).

  Inductive stmt :=
  | Skip
  | Assign (x : var) (e : exp)
  | WriteHead (x : var) (e : exp)
  | WriteTail (x : var) (e : exp)
  | Seq (s1 s2 : stmt)
  | IfThenElse (e : exp) (s1 s2 : stmt)
  | WhileLoop (e : exp) (s1 : stmt).

  Inductive type :=
  | Scalar
  | ListPointer (t : type).

  Definition type_eq : forall t1 t2 : type, sumbool (t1 = t2) (t1 <> t2).
    decide equality.
  Defined.

  Record function := {
    Params : list (var * type);
    Locals : list (var * type);
    Return : type;
    Body : stmt
  }.

  Section fn.
    Variable fn : function.

    Definition vars := Params fn ++ Locals fn ++ [("result", Return fn)].

    Fixpoint varType (x : var) (vs : list (var * type)) : option type :=
      match vs with
      | nil => None
      | (y, t) :: vs' => if y ==v x then Some t else varType x vs'
      end.

    Fixpoint expType (e : exp) : option type :=
      match e with
      | Var x => varType x vars
      | Const _ => Some Scalar
      | Add e1 e2 => match expType e1, expType e2 with
                     | Some Scalar, Some Scalar => Some Scalar
                     | _, _ => None
                     end
      | Head x => match expType x with
                  | Some (ListPointer t) => Some t
                  | _ => None
                  end
      | Tail x => match expType x with
                  | Some (ListPointer t) => Some (ListPointer t)
                  | _ => None
                  end
      | NotNull e1 => match expType e1 with
                      | Some (ListPointer _) => Some Scalar
                      | _ => None
                      end
      end.

    Fixpoint stmtWf (s : stmt) : bool :=
      match s with
      | Skip => true
      | Assign x e => match varType x vars, expType e with
                      | Some t1, Some t2 =>
                        if type_eq t1 t2 then true else false
                      | _, _ => false
                      end
      | WriteHead x e => match varType x vars, expType e with
                         | Some (ListPointer t1), Some t2 =>
                           if type_eq t1 t2 then true else false
                         | _, _ => false
                         end
      | WriteTail x e => match varType x vars, expType e with
                         | Some (ListPointer t1), Some (ListPointer t2) =>
                           if type_eq t1 t2 then true else false
                         | _, _ => false
                         end
      | Seq s1 s2 => stmtWf s1 && stmtWf s2
      | IfThenElse e s1 s2 => match expType e with
                              | Some Scalar => stmtWf s1 && stmtWf s2
                              | _ => false
                              end
      | WhileLoop e s1 => match expType e with
                          | Some Scalar => stmtWf s1
                          | _ => false
                          end
      end.

    Record functionWf : Prop := {
      VarsOk : NoDup (map fst (Params fn ++ Locals fn));
      BodyOk : stmtWf (Body fn) = true
    }.
  End fn.

  Definition heap := fmap (wrd) (wrd * wrd).
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
  | VHead : forall H V e1 p ph pt,
      eval H V e1 p
      -> H $? p = Some (ph, pt)
      -> eval H V (Head e1) ph
  | VTail : forall H V e1 p ph pt,
      eval H V e1 p
      -> H $? p = Some (ph, pt)
      -> eval H V (Tail e1) pt
  | VNotNull : forall H V e1 p,
      eval H V e1 p
      -> eval H V (NotNull e1) (if weq p (^0) then ^1 else ^0).

  Inductive step : heap * valuation * stmt -> heap * valuation * stmt -> Prop :=
  | StAssign : forall H V x e v,
      eval H V e v
      -> step (H, V, Assign x e) (H, V $+ (x, v), Skip)
  | StWriteHead : forall H V x e a v hv tv,
      V $? x = Some a
      -> eval H V e v
      -> H $? a = Some (hv, tv)
      -> step (H, V, WriteHead x e) (H $+ (a, (v, tv)), V, Skip)
  | StWriteTail : forall H V x e a v hv tv,
      V $? x = Some a
      -> eval H V e v
      -> H $? a = Some (hv, tv)
      -> step (H, V, WriteTail x e) (H $+ (a, (hv, v)), V, Skip)
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
End DeeplyEmbedded.


(** * Connecting the two *)

Module MixedToDeep(Import BW : BIT_WIDTH).
  Module Import DE := DeeplyEmbedded(BW).
  Module Import ME := MixedEmbedded(BW).

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

  Fixpoint couldWrite (x : var) (s : stmt) : bool :=
    match s with
    | Assign y _ => if x ==v y then true else false
    | Skip
    | WriteHead _ _
    | WriteTail _ _ => false
    | Seq s1 s2
    | IfThenElse _ s1 s2 => couldWrite x s1 || couldWrite x s2
    | WhileLoop _ s1 => couldWrite x s1
    end.

  Inductive translate (out : var) : valuation -> forall {A}, cmd A -> stmt -> Prop :=
  | TrReturn : forall V (A : Set) (v : A) e,
      translate_exp V v e
      -> translate out V (Return v) (Assign out e)
  | TrReturned : forall V v,
      V $? out = Some v
      -> translate out V (Return v) Skip
  | TrAssign : forall V (B : Set) (v : wrd) (c : wrd -> cmd B) e x s1,
      translate_exp V v e
      -> (forall w, translate out (V $+ (x, w)) (c w) s1)
      -> translate out V (Bind (Return v) c) (Seq (Assign x e) s1)
  | TrAssigned : forall V (B : Set) (v : wrd) (c : wrd -> cmd B) x s1,
      V $? x = Some v
      -> translate out (V $+ (x, v)) (c v) s1
      -> translate out V (Bind (Return v) c) (Seq Skip s1).

  Example adder (a b c : wrd) :=
    Bind (Return (a ^+ b)) (fun ab => Return (ab ^+ c)).

  Ltac freshFor vm k :=
    let rec keepTrying x :=
        let H := fresh in
        (assert (H : vm $? x = None) by (simplify; equality);
         clear H; k x)
        || let x' := eval simpl in (x ++ "'")%string in keepTrying x' in
    keepTrying "tmp".

  Ltac translate :=
    match goal with
    | [ |- translate_exp _ (_ ^+ _) _ ] => eapply TrAdd
    | [ |- translate_exp ?V ?v _ ] =>
      match V with
      | context[add _ ?y v] => apply TrVar with (x := y); simplify; equality
      end

    | [ |- translate _ _ (Return _) _ ] => apply TrReturn
    | [ |- translate _ ?V (Bind (Return _) _) _ ] =>
      freshFor V ltac:(fun y =>
                         eapply TrAssign with (x := y); [ | intro ])
    end.

  Lemma translate_adder : sig (fun s =>
        forall a b c, translate "result" ($0 $+ ("a", a) $+ ("b", b) $+ ("c", c)) (adder a b c) s).
  Proof.
    eexists; simplify.
    unfold adder.
    repeat translate.
  Defined.

  Definition adder_compiled := Eval simpl in proj1_sig translate_adder.

  Record heaps_compat (H : DE.heap) (h : ME.heap) : Prop := {
    DeepToMixedHd : forall a v1 v2, H $? a = Some (v1, v2) -> h $? a = Some v1;
    DeepToMixedTl : forall a v1 v2, H $? a = Some (v1, v2) -> h $? (a ^+ ^1) = Some v2;
    MixedToDeep : forall a v1 v2, h $? a = Some v1 -> h $? (a ^+ ^1) = Some v2
                                  -> H $? a = Some (v1, v2)
  }.

  Inductive translated : forall {A}, DE.heap * valuation * stmt -> ME.heap * cmd A -> Prop :=
  | Translated : forall A H h V s (c : cmd A),
      translate "result" V c s
      -> heaps_compat H h
      -> translated (H, V, s) (h, c).

  Lemma eval_translate : forall H V e v,
      eval H V e v
      -> forall (v' : wrd), translate_exp V v' e
      -> v = v'.
  Proof.
    induct 1; invert 1; simplify.

    apply inj_pair2 in H2; subst.
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

  Lemma step_translate : forall H V s H' V' s',
      DE.step (H, V, s) (H', V', s')
      -> forall h (c : cmd wrd) out,
        translate out V c s
        -> heaps_compat H h
        -> exists c' h', ME.step^* (h, c) (h', c')
                         /\ translate out V' c' s'
                         /\ heaps_compat H' h'.
  Proof.
    induct 1; invert 1; simplify.

    apply inj_pair2 in H1; subst.
    eapply eval_translate in H5; eauto; subst.
    do 2 eexists; propositional.
    eauto.
    apply TrReturned; simplify; auto.
    assumption.

    apply inj_pair2 in H0; subst.
    do 2 eexists; propositional.
    eapply TrcFront.
    eauto.
    eauto.
    replace V' with (V' $+ (x, v)).
    assumption.
    maps_equal.
    symmetry; assumption.
    assumption.

    apply inj_pair2 in H2; subst.
    invert H0.
    do 2 eexists; propositional.
    eauto.
    eapply TrAssigned with (x := x).
    eapply eval_translate in H7; eauto.
    simplify.
    subst.
    reflexivity.
    match goal with
    | [ |- translate _ ?V' _ _ ] => replace V' with (V $+ (x, v)) by (maps_equal; equality)
    end.
    eauto.
    assumption.

    invert H0.
  Qed.

  Theorem translated_simulates : forall H V c h s,
      translate "result" V c s
      -> heaps_compat H h
      -> simulates (translated (A := wrd)) (DE.trsys_of H V s) (ME.multistep_trsys_of h c).
  Proof.
    constructor; simplify.

    propositional; subst.
    eexists; split.
    econstructor.
    eassumption.
    eauto.
    auto.

    invert H2.
    apply inj_pair2 in H5; subst.
    cases st1'.
    cases p.
    eapply step_translate in H6; eauto.
    simp.
    eexists; split; [ | eassumption ].
    econstructor.
    assumption.
    eauto.
  Qed.

  Hint Constructors eval DE.step.

  Lemma translate_exp_sound : forall V v e,
      translate_exp V v e
      -> forall H, eval H V e v.
  Proof.
    induct 1; simplify; eauto.
  Qed.

  Hint Resolve translate_exp_sound.

  Lemma not_stuck : forall A h (c : cmd A) h' c',
      step (h, c) (h', c')
      -> forall out V s, translate out V c s
                         -> forall H, exists p', DE.step (H, V, s) p'.
  Proof.
    induct 1; invert 1; simplify.

    eexists.
    econstructor.
    econstructor.
    eauto.

    eexists.
    econstructor.

    eexists.
    econstructor.
    econstructor.
    eauto.

    eexists.
    econstructor.
  Qed.

  Theorem hoare_triple_sound : forall P (c : cmd wrd) Q V s h H,
      hoare_triple P c Q
      -> P h
      -> heaps_compat H h
      -> translate "result" V c s
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
    eassumption.
    apply invariant_multistepify with (sys := trsys_of h c).
    eauto using hoare_triple_sound.
    invert 1; simp.

    cases st2; simplify; subst.
    invert H6; simplify.
    apply inj_pair2 in H8; subst.
    invert H11.
    apply inj_pair2 in H6; subst.
    right; eexists.
    econstructor; eauto.
    auto.

    invert H6; simp.
    apply inj_pair2 in H8; subst; simplify.
    cases x.
    eapply not_stuck in H7; eauto.
  Qed.

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
    constructor; simplify; equality.
    apply (proj2_sig translate_adder).
    simplify; equality.
  Qed.
End MixedToDeep.


(** * Getting concrete *)

Module Bw64.
  Definition bit_width := 64.
  Theorem bit_width_nonzero : bit_width > 0.
  Proof.
    unfold bit_width; linear_arithmetic.
  Qed.
End Bw64.

Module MixedEmbedded64.
  Module Import ME := MixedEmbedded(Bw64).
End MixedEmbedded64.
