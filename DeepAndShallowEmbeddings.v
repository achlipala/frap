(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 11: Deep and Shallow Embeddings
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

(** * Shared notations and definitions *)

Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).
Definition heap := fmap nat nat.
Definition assertion := heap -> Prop.

Hint Extern 1 (_ <= _) => linear_arithmetic.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.

Example h0 : heap := $0 $+ (0, 2) $+ (1, 1) $+ (2, 8) $+ (3, 6).

Hint Rewrite max_l max_r using linear_arithmetic.


(** * Shallow embedding of a language very similar to the one we used last chapter *)

Module Shallow.
  Definition cmd result := heap -> heap * result.

  Definition hoare_triple (P : assertion) {result} (c : cmd result) (Q : result -> assertion) :=
    forall h, P h
              -> let (h', r) := c h in
                 Q r h'.

  Notation "{{ h ~> P }} c {{ r & h' ~> Q }}" :=
    (hoare_triple (fun h => P) c (fun r h' => Q)) (at level 90, c at next level).

  Theorem consequence : forall P {result} (c : cmd result) Q
                               (P' : assertion) (Q' : _ -> assertion),
      hoare_triple P c Q
      -> (forall h, P' h -> P h)
      -> (forall r h, Q r h -> Q' r h)
      -> hoare_triple P' c Q'.
  Proof.
    unfold hoare_triple; simplify.
    specialize (H h).
    specialize (H0 h).
    cases (c h).
    auto.
  Qed.

  Fixpoint array_max (i acc : nat) : cmd nat :=
    fun h =>
      match i with
      | O => (h, acc)
      | S i' =>
        let h_i' := h $! i' in
        array_max i' (max h_i' acc) h
      end.

  Lemma array_max_ok' : forall len i acc,
    {{ h ~> forall j, i <= j < len -> h $! j <= acc }}
      array_max i acc
    {{ r&h ~> forall j, j < len -> h $! j <= r }}.
  Proof.
    induct i; unfold hoare_triple in *; simplify; propositional; auto.

    specialize (IHi (max (h $! i) acc) h); propositional.
    cases (array_max i (max (h $! i) acc)); simplify; propositional; subst.
    apply IHi; auto.
    simplify.
    cases (j0 ==n i); subst; auto.
    assert (h $! j0 <= acc) by auto.
    linear_arithmetic.
  Qed.

  Theorem array_max_ok : forall len,
    {{ _ ~> True }}
      array_max len 0
    {{ r&h ~> forall i, i < len -> h $! i <= r }}.
  Proof.
    simplify.
    eapply consequence.
    apply array_max_ok' with (len := len).

    simplify.
    linear_arithmetic.

    auto.
  Qed.

  Example run_array_max0 : array_max 4 0 h0 = (h0, 8).
  Proof.
    unfold h0.
    simplify.
    reflexivity.
  Qed.

  Fixpoint increment_all (i : nat) : cmd unit :=
    fun h =>
      match i with
      | O => (h, tt)
      | S i' => increment_all i' (h $+ (i', S (h $! i')))
      end.

  Lemma increment_all_ok' : forall len h0 i,
    {{ h ~> (forall j, j < i -> h $! j = h0 $! j)
       /\ (forall j, i <= j < len -> h $! j = S (h0 $! j)) }}
      increment_all i
    {{ _&h ~> forall j, j < len -> h $! j = S (h0 $! j) }}.
  Proof.
    induct i; unfold hoare_triple in *; simplify; propositional; auto.

    specialize (IHi (h $+ (i, S (h $! i)))); propositional.
    cases (increment_all i (h $+ (i, S (h $! i)))); simplify; propositional; subst.
    apply H; simplify; auto.

    cases (j0 ==n i); subst; auto.
    simplify; auto.
    simplify; auto.
  Qed.

  Theorem increment_all_ok : forall len h0,
    {{ h ~> h = h0 }}
      increment_all len
    {{ _&h ~> forall j, j < len -> h $! j = S (h0 $! j) }}.
  Proof.
    simplify.
    eapply consequence.
    apply increment_all_ok' with (len := len).

    simplify; subst; propositional.
    linear_arithmetic.

    simplify.
    auto.
  Qed.

  Example run_increment_all0 : increment_all 4 h0 = ($0 $+ (0, 3) $+ (1, 2) $+ (2, 9) $+ (3, 7), tt).
  Proof.
    unfold h0.
    simplify.
    f_equal.
    maps_equal.
  Qed.
End Shallow.


(** * A basic deep embedding *)

Module Deep.
  Inductive cmd : Type -> Type :=
  | Return {result} (r : result) : cmd result
  | Bind {result result'} (c1 : cmd result') (c2 : result' -> cmd result) : cmd result
  | Read (a : nat) : cmd nat
  | Write (a v : nat) : cmd unit.

  Notation "x <- c1 ; c2" := (Bind c1 (fun x => c2)) (right associativity, at level 80).

  Fixpoint array_max (i acc : nat) : cmd nat :=
    match i with
    | O => Return acc
    | S i' =>
      h_i' <- Read i';
      array_max i' (max h_i' acc)
    end.

  Fixpoint increment_all (i : nat) : cmd unit :=
    match i with
    | O => Return tt
    | S i' =>
      v <- Read i';
      _ <- Write i' (S v); 
      increment_all i'
    end.

  Fixpoint interp {result} (c : cmd result) (h : heap) : heap * result :=
    match c with
    | Return r => (h, r)
    | Bind c1 c2 =>
      let (h', r) := interp c1 h in
      interp (c2 r) h'
    | Read a => (h, h $! a)
    | Write a v => (h $+ (a, v), tt)
    end.

  Example run_array_max0 : interp (array_max 4 0) h0 = (h0, 8).
  Proof.
    unfold h0.
    simplify.
    reflexivity.
  Qed.

  Example run_increment_all0 : interp (increment_all 4) h0 = ($0 $+ (0, 3) $+ (1, 2) $+ (2, 9) $+ (3, 7), tt).
  Proof.
    unfold h0.
    simplify.
    f_equal.
    maps_equal.
  Qed.

  Inductive hoare_triple : assertion -> forall {result}, cmd result -> (result -> assertion) -> Prop :=
  | HtReturn : forall P {result} (v : result),
      hoare_triple P (Return v) (fun r h => P h /\ r = v)
  | HtBind : forall P {result' result} (c1 : cmd result') (c2 : result' -> cmd result) Q R,
      hoare_triple P c1 Q
      -> (forall r, hoare_triple (Q r) (c2 r) R)
      -> hoare_triple P (Bind c1 c2) R
  | HtRead : forall P a,
      hoare_triple P (Read a) (fun r h => P h /\ r = h $! a)
  | HtWrite : forall P a v,
      hoare_triple P (Write a v) (fun _ h => exists h', P h' /\ h = h' $+ (a, v))
  | HtConsequence : forall {result} (c : cmd result) P Q (P' : assertion) (Q' : _ -> assertion),
      hoare_triple P c Q
      -> (forall h, P' h -> P h)
      -> (forall r h, Q r h -> Q' r h)
      -> hoare_triple P' c Q'.

  Theorem hoare_triple_sound : forall P {result} (c : cmd result) Q,
      hoare_triple P c Q
      -> forall h, P h
                   -> let (h', r) := interp c h in
                      Q r h'.
  Proof.
    induct 1; simplify; propositional; eauto.

    specialize (IHhoare_triple h).
    cases (interp c1 h).
    apply H1; eauto.

    specialize (IHhoare_triple h).
    cases (interp c h).
    eauto.
  Qed.

  Extraction "Deep.ml" array_max increment_all.
End Deep.
