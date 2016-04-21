Set Implicit Arguments.


Section trc.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Inductive trc : A -> A -> Prop :=
  | TrcRefl : forall x, trc x x
  | TrcFront : forall x y z,
    R x y
    -> trc y z
    -> trc x z.

  Hint Constructors trc.

  Theorem trc_one : forall x y, R x y
    -> trc x y.
  Proof.
    eauto.
  Qed.

  Hint Resolve trc_one.

  Theorem trc_trans : forall x y, trc x y
    -> forall z, trc y z
      -> trc x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc_trans.

  Inductive trcEnd : A -> A -> Prop :=
  | TrcEndRefl : forall x, trcEnd x x
  | TrcBack : forall x y z,
    trcEnd x y
    -> R y z
    -> trcEnd x z.

  Hint Constructors trcEnd.

  Lemma TrcFront' : forall x y z,
    R x y
    -> trcEnd y z
    -> trcEnd x z.
  Proof.
    induction 2; eauto.
  Qed.

  Hint Resolve TrcFront'.

  Theorem trc_trcEnd : forall x y, trc x y
    -> trcEnd x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc_trcEnd.

  Lemma TrcBack' : forall x y z,
    trc x y
    -> R y z
    -> trc x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve TrcBack'.

  Theorem trcEnd_trans : forall x y, trcEnd x y
    -> forall z, trcEnd y z
      -> trcEnd x z.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trcEnd_trans.
  
  Theorem trcEnd_trc : forall x y, trcEnd x y
    -> trc x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trcEnd_trc.

  Inductive trcLiteral : A -> A -> Prop :=
  | TrcLiteralRefl : forall x, trcLiteral x x
  | TrcTrans : forall x y z, trcLiteral x y
    -> trcLiteral y z
    -> trcLiteral x z
  | TrcInclude : forall x y, R x y
    -> trcLiteral x y.

  Hint Constructors trcLiteral.

  Theorem trc_trcLiteral : forall x y, trc x y
    -> trcLiteral x y.
  Proof.
    induction 1; eauto.
  Qed.

  Theorem trcLiteral_trc : forall x y, trcLiteral x y
    -> trc x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trc_trcLiteral trcLiteral_trc.

  Theorem trcEnd_trcLiteral : forall x y, trcEnd x y
    -> trcLiteral x y.
  Proof.
    induction 1; eauto.
  Qed.

  Theorem trcLiteral_trcEnd : forall x y, trcLiteral x y
    -> trcEnd x y.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve trcEnd_trcLiteral trcLiteral_trcEnd.
End trc.

Notation "R ^*" := (trc R) (at level 0).
Notation "*^ R" := (trcEnd R) (at level 0).

Hint Constructors trc.
