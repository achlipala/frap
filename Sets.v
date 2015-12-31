Require Import Classical FunctionalExtensionality List.

Set Implicit Arguments.


Axiom prop_ext : forall P Q : Prop,
  (P <-> Q) -> P = Q.

Section set.
  Variable A : Type.

  Definition set := A -> Prop.
  Definition In (x : A) (s : set) := s x.

  Definition constant (ls : list A) : set := fun x => List.In x ls.
  Definition universe : set := fun _ => True.
  Definition check (P : Prop) : set := fun _ => P.

  Definition union (s1 s2 : set) : set := fun x => s1 x \/ s2 x.
  Definition intersection (s1 s2 : set) : set := fun x => s1 x /\ s2 x.
  Definition complement (s : set) : set := fun x => ~s x.

  Definition subseteq (s1 s2 : set) := forall x, s1 x -> s2 x.
  Definition subset (s1 s2 : set) := subseteq s1 s2 /\ ~subseteq s2 s1.

  Definition scomp (P : A -> Prop) : set := P.

  Theorem sets_equal : forall s1 s2 : set, (forall x, s1 x <-> s2 x) -> s1 = s2.
  Proof.
    intros.
    apply functional_extensionality; intros.
    apply prop_ext; auto.
  Qed.
End set.

Infix "\in" := In (at level 70).
Notation "{ }" := (constant nil).
Notation "{ x1 , .. , xN }" := (constant (cons x1 (.. (cons xN nil) ..))).
Notation "[ P ]" := (check P).
Infix "\cup" := union (at level 40).
Infix "\cap" := intersection (at level 40).
Infix "\subseteq" := subseteq (at level 70).
Infix "\subset" := subset (at level 70).
Notation "[ x | P ]" := (scomp (fun x => P)).

Ltac sets' tac :=
  unfold In, constant, universe, check, union, intersection, complement, subseteq, subset, scomp in *;
    tauto || intuition tac.

Ltac sets tac :=
  try match goal with
        | [ |- @eq (set _) _ _ ] => apply sets_equal; intro; split
      end; sets' tac.


(** * Some of the usual properties of set operations *)

Section properties.
  Variable A : Type.
  Variable x : A.
  Variables s1 s2 s3 : set A.

  Theorem union_comm : s1 \cup s2 = s2 \cup s1.
  Proof.
    sets idtac.
  Qed.

  Theorem union_assoc : (s1 \cup s2) \cup s3 = s1 \cup (s2 \cup s3).
  Proof.
    sets idtac.
  Qed.

  Theorem intersection_comm : s1 \cap s2 = s2 \cap s1.
  Proof.
    sets idtac.
  Qed.

  Theorem intersection_assoc : (s1 \cap s2) \cap s3 = s1 \cap (s2 \cap s3).
  Proof.
    sets idtac.
  Qed.

  Theorem not_union : complement (s1 \cup s2) = complement s1 \cap complement s2.
  Proof.
    sets idtac.
  Qed.

  Theorem not_intersection : complement (s1 \cap s2) = complement s1 \cup complement s2.
  Proof.
    sets idtac.
  Qed.

  Theorem subseteq_refl : s1 \subseteq s1.
  Proof.
    unfold subseteq; eauto.
  Qed.

  Theorem subseteq_In : s1 \subseteq s2 -> x \in s1 -> x \in s2.
  Proof.
    unfold subseteq, In; eauto.
  Qed.

  Theorem cap_split : forall (P1 P2 : A -> Prop),
    (forall s, P1 s \/ P2 s)
    -> s1 \cap [s | P1 s] \subseteq s2
    -> s1 \cap [s | P2 s] \subseteq s3
    -> s1 \subseteq (s2 \cap [s | P1 s]) \cup (s3 \cap [s | P2 s]).
  Proof.
    intros; sets eauto.
    specialize (H x0).
    specialize (H0 x0).
    specialize (H1 x0).
    tauto.
  Qed.
End properties.

Hint Resolve subseteq_refl subseteq_In.
