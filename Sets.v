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
  Definition minus (s1 s2 : set) : set := fun x => s1 x /\ ~s2 x.
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
Infix "\setminus" := minus (at level 40).
Infix "\subseteq" := subseteq (at level 70).
Infix "\subset" := subset (at level 70).
Notation "[ x | P ]" := (scomp (fun x => P)).

Ltac sets' tac :=
  unfold In, constant, universe, check, union, intersection, minus, complement, subseteq, subset, scomp in *;
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

  Variables ss1 ss2 : list A.

  Theorem union_constant : constant ss1 \cup constant ss2 = constant (ss1 ++ ss2).
  Proof.
    unfold constant, union; simpl.

    apply sets_equal; simpl; intuition.
  Qed.
End properties.

Hint Resolve subseteq_refl subseteq_In.

Hint Rewrite union_constant.


(** * Removing duplicates from constant sets *)

Inductive removeDups A : list A -> list A -> Prop :=
| RdNil : removeDups nil nil
| RdNew : forall x ls ls',
  ~List.In x ls
  -> removeDups ls ls'
  -> removeDups (x :: ls) (x :: ls')
| RdDup : forall x ls ls',
  List.In x ls
  -> removeDups ls ls'
  -> removeDups (x :: ls) ls'.

Theorem removeDups_fwd : forall A x (ls ls' : list A),
  removeDups ls ls'
  -> List.In x ls
  -> List.In x ls'.
Proof.
  induction 1; simpl; intuition.
  subst; eauto.
Qed.

Theorem removeDups_bwd : forall A x (ls ls' : list A),
  removeDups ls ls'
  -> List.In x ls'
  -> List.In x ls.
Proof.
  induction 1; simpl; intuition.
Qed.

Theorem removeDups_ok : forall A (ls ls' : list A),
  removeDups ls ls'
  -> constant ls = constant ls'.
Proof.
  intros.
  apply sets_equal.
  unfold constant; intuition eauto using removeDups_fwd, removeDups_bwd.
Qed.

Ltac someMatch ls :=
  match ls with
  | ?x :: ?ls' =>
    let rec someMatch' ls :=
        match ls with
        | x :: _ => idtac
        | _ :: ?ls' => someMatch' ls'
        end
    in someMatch' ls'
  | _ :: ?ls' => someMatch ls'
  end.

Ltac removeDups :=
  match goal with
  | [ |- context[constant ?ls] ] =>
    someMatch ls;
    erewrite (@removeDups_ok _ ls)
      by repeat (apply RdNil
                 || (apply RdNew; [ simpl; intuition congruence | ])
                 || (apply RdDup; [ simpl; intuition congruence | ]))
  end.


(** * Simplifying set subtraction with constant sets *)

Inductive doSubtract A : list A -> list A -> list A -> Prop :=
| DsNil : forall ls, doSubtract nil ls nil
| DsKeep : forall x ls ls0 ls',
  ~List.In x ls0
  -> doSubtract ls ls0 ls'
  -> doSubtract (x :: ls) ls0 (x :: ls')
| DsDrop : forall x ls ls0 ls',
  List.In x ls0
  -> doSubtract ls ls0 ls'
  -> doSubtract (x :: ls) ls0 ls'.

Theorem doSubtract_fwd : forall A x (ls ls0 ls' : list A),
  doSubtract ls ls0 ls'
  -> List.In x ls
  -> ~List.In x ls0
  -> List.In x ls'.
Proof.
  induction 1; simpl; intuition.
  subst; eauto.
  tauto.
Qed.

Theorem doSubtract_bwd1 : forall A x (ls ls0 ls' : list A),
  doSubtract ls ls0 ls'
  -> List.In x ls'
  -> List.In x ls.
Proof.
  induction 1; simpl; intuition.
Qed.

Theorem doSubtract_bwd2 : forall A x (ls ls0 ls' : list A),
  doSubtract ls ls0 ls'
  -> List.In x ls'
  -> List.In x ls0
  -> False.
Proof.
  induction 1; simpl; intuition.
  subst; eauto.
Qed.

Theorem doSubtract_ok : forall A (ls ls0 ls' : list A),
  doSubtract ls ls0 ls'
  -> constant ls \setminus constant ls0 = constant ls'.
Proof.
  unfold minus.
  intros.
  apply sets_equal.
  unfold constant; intuition eauto using doSubtract_fwd, doSubtract_bwd1, doSubtract_bwd2.
Qed.

Ltac fancy_neq :=
  solve [ repeat match goal with
                 | [ H : @eq (nat -> _) _ _ |- _ ] => apply (f_equal (fun f => f 0)) in H
                 | [ H : _ = _ |- _ ] => inversion H; clear H; subst
                 end ].

Ltac doSubtract :=
  match goal with
  | [ |- context[constant ?ls \setminus constant ?ls0] ] =>
    erewrite (@doSubtract_ok _ ls ls0)
      by repeat (apply DsNil
                 || (apply DsKeep; [ simpl; intuition (congruence || fancy_neq) | ])
                 || (apply DsDrop; [ simpl; intuition congruence | ]))
  end.


(** Undetermined set variables in fixed points should be turned into the empty set. *)
Ltac unifyTails :=
  match goal with
  | [ |- context[_ \cup ?x] ] => is_evar x;
    match type of x with
    | set ?A => unify x (constant (@nil A))
    | ?A -> Prop => unify x (constant (@nil A))
    end
  end.
