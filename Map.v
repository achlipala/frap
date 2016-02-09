Require Import Classical Sets ClassicalEpsilon FunctionalExtensionality.

Set Implicit Arguments.

Module Type S.
  Parameter fmap : Type -> Type -> Type.

  Parameter empty : forall A B, fmap A B.
  Parameter add : forall A B, fmap A B -> A -> B -> fmap A B.
  Parameter join : forall A B, fmap A B -> fmap A B -> fmap A B.
  Parameter lookup : forall A B, fmap A B -> A -> option B.
  Parameter includes : forall A B, fmap A B -> fmap A B -> Prop.

  Notation "$0" := (empty _ _).
  Notation "m $+ ( k , v )" := (add m k v) (at level 50, left associativity).
  Infix "$++" := join (at level 50, left associativity).
  Infix "$?" := lookup (at level 50, no associativity).
  Infix "$<=" := includes (at level 90).

  Parameter dom : forall A B, fmap A B -> set A.

  Axiom fmap_ext : forall A B (m1 m2 : fmap A B),
    (forall k, m1 $? k = m2 $? k)
    -> m1 = m2.

  Axiom lookup_empty : forall A B k, empty A B $? k = None.

  Axiom includes_lookup : forall A B (m m' : fmap A B) k v,
    m $? k = Some v
    -> m $<= m'
    -> lookup m' k = Some v.

  Axiom includes_add : forall A B (m m' : fmap A B) k v,
    m $<= m'
    -> add m k v $<= add m' k v.

  Axiom lookup_add_eq : forall A B (m : fmap A B) k1 k2 v,
    k1 = k2
    -> add m k1 v $? k2 = Some v.

  Axiom lookup_add_ne : forall A B (m : fmap A B) k k' v,
    k' <> k
    ->  add m k v $? k' = m $? k'.

  Axiom lookup_join1 : forall A B (m1 m2 : fmap A B) k,
    k \in dom m1
    -> (m1 $++ m2) $? k = m1 $? k.

  Axiom lookup_join2 : forall A B (m1 m2 : fmap A B) k,
    ~k \in dom m1
    -> (m1 $++ m2) $? k = m2 $? k.

  Axiom join_comm : forall A B (m1 m2 : fmap A B),
    dom m1 \cap dom m2 = {}
    -> m1 $++ m2 = m2 $++ m1.

  Axiom join_assoc : forall A B (m1 m2 m3 : fmap A B),
    (m1 $++ m2) $++ m3 = m1 $++ (m2 $++ m3).

  Axiom empty_includes : forall A B (m : fmap A B), empty A B $<= m.

  Axiom dom_empty : forall A B, dom (empty A B) = {}.

  Axiom dom_add : forall A B (m : fmap A B) (k : A) (v : B),
    dom (add m k v) = {k} \cup dom m.

  Hint Extern 1 => match goal with
                     | [ H : lookup (empty _ _) _ = Some _ |- _ ] =>
                       rewrite lookup_empty in H; discriminate
                   end.

  Hint Resolve includes_lookup includes_add empty_includes.

  Hint Rewrite lookup_add_eq lookup_add_ne using congruence.

  Ltac maps_equal :=
    apply fmap_ext; intros;
      repeat (subst; autorewrite with core; try reflexivity;
        match goal with
          | [ |- context[lookup (add _ ?k _) ?k' ] ] => destruct (classic (k = k')); subst
        end).

  Hint Extern 3 (_ = _) => maps_equal.
End S.

Module M : S.
  Definition fmap (A B : Type) := A -> option B.

  Definition empty A B : fmap A B := fun _ => None.

  Section decide.
    Variable P : Prop.

    Lemma decided : inhabited (sum P (~P)).
    Proof.
      destruct (classic P).
      constructor; exact (inl _ H).
      constructor; exact (inr _ H).
    Qed.

    Definition decide : sum P (~P) :=
      epsilon decided (fun _ => True).
  End decide.

  Definition add A B (m : fmap A B) (k : A) (v : B) : fmap A B :=
    fun k' => if decide (k' = k) then Some v else m k'.
  Definition join A B (m1 m2 : fmap A B) : fmap A B :=
    fun k => match m1 k with
               | None => m2 k
               | x => x
             end.
  Definition lookup A B (m : fmap A B) (k : A) := m k.
  Definition includes A B (m1 m2 : fmap A B) :=
    forall k v, m1 k = Some v -> m2 k = Some v.

  Definition dom A B (m : fmap A B) : set A := fun x => m x <> None.

  Theorem fmap_ext : forall A B (m1 m2 : fmap A B),
    (forall k, lookup m1 k = lookup m2 k)
    -> m1 = m2.
  Proof.
    intros; extensionality k; auto.
  Qed.

  Theorem lookup_empty : forall A B (k : A), lookup (empty B) k = None.
  Proof.
    auto.
  Qed.

  Theorem includes_lookup : forall A B (m m' : fmap A B) k v,
    lookup m k = Some v
    -> includes m m'
    -> lookup m' k = Some v.
  Proof.
    auto.
  Qed.

  Theorem includes_add : forall A B (m m' : fmap A B) k v,
    includes m m'
    -> includes (add m k v) (add m' k v).
  Proof.
    unfold includes, add; intuition.
    destruct (decide (k0 = k)); auto.
  Qed.

  Theorem lookup_add_eq : forall A B (m : fmap A B) k1 k2 v,
    k1 = k2
    -> lookup (add m k1 v) k2 = Some v.
  Proof.
    unfold lookup, add; intuition.
    destruct (decide (k2 = k1)); try tauto.
    congruence.
  Qed.

  Theorem lookup_add_ne : forall A B (m : fmap A B) k k' v,
    k' <> k
    -> lookup (add m k v) k' = lookup m k'.
  Proof.
    unfold lookup, add; intuition.
    destruct (decide (k' = k)); intuition.
  Qed.

  Theorem lookup_join1 : forall A B (m1 m2 : fmap A B) k,
    k \in dom m1
    -> lookup (join m1 m2) k = lookup m1 k.
  Proof.
    unfold lookup, join, dom, In; intros.
    destruct (m1 k); congruence.
  Qed.

  Theorem lookup_join2 : forall A B (m1 m2 : fmap A B) k,
    ~k \in dom m1
    -> lookup (join m1 m2) k = lookup m2 k.
  Proof.
    unfold lookup, join, dom, In; intros.
    destruct (m1 k); try congruence.
    exfalso; apply H; congruence.
  Qed.

  Theorem join_comm : forall A B (m1 m2 : fmap A B),
    dom m1 \cap dom m2 = {}
    -> join m1 m2 = join m2 m1.
  Proof.
    intros; apply fmap_ext; unfold join, lookup; intros.
    apply (f_equal (fun f => f k)) in H.
    unfold dom, intersection, constant in H; simpl in H.
    destruct (m1 k), (m2 k); auto.
    exfalso; rewrite <- H.
    intuition congruence.
  Qed.

  Theorem join_assoc : forall A B (m1 m2 m3 : fmap A B),
    join (join m1 m2) m3 = join m1 (join m2 m3).
  Proof.
    intros; apply fmap_ext; unfold join, lookup; intros.
    destruct (m1 k); auto.
  Qed.

  Theorem empty_includes : forall A B (m : fmap A B), includes (empty (A := A) B) m.
  Proof.
    unfold includes, empty; intuition congruence.
  Qed.

  Theorem dom_empty : forall A B, dom (empty (A := A) B) = {}.
  Proof.
    unfold dom, empty; intros; sets idtac.
  Qed.

  Theorem dom_add : forall A B (m : fmap A B) (k : A) (v : B),
    dom (add m k v) = {k} \cup dom m.
  Proof.
    unfold dom, add; simpl; intros.
    sets ltac:(simpl in *; try match goal with
                                 | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
                               end; intuition congruence).
  Qed.
End M.

Export M.
