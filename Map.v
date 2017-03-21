Require Import Classical Sets ClassicalEpsilon FunctionalExtensionality.

Set Implicit Arguments.

Module Type S.
  Parameter fmap : Type -> Type -> Type.

  Parameter empty : forall A B, fmap A B.
  Parameter lookup : forall A B, fmap A B -> A -> option B.
  Parameter add : forall A B, fmap A B -> A -> B -> fmap A B.

  Parameter remove : forall A B, fmap A B -> A -> fmap A B.
  Parameter join : forall A B, fmap A B -> fmap A B -> fmap A B.
  Parameter merge : forall A B, (option B -> option B -> option B) -> fmap A B -> fmap A B -> fmap A B.
  Parameter restrict : forall A B, (A -> Prop) -> fmap A B -> fmap A B.
  Parameter includes : forall A B, fmap A B -> fmap A B -> Prop.

  Notation "$0" := (empty _ _).
  Notation "m $+ ( k , v )" := (add m k v) (at level 50, left associativity).
  Infix "$-" := remove (at level 50, left associativity).
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

  Axiom lookup_remove_eq : forall A B (m : fmap A B) k1 k2,
    k1 = k2
    -> remove m k1 $? k2 = None.

  Axiom lookup_remove_ne : forall A B (m : fmap A B) k k',
    k' <> k
    ->  remove m k $? k' = m $? k'.

  Axiom lookup_join1 : forall A B (m1 m2 : fmap A B) k,
    k \in dom m1
    -> (m1 $++ m2) $? k = m1 $? k.

  Axiom lookup_join2 : forall A B (m1 m2 : fmap A B) k,
    ~k \in dom m1
    -> (m1 $++ m2) $? k = m2 $? k.

  Axiom join_comm : forall A B (m1 m2 : fmap A B),
    dom m1 \cap dom m2 = constant nil
    -> m1 $++ m2 = m2 $++ m1.

  Axiom join_assoc : forall A B (m1 m2 m3 : fmap A B),
    (m1 $++ m2) $++ m3 = m1 $++ (m2 $++ m3).

  Axiom lookup_merge : forall A B f (m1 m2 : fmap A B) k,
    merge f m1 m2 $? k = f (m1 $? k) (m2 $? k).

  Axiom merge_empty1 : forall A B f (m : fmap A B),
    (forall x, f None x = x)
    -> merge f (@empty _ _) m = m.

  Axiom merge_empty2 : forall A B f (m : fmap A B),
    (forall x, f x None = x)
    -> merge f m (@empty _ _) = m.

  Axiom merge_empty1_alt : forall A B f (m : fmap A B),
    (forall x, f None x = None)
    -> merge f (@empty _ _) m = @empty _ _.

  Axiom merge_empty2_alt : forall A B f (m : fmap A B),
    (forall x, f x None = None)
    -> merge f m (@empty _ _) = @empty _ _.

  Axiom merge_add1 : forall A B f (m1 m2 : fmap A B) k v,
    (forall x y, f (Some x) y = None -> False)
    -> ~k \in dom m1
    -> merge f (add m1 k v) m2 = match f (Some v) (lookup m2 k) with
                                 | None => merge f m1 m2
                                 | Some v => add (merge f m1 m2) k v
                                 end.

  Axiom merge_add2 : forall A B f (m1 m2 : fmap A B) k v,
    (forall x y, f x (Some y) = None -> False)
    -> ~k \in dom m2
    -> merge f m1 (add m2 k v) = match f (lookup m1 k) (Some v) with
                                 | None => merge f m1 m2
                                 | Some v => add (merge f m1 m2) k v
                                 end.

  Axiom merge_add1_alt : forall A B f (m1 m2 : fmap A B) k v,
    (forall x y, f (Some x) (Some y) = None -> False)
    -> ~k \in dom m1
    -> k \in dom m2
    -> merge f (add m1 k v) m2 = match f (Some v) (lookup m2 k) with
                                 | None => merge f m1 m2
                                 | Some v => add (merge f m1 m2) k v
                                 end.

  Axiom empty_includes : forall A B (m : fmap A B), empty A B $<= m.

  Axiom dom_empty : forall A B, dom (empty A B) = constant nil.

  Axiom dom_add : forall A B (m : fmap A B) (k : A) (v : B),
    dom (add m k v) = constant (k :: nil) \cup dom m.

  Axiom lookup_restrict_true : forall A B (P : A -> Prop) (m : fmap A B) k,
    P k
    -> lookup (restrict P m) k = lookup m k.

  Axiom lookup_restrict_false : forall A B (P : A -> Prop) (m : fmap A B) k,
    ~P k
    -> lookup (restrict P m) k = None.

  Axiom lookup_restrict_true_fwd : forall A B (P : A -> Prop) (m : fmap A B) k v,
    lookup (restrict P m) k = Some v
    -> P k.

  Hint Extern 1 => match goal with
                     | [ H : lookup (empty _ _) _ = Some _ |- _ ] =>
                       rewrite lookup_empty in H; discriminate
                   end.

  Hint Resolve includes_lookup includes_add empty_includes.

  Hint Rewrite lookup_empty lookup_add_eq lookup_add_ne lookup_remove_eq lookup_remove_ne
       lookup_merge lookup_restrict_true lookup_restrict_false using congruence.

  Hint Rewrite dom_empty dom_add.

  Ltac maps_equal :=
    apply fmap_ext; intros;
      repeat (subst; autorewrite with core; try reflexivity;
        match goal with
          | [ |- context[lookup (add _ ?k _) ?k' ] ] => destruct (classic (k = k')); subst
        end).

  Hint Extern 3 (_ = _) => maps_equal.

  Axiom lookup_split : forall A B (m : fmap A B) k v k' v',
    (m $+ (k, v)) $? k' = Some v'
    -> (k' <> k /\ m $? k' = Some v') \/ (k' = k /\ v' = v).

  Hint Rewrite merge_empty1 merge_empty2 using solve [ eauto 1 ].
  Hint Rewrite merge_empty1_alt merge_empty2_alt using congruence.

  Hint Rewrite merge_add1 using solve [ eauto | unfold Sets.In; autorewrite with core in *; simpl in *; try (normalize_set; simpl); intuition congruence ].
  Hint Rewrite merge_add1_alt using solve [ congruence | unfold Sets.In; autorewrite with core in *; simpl in *; try (normalize_set; simpl); intuition congruence ].

  Axiom includes_intro : forall K V (m1 m2 : fmap K V),
      (forall k v, m1 $? k = Some v -> m2 $? k = Some v)
      -> m1 $<= m2.
  
  Axiom lookup_Some_dom : forall K V (m : fmap K V) k v,
      m $? k = Some v
      -> k \in dom m.

  Axiom lookup_None_dom : forall K V (m : fmap K V) k,
      m $? k = None
      -> ~ k \in dom m.

  (* Bits meant for separation logic *)
  Section splitting.
    Variables K V : Type.

    Definition disjoint (h1 h2 : fmap K V) : Prop :=
      forall a, h1 $? a <> None
                -> h2 $? a <> None
                -> False.

    Definition split (h h1 h2 : fmap K V) : Prop :=
      h = h1 $++ h2.

    Axiom split_empty_fwd : forall h h1,
        split h h1 $0
        -> h = h1.

    Axiom split_empty_fwd' : forall h h1,
      split h $0 h1
      -> h = h1.

    Axiom split_empty_bwd : forall h,
      split h h $0.

    Axiom split_empty_bwd' : forall h,
      split h $0 h.

    Axiom disjoint_hemp : forall h,
      disjoint h $0.

    Axiom disjoint_hemp' : forall h,
      disjoint $0 h.

    Axiom disjoint_comm : forall h1 h2,
      disjoint h1 h2
      -> disjoint h2 h1.

    Axiom split_comm : forall h h1 h2,
      disjoint h1 h2
      -> split h h1 h2
      -> split h h2 h1.

    Axiom split_assoc1 : forall h h1 h' h2 h3,
      split h h1 h'
      -> split h' h2 h3
      -> split h (join h1 h2) h3.

    Axiom split_assoc2' : forall h h1 h' h2 h3,
      split h h1 h'
      -> split h' h2 h3
      -> disjoint h1 h'
      -> disjoint h2 h3
      -> split h h2 (join h3 h1).

    Axiom split_assoc2 : forall h h1 h' h2 h3,
      split h h' h1
      -> split h' h2 h3
      -> disjoint h' h1
      -> disjoint h2 h3
      -> split h h2 (join h3 h1).

    Axiom disjoint_assoc1 : forall h h1 h' h2 h3,
      split h h1 h'
      -> split h' h2 h3
      -> disjoint h1 h'
      -> disjoint h2 h3
      -> disjoint (join h1 h2) h3.

    Axiom disjoint_assoc2 : forall h h1 h' h2 h3,
      split h h' h1
      -> split h' h2 h3
      -> disjoint h' h1
      -> disjoint h2 h3
      -> disjoint h2 (join h3 h1).

    Axiom split_join : forall h1 h2,
      split (join h1 h2) h1 h2.

    Axiom split_disjoint : forall h h1 h2 h' h3,
      split h h1 h'
      -> split h' h2 h3
      -> disjoint h1 h'
      -> disjoint h2 h3
      -> disjoint h1 h2.

    Axiom disjoint_assoc3 : forall h h1 h2 h3,
      disjoint h h2
      -> split h h1 h3
      -> disjoint h1 h3
      -> disjoint h3 h2.
  End splitting.

  Hint Immediate disjoint_comm split_comm.
  Hint Immediate split_empty_bwd disjoint_hemp disjoint_hemp' split_assoc1 split_assoc2.
  Hint Immediate disjoint_assoc1 disjoint_assoc2 split_join split_disjoint disjoint_assoc3.
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
  Definition remove A B (m : fmap A B) (k : A) : fmap A B :=
    fun k' => if decide (k' = k) then None else m k'.
  Definition join A B (m1 m2 : fmap A B) : fmap A B :=
    fun k => match m1 k with
               | None => m2 k
               | x => x
             end.
  Definition merge A B f (m1 m2 : fmap A B) : fmap A B :=
    fun k => f (m1 k) (m2 k).
  Definition lookup A B (m : fmap A B) (k : A) := m k.
  Definition restrict A B (P : A -> Prop) (m : fmap A B) : fmap A B :=
    fun k => if decide (P k) then m k else None.
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

  Theorem lookup_remove_eq : forall A B (m : fmap A B) k1 k2,
    k1 = k2
    -> lookup (remove m k1) k2 = None.
  Proof.
    unfold lookup, remove; intuition.
    destruct (decide (k2 = k1)); try tauto.
    congruence.
  Qed.

  Theorem lookup_remove_ne : forall A B (m : fmap A B) k k',
    k' <> k
    -> lookup (remove m k) k' = lookup m k'.
  Proof.
    unfold lookup, remove; intuition.
    destruct (decide (k' = k)); try tauto.
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
    dom m1 \cap dom m2 = constant nil
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

  Theorem lookup_merge : forall A B f (m1 m2 : fmap A B) k,
      lookup (merge f m1 m2) k = f (m1 k) (m2 k).
  Proof.
    auto.
  Qed.

  Theorem merge_empty1 : forall A B f (m : fmap A B),
    (forall x, f None x = x)
    -> merge f (@empty _ _) m = m.
  Proof.
    intros; apply fmap_ext; unfold lookup, merge; auto.
  Qed.

  Theorem merge_empty2 : forall A B f (m : fmap A B),
    (forall x, f x None = x)
    -> merge f m (@empty _ _) = m.
  Proof.
    intros; apply fmap_ext; unfold lookup, merge; auto.
  Qed.

  Theorem merge_empty1_alt : forall A B f (m : fmap A B),
    (forall x, f None x = None)
    -> merge f (@empty _ _) m = @empty _ _.
  Proof.
    intros; apply fmap_ext; unfold lookup, merge; auto.
  Qed.

  Theorem merge_empty2_alt : forall A B f (m : fmap A B),
    (forall x, f x None = None)
    -> merge f m (@empty _ _) = @empty _ _.
  Proof.
    intros; apply fmap_ext; unfold lookup, merge; auto.
  Qed.

  Theorem merge_add1 : forall A B f (m1 m2 : fmap A B) k v,
    (forall x y, f (Some x) y = None -> False)
    -> ~k \in dom m1
    -> merge f (add m1 k v) m2 = match f (Some v) (lookup m2 k) with
                                 | None => merge f m1 m2
                                 | Some v => add (merge f m1 m2) k v
                                 end.
  Proof.
    intros; apply fmap_ext; unfold lookup, merge, add; intros.
    destruct (decide (k0 = k)); auto; subst.
    case_eq (f (Some v) (m2 k)); intros.
    case_eq (decide (k = k)); congruence.
    exfalso; eauto.

    case_eq (f (Some v) (m2 k)); intros.
    destruct (decide (k0 = k)); congruence.
    auto.
  Qed.

  Theorem merge_add2 : forall A B f (m1 m2 : fmap A B) k v,
    (forall x y, f x (Some y) = None -> False)
    -> ~k \in dom m2
    -> merge f m1 (add m2 k v) = match f (lookup m1 k) (Some v) with
                                 | None => merge f m1 m2
                                 | Some v => add (merge f m1 m2) k v
                                 end.
  Proof.
    intros; apply fmap_ext; unfold lookup, merge, add; intros.
    destruct (decide (k0 = k)); auto; subst.
    case_eq (f (m1 k) (Some v)); intros.
    case_eq (decide (k = k)); congruence.
    exfalso; eauto.

    case_eq (f (m1 k) (Some v)); intros.
    destruct (decide (k0 = k)); congruence.
    auto.
  Qed.

  Theorem merge_add1_alt : forall A B f (m1 m2 : fmap A B) k v,
    (forall x y, f (Some x) (Some y) = None -> False)
    -> ~k \in dom m1
    -> k \in dom m2
    -> merge f (add m1 k v) m2 = match f (Some v) (lookup m2 k) with
                                 | None => merge f m1 m2
                                 | Some v => add (merge f m1 m2) k v
                                 end.
  Proof.
    intros; apply fmap_ext; unfold lookup, merge, add; intros.
    destruct (decide (k0 = k)); auto; subst.
    case_eq (f (Some v) (m2 k)); intros.
    case_eq (decide (k = k)); congruence.
    case_eq (m2 k); intros.
    rewrite H3 in H2.
    exfalso; eauto.
    congruence.

    case_eq (f (Some v) (m2 k)); intros.
    destruct (decide (k0 = k)); congruence.
    auto.
  Qed.

  Theorem empty_includes : forall A B (m : fmap A B), includes (empty (A := A) B) m.
  Proof.
    unfold includes, empty; intuition congruence.
  Qed.

  Theorem dom_empty : forall A B, dom (empty (A := A) B) = constant nil.
  Proof.
    unfold dom, empty; intros; sets idtac.
  Qed.

  Theorem dom_add : forall A B (m : fmap A B) (k : A) (v : B),
    dom (add m k v) = constant (k :: nil) \cup dom m.
  Proof.
    unfold dom, add; simpl; intros.
    sets ltac:(simpl in *; try match goal with
                                 | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
                               end; intuition congruence).
  Qed.

  Lemma lookup_split : forall A B (m : fmap A B) k v k' v',
    lookup (add m k v) k' = Some v'
    -> (k' <> k /\ lookup m k' = Some v') \/ (k' = k /\ v' = v).
  Proof.
    unfold lookup, add; simpl; intros.
    destruct (decide (k' = k)); intuition congruence.
  Qed.

  Theorem lookup_restrict_true : forall A B (P : A -> Prop) (m : fmap A B) k,
    P k
    -> lookup (restrict P m) k = lookup m k.
  Proof.
    unfold lookup, restrict; intros.
    destruct (decide (P k)); tauto.
  Qed.

  Theorem lookup_restrict_false : forall A B (P : A -> Prop) (m : fmap A B) k,
    ~P k
    -> lookup (restrict P m) k = None.
  Proof.
    unfold lookup, restrict; intros.
    destruct (decide (P k)); tauto.
  Qed.

  Theorem lookup_restrict_true_fwd : forall A B (P : A -> Prop) (m : fmap A B) k v,
    lookup (restrict P m) k = Some v
    -> P k.
  Proof.
    unfold lookup, restrict; intros.
    destruct (decide (P k)); intuition congruence.
  Qed.

  Lemma includes_intro : forall K V (m1 m2 : fmap K V),
      (forall k v, lookup m1 k = Some v -> lookup m2 k = Some v)
      -> includes m1 m2.
  Proof.
    auto.
  Qed.
  
  Lemma lookup_Some_dom : forall K V (m : fmap K V) k v,
      lookup m k = Some v
      -> k \in dom m.
  Proof.
    unfold lookup, dom, In; congruence.
  Qed.

  Lemma lookup_None_dom : forall K V (m : fmap K V) k,
      lookup m k = None
      -> ~ k \in dom m.
  Proof.
    unfold lookup, dom, In; congruence.
  Qed.

  Section splitting.
    Variables K V : Type.

    Notation "$0" := (@empty K V).
    Notation "m $+ ( k , v )" := (add m k v) (at level 50, left associativity).
    Infix "$-" := remove (at level 50, left associativity).
    Infix "$++" := join (at level 50, left associativity).
    Infix "$?" := lookup (at level 50, no associativity).
    Infix "$<=" := includes (at level 90).

    Definition disjoint (h1 h2 : fmap K V) : Prop :=
      forall a, h1 $? a <> None
                -> h2 $? a <> None
                -> False.

    Definition split (h h1 h2 : fmap K V) : Prop :=
      h = h1 $++ h2.

    Hint Extern 2 (_ <> _) => congruence.

    Ltac splt := unfold disjoint, split, join, lookup in *; intros; subst;
                 try match goal with
                     | [ |- @eq (fmap K V) _ _ ] => let a := fresh "a" in extensionality a; simpl
                     end;
                 repeat match goal with
                        | [ a : K, H : forall a : K, _ |- _ ] => specialize (H a)
                        end;
                 repeat match goal with
                        | [ H : _ |- _ ] => rewrite H
                        | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E
                        | [ _ : context[match ?E with Some _ => _ | None => _ end] |- _  ] => destruct E
                        end; eauto; try solve [ exfalso; eauto ].

    Lemma split_empty_fwd : forall h h1,
        split h h1 $0
        -> h = h1.
    Proof.
      splt.
    Qed.

    Lemma split_empty_fwd' : forall h h1,
      split h $0 h1
      -> h = h1.
    Proof.
      splt.
    Qed.

    Lemma split_empty_bwd : forall h,
      split h h $0.
    Proof.
      splt.
    Qed.

    Lemma split_empty_bwd' : forall h,
      split h $0 h.
    Proof.
      splt.
    Qed.

    Lemma disjoint_hemp : forall h,
      disjoint h $0.
    Proof.
      splt.
    Qed.

    Lemma disjoint_hemp' : forall h,
      disjoint $0 h.
    Proof.
      splt.
    Qed.

    Lemma disjoint_comm : forall h1 h2,
      disjoint h1 h2
      -> disjoint h2 h1.
    Proof.
      splt.
    Qed.

    Lemma split_comm : forall h h1 h2,
      disjoint h1 h2
      -> split h h1 h2
      -> split h h2 h1.
    Proof.
      splt.
    Qed.

    Hint Immediate disjoint_comm split_comm.

    Lemma split_assoc1 : forall h h1 h' h2 h3,
      split h h1 h'
      -> split h' h2 h3
      -> split h (join h1 h2) h3.
    Proof.
      splt.
    Qed.

    Lemma split_assoc2' : forall h h1 h' h2 h3,
      split h h1 h'
      -> split h' h2 h3
      -> disjoint h1 h'
      -> disjoint h2 h3
      -> split h h2 (join h3 h1).
    Proof.
      splt.
    Qed.

    Lemma split_assoc2 : forall h h1 h' h2 h3,
      split h h' h1
      -> split h' h2 h3
      -> disjoint h' h1
      -> disjoint h2 h3
      -> split h h2 (join h3 h1).
    Proof.
      intros; eapply split_assoc2'; eauto.
    Qed.

    Lemma disjoint_assoc1 : forall h h1 h' h2 h3,
      split h h1 h'
      -> split h' h2 h3
      -> disjoint h1 h'
      -> disjoint h2 h3
      -> disjoint (join h1 h2) h3.
    Proof.
      splt.
    Qed.

    Lemma disjoint_assoc2 : forall h h1 h' h2 h3,
      split h h' h1
      -> split h' h2 h3
      -> disjoint h' h1
      -> disjoint h2 h3
      -> disjoint h2 (join h3 h1).
    Proof.
      splt.
    Qed.

    Lemma split_join : forall h1 h2,
      split (join h1 h2) h1 h2.
    Proof.
      splt.
    Qed.

    Lemma split_disjoint : forall h h1 h2 h' h3,
      split h h1 h'
      -> split h' h2 h3
      -> disjoint h1 h'
      -> disjoint h2 h3
      -> disjoint h1 h2.
    Proof.
      splt.
    Qed.

    Lemma disjoint_assoc3 : forall h h1 h2 h3,
      disjoint h h2
      -> split h h1 h3
      -> disjoint h1 h3
      -> disjoint h3 h2.
    Proof.
      splt.
    Qed.
  End splitting.
End M.

Export M.
