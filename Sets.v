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
Notation "[ P ]" := (check P).
Infix "\cup" := union (at level 40).
Infix "\cap" := intersection (at level 40).
Infix "\setminus" := minus (at level 40).
Infix "\subseteq" := subseteq (at level 70).
Infix "\subset" := subset (at level 70).
Notation "[ x | P ]" := (scomp (fun x => P)).

Module Type EMPTY.
End EMPTY.
Module SetNotations(M : EMPTY).
  Notation "{ }" := (constant nil).
  Notation "{ x1 , .. , xN }" := (constant (cons x1 (.. (cons xN nil) ..))).
End SetNotations.


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

(*Hint Rewrite union_constant.*)


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
  | [ |- context[@minus ?A (@constant ?A1 ?ls) (@constant ?A2 ?ls0)] ] =>
    match A with
    | A1 => idtac
    | _ => change (@constant A1 ls) with (@constant A ls)
    end;
    match A with
    | A2 => idtac
    | _ => change (@constant A2 ls0) with (@constant A ls0)
    end;
    erewrite (@doSubtract_ok A ls ls0)
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


(** * But wait... there's a reflective way to do some of this, too. *)

Require Import Arith.
Import List ListNotations.

Section setexpr.
  Variable A : Type.

  Inductive setexpr :=
  | Literal (vs : list nat)
  | Constant (s : set A)
  | Union (e1 e2 : setexpr).

  Fixpoint interp_setexpr (env : list A) (e : setexpr) : set A :=
    match e with
    | Literal vs =>
      match env with
      | [] => constant []
      | x :: _ => constant (map (nth_default x env) vs)
      end
    | Constant s => s
    | Union e1 e2 => interp_setexpr env e1 \cup interp_setexpr env e2
    end.

  Record normal_form := {
    Elements : list nat;
    Other : option (set A)
  }.

  Fixpoint member (n : nat) (ls : list nat) : bool :=
    match ls with
    | [] => false
    | m :: ls' => (n =? m) || member n ls'
    end.

  Fixpoint dedup (ls : list nat) : list nat :=
    match ls with
    | [] => []
    | n :: ls =>
      let ls' := dedup ls in
      if member n ls' then ls' else n :: ls'
    end.

  Fixpoint setmerge (ls1 ls2 : list nat) : list nat :=
    match ls1 with
    | [] => ls2
    | n :: ls1' =>
      if member n ls2 then setmerge ls1' ls2 else n :: setmerge ls1' ls2
    end.

  Fixpoint normalize_setexpr (e : setexpr) : normal_form :=
    match e with
    | Literal vs => {| Elements := dedup vs; Other := None |}
    | Constant s => {| Elements := []; Other := Some s |}
    | Union e1 e2 =>
      let nf1 := normalize_setexpr e1 in
      let nf2 := normalize_setexpr e2 in
        {| Elements := setmerge nf1.(Elements) nf2.(Elements);
           Other := match nf1.(Other), nf2.(Other) with
                    | None, None => None
                    | o, None => o
                    | None, o => o
                    | Some s1, Some s2 => Some (s1 \cup s2)
                    end |}
    end.

  Definition interp_normal_form (env : list A) (nf : normal_form) : set A :=
    let cs := match env with
              | [] => constant []
              | x :: _ => constant (map (nth_default x env) nf.(Elements))
              end in
    match nf.(Other) with
    | None => cs
    | Some o => cs \cup o
    end.

  Lemma member_ok : forall n ns,
      if member n ns then In n ns else ~In n ns.
  Proof.
    induction ns; simpl; intuition.
    case_eq (n =? a); simpl; intros.
    apply beq_nat_true in H; auto.
    apply beq_nat_false in H.
    destruct (member n ns); intuition.
  Qed.

  Lemma In_dedup_fwd : forall n ns,
      In n (dedup ns)
      -> In n ns.
  Proof.
    induction ns; simpl; intuition.
    pose proof (member_ok a (dedup ns)).
    destruct (member a (dedup ns)); simpl in *; intuition.
  Qed.

  Lemma In_dedup_bwd : forall n ns,
      In n ns
      -> In n (dedup ns).
  Proof.
    induction ns; simpl; intuition.
    pose proof (member_ok a (dedup ns)).
    destruct (member a (dedup ns)); simpl in *; intuition congruence.
    pose proof (member_ok a (dedup ns)).
    destruct (member a (dedup ns)); simpl in *; intuition congruence.
  Qed.

  Lemma constant_dedup : forall (f : _ -> A) vs,
      constant (map f (dedup vs)) = constant (map f vs).
  Proof.
    induction vs; simpl; intuition.
    pose proof (member_ok a (dedup vs)).
    case_eq (member a (dedup vs)); intro.
    rewrite IHvs.
    rewrite H0 in H.
    apply In_dedup_fwd in H.
    apply sets_equal.
    unfold constant.
    simpl.
    intuition.
    apply in_map_iff.
    eauto.
    simpl.
    apply sets_equal.
    simpl.
    intuition congruence.
  Qed.

  Lemma constant_map_setmerge : forall (f : _ -> A) ns2 ns1,
      constant (map f (setmerge ns1 ns2)) = constant (map f ns1) \cup constant (map f ns2).
  Proof.
    induction ns1; simpl; intros.

    sets ltac:(simpl in *; intuition).

    pose proof (member_ok a ns2).
    destruct (member a ns2).
    rewrite IHns1.
    sets ltac:(simpl in *; intuition).
    right.
    eapply in_map_iff; eauto.

    simpl.
    sets ltac:(simpl in *; intuition).
    change (In x (map f (setmerge ns1 ns2))) with ((fun x => In x (map f (setmerge ns1 ns2))) x) in H1.
    rewrite IHns1 in H1.
    tauto.
    change (In x (map f (setmerge ns1 ns2))) with ((fun x => In x (map f (setmerge ns1 ns2))) x).
    rewrite IHns1.
    tauto.
    change (In x (map f (setmerge ns1 ns2))) with ((fun x => In x (map f (setmerge ns1 ns2))) x).
    rewrite IHns1.
    tauto.
  Qed.

  Theorem normalize_setexpr_ok : forall env e,
      interp_normal_form env (normalize_setexpr e) = interp_setexpr env e.
  Proof.
    induction e; simpl; intros.

    unfold interp_normal_form; simpl.
    destruct env; trivial.
    apply constant_dedup.

    unfold interp_normal_form; simpl.
    destruct env; sets ltac:(simpl in *; intuition).

    unfold interp_normal_form in *; simpl in *.
    destruct (Other (normalize_setexpr e1)), (Other (normalize_setexpr e2)).
    destruct env.
    rewrite <- IHe1.
    rewrite <- IHe2.
    sets ltac:(simpl in *; intuition).
    rewrite <- IHe1.
    rewrite <- IHe2.
    rewrite constant_map_setmerge.
    sets ltac:(simpl in *; intuition).
    destruct env.
    rewrite <- IHe1.
    rewrite <- IHe2.
    sets ltac:(simpl in *; intuition).
    rewrite constant_map_setmerge.
    rewrite <- IHe1.
    rewrite <- IHe2.
    sets ltac:(simpl in *; intuition).
    destruct env.
    rewrite <- IHe1.
    rewrite <- IHe2.
    sets ltac:(simpl in *; intuition).
    rewrite constant_map_setmerge.
    rewrite <- IHe1.
    rewrite <- IHe2.
    sets ltac:(simpl in *; intuition).
    destruct env.
    rewrite <- IHe1.
    rewrite <- IHe2.
    sets ltac:(simpl in *; intuition).
    rewrite constant_map_setmerge.
    rewrite <- IHe1.
    rewrite <- IHe2.
    sets ltac:(simpl in *; intuition).
  Qed.

  Fixpoint included (ns1 ns2 : list nat) : bool :=
    match ns1 with
    | [] => true
    | n :: ns1' => member n ns2 && included ns1' ns2
    end.

  Lemma included_true : forall ns2 ns1,
      included ns1 ns2 = true
      -> (forall x, In x ns1 -> In x ns2).
  Proof.
    induction ns1; simpl; intuition subst.

    pose proof (member_ok x ns2).
    destruct (member x ns2); simpl in *; auto; congruence.

    pose proof (member_ok a ns2).
    destruct (member a ns2); simpl in *; auto; congruence.
  Qed.

  Require Import Bool.

  Theorem compare_sets : forall env e1 e2,
      let nf1 := normalize_setexpr e1 in
      let nf2 := normalize_setexpr e2 in
      match Other nf1, Other nf2 with
      | None, None => included nf1.(Elements) nf2.(Elements)
                      && included nf2.(Elements) nf1.(Elements) = true
      | _, _ => False
      end
      -> interp_setexpr env e1 = interp_setexpr env e2.
  Proof.
    intros.
    do 2 rewrite <- normalize_setexpr_ok.
    subst nf1.
    subst nf2.
    unfold interp_normal_form.
    destruct (Other (normalize_setexpr e1)), (Other (normalize_setexpr e2)); intuition.
    destruct env; trivial.
    apply andb_true_iff in H; intuition.
    specialize (included_true _ _ H0).
    specialize (included_true _ _ H1).
    clear H0 H1.
    intros.
    apply sets_equal.
    unfold constant; simpl; intuition.
    apply in_map_iff.
    apply in_map_iff in H1.
    firstorder.
    apply in_map_iff.
    apply in_map_iff in H1.
    firstorder.
  Qed.
End setexpr.

Ltac quote E env k :=
  let T := type of E in
  match eval hnf in T with
  | ?A -> Prop => 
    let rec lookup E env k :=
        match env with
        | [] => k 0 [E]
        | E :: _ => k 0 env
        | ?E' :: ?env' =>
          lookup E env' ltac:(fun pos env'' => k (S pos) (E' :: env''))
        end in

    let rec lookups Es env k :=
        match Es with
        | [] => k (@nil nat) env
        | ?E :: ?Es' =>
          lookup E env ltac:(fun pos env' =>
              lookups Es' env' ltac:(fun poss env'' =>
                                       k (pos :: poss) env''))
        end in

    let rec quote' E env k :=
        match E with
        | constant ?Es =>
          lookups Es env ltac:(fun poss env' => k (Literal A poss) env')
        | ?E1 \cup ?E2 =>
          quote' E1 env ltac:(fun e1 env' =>
            quote' E2 env' ltac:(fun e2 env'' =>
              k (Union e1 e2) env''))
        | _ =>
          (let pf := constr:(eq_refl : E = constant []) in
           k (Literal A []) env)
          || k (Constant E) env
        end in

    quote' E env k
  end.

Ltac sets_cbv := cbv beta iota zeta delta [interp_normal_form normalize_setexpr nth_default
                                           setmerge Elements Other nth_error map dedup member beq_nat orb
                                           andb included].

Ltac sets_cbv_in H := cbv beta iota zeta delta [interp_normal_form normalize_setexpr nth_default
                                                                   setmerge Elements Other nth_error map dedup member beq_nat orb
                                                                   andb included] in H.
                     
Ltac normalize_set :=
  match goal with
  | [ |- context[@union ?A ?X ?Y] ] =>
    quote (@union A X Y) (@nil A) ltac:(fun e env =>
      change (@union A X Y) with (interp_setexpr env e));
    rewrite <- normalize_setexpr_ok; sets_cbv
  | [ H : context[@union ?A ?X ?Y] |- _ ] =>
    quote (@union A X Y) (@nil A) ltac:(fun e env =>
      change (@union A X Y) with (interp_setexpr env e) in H);
    rewrite <- normalize_setexpr_ok in H; sets_cbv_in H
  end.

Ltac compare_sets :=
  match goal with
  | [ |- @eq ?T ?X ?Y ] =>
    match eval hnf in T with
    | ?A -> _ =>
      quote X (@nil A) ltac:(fun x env =>
        quote Y env ltac:(fun y env' =>
          change (interp_setexpr env' x = interp_setexpr env' y)));
      apply compare_sets; sets_cbv; reflexivity
    end
  end.
