Require Import Frap.

Definition eclass := nat.

Record egraph := {
    NextEclass : eclass;
    Vars : fmap var eclass;
    Links : fmap eclass eclass
  }.

Definition empty : egraph := {|
  NextEclass := 0;
  Vars := $0;
  Links := $0                         
|}.

Definition M (A : Set) := egraph -> egraph * A.
Definition ret {A : Set} (v : A) : M A :=
  fun g => (g, v).
Definition bind {A B : Set} (m1 : M A) (m2 : A -> M B) : M B :=
  fun g => let (g', v) := m1 g in m2 v g'.

Notation "x <- m1 ; m2" := (bind m1 (fun x => m2))
  (right associativity, at level 60).

Definition linkOf (ec : eclass) : M (option eclass) := fun g =>
  (g, g.(Links) $? ec).

Definition setLink (ec1 ec2 : eclass) : M unit := fun g =>
  ({| NextEclass := g.(NextEclass);
     Vars := g.(Vars);
     Links := g.(Links) $+ (ec1, ec2)|},
    tt).

Fixpoint followLinks' (fuel : nat) (ec : eclass) : M eclass :=
  ec' <- linkOf ec;
  match ec' with
  | None => ret ec
  | Some ec' =>
      match fuel with
      | O => ret ec
      | S fuel' =>
          (ec'' <- followLinks' fuel' ec';
           _ <- (if ec'' ==n ec' then
                   ret tt
                 else
                   setLink ec ec'');
          ret ec'')
      end
  end.

Definition followLinks (ec : eclass) : M eclass :=
  followLinks' (S ec) ec.

Definition classOf (x : var) : M eclass := fun g =>
  match g.(Vars) $? x with
  | Some ec => followLinks ec g
  | None =>
      ({| NextEclass := S g.(NextEclass);
         Vars := g.(Vars) $+ (x, g.(NextEclass));
         Links := g.(Links) |},
        g.(NextEclass))
  end.

Definition assertEqual (x1 x2 : var) : M unit :=
  ec1 <- classOf x1;
  ec2 <- classOf x2;
  let (ec1, ec2) := (min ec1 ec2, max ec1 ec2) in
  setLink ec2 ec1.

Definition checkEqual (x1 x2 : var) : M bool :=
  ec1 <- classOf x1;
  ec2 <- classOf x2;
  ret (if ec1 ==n ec2 then true else false).

Record valid (g : egraph) : Prop := {
    LinksDecrease : forall ec1 ec2, g.(Links) $? ec1 = Some ec2 -> ec2 < ec1;
    VarsInBounds : forall x ec, g.(Vars) $? x = Some ec -> ec < g.(NextEclass);
    LinksInBounds : forall ec1 ec2, g.(Links) $? ec1 = Some ec2 -> ec1 < g.(NextEclass);
    FiniteVars : exists vs, dom g.(Vars) = constant vs
  }.

Hint Resolve LinksDecrease VarsInBounds LinksInBounds FiniteVars : core.

Record valuation := {
    Domain : Set;
    Values : fmap var Domain
  }.
Definition valuations := set valuation.

Inductive representative (g : egraph) : eclass -> eclass -> Prop :=
| RepDone : forall ec1,
    g.(Links) $? ec1 = None
    -> representative g ec1 ec1
| RepStep : forall ec1 ec2 ec3,
    g.(Links) $? ec1 = Some ec2
    -> representative g ec2 ec3
    -> representative g ec1 ec3.

Definition varRepresentative (g : egraph) (x : var) (ec : eclass) : Prop :=
  exists ec', g.(Vars) $? x = Some ec'
              /\ representative g ec' ec.

Definition varsMustAgree (g : egraph) (x1 x2 : var) :=
  exists ec,
    varRepresentative g x1 ec
    /\ varRepresentative g x2 ec.

Definition rep (g : egraph) : valuations := fun v => forall x1 x2,
  varsMustAgree g x1 x2
  -> forall v1 v2,
    v.(Values) $? x1 = Some v1
    -> v.(Values) $? x2 = Some v2
    -> v1 = v2.

Definition all : valuations := fun _ => True.

Theorem valid_empty : valid empty.
Proof.
  constructor; simplify; eauto; equality.
Qed.

Theorem rep_empty : rep empty = all.
Proof.
  unfold rep, varsMustAgree, all; simplify.
  apply sets_equal; simplify; first_order.
  simplify.
  equality.
Qed.

Definition wpre {A} (g : egraph) (m : M A) (Q : egraph -> A -> Prop) : Prop :=
  valid g -> let (g', v) := m g in valid g' /\ Q g' v.

Lemma wpre_ret : forall (A : Set) (x : A) g (Q : egraph -> A -> Prop),
    (valid g -> Q g x)
    -> wpre g (ret x) Q.
Proof.
  unfold wpre; simplify.
  propositional.
Qed.

Lemma wpre_bind : forall A B (m1 : M A) (m2 : A -> M B) g Q,
    wpre g m1 (fun g' r => wpre g' (m2 r) Q)
    -> wpre g (bind m1 m2) Q.
Proof.
  unfold wpre, bind; simplify.
  cases (m1 g); propositional.
Qed.

Lemma wpre_valid : forall A (m : M A) g Q,
    (valid g -> wpre g m Q)
    -> wpre g m Q.
Proof.
  unfold wpre; propositional.
Qed.

Lemma representative_None : forall g ec1 ec2,
    representative g ec1 ec2
    -> g.(Links) $? ec2 = None.
Proof.
  induct 1; simplify; auto.
Qed.

Lemma representative_le : forall g ec1 ec2,
    representative g ec1 ec2
    -> valid g
    -> ec2 <= ec1.
Proof.
  induct 1; simplify; propositional.

  linear_arithmetic.

  apply LinksDecrease in H; try assumption.
  linear_arithmetic.
Qed.

Hint Constructors representative : core.

Lemma representative_func : forall g ec1 ec2,
    representative g ec1 ec2
    -> forall ec2', representative g ec1 ec2'
    -> ec2 = ec2'.
Proof.
  induct 1; invert 1; try equality.

  rewrite H in H2; invert H2.
  eauto.
Qed.

Definition preserve_reps (g g' : egraph) :=
  forall ec ec', representative g ec ec'
                 <-> representative g' ec ec'.

Lemma preserve_reps_use : forall g g' ec1 ec2,
    preserve_reps g g'
    -> representative g ec1 ec2
    -> representative g' ec1 ec2.
Proof.
  unfold preserve_reps; first_order.
Qed.

Lemma preserve_reps_refl : forall g,
    preserve_reps g g.
Proof.
  unfold preserve_reps; first_order.
Qed.

Lemma preserve_reps_symm : forall g g',
    preserve_reps g g'
    -> preserve_reps g' g.
Proof.
  unfold preserve_reps; first_order.
Qed.

Lemma preserve_reps_trans : forall g g' g'',
    preserve_reps g g'
    -> preserve_reps g' g''
    -> preserve_reps g g''.
Proof.
  unfold preserve_reps; first_order.
  apply H in H1; first_order.
  apply H0 in H1; first_order.
Qed.

Lemma representative_same_Links : forall g g' e r,
    g.(Links) = g'.(Links)
    -> representative g e r
    -> representative g' e r.
Proof.
  induct 2; simplify.
  rewrite H in H0; eauto.
  rewrite H in H0; eauto.
Qed.

Lemma preserve_reps_Links : forall g g',
    g.(Links) = g'.(Links)
    -> preserve_reps g g'.
Proof.
  unfold preserve_reps; propositional; eauto using representative_same_Links.
Qed.

Definition gadd (g : egraph) (ec r : eclass) : egraph :=
  {| NextEclass := g.(NextEclass);
    Vars := g.(Vars);
    Links := g.(Links) $+ (ec, r) |}.

Lemma preserve_reps_add_fwd : forall g ec r,
    representative g ec r
    -> ec <> r
    -> forall ec1 ec2, representative g ec1 ec2
                       -> representative (gadd g ec r) ec1 ec2.
Proof.
  induct 3.

  cases (ec ==n ec1); subst.
  econstructor 2; simplify; eauto.
  invert H; equality.
  constructor; simplify; auto.

  cases (ec ==n ec1); subst.
  econstructor 2; simplify; eauto.
  replace ec3 with r by eauto using representative_func.
  constructor.
  simplify; eauto using representative_None.
  econstructor 2; simplify; eauto.
Qed.

Lemma preserve_reps_add_bwd : forall g ec r,
    representative g ec r
    -> ec <> r
    -> forall ec1 ec2, representative (gadd g ec r) ec1 ec2
                       -> representative g ec1 ec2.
Proof.
  induct 3.

  cases (ec ==n ec1); subst; simplify; eauto; equality.

  cases (ec ==n ec1); subst; simplify; eauto.
  invert H1.
  assert (g.(Links) $? ec2 = None) by eauto using representative_None.
  invert IHrepresentative; equality.
Qed.

Lemma preserve_reps_add : forall g ec r,
    representative g ec r
    -> ec <> r
    -> preserve_reps g (gadd g ec r).
Proof.
  unfold preserve_reps; propositional;
    eauto using preserve_reps_add_fwd, preserve_reps_add_bwd.
Qed.

Lemma wpre_followLinks' : forall fuel g ec Q,
    ec < fuel
    -> (forall g' r,
        preserve_reps g g'
        -> g'.(NextEclass) = g.(NextEclass)
        -> g'.(Vars) = g.(Vars)
        -> representative g ec r
        -> Q g' r)
    -> wpre g (followLinks' fuel ec) Q.
Proof.
  induct fuel; simplify.

  linear_arithmetic.

  apply wpre_bind.
  red; unfold linkOf; simplify; propositional.
  cases (Links g $? ec).

  apply wpre_bind.
  apply IHfuel; clear IHfuel.
  apply LinksDecrease in Heq; try assumption.
  linear_arithmetic.
  simplify.
  cases (r ==n e).
  subst.
  apply wpre_bind.
  apply wpre_ret; intro.
  apply wpre_ret; intro.
  apply H0; trivial.
  eauto.

  apply wpre_bind.
  red; unfold setLink; simplify; propositional.
  constructor; simplify.

  cases (ec ==n ec1); subst; simplify.
  invert H7.
  apply representative_le in H5; try assumption.
  apply LinksDecrease in Heq; try assumption.
  linear_arithmetic.
  apply LinksDecrease in H7; assumption.
  apply VarsInBounds in H7; assumption.

  cases (ec ==n ec1); subst; simplify.
  invert H7.
  apply LinksInBounds in Heq; try assumption.
  linear_arithmetic.
  apply LinksInBounds in H7; assumption.
  rewrite H4; eauto.

  apply wpre_ret; intro.
  apply H0; simplify; eauto.
  eapply preserve_reps_trans; eauto.
  apply preserve_reps_add.
  eauto using preserve_reps_use.
  apply LinksDecrease in Heq; auto.
  apply representative_le in H5; auto.
  linear_arithmetic.

  apply wpre_ret; intro.
  apply H0; simplify; eauto.
  apply preserve_reps_refl.
Qed.

Lemma wpre_followLinks : forall g ec Q,
    (forall g' r,
        preserve_reps g g'
        -> g'.(NextEclass) = g.(NextEclass)
        -> g'.(Vars) = g.(Vars)
        -> representative g ec r
        -> Q g' r)
    -> wpre g (followLinks ec) Q.
Proof.
  eauto using wpre_followLinks'.
Qed.

Fixpoint followLinks_noCompress' (fuel : nat) (ec : eclass) (g : egraph) : eclass :=
  match g.(Links) $? ec with
  | None => ec
  | Some ec' =>
      match fuel with
      | O => ec
      | S fuel' => followLinks_noCompress' fuel' ec' g
      end
  end.

Definition followLinks_noCompress (ec : eclass) (g : egraph) : eclass :=
  followLinks_noCompress' (S ec) ec g.

Fixpoint literal_values (g : egraph) (vs : list var) : fmap var eclass :=
  match vs with
  | nil => $0
  | v :: vs' =>
      match g.(Vars) $? v with
      | None => $0
      | Some ec => literal_values g vs' $+ (v, followLinks_noCompress ec g)
      end
  end.

Definition literal_valuation (g : egraph) (vs : list var) : valuation := {|
  Domain := eclass;
  Values := literal_values g vs
|}.

Lemma literal_values_Some_bwd : forall g x ec vs,
    literal_values g vs $? x = Some ec
    -> In x vs /\ exists ec', g.(Vars) $? x = Some ec' /\ ec = followLinks_noCompress ec' g.
Proof.
  induct vs; simplify; try equality.

  cases (Vars g $? a); simplify; try equality.
  cases (a ==v x); subst; simplify; propositional.
  invert H.
  eauto.
Qed.

Lemma literal_values_Some_fwd : forall g x ec vs,
    Forall (fun y => g.(Vars) $? y <> None) vs
    -> In x vs
    -> g.(Vars) $? x = Some ec
    -> literal_values g vs $? x = Some (followLinks_noCompress ec g).
Proof.
  induct 1; simplify; try equality.
  propositional; subst; simplify.

  rewrite H2.
  simplify.
  auto.

  cases (Vars g $? x0); simplify; try equality.
  cases (x ==v x0); subst; simplify; auto.
  equality.
Qed.

Lemma representative_followLinks_noCompress'_bwd : forall g fuel x,
    valid g
    -> x < fuel
    -> representative g x (followLinks_noCompress' fuel x g).
Proof.
  induct fuel; simplify.
  linear_arithmetic.
  cases (Links g $? x); auto.
  econstructor.
  eassumption.
  apply IHfuel; auto.
  assert (e < x) by eauto.
  linear_arithmetic.
Qed.

Lemma representative_followLinks_noCompress_bwd : forall g x,
    valid g
    -> representative g x (followLinks_noCompress x g).
Proof.
  simplify.
  apply representative_followLinks_noCompress'_bwd; auto.
Qed.

Lemma representative_followLinks_noCompress'_fwd : forall g fuel x ec,
    valid g
    -> x < fuel
    -> representative g x ec
    -> ec = followLinks_noCompress' fuel x g.
Proof.
  induct fuel; simplify.
  linear_arithmetic.
  cases (Links g $? x).
  invert H1; try equality.
  rewrite Heq in H2; invert H2.
  apply IHfuel; auto.
  assert (ec2 < x) by eauto.
  linear_arithmetic.

  invert H1; equality.
Qed.

Lemma representative_followLinks_noCompress_fwd : forall g x ec,
    valid g
    -> representative g x ec
    -> ec = followLinks_noCompress x g.
Proof.
  simplify.
  apply representative_followLinks_noCompress'_fwd; auto.
Qed.

Local Hint Resolve representative_followLinks_noCompress_bwd representative_followLinks_noCompress_fwd : core.

Lemma varRepresentative_literal_values_bwd : forall g vs x ec,
    valid g
    -> literal_values g vs $? x = Some ec
    -> varRepresentative g x ec.
Proof.
  simplify.
  apply literal_values_Some_bwd in H0; propositional.
  invert H2; propositional; subst.
  red.
  eauto.
Qed.

Lemma varRepresentative_literal_values_fwd : forall g vs x ec,
    valid g
    -> Forall (fun y => Vars g $? y <> None) vs
    -> In x vs
    -> varRepresentative g x ec
    -> literal_values g vs $? x = Some ec.
Proof.
  simplify.
  invert H2; propositional.
  apply representative_followLinks_noCompress_fwd in H4; auto.
  subst.
  auto using literal_values_Some_fwd.
Qed.

Local Hint Resolve varRepresentative_literal_values_bwd : core.

Lemma varRepresentative_func : forall g x ec1 ec2,
    varRepresentative g x ec1
    -> varRepresentative g x ec2
    -> ec1 = ec2.
Proof.
  simplify.
  invert H; propositional.
  invert H0; propositional.
  rewrite H in H0; invert H0.
  eauto using representative_func.
Qed.

Lemma rep_literal_valuation : forall g vs,
    dom g.(Vars) = constant vs
    -> valid g
    -> rep g (literal_valuation g vs).
Proof.
  unfold rep; simplify.
  invert H1; propositional.
  apply varRepresentative_literal_values_bwd in H2; auto.
  apply varRepresentative_literal_values_bwd in H3; auto.
  eapply varRepresentative_func in H2; try eassumption; subst.
  eapply varRepresentative_func in H3; try eassumption; subst.
Qed.  

Lemma dom_Forall : forall (m : fmap var eclass) vs,
    dom m = constant vs
    -> Forall (fun y => m $? y <> None) vs.
Proof.
  simplify.
  apply Forall_forall; simplify.
  cases (m $? x); try equality.
  apply lookup_None_dom in Heq.
  sets.
Qed.

Lemma dom_In : forall (m : fmap var eclass) vs x y,
    dom m = constant vs
    -> m $? x = Some y
    -> In x vs.
Proof.
  simplify.
  apply lookup_Some_dom in H0.
  sets.
Qed.

Local Hint Resolve dom_Forall dom_In : core.

Lemma preserve_varRepresentative : forall g g' x ec,
    preserve_reps g g'
    -> g.(Vars) = g'.(Vars)
    -> varRepresentative g x ec
    -> varRepresentative g' x ec.
Proof.
  unfold preserve_reps, varRepresentative; first_order.
  rewrite <- H0.
  first_order.
Qed.

Lemma preserve_varsMustAgree : forall g g' x1 x2,
    preserve_reps g g'
    -> g.(Vars) = g'.(Vars)
    -> varsMustAgree g x1 x2
    -> varsMustAgree g' x1 x2.
Proof.
  unfold varsMustAgree; first_order.
  do 2 esplit.
  eapply preserve_varRepresentative; eauto.
  unfold varRepresentative; eauto.
  eapply preserve_varRepresentative; eauto.
  unfold varRepresentative; eauto.
Qed.

Lemma preserve_rep : forall g g',
    preserve_reps g g'
    -> (forall y z, y <> z -> varsMustAgree g y z <-> varsMustAgree g' y z)
    -> rep g = rep g'.
Proof.
  unfold rep; simplify.
  apply sets_equal; propositional;
    eauto using preserve_varsMustAgree, preserve_reps_symm.

  cases (x1 ==v x2); subst; try equality.
  eapply H1; eauto.
  apply H0; auto.

  cases (x1 ==v x2); subst; try equality.
  eapply H1; eauto.
  apply H0; auto.
Qed.

Lemma representative_next : forall g ec,
    valid g
    -> representative g (NextEclass g) ec
    -> ec = NextEclass g.
Proof.
  invert 2; auto.
  apply LinksInBounds in H1; auto.
  linear_arithmetic.
Qed.

Lemma wpre_classOf : forall g x Q,
    (forall g' r,
        preserve_reps g g'
        -> g.(Vars) $<= g'.(Vars)
        -> (forall y z, y <> z -> varsMustAgree g y z <-> varsMustAgree g' y z)
        -> varRepresentative g' x r
        -> Q g' r)
    -> wpre g (classOf x) Q.
Proof.
  unfold classOf; simplify.
  unfold wpre; simplify.
  cases (Vars g $? x).

  generalize H0.
  change (wpre g (followLinks e) Q).
  apply wpre_followLinks; simplify.
  apply H; auto.
  rewrite H3; apply includes_refl.
  propositional; eauto using preserve_varsMustAgree, preserve_reps_symm.
  eapply preserve_varRepresentative; eauto.
  red; eauto.
  
  assert (Hvalid : valid {|
                       NextEclass := S (NextEclass g);
                       Vars := Vars g $+ (x, NextEclass g);
                       Links := Links g
                     |}).
  {
    constructor; simplify; eauto.
    cases (x ==v x0); subst; simplify; eauto.
    invert H1.
    linear_arithmetic.
    assert (ec < NextEclass g) by eauto.
    linear_arithmetic.
    assert (ec1 < NextEclass g) by eauto.
    linear_arithmetic.
    apply FiniteVars in H0.
    invert H0.
    exists (x :: x0).
    sets.
  }
  propositional.
  apply H; simplify.
  apply preserve_reps_Links; trivial.
  apply includes_intro; simplify; auto.

  propositional.
  invert H2; propositional.
  invert H2; propositional.
  invert H4; propositional.
  do 4 esplit; simplify; try eassumption.
  eapply representative_same_Links; try eassumption; trivial.
  eapply representative_same_Links; try eassumption; trivial.
  invert H2; propositional.
  invert H2; simplify; propositional.
  invert H4; simplify; propositional.
  cases (y ==v x); subst; simplify.
  invert H2.
  apply representative_same_Links with (g' := g) in H5; auto.
  apply representative_next in H5; auto; subst.
  apply representative_same_Links with (g' := g) in H6; auto.
  apply representative_le in H6; auto.
  apply VarsInBounds in H4; auto.
  linear_arithmetic.
  cases (z ==v x); subst; simplify.
  invert H4.
  apply representative_same_Links with (g' := g) in H6; auto.
  apply representative_next in H6; auto; subst.
  apply representative_same_Links with (g' := g) in H5; auto.
  apply representative_le in H5; auto.
  apply VarsInBounds in H2; auto.
  linear_arithmetic.
  apply representative_same_Links with (g' := g) in H5; auto.
  apply representative_same_Links with (g' := g) in H6; auto.
  unfold varsMustAgree, varRepresentative; eauto 7.

  exists (NextEclass g); simplify; propositional.
  constructor; simplify.
  cases (Links g $? NextEclass g); auto.
  assert (NextEclass g < NextEclass g) by eauto.
  linear_arithmetic.
Qed.

Lemma varRepresentative_lt : forall g x ec,
    valid g
    -> varRepresentative g x ec
    -> ec < NextEclass g.
Proof.
  invert 2; propositional.
  apply VarsInBounds in H0; auto.
  apply representative_le in H2; auto.
  linear_arithmetic.
Qed.

Theorem wpre_checkEqual : forall g x1 x2 Q,
    (forall g' r,
        rep g' = rep g
        -> (r = true <->
              (forall v, rep g' v -> forall v1 v2,
                    v.(Values) $? x1 = Some v1
                    -> v.(Values) $? x2 = Some v2
                    -> v1 = v2))
        -> Q g' r)
    -> wpre g (checkEqual x1 x2) Q.
Proof.
  unfold checkEqual; simplify.
  apply wpre_bind.
  apply wpre_classOf; simplify.
  eapply wpre_bind.
  apply wpre_classOf; simplify.
  apply wpre_ret; simplify.
  apply H.

  eapply preserve_rep; eauto using preserve_reps_trans, preserve_reps_symm.
  propositional.
  apply H2; auto.
  apply H6; auto.
  apply H6; auto.
  apply H2; auto.

  propositional.

  cases (r ==n r0); subst; try equality.
  assert (varsMustAgree g'0 x1 x2).
  invert H3; propositional.
  invert H7; propositional.
  do 4 esplit.
  eapply includes_lookup; try apply H5.
  eassumption.
  eapply preserve_reps_use; try eassumption.
  eassumption.
  assumption.
  red in H10.
  eauto.

  pose proof (FiniteVars _ H8).
  invert H10.
  assert (rep g'0 (literal_valuation g'0 x)) by eauto using rep_literal_valuation.
  invert H3; propositional.
  invert H7; propositional.
  eapply H9 in H10; clear H9.
  2: apply varRepresentative_literal_values_fwd; auto.
  2: eapply dom_In; eauto.
  2: do 2 esplit; try eapply includes_lookup; try apply H5; eauto.
  2: apply varRepresentative_literal_values_fwd; auto.
  2: eapply dom_In; eauto.
  2: do 2 esplit; eauto.
  cases (r ==n r0); subst; try equality.
  apply preserve_reps_use with (g' := g'0) in H13; eauto.
Qed.
