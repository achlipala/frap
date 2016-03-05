(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 7: Abstract Interpretation and Dataflow Analysis
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap Imp.

Set Implicit Arguments.


Module SimpleAbstractInterpreter.
  Record absint := {
    Typeof :> Set;
    (* This [:>] notation lets us treat any [absint] as its [Typeof],
     * automatically. *)
    Top : Typeof;
    (* A lattice element that describes all concrete values *)
    Constant : nat -> Typeof;
    (* Most accurate representation of a constant *)
    Add : Typeof -> Typeof -> Typeof;
    Subtract : Typeof -> Typeof -> Typeof;
    Multiply : Typeof -> Typeof -> Typeof;
    (* Abstract versions of arithmetic operators *)
    Join : Typeof -> Typeof -> Typeof;
    (* Least upper bound of two elements *)
    Represents : nat -> Typeof -> Prop
    (* Which lattice elements represent which numbers? *)
  }.

  Record absint_sound (a : absint) : Prop := {
    TopSound : forall n, a.(Represents) n a.(Top);
    
    ConstSound : forall n, a.(Represents) n (a.(Constant) n);

    AddSound : forall n na m ma, a.(Represents) n na
                                 -> a.(Represents) m ma
                                 -> a.(Represents) (n + m) (a.(Add) na ma);
    SubtractSound: forall n na m ma, a.(Represents) n na
                                     -> a.(Represents) m ma
                                     -> a.(Represents) (n - m) (a.(Subtract) na ma);
    MultiplySound : forall n na m ma, a.(Represents) n na
                                      -> a.(Represents) m ma
                                      -> a.(Represents) (n * m) (a.(Multiply) na ma);

    AddMonotone : forall na na' ma ma', (forall n, a.(Represents) n na -> a.(Represents) n na')
                                        -> (forall n, a.(Represents) n ma -> a.(Represents) n ma')
                                        -> (forall n, a.(Represents) n (a.(Add) na ma)
                                                      -> a.(Represents) n (a.(Add) na' ma'));
    SubtractMonotone : forall na na' ma ma', (forall n, a.(Represents) n na -> a.(Represents) n na')
                                             -> (forall n, a.(Represents) n ma -> a.(Represents) n ma')
                                             -> (forall n, a.(Represents) n (a.(Subtract) na ma)
                                                           -> a.(Represents) n (a.(Subtract) na' ma'));
    MultiplyMonotone : forall na na' ma ma', (forall n, a.(Represents) n na -> a.(Represents) n na')
                                             -> (forall n, a.(Represents) n ma -> a.(Represents) n ma')
                                             -> (forall n, a.(Represents) n (a.(Multiply) na ma)
                                                           -> a.(Represents) n (a.(Multiply) na' ma'));

    JoinSoundLeft : forall x y n, a.(Represents) n x
                                  -> a.(Represents) n (a.(Join) x y);
    JoinSoundRight : forall x y n, a.(Represents) n y
                                   -> a.(Represents) n (a.(Join) x y)
  }.

  Hint Resolve TopSound ConstSound AddSound SubtractSound MultiplySound
       AddMonotone SubtractMonotone MultiplyMonotone
       JoinSoundLeft JoinSoundRight.

  Definition astate (a : absint) := fmap var a.
  Definition astates (a : absint) := fmap cmd (astate a).

  Fixpoint absint_interp (e : arith) a (s : astate a) : a :=
    match e with
    | Const n => a.(Constant) n
    | Var x => match s $? x with
               | None => a.(Top)
               | Some xa => xa
               end
    | Plus e1 e2 => a.(Add) (absint_interp e1 s) (absint_interp e2 s)
    | Minus e1 e2 => a.(Subtract) (absint_interp e1 s) (absint_interp e2 s)
    | Times e1 e2 => a.(Multiply) (absint_interp e1 s) (absint_interp e2 s)
    end.

  Fixpoint absint_step a (s : astate a) (c : cmd) (wrap : cmd -> cmd) : option (astates a) :=
    match c with
    | Skip => None
    | Assign x e => Some ($0 $+ (wrap Skip, s $+ (x, absint_interp e s)))
    | Sequence c1 c2 =>
      match absint_step s c1 (fun c => wrap (Sequence c c2)) with
      | None => Some ($0 $+ (wrap c2, s))
      | v => v
      end
    | If e then_ else_ => Some ($0 $+ (wrap then_, s) $+ (wrap else_, s))
    | While e body => Some ($0 $+ (wrap Skip, s) $+ (wrap (Sequence body (While e body)), s))
    end.

  Definition compatible1 a (s : astate a) (v : valuation) : Prop :=
    forall x xa, s $? x = Some xa
                 -> exists n, v $? x = Some n
                              /\ a.(Represents) n xa.

  Theorem absint_interp_ok : forall a, absint_sound a
    -> forall (s : astate a) v e,
      compatible1 s v
      -> a.(Represents) (interp e v) (absint_interp e s).
  Proof.
    induct e; simplify; eauto.
    cases (s $? x); auto.
    unfold compatible1 in H0.
    apply H0 in Heq.
    invert Heq.
    propositional.
    rewrite H2.
    assumption.
  Qed.

  Lemma compatible1_add : forall a (s : astate a) v x na n,
    compatible1 s v
    -> a.(Represents) n na
    -> compatible1 (s $+ (x, na)) (v $+ (x, n)).
  Proof.
    unfold compatible1; simplify.
    cases (x ==v x0); simplify; eauto.
    invert H1; eauto.
  Qed.

  Hint Resolve compatible1_add absint_interp_ok.

  Lemma command_equal : forall c1 c2 : cmd, sumbool (c1 = c2) (c1 <> c2).
  Proof.
    repeat decide equality.
  Qed.

  Theorem absint_step_ok : forall a, absint_sound a
    -> forall (s : astate a) v, compatible1 s v
    -> forall c v' c', step (v, c) (v', c')
                       -> forall wrap, exists ss s', absint_step s c wrap = Some ss
                                                     /\ ss $? wrap c' = Some s'
                                                     /\ compatible1 s' v'.
  Proof.
    induct 2; simplify.

    do 2 eexists; propositional.
    simplify; equality.
    eauto.

    eapply IHstep in H0; auto.
    invert H0.
    invert H2.
    propositional.
    rewrite H2.
    eauto.

    do 2 eexists; propositional.
    simplify; equality.
    assumption.

    do 2 eexists; propositional.
    cases (command_equal (wrap c') (wrap else_)).
    simplify; equality.
    simplify; equality.
    assumption.

    do 2 eexists; propositional.
    simplify; equality.
    assumption.

    do 2 eexists; propositional.
    simplify; equality.
    assumption.

    do 2 eexists; propositional.
    cases (command_equal (wrap Skip) (wrap (body;; while e loop body done))).
    simplify; equality.
    simplify; equality.
    assumption.
  Qed.

  Inductive abs_step a : astate a * cmd -> astate a * cmd -> Prop :=
  | AbsStep : forall s c ss s' c',
    absint_step s c (fun x => x) = Some ss
    -> ss $? c' = Some s'
    -> abs_step (s, c) (s', c').

  Hint Constructors abs_step.

  Definition absint_trsys a (c : cmd) := {|
    Initial := {($0, c)};
    Step := abs_step (a := a)
  |}.

  Inductive Rabsint a : valuation * cmd -> astate a * cmd -> Prop :=
  | RAbsint : forall v s c,
    compatible1 s v
    -> Rabsint (v, c) (s, c).

  Hint Constructors abs_step Rabsint.

  Theorem absint_simulates : forall a v c,
    absint_sound a
    -> simulates (Rabsint (a := a)) (trsys_of v c) (absint_trsys a c).
  Proof.
    simplify.
    constructor; simplify.

    exists ($0, c); propositional.
    subst.
    constructor.
    unfold compatible1.
    simplify.
    equality.

    invert H0.
    cases st1'.
    eapply absint_step_ok in H1; eauto.
    invert H1.
    invert H0.
    propositional.
    eauto.
  Qed.

  Definition merge_astate a : astate a -> astate a -> astate a :=
    merge (fun x y =>
             match x with
             | None => None
             | Some x' =>
               match y with
               | None => None
               | Some y' => Some (a.(Join) x' y')
               end
             end).

  Definition merge_astates a : astates a -> astates a -> astates a :=
    merge (fun x y =>
             match x with
             | None => y
             | Some x' =>
               match y with
               | None => Some x'
               | Some y' => Some (merge_astate x' y')
               end
             end).

  Inductive oneStepClosure a : astates a -> astates a -> Prop :=
  | OscNil :
    oneStepClosure $0 $0
  | OscCons : forall ss c s ss',
    oneStepClosure ss ss'
    -> oneStepClosure (ss $+ (c, s)) (match absint_step s c (fun x => x) with
                                      | None => ss'
                                      | Some ss'' => merge_astates ss'' ss'
                                      end).

  Inductive interpret a : astates a -> astates a -> Prop :=
  | InterpretDone : forall ss,
    oneStepClosure ss ss
    -> interpret ss ss

  | InterpretStep : forall ss ss' ss'',
    oneStepClosure ss ss'
    -> interpret (merge_astates ss ss') ss''
    -> interpret ss ss''.

  Definition subsumed a (s1 s2 : astate a) :=
    forall x, match s1 $? x with
              | None => s2 $? x = None
              | Some xa1 =>
                forall xa2, s2 $? x = Some xa2
                            -> forall n, a.(Represents) n xa1
                                         -> a.(Represents) n xa2
              end.

  Theorem subsumed_refl : forall a (s : astate a),
    subsumed s s.
  Proof.
    unfold subsumed; simplify.
    cases (s $? x); equality.
  Qed.

  Hint Resolve subsumed_refl.

  Definition subsumeds a (ss1 ss2 : astates a) :=
    forall c s1, ss1 $? c = Some s1
                 -> exists s2, ss2 $? c = Some s2
                               /\ subsumed s1 s2.

  Theorem subsumeds_refl : forall a (ss : astates a),
    subsumeds ss ss.
  Proof.
    unfold subsumeds; simplify; eauto.
  Qed.

  Hint Resolve subsumeds_refl.

  Lemma oneStepClosure_sound : forall a, absint_sound a
    -> forall ss ss' : astates a, oneStepClosure ss ss'
    -> forall c s s' c', ss $? c = Some s
                         -> abs_step (s, c) (s', c')
                            -> exists s'', ss' $? c' = Some s''
                                           /\ subsumed s' s''.
  Proof.
    induct 2; simplify.

    equality.

    cases (command_equal c c0); subst; simplify.

    invert H1.
    invert H2.
    rewrite H5.
    unfold merge_astates; simplify.
    rewrite H7.
    cases (ss' $? c').
    eexists; propositional.
    unfold subsumed; simplify.
    unfold merge_astate; simplify.
    cases (s' $? x); try equality.
    cases (a0 $? x); simplify; try equality.
    invert H1; eauto.
    eauto.

    apply IHoneStepClosure in H2; auto.
    invert H2; propositional.
    cases (absint_step s c (fun x => x)); eauto.
    unfold merge_astates; simplify.
    rewrite H2.
    cases (a0 $? c'); eauto.
    eexists; propositional.
    unfold subsumed; simplify.
    unfold merge_astate; simplify.
    specialize (H4 x0).
    cases (s' $? x0).
    cases (a1 $? x0); try equality.
    cases (x $? x0); try equality.
    invert 1.
    eauto.

    rewrite H4.
    cases (a1 $? x0); equality.
  Qed.

  Lemma subsumed_add : forall a, absint_sound a
    -> forall (s1 s2 : astate a) x v1 v2,
    subsumed s1 s2
    -> (forall n, a.(Represents) n v1 -> a.(Represents) n v2)
    -> subsumed (s1 $+ (x, v1)) (s2 $+ (x, v2)).
  Proof.
    unfold subsumed; simplify.
    cases (x ==v x0); subst; simplify; eauto.
    invert H2; eauto.
    specialize (H0 x0); eauto.
  Qed.

  Hint Resolve subsumed_add.

  Lemma subsumeds_add : forall a (ss1 ss2 : astates a) c s1 s2,
    subsumeds ss1 ss2
    -> subsumed s1 s2
    -> subsumeds (ss1 $+ (c, s1)) (ss2 $+ (c, s2)).
  Proof.
    unfold subsumeds; simplify.
    cases (command_equal c c0); subst; simplify; eauto.
    invert H1; eauto.
  Qed.

  Hint Resolve subsumeds_add.

  Lemma subsumed_use : forall a (s s' : astate a) x n t0 t,
    s $? x = Some t0
    -> subsumed s s'
    -> s' $? x = Some t
    -> Represents a n t0
    -> Represents a n t.
  Proof.
    unfold subsumed; simplify.
    specialize (H0 x).
    rewrite H in H0.
    eauto.
  Qed.

  Lemma subsumed_use_empty : forall a (s s' : astate a) x n t0 t,
    s $? x = None
    -> subsumed s s'
    -> s' $? x = Some t
    -> Represents a n t0
    -> Represents a n t.
  Proof.
    unfold subsumed; simplify.
    specialize (H0 x).
    rewrite H in H0.
    equality.
  Qed.

  Hint Resolve subsumed_use subsumed_use_empty.

  Lemma absint_interp_monotone : forall a, absint_sound a
    -> forall (s : astate a) e s' n,
      a.(Represents) n (absint_interp e s)
      -> subsumed s s'
      -> a.(Represents) n (absint_interp e s').
  Proof.
    induct e; simplify; eauto.

    cases (s' $? x); eauto.
    cases (s $? x); eauto.
  Qed.

  Hint Resolve absint_interp_monotone.

  Lemma absint_step_monotone_None : forall a (s : astate a) c wrap,
      absint_step s c wrap = None
      -> forall s' : astate a, absint_step s' c wrap = None.
  Proof.
    induct c; simplify; try equality.
    cases (absint_step s c1 (fun c => wrap (c;; c2))); equality.
  Qed.

  Lemma absint_step_monotone : forall a, absint_sound a
      -> forall (s : astate a) c wrap ss,
        absint_step s c wrap = Some ss
        -> forall s', subsumed s s'
                      -> exists ss', absint_step s' c wrap = Some ss'
                                     /\ subsumeds ss ss'.
  Proof.
    induct c; simplify.

    equality.

    invert H0.
    eexists; propositional.
    eauto.
    apply subsumeds_add; eauto.

    cases (absint_step s c1 (fun c => wrap (c;; c2))).

    invert H0.
    eapply IHc1 in Heq; eauto.
    invert Heq; propositional.
    rewrite H2; eauto.

    invert H0.
    eapply absint_step_monotone_None in Heq; eauto.
    rewrite Heq; eauto.

    invert H0; eauto.

    invert H0; eauto.
  Qed.

  Lemma abs_step_monotone : forall a, absint_sound a
    -> forall (s : astate a) c s' c',
      abs_step (s, c) (s', c')
      -> forall s1, subsumed s s1
                    -> exists s1', abs_step (s1, c) (s1', c')
                                   /\ subsumed s' s1'.
  Proof.
    invert 2; simplify.
    eapply absint_step_monotone in H4; eauto.
    invert H4; propositional.
    apply H3 in H6.
    invert H6; propositional; eauto.
  Qed.    

  Lemma subsumed_trans : forall a (s1 s2 s3 : astate a),
    subsumed s1 s2
    -> subsumed s2 s3
    -> subsumed s1 s3.
  Proof.
    unfold subsumed; simplify.
    specialize (H x); specialize (H0 x).
    cases (s1 $? x); simplify.
    cases (s2 $? x); eauto.
    cases (s2 $? x); eauto.
    equality.
  Qed.

  Lemma interpret_sound' : forall c a, absint_sound a
    -> forall ss ss' : astates a, interpret ss ss'
      -> ss $? c = Some $0
      -> invariantFor (absint_trsys a c) (fun p => exists s, ss' $? snd p = Some s
                                                             /\ subsumed (fst p) s).
  Proof.
    induct 2; simplify.

    apply invariant_induction; simplify; propositional; subst; simplify; eauto.

    invert H2; propositional.
    cases s.
    cases s'.
    simplify.
    eapply abs_step_monotone in H3; eauto.
    invert H3; propositional.
    eapply oneStepClosure_sound in H3; eauto.
    invert H3; propositional.
    eexists; propositional.
    eassumption.
    eauto using subsumed_trans.

    apply IHinterpret.
    unfold merge_astates; simplify.
    rewrite H2.
    cases (ss' $? c); trivial.
    unfold merge_astate; simplify.
    f_equal.
    maps_equal.
  Qed.

  Theorem interpret_sound : forall c a (ss : astates a),
    absint_sound a
    -> interpret ($0 $+ (c, $0)) ss
    -> invariantFor (absint_trsys a c) (fun p => exists s, ss $? snd p = Some s
                                                           /\ subsumed (fst p) s).
  Proof.
    simplify.
    eapply interpret_sound'; eauto.
    simplify; equality.
  Qed.


  (** * Example: even-odd analysis *)

  Inductive parity := Even | Odd | Either.

  Definition isEven (n : nat) := exists k, n = k * 2.
  Definition isOdd (n : nat) := exists k, n = k * 2 + 1.

  Theorem decide_parity : forall n, isEven n \/ isOdd n.
  Proof.
    induct n; simplify; propositional.

    left; exists 0; linear_arithmetic.

    invert H.
    right.
    exists x; linear_arithmetic.

    invert H.
    left.
    exists (x + 1); linear_arithmetic.
  Qed.

  Theorem notEven_odd : forall n, ~isEven n -> isOdd n.
  Proof.
    simplify.
    assert (isEven n \/ isOdd n).
    apply decide_parity.
    propositional.
  Qed.

  Theorem odd_notEven : forall n, isOdd n -> ~isEven n.
  Proof.
    propositional.
    invert H.
    invert H0.
    linear_arithmetic.
  Qed.

  Theorem isEven_0 : isEven 0.
  Proof.
    exists 0; linear_arithmetic.
  Qed.

  Theorem isEven_1 : ~isEven 1.
  Proof.
    propositional; invert H; linear_arithmetic.
  Qed.

  Theorem isEven_S_Even : forall n, isEven n -> ~isEven (S n).
  Proof.
    propositional; invert H; invert H0; linear_arithmetic.
  Qed.

  Theorem isEven_S_Odd : forall n, ~isEven n -> isEven (S n).
  Proof.
    propositional.
    apply notEven_odd in H.
    invert H.
    exists (x + 1); linear_arithmetic.
  Qed.

  Hint Resolve isEven_0 isEven_1 isEven_S_Even isEven_S_Odd.  

  Definition parity_flip (p : parity) :=
    match p with
    | Even => Odd
    | Odd => Even
    | Either => Either
    end.

  Fixpoint parity_const (n : nat) :=
    match n with
    | O => Even
    | S n' => parity_flip (parity_const n')
    end.

  Definition parity_add (x y : parity) :=
    match x, y with
    | Even, Even => Even
    | Odd, Odd => Even
    | Even, Odd => Odd
    | Odd, Even => Odd
    | _, _ => Either
    end.

  Definition parity_subtract (x y : parity) :=
    match x, y with
    | Even, Even => Even
    | _, _ => Either
    end.
  (* Note subtleties with [Either]s above, to deal with underflow at zero! *)

  Definition parity_multiply (x y : parity) :=
    match x, y with
    | Even, Even => Even
    | Odd, Odd => Odd
    | Even, Odd => Even
    | Odd, Even => Even
    | _, _ => Either
    end.

  Definition parity_join (x y : parity) :=
    match x, y with
    | Even, Even => Even
    | Odd, Odd => Odd
    | _, _ => Either
    end.

  Inductive parity_rep : nat -> parity -> Prop :=
  | PrEven : forall n,
    isEven n
    -> parity_rep n Even
  | PrOdd : forall n,
    ~isEven n
    -> parity_rep n Odd
  | PrEither : forall n,
    parity_rep n Either.

  Hint Constructors parity_rep.

  Definition parity_absint := {|
    Top := Either;
    Constant := parity_const;
    Add := parity_add;
    Subtract := parity_subtract;
    Multiply := parity_multiply;
    Join := parity_join;
    Represents := parity_rep
  |}.

  Lemma parity_const_sound : forall n,
    parity_rep n (parity_const n).
  Proof.
    induct n; simplify; eauto.
    cases (parity_const n); simplify; eauto.
    invert IHn; eauto.
    invert IHn; eauto.
  Qed.

  Hint Resolve parity_const_sound.

  Lemma even_not_odd :
    (forall n, parity_rep n Even -> parity_rep n Odd)
    -> False.
  Proof.
    simplify.
    specialize (H 0).
    assert (parity_rep 0 Even) by eauto.
    apply H in H0.
    invert H0.
    apply H1.
    auto.
  Qed.

  Lemma odd_not_even :
    (forall n, parity_rep n Odd -> parity_rep n Even)
    -> False.
  Proof.
    simplify.
    specialize (H 1).
    assert (parity_rep 1 Odd) by eauto.
    apply H in H0.
    invert H0.
    invert H1.
    linear_arithmetic.
  Qed.

  Hint Resolve even_not_odd odd_not_even.

  Theorem parity_sound : absint_sound parity_absint.
  Proof.
    constructor; simplify; eauto;
    repeat match goal with
           | [ H : parity_rep _ _ |- _ ] => invert H
           | [ H : ~isEven _ |- _ ] => apply notEven_odd in H; invert H
           | [ H : isEven _ |- _ ] => invert H
           | [ p : parity |- _ ] => cases p; simplify; try equality
           end; try solve [ exfalso; eauto ]; try (constructor; try apply odd_notEven).
    exists (x0 + x); ring.
    exists (x0 + x); ring.
    exists (x0 + x); ring.
    exists (x0 + x + 1); ring.
    exists (x - x0); linear_arithmetic.
    exists (x * x0 * 2); ring.
    exists ((x * 2 + 1) * x0); ring.
    exists ((x * 2 + 1) * x0); ring.
    exists (2 * x * x0 + x + x0); ring.
    exists x; ring.
    exists x; ring.
    exists x; ring.
    exists x; ring.
    exists x; ring.
    exists x; ring.
    exists x; ring.
    exists x; ring.
    exists x; ring.
    exists x; ring.
    exists x; ring.
    exists x0; ring.
    exists x0; ring.
  Qed.

  Definition loopy :=
    "n" <- 100;;
    "a" <- 0;;
    while "n" loop
      "a" <- "a" + "n";;
      "n" <- "n" - 2
    done.

  Hint Rewrite merge_empty1 merge_empty2 using solve [ eauto 1 ].
  Hint Rewrite merge_empty1_alt merge_empty2_alt using congruence.

  Lemma merge_astates_fok : forall x : option (astate parity_absint),
    match x with Some x' => Some x' | None => None end = x.
  Proof.
    simplify; cases x; equality.
  Qed.

  Lemma merge_astates_fok2 : forall x (y : option (astate parity_absint)),
      match y with
      | Some y' => Some (merge_astate x y')
      | None => Some x
      end = None -> False.
  Proof.
    simplify; cases y; equality.
  Qed.

  Hint Resolve merge_astates_fok merge_astates_fok2.

  Hint Rewrite merge_add1 using solve [ eauto | unfold Sets.In; simplify; equality ].
  Hint Rewrite merge_add1_alt using solve [ congruence | unfold Sets.In; simplify; equality ].

  Ltac inList x xs :=
    match xs with
    | (x, _) => constr:true
    | (_, ?xs') => inList x xs'
    | _ => constr:false
    end.

  Ltac maybe_simplify_map m found kont :=
    match m with
    | @empty ?A ?B => kont (@empty A B)
    | ?m' $+ (?k, ?v) =>
      let iL := inList k found in
      match iL with
      | true => maybe_simplify_map m' found kont
      | false =>
        maybe_simplify_map m' (k, found) ltac:(fun m' => kont (m' $+ (k, v)))
      end
    end.

  Ltac simplify_map' m found kont :=
    match m with
    | ?m' $+ (?k, ?v) =>
      let iL := inList k found in
        match iL with
        | true => maybe_simplify_map m' found kont
        | false =>
          simplify_map' m' (k, found) ltac:(fun m' => kont (m' $+ (k, v)))
        end
    end.

  Ltac simplify_map :=
    match goal with
    | [ |- context[?m $+ (?k, ?v)] ] =>
      simplify_map' (m $+ (k, v)) tt ltac:(fun m' =>
                                             replace (m $+ (k, v)) with m' by maps_equal)
    end.

  Definition easy :=
    "n" <- 10;;
    while "n" loop
      "n" <- "n" - 2
    done.

  Theorem easy_even : forall v n,
    isEven n
    -> invariantFor (trsys_of v easy) (fun p => exists n, fst p $? "n" = Some n /\ isEven n).
  Proof.
    simplify.
    eapply invariant_weaken.

    unfold easy.
    eapply invariant_simulates.
    apply absint_simulates with (a := parity_absint).
    apply parity_sound.

    apply interpret_sound.
    apply parity_sound.

    Ltac interpret1 := eapply InterpretStep; [ repeat (apply OscNil || apply OscCons)
                                             | unfold merge_astates, merge_astate;
                                               simplify; repeat simplify_map ].

    interpret1.
    interpret1.
    interpret1.

    eapply InterpretStep.
    repeat (apply OscNil || apply OscCons).
    simplify.
    unfold merge_astates, merge_astate.
    simplify.

    interpret1.

    simplify.

    simplify_map.

    Ltac interpret1 :=
      eapply InterpretStep; [ (repeat (apply OscNil || eapply OscCons);
                                invert 1; repeat (match goal with
                                                  | [ H : step _ _ |- _ ] => invert H
                                                  | [ _ : match ?E with
                                                          | Some n => n
                                                          | None => 0
                                                          end = 0 |- _ ] => cases E; try linear_arithmetic
                                                  end; simplify); simplify;
                                try solve [ eapply compatible_skip; eassumption
                                          | eapply compatible_skip2; eassumption || congruence
                                          | eapply compatible_const; eassumption ]) | ];
      repeat match goal with
             | [ |- context[@add ?A ?B ?m _ _] ] =>
               match m with
               | @empty _ _ => fail 1
               | _ => unify m (@empty A B)
               end
             end.

    interpret1.
    unfold merge_astates, merge_astate; simplify.
    interpret1.
    unfold merge_astates, merge_astate; simplify.
    simplify_map.
    interpret1.
    unfold merge_astates, merge_astate; simplify.
    simplify_map.
    interpret1.
