(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 9: Compiler Correctness
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.


(* In this chapter, we'll work with a small variation on the imperative language
 * from the previous chapter. *)

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (then_ else_ : cmd)
| While (e : arith) (body : cmd)
| Output (e : arith).
(* The last constructor above is the new one, for generating an _output_ value,
 * say to display in a terminal.  By including this operation, we create
 * interesting differences between the behaviors of different nonterminating
 * programs.  A correct compiler should preserve these differences. *)

(* The next span of notations and definitions is the same as last chapter. *)

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' then_ 'else' else_ 'done'" := (If e%arith then_ else_) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

Definition valuation := fmap var nat.
Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

Inductive context :=
| Hole
| CSeq (C : context) (c : cmd).

Inductive plug : context -> cmd -> cmd -> Prop :=
| PlugHole : forall c, plug Hole c c
| PlugSeq : forall c C c' c2,
  plug C c c'
  -> plug (CSeq C c2) c (Sequence c' c2).

(* Here's our first difference.  We add a new parameter to [step0], giving a
 * _label_ that records which _externally visible effect_ the step has.  For
 * this language, output is the only externally visible effect, so a label
 * records an optional output value. *)

Inductive step0 : valuation * cmd -> option nat -> valuation * cmd -> Prop :=
| Step0Assign : forall v x e,
  step0 (v, Assign x e) None (v $+ (x, interp e v), Skip)
| Step0Seq : forall v c2,
  step0 (v, Sequence Skip c2) None (v, c2)
| Step0IfTrue : forall v e then_ else_,
  interp e v <> 0
  -> step0 (v, If e then_ else_) None (v, then_)
| Step0IfFalse : forall v e then_ else_,
  interp e v = 0
  -> step0 (v, If e then_ else_) None (v, else_)
| Step0WhileTrue : forall v e body,
  interp e v <> 0
  -> step0 (v, While e body) None (v, Sequence body (While e body))
| Step0WhileFalse : forall v e body,
  interp e v = 0
  -> step0 (v, While e body) None (v, Skip)
| Step0Output : forall v e,
  step0 (v, Output e) (Some (interp e v)) (v, Skip).

Inductive cstep : valuation * cmd -> option nat -> valuation * cmd -> Prop :=
| CStep : forall C v c l v' c' c1 c2,
  plug C c c1
  -> step0 (v, c) l (v', c')
  -> plug C c' c2
  -> cstep (v, c1) l (v', c2).

(* To characterize correct compilation, it is helpful to define a relation to
 * capture which output _traces_ a command might generate.  Note that, for us, a
 * trace is a list of output values, where [None] labels are simply dropped. *)
Inductive generate : valuation * cmd -> list nat -> Prop :=
| GenDone : forall vc,
  generate vc []
| GenSilent : forall vc vc' ns,
  cstep vc None vc'
  -> generate vc' ns
  -> generate vc ns
| GenOutput : forall vc n vc' ns,
  cstep vc (Some n) vc'
  -> generate vc' ns
  -> generate vc (n :: ns).

Hint Constructors plug step0 cstep generate.

Definition traceInclusion (vc1 vc2 : valuation * cmd) :=
  forall ns, generate vc1 ns -> generate vc2 ns.
Infix "<|" := traceInclusion (at level 70).

Definition traceEquivalence (vc1 vc2 : valuation * cmd) :=
  vc1 <| vc2 /\ vc2 <| vc1.
Infix "=|" := traceEquivalence (at level 70).


(** * Basic Simulation Arguments and Optimizing Expressions *)

Fixpoint cfoldArith (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 =>
    let e1' := cfoldArith e1 in
    let e2' := cfoldArith e2 in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 + n2)
    | _, _ => Plus e1' e2'
    end
  | Minus e1 e2 =>
    let e1' := cfoldArith e1 in
    let e2' := cfoldArith e2 in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 - n2)
    | _, _ => Minus e1' e2'
    end
  | Times e1 e2 =>
    let e1' := cfoldArith e1 in
    let e2' := cfoldArith e2 in
    match e1', e2' with
    | Const n1, Const n2 => Const (n1 * n2)
    | _, _ => Times e1' e2'
    end
  end.

Theorem cfoldArith_ok : forall v e,
    interp (cfoldArith e) v = interp e v.
Proof.
  induct e; simplify; try equality;
  repeat (match goal with
          | [ |- context[match ?E with _ => _ end] ] => cases E
          | [ H : _ = interp _ _ |- _ ] => rewrite <- H
          end; simplify); subst; ring.
Qed.  

Fixpoint cfoldExprs (c : cmd) : cmd :=
  match c with
  | Skip => c
  | Assign x e => Assign x (cfoldArith e)
  | Sequence c1 c2 => Sequence (cfoldExprs c1) (cfoldExprs c2)
  | If e then_ else_ => If (cfoldArith e) (cfoldExprs then_) (cfoldExprs else_)
  | While e body => While (cfoldArith e) (cfoldExprs body)
  | Output e => Output (cfoldArith e)
  end.

Theorem skip_or_step : forall v c,
    c = Skip
    \/ exists v' l c', cstep (v, c) l (v', c').
Proof.
  induct c; simplify; first_order; subst;
    try match goal with
        | [ H : cstep _ _ _ |- _ ] => invert H
        end;
    try match goal with
        | [ |- context[cstep (?v, If ?e _ _)] ] => cases (interp e v ==n 0)
        | [ |- context[cstep (?v, While ?e _)] ] => cases (interp e v ==n 0)
        end; eauto 10.
Qed.

Lemma deterministic0 : forall vc l vc',
  step0 vc l vc'
  -> forall l' vc'', step0 vc l' vc''
                     -> l = l' /\ vc'' = vc'.
Proof.
  invert 1; invert 1; simplify; propositional.
Qed.

Theorem plug_function : forall C c1 c2, plug C c1 c2
  -> forall c2', plug C c1 c2'
  -> c2 = c2'.
Proof.
  induct 1; invert 1; eauto.
  apply IHplug in H5.
  equality.
Qed.

Lemma peel_cseq : forall C1 C2 c (c1 c2 : cmd),
    C1 = C2 /\ c1 = c2
    -> CSeq C1 c = CSeq C2 c /\ c1 = c2.
Proof.
  equality.
Qed.

Hint Resolve peel_cseq.

Lemma plug_deterministic : forall v C c1 c2, plug C c1 c2
  -> forall l vc1, step0 (v, c1) l vc1
  -> forall C' c1', plug C' c1' c2
  -> forall l' vc1', step0 (v, c1') l' vc1'
  -> C' = C /\ c1' = c1.
Proof.
  induct 1; invert 1; invert 1; invert 1; auto;
    try match goal with
        | [ H : plug _ _ _ |- _ ] => invert1 H
        end; eauto.
Qed.

Theorem deterministic : forall vc l vc',
  cstep vc l vc'
  -> forall l' vc'', cstep vc l' vc''
                     -> l = l' /\ vc' = vc''.
Proof.
  invert 1; invert 1; simplify.
  eapply plug_deterministic in H0; eauto.
  invert H0.
  eapply deterministic0 in H1; eauto.
  propositional; subst; auto.
  invert H0.
  auto.
  eapply plug_function in H2; eauto.
  equality.
Qed.

Section simulation.
  Variable R : valuation * cmd -> valuation * cmd -> Prop.

  Hypothesis one_step : forall vc1 vc2, R vc1 vc2
    -> forall vc1' l, cstep vc1 l vc1'
      -> exists vc2', cstep vc2 l vc2' /\ R vc1' vc2'.

  Hypothesis agree_on_termination : forall v1 v2 c2, R (v1, Skip) (v2, c2)
    -> c2 = Skip.

  Lemma simulation_fwd' : forall vc1 ns, generate vc1 ns
    -> forall vc2, R vc1 vc2
      -> generate vc2 ns.
  Proof.
    induct 1; simplify; eauto.

    eapply one_step in H; eauto.
    first_order.
    eauto.

    eapply one_step in H1; eauto.
    first_order.
    eauto.
  Qed.

  Theorem simulation_fwd : forall vc1 vc2, R vc1 vc2
    -> vc1 <| vc2.
  Proof.
    unfold traceInclusion; eauto using simulation_fwd'.
  Qed.

  Lemma simulation_bwd' : forall vc2 ns, generate vc2 ns
    -> forall vc1, R vc1 vc2
      -> generate vc1 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc1; cases vc.
    assert (c = Skip \/ exists v' l c', cstep (v, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H1; subst.
    invert H.
    invert H3.
    invert H4.
    specialize (one_step H1 H2).
    first_order.
    eapply deterministic in H; eauto.
    propositional; subst.
    eauto.

    cases vc1; cases vc.
    assert (c = Skip \/ exists v' l c', cstep (v, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H1; subst.
    invert H.
    invert H3.
    invert H4.
    specialize (one_step H1 H2).
    first_order.
    eapply deterministic in H; eauto.
    propositional; subst.
    eauto.
  Qed.

  Theorem simulation_bwd : forall vc1 vc2, R vc1 vc2
    -> vc2 <| vc1.
  Proof.
    unfold traceInclusion; eauto using simulation_bwd'.
  Qed.

  Theorem simulation : forall vc1 vc2, R vc1 vc2
    -> vc1 =| vc2.
  Proof.
    simplify; split; auto using simulation_fwd, simulation_bwd.
  Qed.
End simulation.

Lemma cfoldExprs_ok' : forall v1 c1 l v2 c2,
    step0 (v1, c1) l (v2, c2)
    -> step0 (v1, cfoldExprs c1) l (v2, cfoldExprs c2).
Proof.
  invert 1; simplify;
    try match goal with
        | [ _ : context[interp ?e ?v] |- _ ] => rewrite <- (cfoldArith_ok v e) in *
        | [ |- context[interp ?e ?v] ] => rewrite <- (cfoldArith_ok v e)
        end; eauto.
Qed.

Fixpoint cfoldExprsContext (C : context) : context :=
  match C with
  | Hole => Hole
  | CSeq C c => CSeq (cfoldExprsContext C) (cfoldExprs c)
  end.

Lemma plug_cfoldExprs1 : forall C c1 c2, plug C c1 c2
  -> plug (cfoldExprsContext C) (cfoldExprs c1) (cfoldExprs c2).
Proof.
  induct 1; simplify; eauto.
Qed.

Hint Resolve plug_cfoldExprs1.

Lemma cfoldExprs_ok : forall v c,
    (v, c) =| (v, cfoldExprs c).
Proof.
  simplify.
  apply simulation with (R := fun vc1 vc2 => fst vc1 = fst vc2
                                             /\ snd vc2 = cfoldExprs (snd vc1));
    simplify; propositional.

  invert H0; simplify; subst.
  apply cfoldExprs_ok' in H3.
  cases vc2; simplify; subst.
  eauto 7.
Qed.


(** * Simulations That Allow Skipping Steps *)

Fixpoint cfold (c : cmd) : cmd :=
  match c with
  | Skip => c
  | Assign x e => Assign x (cfoldArith e)
  | Sequence c1 c2 => Sequence (cfold c1) (cfold c2)
  | If e then_ else_ =>
    let e' := cfoldArith e in
    match e' with
    | Const n => if n ==n 0 then cfold else_ else cfold then_
    | _ => If e' (cfold then_) (cfold else_)
    end
  | While e body => While (cfoldArith e) (cfold body)
  | Output e => Output (cfoldArith e)
  end.

Section simulation_skipping.
  Variable R : nat -> valuation * cmd -> valuation * cmd -> Prop.

  Hypothesis one_step : forall n vc1 vc2, R n vc1 vc2
    -> forall vc1' l, cstep vc1 l vc1'
                      -> (exists n', n = S n' /\ l = None /\ R n' vc1' vc2)
                         \/ exists n' vc2', cstep vc2 l vc2' /\ R n' vc1' vc2'.

  Hypothesis agree_on_termination : forall n v1 v2 c2, R n (v1, Skip) (v2, c2)
    -> c2 = Skip.

  Lemma simulation_skipping_fwd' : forall vc1 ns, generate vc1 ns
    -> forall n vc2, R n vc1 vc2
      -> generate vc2 ns.
  Proof.
    induct 1; simplify; eauto.

    eapply one_step in H; eauto.
    first_order.
    eauto.

    eapply one_step in H1; eauto.
    first_order.
    equality.
    eauto.
  Qed.

  Theorem simulation_skipping_fwd : forall n vc1 vc2, R n vc1 vc2
    -> vc1 <| vc2.
  Proof.
    unfold traceInclusion; eauto using simulation_skipping_fwd'.
  Qed.

  Lemma generate_Skip : forall v a ns,
      generate (v, Skip) (a :: ns)
      -> False.
  Proof.
    induct 1; simplify.

    invert H.
    invert H3.
    invert H4.

    invert H.
    invert H3.
    invert H4.
  Qed.

  Notation silent_cstep := (fun a b => cstep a None b).

  Lemma match_step : forall n vc2 l vc2' vc1,
      cstep vc2 l vc2'
      -> R n vc1 vc2
      -> exists vc1' vc1'' n', silent_cstep^* vc1 vc1'
                              /\ cstep vc1' l vc1''
                              /\ R n' vc1'' vc2'.
  Proof.
    induct n; simplify.

    cases vc1; cases vc2.
    assert (c = Skip \/ exists v' l' c', cstep (v, c) l' (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H0; subst.
    invert H.
    invert H2.
    invert H3.
    eapply one_step in H0; eauto.
    first_order; subst.
    equality.
    eapply deterministic in H; eauto.
    first_order; subst.
    eauto 6.
    
    cases vc1; cases vc2.
    assert (c = Skip \/ exists v' l' c', cstep (v, c) l' (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H0; subst.
    invert H.
    invert H2.
    invert H3.
    eapply one_step in H0; eauto.
    first_order; subst.
    invert H0.
    eapply IHn in H3; eauto.
    first_order.
    eauto 8.
    eapply deterministic in H; eauto.
    first_order; subst.
    eauto 6.
  Qed.

  Lemma silent_generate : forall ns vc vc',
      silent_cstep^* vc vc'
      -> generate vc' ns
      -> generate vc ns.
  Proof.
    induct 1; eauto.
  Qed.

  Hint Resolve silent_generate.

  Lemma simulation_skipping_bwd' : forall ns vc2, generate vc2 ns
    -> forall n vc1, R n vc1 vc2
      -> generate vc1 ns.
  Proof.
    induct 1; simplify; eauto.

    eapply match_step in H1; eauto.
    first_order.
    eauto.

    eapply match_step in H1; eauto.
    first_order.
    eauto.
  Qed.

  Theorem simulation_skipping_bwd : forall n vc1 vc2, R n vc1 vc2
    -> vc2 <| vc1.
  Proof.
    unfold traceInclusion; eauto using simulation_skipping_bwd'.
  Qed.

  Theorem simulation_skipping : forall n vc1 vc2, R n vc1 vc2
    -> vc1 =| vc2.
  Proof.
    simplify; split; eauto using simulation_skipping_fwd, simulation_skipping_bwd.
  Qed.
End simulation_skipping.

Fixpoint countIfs (c : cmd) : nat :=
  match c with
  | Skip => 0
  | Assign _ _ => 0
  | Sequence c1 c2 => countIfs c1 + countIfs c2
  | If _ c1 c2 => 1 + countIfs c1 + countIfs c2
  | While _ c1 => countIfs c1
  | Output _ => 0
  end.

Hint Extern 1 (_ < _) => linear_arithmetic.

Lemma cfold_ok' : forall v1 c1 l v2 c2,
    step0 (v1, c1) l (v2, c2)
    -> step0 (v1, cfold c1) l (v2, cfold c2)
       \/ (l = None /\ v1 = v2 /\ cfold c1 = cfold c2 /\ countIfs c2 < countIfs c1).
Proof.
  invert 1; simplify;
    try match goal with
        | [ _ : context[interp ?e ?v] |- _ ] => rewrite <- (cfoldArith_ok v e) in *
        | [ |- context[interp ?e ?v] ] => rewrite <- (cfoldArith_ok v e)
        end;
    repeat match goal with
           | [ |- context[match ?E with _ => _ end] ] => cases E; subst; simplify
           end; propositional; eauto.
Qed.

Fixpoint cfoldContext (C : context) : context :=
  match C with
  | Hole => Hole
  | CSeq C c => CSeq (cfoldContext C) (cfold c)
  end.

Lemma plug_cfold1 : forall C c1 c2, plug C c1 c2
  -> plug (cfoldContext C) (cfold c1) (cfold c2).
Proof.
  induct 1; simplify; eauto.
Qed.

Hint Resolve plug_cfold1.

Lemma plug_samefold : forall C c1 c1',
    plug C c1 c1'
    -> forall c2 c2', plug C c2 c2'
    -> cfold c1 = cfold c2
    -> cfold c1' = cfold c2'.
Proof.
  induct 1; invert 1; simplify; propositional.
  f_equal; eauto.
Qed.

Hint Resolve plug_samefold.

Lemma plug_countIfs : forall C c1 c1',
    plug C c1 c1'
    -> forall c2 c2', plug C c2 c2'
    -> countIfs c1 < countIfs c2
    -> countIfs c1' < countIfs c2'.
Proof.
  induct 1; invert 1; simplify; propositional.
  apply IHplug in H5; linear_arithmetic.
Qed.

Hint Resolve plug_countIfs.

Lemma cfold_ok : forall v c,
    (v, c) =| (v, cfold c).
Proof.
  simplify.
  apply simulation_skipping with (R := fun n vc1 vc2 => fst vc1 = fst vc2
                                                        /\ snd vc2 = cfold (snd vc1)
                                                        /\ countIfs (snd vc1) < n)
                                   (n := S (countIfs c));
    simplify; propositional; auto.

  invert H0; simplify; subst.
  apply cfold_ok' in H4.
  propositional; subst.
  cases vc2; simplify; subst.
  eauto 11.
  cases vc2; simplify; subst.
  cases n; try linear_arithmetic.
  assert (countIfs c2 < n).
  eapply plug_countIfs in H2; eauto.
  eauto.
  eauto 10.
Qed.
