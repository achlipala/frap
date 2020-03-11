(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 9: Compiler Correctness
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.


(* Let's look at another example of what we can model with operational
 * semantics: correctness of compiler transformations.  Our inspiration here is
 * the seminal project CompCert, which uses Coq to verify a realistic C
 * compiler.  We will adopt the same *simulation*-based techniques as CompCert,
 * albeit on a simpler language and with simpler compiler phases.  We'll stick
 * to transformations from the source language to itself, since that's enough to
 * illustrate the big ideas.  Here's the object language that we'll use, which
 * is _almost_ the same as from Chapter 7. *)

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

(* The next span of notations and definitions is the same as from Chapter 7. *)

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
(*Declare Scope arith_scope.*)
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
 * records an optional output value.  Including this element makes our semantics
 * a _labelled transition system_. *)

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

(* It's easy to push labels through steps with context. *)
Inductive cstep : valuation * cmd -> option nat -> valuation * cmd -> Prop :=
| CStep : forall C v c l v' c' c1 c2,
  plug C c c1
  -> step0 (v, c) l (v', c')
  -> plug C c' c2
  -> cstep (v, c1) l (v', c2).

(* To characterize correct compilation, it is helpful to define a relation to
 * capture which output _traces_ a command might generate.  Note that, for us, a
 * trace is a list of output values and/or terminating markers.  We drop silent
 * labels as we run, and we use [Some n] for outputting of [n] and [None] for
 * termination. *)
Inductive generate : valuation * cmd -> list (option nat) -> Prop :=
| GenDone : forall vc,
  generate vc []
| GenSkip : forall v,
  generate (v, Skip) [None]
| GenSilent : forall vc vc' ns,
  cstep vc None vc'
  -> generate vc' ns
  -> generate vc ns
| GenOutput : forall vc n vc' ns,
  cstep vc (Some n) vc'
  -> generate vc' ns
  -> generate vc (Some n :: ns).

Hint Constructors plug step0 cstep generate : core.

(* Notice that [generate] is defined so that, for any two of a starting state's
 * traces, one is a prefix of the other.  The same wouldn't necessarily hold if
 * our language were nondeterministic. *)

(* We define trace inclusion to capture the notion of
 * _preserving all behaviors_. *)
Definition traceInclusion (vc1 vc2 : valuation * cmd) :=
  forall ns, generate vc1 ns -> generate vc2 ns.
Infix "<|" := traceInclusion (at level 70).

(* And trace equivalence captures _having the same behaviors_. *)
Definition traceEquivalence (vc1 vc2 : valuation * cmd) :=
  vc1 <| vc2 /\ vc2 <| vc1.
Infix "=|" := traceEquivalence (at level 70).

(* Trace equivalence is an appropriate notion of correctness, to relate the
 * "before" and "after" programs of a compiler transformation.  Note that here
 * we break from our usual modus operandi, as we will not be using invariants to
 * characterize correctness!  This kind of trace equivalence is one of the other
 * big concepts that competes with invariants to unify different correctness
 * notions. *)

(* Here's a simple example program, which outputs how many days have elapsed at
 * the end of each one-month period (with a simplified notion of "month"!). *)

Definition daysPerWeek := 7.
Definition weeksPerMonth := 4.
Definition daysPerMonth := (daysPerWeek * weeksPerMonth)%arith.
(* We are purposely building an expression with arithmetic that can be resolved
 * at compile time, to give our optimizations something to do. *)

Example month_boundaries_in_days :=
  "acc" <- 0;;
  while 1 loop
    when daysPerMonth then
      "acc" <- "acc" + daysPerMonth;;
      Output "acc"
    else
      (* Oh no!  We must have calculated it wrong, since we got zero! *)
      (* And, yes, we know this spot can never be reached.  Some of our
       * optimizations will prove it for us! *)
      Skip
    done
  done.

(* Moderately laboriously, we can prove a particular example trace for this
 * program, including its first two outputs.  Traces of all lengths exist,
 * because the program does not terminate, generating new output infinitely
 * often. *)

Hint Extern 1 (interp _ _ = _) => simplify; equality : core.
Hint Extern 1 (interp _ _ <> _) => simplify; equality : core.

Theorem first_few_values :
  generate ($0, month_boundaries_in_days) [Some 28; Some 56].
Proof.
  unfold month_boundaries_in_days.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenSilent.
  eapply CStep with (C := Hole); eauto.
  eapply GenSilent.
  eapply CStep with (C := Hole); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq (CSeq Hole _) _); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenOutput.
  eapply CStep with (C := CSeq Hole _); eauto.
  replace 28 with (interp "acc"
    ($0 $+ ("acc", interp 0 $0)
      $+ ("acc", interp ("acc" + daysPerMonth)%arith ($0 $+ ("acc", interp 0 $0))))); eauto.
  eapply GenSilent.
  eapply CStep with (C := Hole); eauto.
  eapply GenSilent.
  eapply CStep with (C := Hole); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq (CSeq Hole _) _); eauto.
  eapply GenSilent.
  eapply CStep with (C := CSeq Hole _); eauto.
  eapply GenOutput.
  eapply CStep with (C := CSeq Hole _); eauto.
  replace 56 with (interp "acc"
    ($0 $+ ("acc", interp 0 $0) $+ ("acc",
     interp ("acc" + daysPerMonth)%arith ($0 $+ ("acc", interp 0 $0))) $+ ("acc",
     interp ("acc" + daysPerMonth)%arith
       ($0 $+ ("acc", interp 0 $0) $+ ("acc",
        interp ("acc" + daysPerMonth)%arith ($0 $+ ("acc", interp 0 $0))))))); eauto.
  constructor.
Qed.


(** * Basic Simulation Arguments and Optimizing Expressions *)

(* Let's define an optimization that just simplifies expressions. *)

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

(* Here's what our optimization does to the example program. *)
Compute cfoldExprs month_boundaries_in_days.

(* It's actually not obvious how to prove trace equivalence for this kind of
 * optimization, and we should be on the lookout for general principles that
 * help us avoid rehashing the same argument structure for each optimization.
 * To let us prove such principles, we first establish a few key properties of
 * the object language. *)

(* First, any program that isn't a [Skip] can make progress. *)
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

(* Now, a set of (boring) lemmas relevant to contexts: *)

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

Hint Resolve peel_cseq : core.

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

(* Finally, the big theorem we are after: the [cstep] relation is
 * deterministic. *)

Lemma deterministic0 : forall vc l vc',
  step0 vc l vc'
  -> forall l' vc'', step0 vc l' vc''
                     -> l = l' /\ vc'' = vc'.
Proof.
  invert 1; invert 1; simplify; propositional.
Qed.

Theorem deterministic : forall vc l vc',
  cstep vc l vc'
  -> forall l' vc'', cstep vc l' vc''
                     -> l = l' /\ vc' = vc''.
Proof.
  invert 1; invert 1; simplify.
  eapply plug_deterministic in H0; eauto.
  invert H0.
  match goal with
  | [ H : step0 _ _ _, H' : step0 _ _ _ |- _ ] => eapply deterministic0 in H; [ | apply H' ]
  end.
  propositional; subst; auto.
  invert H0.
  auto.
  eapply plug_function in H2; eauto.
  equality.
Qed.

(* OK, we are ready for the first variant of today's big proof technique,
 * _simulation_.  The method is much like with invariants.  Recall that, in our
 * old workhorse technique, we pick a predicate over states, and we show that
 * all steps preserve it.  Simulation is very similar, but now we have a
 * two-argument predicate or _relation_ between states of two systems.  The
 * relation is a simulation when it is able to track execution in one system by
 * playing appropriate steps in the other.  For deterministic systems like ours,
 * the existence of a simulation implies trace equivalence. *)
Section simulation.
  (* Here's the kind of relation we assume. *)
  Variable R : valuation * cmd -> valuation * cmd -> Prop.

  (* Starting from two related states, when the lefthand one makes a step, the
   * righthand one can make a matching step, such that the new states are also
   * related. *)
  Hypothesis one_step : forall vc1 vc2, R vc1 vc2
    -> forall vc1' l, cstep vc1 l vc1'
      -> exists vc2', cstep vc2 l vc2' /\ R vc1' vc2'.

  (* When a righthand command is related to [Skip], it must be [Skip], too. *)
  Hypothesis agree_on_termination : forall v1 v2 c2, R (v1, Skip) (v2, c2)
    -> c2 = Skip.

  (* First (easy) step: [R] implies left-to-right trace inclusion. *)

  Lemma simulation_fwd' : forall vc1 ns, generate vc1 ns
    -> forall vc2, R vc1 vc2
      -> generate vc2 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc2.
    apply agree_on_termination in H; subst.
    auto.

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

  (* Second (slightly harder) step: [R] implies right-to-left trace
   * inclusion. *)

  Lemma simulation_bwd' : forall vc2 ns, generate vc2 ns
    -> forall vc1, R vc1 vc2
      -> generate vc1 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc1.
    assert (c = Skip \/ exists v' l c', cstep (v0, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    auto.
    eapply one_step in H; eauto.
    first_order.
    invert H.
    invert H4.
    invert H5.
    
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

  (* Put them together and we have trace equivalence. *)

  Theorem simulation : forall vc1 vc2, R vc1 vc2
    -> vc1 =| vc2.
  Proof.
    simplify; split; auto using simulation_fwd, simulation_bwd.
  Qed.
End simulation.

(* Now to prove our particular optimization.  First, original steps can be
 * lifted into optimized steps. *)

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

(* It helps to add optimization on contexts, as a proof device. *)
Fixpoint cfoldExprsContext (C : context) : context :=
  match C with
  | Hole => Hole
  | CSeq C c => CSeq (cfoldExprsContext C) (cfoldExprs c)
  end.

(* The optimization can be applied over [plug]. *)
Lemma plug_cfoldExprs1 : forall C c1 c2, plug C c1 c2
  -> plug (cfoldExprsContext C) (cfoldExprs c1) (cfoldExprs c2).
Proof.
  induct 1; simplify; eauto.
Qed.

Hint Resolve plug_cfoldExprs1 : core.

(* The main correctness property! *)
Theorem cfoldExprs_ok : forall v c,
    (v, c) =| (v, cfoldExprs c).
Proof.
  simplify.
  (* Notice our clever choice of a simulation relation here, much as we often
   * choose strengthened invariants.  We basically just recast the theorem
   * statement as a two-state predicate using equality. *)
  apply simulation with (R := fun vc1 vc2 => fst vc1 = fst vc2
                                             /\ snd vc2 = cfoldExprs (snd vc1));
    simplify; propositional.

  invert H0; simplify; subst.
  apply cfoldExprs_ok' in H3.
  cases vc2; simplify; subst.
  eauto 7.
Qed.


(** * Simulations That Allow Skipping Steps *)

(* Here's a reasonable variant of the last optimization: when an [If] test
 * expression reduces to a constant, replace the [If] with whichever branch is
 * guaranteed to run. *)
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

(* Here's how our running example optimizes further. *)
Compute cfold month_boundaries_in_days.

(* It will be helpful to have a shorthand for steps that don't generate output.
 * [Notation] is a useful way to introduce a shorthand so that it looks exactly
 * the same as its expansion, to all Coq tactics. *)
Notation silent_cstep := (fun a b => cstep a None b).

(* Silent steps have a few interesting properties, proved here. *)

Lemma silent_generate_fwd : forall ns vc vc',
    silent_cstep^* vc vc'
    -> generate vc ns
    -> generate vc' ns.
Proof.
  induct 1; simplify; eauto.
  invert H1; auto.

  invert H.
  invert H3.
  invert H4.

  eapply deterministic in H; eauto.
  propositional; subst.
  auto.

  eapply deterministic in H; eauto.
  equality.
Qed.

Lemma silent_generate_bwd : forall ns vc vc',
    silent_cstep^* vc vc'
    -> generate vc' ns
    -> generate vc ns.
Proof.
  induct 1; eauto.
Qed.

Lemma generate_Skip : forall v a ns,
    generate (v, Skip) (Some a :: ns)
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

Hint Resolve silent_generate_fwd silent_generate_bwd generate_Skip : core.

(* You might have noticed that our old notion of simulation doesn't apply to the
 * new optimization.  The reason is that, because the optimized program skips
 * some steps, some steps in the source program may not have matching steps in
 * the optimized program.  Let's extend simulation to allow skipped steps. *)
Section simulation_skipping.
  (* Now the relation takes a number as an argument.  The idea is that, for
   * [R n vc1 vc2], at most [n] steps of [vc1] may go unmatched by [vc2], before
   * we finally find one that matches.  It is an interesting exercise to work
   * out why, without tracking such quantities, this notion of simulation
   * wouldn't imply trace equivalence! *)
  Variable R : nat -> valuation * cmd -> valuation * cmd -> Prop.

  (* Now this key hypothesis has two cases. *)
  Hypothesis one_step : forall n vc1 vc2, R n vc1 vc2
    -> forall vc1' l, cstep vc1 l vc1'

                         (* Case 1: Skipping a (silent!) step, decreasing [n] *)
                      -> (exists n', n = S n' /\ l = None /\ R n' vc1' vc2)

                         (* Case 2: Matching the step like before; note how [n]
                          * resets to an arbitrary new limit! *)
                         \/ exists n' vc2', cstep vc2 l vc2' /\ R n' vc1' vc2'.

  Hypothesis agree_on_termination : forall n v1 v2 c2, R n (v1, Skip) (v2, c2)
    -> c2 = Skip.

  (* The forward direction is just as easy to prove. *)

  Lemma simulation_skipping_fwd' : forall vc1 ns, generate vc1 ns
    -> forall n vc2, R n vc1 vc2
      -> generate vc2 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc2.
    apply agree_on_termination in H.
    subst.
    auto.

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

  (* This one isn't so obvious: a step on the right can now be matched by
   * _one or more_ steps on the left, preserving [R]. *)
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

  Lemma step_to_termination : forall vc v,
      silent_cstep^* vc (v, Skip)
      -> generate vc [None].
  Proof.
    clear; induct 1; eauto.
  Qed.

  Hint Resolve step_to_termination : core.

  Lemma R_Skip : forall n vc1 v,
      R n vc1 (v, Skip)
      -> exists v', silent_cstep^* vc1 (v', Skip).
  Proof.
    induct n; simplify.

    cases vc1.
    assert (c = Skip \/ exists v' l c', cstep (v0, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    eauto.
    eapply one_step in H; eauto.
    first_order.
    equality.
    invert H.
    invert H4.
    invert H5.

    cases vc1.
    assert (c = Skip \/ exists v' l c', cstep (v0, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    eauto.
    eapply one_step in H; eauto.
    first_order; subst.
    invert H.
    apply IHn in H2.
    first_order.
    eauto.
    invert H.
    invert H4.
    invert H5.
  Qed.

  Lemma simulation_skipping_bwd' : forall ns vc2, generate vc2 ns
    -> forall n vc1, R n vc1 vc2
      -> generate vc1 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc1.
    apply R_Skip in H; first_order.
    eauto.

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

Hint Extern 1 (_ < _) => linear_arithmetic : core.
Hint Extern 1 (_ >= _) => linear_arithmetic : core.
Hint Extern 1 (_ <> _) => linear_arithmetic : core.

(* We will need to do some bookkeeping of [n] values.  This function is the
 * trick, as we only need to skip steps based on removing [If]s from the code.
 * That means the number of [If]s in a program is an upper bound on skipped
 * steps.  (It's not a tight bound, because some [If]s may be in branches that
 * are themselves removed by the optimization!) *)
Fixpoint countIfs (c : cmd) : nat :=
  match c with
  | Skip => 0
  | Assign _ _ => 0
  | Sequence c1 c2 => countIfs c1 + countIfs c2
  | If _ c1 c2 => 1 + countIfs c1 + countIfs c2
  | While _ c1 => countIfs c1
  | Output _ => 0
  end.

(* Our notion of [step0] porting must now allow some skipped steps, also showing
 * that they decrease [If] count. *)
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

(* Now some fiddling with contexts: *)

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

Hint Resolve plug_cfold1 : core.

Lemma plug_samefold : forall C c1 c1',
    plug C c1 c1'
    -> forall c2 c2', plug C c2 c2'
    -> cfold c1 = cfold c2
    -> cfold c1' = cfold c2'.
Proof.
  induct 1; invert 1; simplify; propositional.
  f_equal; eauto.
Qed.

Hint Resolve plug_samefold : core.

Lemma plug_countIfs : forall C c1 c1',
    plug C c1 c1'
    -> forall c2 c2', plug C c2 c2'
    -> countIfs c1 < countIfs c2
    -> countIfs c1' < countIfs c2'.
Proof.
  induct 1; invert 1; simplify; propositional.
  apply IHplug in H5; linear_arithmetic.
Qed.

Hint Resolve plug_countIfs : core.

Hint Extern 1 (interp ?e _ = _) =>
  match goal with
  | [ H : cfoldArith e = _ |- _ ] => rewrite <- cfoldArith_ok; rewrite H
  end : core.
Hint Extern 1 (interp ?e _ <> _) =>
  match goal with
  | [ H : cfoldArith e = _ |- _ ] => rewrite <- cfoldArith_ok; rewrite H
  end : core.

(* The final proof is fairly straightforward now. *)
Lemma cfold_ok : forall v c,
    (v, c) =| (v, cfold c).
Proof.
  simplify.
  (* Note the use of [countIfs] in the simulation relation. *)
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


(** * Simulations That Allow Taking Multiple Matching Steps *)

(* Some optimizations actually transform code toward lower-level languages.
 * Let's take the example of breaking compound expressions into step-by-step
 * computations using new temporary variables. *)

(* We'll use this function to give us an infinite supply of disjoint
 * temporaries. *)
Fixpoint tempVar (n : nat) : string :=
  match n with
  | O => "_tmp"
  | S n' => tempVar n' ++ "'"
  end%string.

Compute tempVar 0.
Compute tempVar 1.
Compute tempVar 2.

(* With that kind of temporary, we need to watch our for name clashes with
 * variables that already exist in a program.  These Boolean functions check for
 * lack of clashes.  We also prove some properties that will come in handy
 * later. *)

Definition noUnderscoreVar (x : var) : bool :=
  match x with
  | String "_" _ => false
  | _ => true
  end.

Lemma append_assoc : forall a b c,
    (a ++ (b ++ c) = (a ++ b) ++ c)%string.
Proof.
  induct a; simplify; equality.
Qed.

Lemma append_assoc_String : forall a b,
    (String a b = String a "" ++ b)%string.
Proof.
  induct b; simplify; equality.
Qed.

Lemma noUnderscoreVar_tempVar' : forall n,
    exists s, tempVar n = ("_tmp" ++ s)%string.
Proof.
  induct n; simplify; first_order.

  exists ""; auto.

  rewrite H.
  exists (x ++ "'")%string.
  repeat match goal with
         | [ |- context[String ?c ?x] ] =>
           match x with
           | "" => fail 1
           | _ => rewrite (append_assoc_String c x)
           end
         end.
  repeat rewrite append_assoc.
  reflexivity.
Qed.  

Theorem noUnderscoreVar_tempVar : forall x,
    noUnderscoreVar x = true
    -> forall n, x <> tempVar n.
Proof.
  unfold not; simplify.
  subst.
  pose proof (noUnderscoreVar_tempVar' n).
  first_order.
  rewrite H0 in H.
  simplify.
  equality.
Qed.

Lemma tempVar_inj' : forall s1 s2,
    (s1 ++ "'" = s2 ++ "'")%string
    -> s1 = s2.
Proof.
  induct s1; simplify.

  cases s2; simplify; try equality.
  invert H.
  cases s2; simplify; equality.

  cases s2; simplify.
  invert H.
  cases s1; simplify; equality.
  invert H.
  f_equal; auto.
Qed.

Theorem tempVar_inj : forall n1 n2,
    tempVar n1 = tempVar n2
    -> n1 = n2.
Proof.
  induct n1; simplify; cases n2; simplify; try equality.

  repeat match goal with
         | [ _ : context[(?s ++ "'")%string] |- _ ] => cases s; simplify; try equality
         end.

  repeat match goal with
         | [ _ : context[(?s ++ "'")%string] |- _ ] => cases s; simplify; try equality
         end.

  auto using tempVar_inj'.
Qed.

Fixpoint noUnderscoreArith (e : arith) : bool :=
  match e with
  | Const _ => true
  | Var x => noUnderscoreVar x
  | Plus e1 e2
  | Minus e1 e2
  | Times e1 e2 => noUnderscoreArith e1 && noUnderscoreArith e2
  end.

Fixpoint noUnderscore (c : cmd) : bool :=
  match c with
  | Skip => true
  | Assign x e => noUnderscoreVar x && noUnderscoreArith e
  | Sequence c1 c2 => noUnderscore c1 && noUnderscore c2
  | If e then_ else_ => noUnderscoreArith e && noUnderscore then_ && noUnderscore else_
  | While e body => noUnderscoreArith e && noUnderscore body
  | Output e => noUnderscoreArith e
  end.

(* It's good to verify that our example program makes the grade. *)
Compute noUnderscore month_boundaries_in_days.

(* Now here's the optimization.  First, we flatten expressions.  The idea is
 * that argument [tempCount] gives us the index of the next temporary we should
 * use, also guaranteeing that earlier code only uses lower-numbered
 * temporaries.  Argument [dst] is a variable where we should write the result
 * of the expression.  A return value is a command that has the
 * effect of writing the value of [e] into [dst]. *)
Fixpoint flattenArith (tempCount : nat) (dst : var) (e : arith) : cmd :=
  match e with
  | Const _
  | Var _ => Assign dst e
  | Plus e1 e2 =>
    let x1 := tempVar tempCount in
    let c1 := flattenArith (S tempCount) x1 e1 in
    let x2 := tempVar (S tempCount) in
    let c2 := flattenArith (S (S tempCount)) x2 e2 in
    Sequence c1 (Sequence c2 (Assign dst (Plus x1 x2)))
  | Minus e1 e2 =>
    let x1 := tempVar tempCount in
    let c1 := flattenArith (S tempCount) x1 e1 in
    let x2 := tempVar (S tempCount) in
    let c2 := flattenArith (S (S tempCount)) x2 e2 in
    Sequence c1 (Sequence c2 (Assign dst (Minus x1 x2)))
  | Times e1 e2 =>
    let x1 := tempVar tempCount in
    let c1 := flattenArith (S tempCount) x1 e1 in
    let x2 := tempVar (S tempCount) in
    let c2 := flattenArith (S (S tempCount)) x2 e2 in
    Sequence c1 (Sequence c2 (Assign dst (Times x1 x2)))
  end.

(* For simplicity, the main optimization only flattens variables in
 * assignments. *)
Fixpoint flatten (c : cmd) : cmd :=
  match c with
  | Skip => c
  | Assign x e => flattenArith 0 x e
  | Sequence c1 c2 => Sequence (flatten c1) (flatten c2)
  | If e then_ else_ => If e (flatten then_) (flatten else_)
  | While e body => While e (flatten body)
  | Output _ => c
  end.

(* Here's what it does on our example. *)
Compute flatten month_boundaries_in_days.

(* The alert reader may noticed that, yet again, we picked a transformation that
 * our existing simulation relations can't handle directly, at least if we put
 * the original system on the left and the compiled version on the right.  Now
 * we need a single step on the left to be matched by _one or more_ steps on the
 * right. *)
Section simulation_multiple.
  (* At least we can remove that pesky numeric parameter of [R]. *)
  Variable R : valuation * cmd -> valuation * cmd -> Prop.

  Hypothesis one_step : forall vc1 vc2, R vc1 vc2
    -> forall vc1' l, cstep vc1 l vc1'
                      -> exists vc2' vc2'',
                        silent_cstep^* vc2 vc2'
                        /\ cstep vc2' l vc2''
                        /\ R vc1' vc2''.

  Hypothesis agree_on_termination : forall v1 v2 c2, R (v1, Skip) (v2, c2)
    -> c2 = Skip.

  (* The forward direction is easy, as usual. *)

  Lemma simulation_multiple_fwd' : forall vc1 ns, generate vc1 ns
    -> forall vc2, R vc1 vc2
      -> generate vc2 ns.
  Proof.
    induct 1; simplify; eauto.

    cases vc2.
    apply agree_on_termination in H; subst.
    auto.

    eapply one_step in H; eauto.
    first_order.
    eauto.

    eapply one_step in H1; eauto.
    first_order.
    eauto.
  Qed.

  Theorem simulation_multiple_fwd : forall vc1 vc2, R vc1 vc2
    -> vc1 <| vc2.
  Proof.
    unfold traceInclusion; eauto using simulation_multiple_fwd'.
  Qed.

  (* The backward proof essentially proceeds by strong induction on
   * _how many steps it took to generate a trace_, which we facilitate by
   * defining a [generate] variant parameterized by a step count. *)
  Inductive generateN : nat -> valuation * cmd -> list (option nat) -> Prop :=
  | GenDoneN : forall vc,
      generateN 0 vc []
  | GenSkupN : forall v,
      generateN 0 (v, Skip) [None]
  | GenSilentN : forall sc vc vc' ns,
      cstep vc None vc'
      -> generateN sc vc' ns
      -> generateN (S sc) vc ns
  | GenOutputN : forall sc vc n vc' ns,
      cstep vc (Some n) vc'
      -> generateN sc vc' ns
      -> generateN (S sc) vc (Some n :: ns).

  (* We won't comment on the other proof details, though they could be
   * interesting reading. *)

  Hint Constructors generateN : core.

  Lemma generateN_fwd : forall sc vc ns,
      generateN sc vc ns
      -> generate vc ns.
  Proof.
    induct 1; eauto.
  Qed.

  Hint Resolve generateN_fwd : core.

  Lemma generateN_bwd : forall vc ns,
      generate vc ns
      -> exists sc, generateN sc vc ns.
  Proof.
    induct 1; first_order; eauto.
  Qed.

  Lemma generateN_silent_cstep : forall sc vc ns,
      generateN sc vc ns
      -> forall vc', silent_cstep^* vc vc'
      -> exists sc', sc' <= sc /\ generateN sc' vc' ns.
  Proof.
    clear; induct 1; simplify; eauto.

    invert H; eauto.
    invert H0.
    invert H3.
    invert H4.

    invert H1; eauto.
    eapply deterministic in H; eauto.
    propositional; subst.
    apply IHgenerateN in H3.
    first_order.
    eauto.

    invert H1; eauto.
    eapply deterministic in H; eauto.
    equality.
  Qed.

  Lemma termination_is_last : forall sc vc ns,
      generateN sc vc (None :: ns)
      -> ns = [].
  Proof.
    induct 1; eauto.
  Qed.

  Lemma simulation_multiple_bwd' : forall sc sc', sc' < sc
    -> forall vc2 ns, generateN sc' vc2 ns
    -> forall vc1, R vc1 vc2
    -> generate vc1 ns.
  Proof.
    induct sc; simplify.

    linear_arithmetic.

    cases sc'.
    invert H0.
    auto.

    cases vc1.
    assert (c = Skip \/ exists v' l c', cstep (v0, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    auto.
    eapply one_step in H1; eauto.
    first_order.
    invert H1.
    invert H2.
    invert H5.
    invert H6.
    invert H4.
    invert H7.
    invert H8.

    cases vc1; cases vc2.
    assert (c = Skip \/ exists v' l c', cstep (v, c) l (v', c')) by apply skip_or_step.
    first_order; subst.
    apply agree_on_termination in H1; subst.
    cases ns; auto.
    cases o.
    exfalso; eauto.
    eapply termination_is_last in H0; subst.
    auto.

    eapply one_step in H1; eauto.
    first_order.
    eapply generateN_silent_cstep in H0; eauto.
    first_order.
    invert H5; auto.
    invert H3.
    invert H7.
    invert H8.
    eapply deterministic in H3; eauto.
    propositional; subst.
    econstructor.
    eauto.
    eapply IHsc; try eassumption.
    linear_arithmetic.

    eapply deterministic in H3; eauto.
    propositional; subst.
    eapply GenOutput.
    eauto.
    eapply IHsc; try eassumption.
    linear_arithmetic.
  Qed.

  Theorem simulation_multiple_bwd : forall vc1 vc2, R vc1 vc2
    -> vc2 <| vc1.
  Proof.
    unfold traceInclusion; simplify.
    apply generateN_bwd in H0.
    first_order.
    eauto using simulation_multiple_bwd'.
  Qed.

  Theorem simulation_multiple : forall vc1 vc2, R vc1 vc2
    -> vc1 =| vc2.
  Proof.
    simplify; split; auto using simulation_multiple_fwd, simulation_multiple_bwd.
  Qed.
End simulation_multiple.

(* Now, to verify our particular flattening translation.  First, one wrinkle is
 * that, by writing to new temporary variables, valuations will _not_ be exactly
 * the same across the sides of our relation.  Here is the sense in which we
 * need the sides to agree: *)
Definition agree (v v' : valuation) :=
  forall x,
    noUnderscoreVar x = true
    -> v $? x = v' $? x.
(* That is, they only need to agree on variables that aren't legal
 * temporaries. *)

(* There now follow a whole bunch of thrilling lemmas about agreement. *)

Ltac bool :=
  simplify;
  repeat match goal with
         | [ H : _ && _ = true |- _ ] => apply andb_true_iff in H; propositional
         end.

Lemma interp_agree : forall v v', agree v v'
  -> forall e, noUnderscoreArith e = true
  -> interp e v = interp e v'.
Proof.
  induct e; bool; try equality.

  unfold agree in H.
  specialize (H _ H0).
  rewrite H.
  equality.
Qed.

Lemma agree_add : forall v v' x n,
    agree v v'
    -> agree (v $+ (x, n)) (v' $+ (x, n)).
Proof.
  unfold agree; simplify.
  apply H in H0.
  cases (x ==v x0); simplify; auto.
Qed.

Lemma agree_add_tempVar_fwd : forall v v' n nv,
    agree v v'
    -> agree (v $+ (tempVar n, nv)) v'.
Proof.
  unfold agree; simplify.
  cases (x ==v tempVar n); simplify; subst; auto.
  eapply noUnderscoreVar_tempVar in H0.
  propositional.
Qed.

Lemma agree_add_tempVar_bwd : forall v v' n nv,
    agree (v $+ (tempVar n, nv)) v'
    -> agree v v'.
Proof.
  unfold agree; simplify.
  specialize (H _ H0).
  cases (x ==v tempVar n); simplify; subst; auto.
  eapply noUnderscoreVar_tempVar in H0.
  propositional.
Qed.

Lemma agree_add_tempVar_bwd_prime : forall v v' n nv,
    agree (v $+ (tempVar n ++ "'", nv)%string) v'
    -> agree v v'.
Proof.
  simplify.
  change (tempVar n ++ "'")%string with (tempVar (S n)) in *.
  eauto using agree_add_tempVar_bwd.
Qed.

Lemma agree_refl : forall v,
    agree v v.
Proof.
  first_order.
Qed.

Hint Resolve agree_add agree_add_tempVar_fwd agree_add_tempVar_bwd agree_add_tempVar_bwd_prime agree_refl : core.

(* And here are two more unremarkable lemmas. *)

Lemma silent_csteps_front : forall c v1 v2 c1 c2,
    silent_cstep^* (v1, c1) (v2, c2)
    -> silent_cstep^* (v1, c1;; c) (v2, c2;; c).
Proof.
  induct 1; eauto.
  invert H.
  eauto 6.
Qed.

Hint Resolve silent_csteps_front : core.

Lemma tempVar_contra : forall n1 n2,
    tempVar n1 = tempVar n2
    -> n1 <> n2
    -> False.
Proof.
  pose proof tempVar_inj.
  first_order.
Qed.

Hint Resolve tempVar_contra : core.

Lemma self_prime_contra : forall s,
    (s ++ "'")%string = s -> False.
Proof.
  induct s; simplify; equality.
Qed.

Hint Resolve self_prime_contra : core.

(* We've now proved all properties of [tempVar] that we need, so let's ask Coq
 * not to reduce applications of it anymore, to keep goals simpler. *)
Opaque tempVar.

(* This is our workhorse lemma, establishing correct compilation of assignments
 * with [flattenArith]. *)
Lemma flatten_Assign : forall e dst tempCount,
  noUnderscoreArith e = true
  (* We compile an expression [e] with no variable clashes. *)

  -> (forall n, n >= tempCount -> dst <> tempVar n)
  (* Our destination variable [dst] is distinct from any temporary that we give
   * [flattenArith] permission to use. *)

  -> forall v1 v2, agree v1 v2
  (* The valuations on the two sides agree on non-temporaries. *)

  (* THEN we conclude existence of further values, such that *)
  -> exists v c v2',
    silent_cstep^* (v2, flattenArith tempCount dst e) (v, c)
    (* The compiled program steps silently to an intermediate state. *)

    /\ cstep (v, c) None (v2', Skip)
    (* Next, it runs one final silent step (arithmetic never outputs). *)

    /\ agree (v1 $+ (dst, interp e v1)) v2'
    (* The place we end up agrees with the original lefthand valuation, with the
     * destination updated with the requested value. *)

    /\ v2' $? dst = Some (interp e v1)
    (* The destination has had the right value set.  (This isn't redundant with
     * the last fact because the destination might be a temporary, in which case
     * [agree] ignores it.) *)

    /\ (forall n, n < tempCount -> dst <> tempVar n -> v2' $? tempVar n = v2 $? tempVar n)
    (* We have not touched any temporaries both less than [tempCount] and not
     * equal to the destination *).
Proof.
  induct e; bool.

  do 3 eexists.
  split.
  auto.
  split.
  eauto.
  split.
  eauto.
  propositional; auto.
  simplify; auto.
  simplify.
  cases (dst ==v tempVar n0); simplify; subst; auto.

  do 3 eexists.
  split.
  auto.
  split.
  eauto.
  split.
  eauto.
  propositional; auto.
  simplify.
  unfold agree in H1.
  apply H1 in H.
  rewrite H.
  eauto.
  simplify.
  unfold agree in H1.
  apply H1 in H.
  rewrite H.
  split.
  equality.
  simplify.
  equality.

  eapply IHe1 with (dst := tempVar tempCount) (tempCount := S tempCount) in H1; eauto; clear IHe1.
  first_order.
  eapply IHe2 with (dst := tempVar (S tempCount)) (tempCount := S (S tempCount)) in H4; eauto; clear IHe2.
  first_order.
  eexists; exists (dst <- tempVar tempCount + tempVar (S tempCount)); eexists.
  split.
  apply trc_trans with (y := (x2, x3;; dst <- tempVar tempCount + tempVar (S tempCount))).
  apply trc_trans with (y := (x1, flattenArith (S (S tempCount)) (tempVar (S tempCount)) e2;; dst <- tempVar tempCount + tempVar (S tempCount))).
  eauto 7 using trc_trans.
  eauto 7 using trc_trans.
  eauto 7 using trc_trans.
  split.
  eauto.
  split.
  simplify.
  rewrite H9.
  rewrite H10 by eauto.
  rewrite H5.
  erewrite interp_agree with (v := v1 $+ (tempVar tempCount, interp e1 v1)) (v' := v1) by eauto.
  eauto.
  simplify.
  propositional.
  rewrite H9.
  rewrite H10 by eauto.
  rewrite H5.
  erewrite interp_agree with (v := v1 $+ (tempVar tempCount, interp e1 v1)) (v' := v1) by eauto.
  auto.
  simplify.
  rewrite H10 by eauto.
  eauto.

  (* Apologies for the copy-and-paste between the binary-operator cases! *)
  eapply IHe1 with (dst := tempVar tempCount) (tempCount := S tempCount) in H1; eauto; clear IHe1.
  first_order.
  eapply IHe2 with (dst := tempVar (S tempCount)) (tempCount := S (S tempCount)) in H4; eauto; clear IHe2.
  first_order.
  eexists; exists (dst <- tempVar tempCount - tempVar (S tempCount)); eexists.
  split.
  apply trc_trans with (y := (x2, x3;; dst <- tempVar tempCount - tempVar (S tempCount))).
  apply trc_trans with (y := (x1, flattenArith (S (S tempCount)) (tempVar (S tempCount)) e2;; dst <- tempVar tempCount - tempVar (S tempCount))).
  eauto 7 using trc_trans.
  eauto 7 using trc_trans.
  eauto 7 using trc_trans.
  split.
  eauto.
  split.
  simplify.
  rewrite H9.
  rewrite H10 by eauto.
  rewrite H5.
  erewrite interp_agree with (v := v1 $+ (tempVar tempCount, interp e1 v1)) (v' := v1) by eauto.
  eauto.
  simplify.
  propositional.
  rewrite H9.
  rewrite H10 by eauto.
  rewrite H5.
  erewrite interp_agree with (v := v1 $+ (tempVar tempCount, interp e1 v1)) (v' := v1) by eauto.
  auto.
  simplify.
  rewrite H10 by eauto.
  eauto.

  eapply IHe1 with (dst := tempVar tempCount) (tempCount := S tempCount) in H1; eauto; clear IHe1.
  first_order.
  eapply IHe2 with (dst := tempVar (S tempCount)) (tempCount := S (S tempCount)) in H4; eauto; clear IHe2.
  first_order.
  eexists; exists (dst <- tempVar tempCount * tempVar (S tempCount)); eexists.
  split.
  apply trc_trans with (y := (x2, x3;; dst <- tempVar tempCount * tempVar (S tempCount))).
  apply trc_trans with (y := (x1, flattenArith (S (S tempCount)) (tempVar (S tempCount)) e2;; dst <- tempVar tempCount * tempVar (S tempCount))).
  eauto 7 using trc_trans.
  eauto 7 using trc_trans.
  eauto 7 using trc_trans.
  split.
  eauto.
  split.
  simplify.
  rewrite H9.
  rewrite H10 by eauto.
  rewrite H5.
  erewrite interp_agree with (v := v1 $+ (tempVar tempCount, interp e1 v1)) (v' := v1) by eauto.
  eauto.
  simplify.
  propositional.
  rewrite H9.
  rewrite H10 by eauto.
  rewrite H5.
  erewrite interp_agree with (v := v1 $+ (tempVar tempCount, interp e1 v1)) (v' := v1) by eauto.
  auto.
  simplify.
  rewrite H10 by eauto.
  eauto.
Qed.

(* Now our reasoning can be fit within a general theorem about [step0].  Note
 * how the conclusions use [cstep] instead of [step0], to accommodate steps
 * within the structure of a term in the [Assign] case. *)
Lemma flatten_ok' : forall v1 c1 l v2 c2,
    step0 (v1, c1) l (v2, c2)
    -> noUnderscore c1 = true
    -> forall v1', agree v1 v1'
    -> exists v c v2', silent_cstep^* (v1', flatten c1) (v, c)
                       /\ cstep (v, c) l (v2', flatten c2)
                       /\ agree v2 v2'.
Proof.
  invert 1; simplify; bool;
    repeat erewrite interp_agree in * by eassumption; eauto 10.

  assert (Hnu : noUnderscoreArith e = true) by assumption.
  eapply flatten_Assign with (tempCount := 0) (dst := x) in Hnu; try eassumption.
  first_order.
  do 3 eexists.
  split.
  eassumption.
  split.
  eassumption.
  erewrite <- interp_agree; eauto.
  simplify.
  eauto using noUnderscoreVar_tempVar.
Qed.

(* Now, some thrilling lemmas about underscores and plugging! *)

Lemma noUnderscore_plug : forall C c0 c1,
    plug C c0 c1
    -> noUnderscore c1 = true
    -> noUnderscore c0 = true.
Proof.
  induct 1; bool; auto.
Qed.

Hint Immediate noUnderscore_plug : core.

Lemma silent_csteps_plug : forall C c1 c1',
    plug C c1 c1'
    -> forall v1 v2 c2 c2', plug C c2 c2'
    -> silent_cstep^* (v1, c1) (v2, c2)
    -> silent_cstep^* (v1, c1') (v2, c2').
Proof.
  induct 1; invert 1; eauto.
Qed.

Hint Resolve silent_csteps_plug : core.

Fixpoint flattenContext (C : context) : context :=
  match C with
  | Hole => Hole
  | CSeq C c => CSeq (flattenContext C) (flatten c)
  end.

Lemma plug_flatten : forall C c1 c2, plug C c1 c2
  -> plug (flattenContext C) (flatten c1) (flatten c2).
Proof.
  induct 1; simplify; eauto.
Qed.

Hint Resolve plug_flatten : core.

Lemma plug_total : forall c C, exists c', plug C c c'.
Proof.
  induct C; first_order; eauto.
Qed.

Lemma plug_cstep : forall C c1 c1', plug C c1 c1'
  -> forall c2 c2', plug C c2 c2'
  -> forall v l v', cstep (v, c1) l (v', c2)
                    -> cstep (v, c1') l (v', c2').
Proof.
  induct 1; invert 1; first_order; eauto.
  eapply IHplug in H0; eauto.
  first_order.
  invert H0.
  eauto.
Qed.

Hint Resolve plug_cstep : core.

Lemma step0_noUnderscore : forall v c l v' c',
    step0 (v, c) l (v', c')
    -> noUnderscore c = true
    -> noUnderscore c' = true.
Proof.
  invert 1; bool; auto.
  rewrite H0, H1.
  reflexivity.
Qed.

Hint Resolve step0_noUnderscore : core.

Fixpoint noUnderscoreContext (C : context) : bool :=
  match C with
  | Hole => true
  | CSeq C' c => noUnderscoreContext C' && noUnderscore c
  end.

Lemma noUnderscore_plug_context : forall C c0 c1,
    plug C c0 c1
    -> noUnderscore c1 = true
    -> noUnderscoreContext C = true.
Proof.
  induct 1; bool; auto.
  rewrite H0, H2; reflexivity.
Qed.

Lemma noUnderscore_plug_fwd : forall C c0 c1,
    plug C c0 c1
    -> noUnderscoreContext C = true
    -> noUnderscore c0 = true
    -> noUnderscore c1 = true.
Proof.
  induct 1; bool; auto.
  rewrite H4, H3; reflexivity.
Qed.

Hint Resolve noUnderscore_plug_context noUnderscore_plug_fwd : core.

(* Finally, the main correctness theorem. *)
Lemma flatten_ok : forall v c,
    noUnderscore c = true
    -> (v, c) =| (v, flatten c).
Proof.
  simplify.
  (* Note that our simulation relation remembers lack of underscores, and it
   * enforces mere agreement between valuations, rather than full equality. *)
  apply simulation_multiple with (R := fun vc1 vc2 => noUnderscore (snd vc1) = true
                                                      /\ agree (fst vc1) (fst vc2)
                                                      /\ snd vc2 = flatten (snd vc1));
    simplify; propositional; eauto.

  invert H1; simplify; subst.
  assert (noUnderscore c2 = true) by eauto 4.
  eapply flatten_ok' in H5; eauto 4.
  first_order.
  cases vc2; simplify; subst.
  pose proof (plug_total x0 (flattenContext C)).
  first_order.
  do 2 eexists.
  split.
  eapply silent_csteps_plug; try apply H4; eauto.
  eauto 6.
Qed.
