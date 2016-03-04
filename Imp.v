Require Import Frap.

Set Implicit Arguments.


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
| While (e : arith) (body : cmd).

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

Inductive eval : valuation -> cmd -> valuation -> Prop :=
| EvalSkip : forall v,
  eval v Skip v
| EvalAssign : forall v x e,
  eval v (Assign x e) (v $+ (x, interp e v))
| EvalSeq : forall v c1 v1 c2 v2,
  eval v c1 v1
  -> eval v1 c2 v2
  -> eval v (Sequence c1 c2) v2
| EvalIfTrue : forall v e then_ else_ v',
  interp e v <> 0
  -> eval v then_ v'
  -> eval v (If e then_ else_) v'
| EvalIfFalse : forall v e then_ else_ v',
  interp e v = 0
  -> eval v else_ v'
  -> eval v (If e then_ else_) v'
| EvalWhileTrue : forall v e body v' v'',
  interp e v <> 0
  -> eval v body v'
  -> eval v' (While e body) v''
  -> eval v (While e body) v''
| EvalWhileFalse : forall v e body,
  interp e v = 0
  -> eval v (While e body) v.

Inductive step : valuation * cmd -> valuation * cmd -> Prop :=
| StepAssign : forall v x e,
  step (v, Assign x e) (v $+ (x, interp e v), Skip)
| StepSeq1 : forall v c1 c2 v' c1',
  step (v, c1) (v', c1')
  -> step (v, Sequence c1 c2) (v', Sequence c1' c2)
| StepSeq2 : forall v c2,
  step (v, Sequence Skip c2) (v, c2)
| StepIfTrue : forall v e then_ else_,
  interp e v <> 0
  -> step (v, If e then_ else_) (v, then_)
| StepIfFalse : forall v e then_ else_,
  interp e v = 0
  -> step (v, If e then_ else_) (v, else_)
| StepWhileTrue : forall v e body,
  interp e v <> 0
  -> step (v, While e body) (v, Sequence body (While e body))
| StepWhileFalse : forall v e body,
  interp e v = 0
  -> step (v, While e body) (v, Skip).

Hint Constructors trc step eval.

Lemma step_star_Seq : forall v c1 c2 v' c1',
  step^* (v, c1) (v', c1')
  -> step^* (v, Sequence c1 c2) (v', Sequence c1' c2).
Proof.
  induct 1; eauto.
  cases y; eauto.
Qed.

Hint Resolve step_star_Seq.

Theorem big_small : forall v c v', eval v c v'
  -> step^* (v, c) (v', Skip).
Proof.
  induct 1; eauto 6 using trc_trans.
Qed.

Lemma small_big'' : forall v c v' c', step (v, c) (v', c')
                                      -> forall v'', eval v' c' v''
                                                     -> eval v c v''.
Proof.
  induct 1; simplify;
  repeat match goal with
         | [ H : eval _ _ _ |- _ ] => invert1 H
         end; eauto.
Qed.

Hint Resolve small_big''.

Lemma small_big' : forall v c v' c', step^* (v, c) (v', c')
                                     -> forall v'', eval v' c' v''
                                                    -> eval v c v''.
Proof.
  induct 1; eauto.
  cases y; eauto.
Qed.

Hint Resolve small_big'.

Theorem small_big : forall v c v', step^* (v, c) (v', Skip)
                                   -> eval v c v'.
Proof.
  eauto.
Qed.

Definition trsys_of (v : valuation) (c : cmd) : trsys (valuation * cmd) := {|
  Initial := {(v, c)};
  Step := step
|}.

Inductive context :=
| Hole
| CSeq (C : context) (c : cmd).

Inductive plug : context -> cmd -> cmd -> Prop :=
| PlugHole : forall c, plug Hole c c
| PlugSeq : forall c C c' c2,
  plug C c c'
  -> plug (CSeq C c2) c (Sequence c' c2).

Inductive step0 : valuation * cmd -> valuation * cmd -> Prop :=
| Step0Assign : forall v x e,
  step0 (v, Assign x e) (v $+ (x, interp e v), Skip)
| Step0Seq : forall v c2,
  step0 (v, Sequence Skip c2) (v, c2)
| Step0IfTrue : forall v e then_ else_,
  interp e v <> 0
  -> step0 (v, If e then_ else_) (v, then_)
| Step0IfFalse : forall v e then_ else_,
  interp e v = 0
  -> step0 (v, If e then_ else_) (v, else_)
| Step0WhileTrue : forall v e body,
  interp e v <> 0
  -> step0 (v, While e body) (v, Sequence body (While e body))
| Step0WhileFalse : forall v e body,
  interp e v = 0
  -> step0 (v, While e body) (v, Skip).

Inductive cstep : valuation * cmd -> valuation * cmd -> Prop :=
| CStep : forall C v c v' c' c1 c2,
  plug C c c1
  -> step0 (v, c) (v', c')
  -> plug C c' c2
  -> cstep (v, c1) (v', c2).

Hint Constructors plug step0 cstep.

Theorem step_cstep : forall v c v' c',
  step (v, c) (v', c')
  -> cstep (v, c) (v', c').
Proof.
  induct 1; repeat match goal with
                   | [ H : cstep _ _ |- _ ] => invert H
                   end; eauto.
Qed.

Hint Resolve step_cstep.

Lemma step0_step : forall v c v' c',
  step0 (v, c) (v', c')
  -> step (v, c) (v', c').
Proof.
  invert 1; eauto.
Qed.

Hint Resolve step0_step.

Lemma cstep_step' : forall C c0 c,
  plug C c0 c
  -> forall v' c'0 v c', step0 (v, c0) (v', c'0)
  -> plug C c'0 c'
  -> step (v, c) (v', c').
Proof.
  induct 1; simplify; repeat match goal with
                             | [ H : plug _ _ _ |- _ ] => invert1 H
                             end; eauto.
Qed.

Hint Resolve cstep_step'.

Theorem cstep_step : forall v c v' c',
  cstep (v, c) (v', c')
  -> step (v, c) (v', c').
Proof.
  invert 1; eauto.
Qed.
