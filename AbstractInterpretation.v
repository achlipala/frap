(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 8: Abstract Interpretation and Dataflow Analysis
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap Imp.

Set Implicit Arguments.


(* With model checking, we were able to find invariants automatically for
 * nontrivial transition systems.  With operational semantics, we're able to
 * build transition systems automatically from program syntax.  Let's put these
 * two sorts of examples together into an even more computationally efficient
 * technique: abstract interpretation. *)

(* Apologies for jumping right into abstract formal details, but that's what the
 * medium of Coq forces on us!  We will apply abstract interpretation to the
 * imperative language that we formalized in the last chapter.  Here's a record
 * capturing the idea of an abstract interpretation for that language. *)
Record absint := {
  Domain :> Set;
  (* We will represent concrete values (natural numbers) with this alternative,
   * abstract set.  This [:>] notation lets us treat any [absint] as its
   * [Domain], automatically.  See below for examples (e.g., return type of
   * [absint_interp]). *)
  Top : Domain;
  (* A universal (least informative) element, describing *all* concrete
   * values *)
  Constant : nat -> Domain;
  (* Most accurate representation of a constant *)
  Add : Domain -> Domain -> Domain;
  Subtract : Domain -> Domain -> Domain;
  Multiply : Domain -> Domain -> Domain;
  (* Abstract versions of arithmetic operators *)
  Join : Domain -> Domain -> Domain;
  (* Returns some new element that covers all cases of each of its inputs *)
  Represents : nat -> Domain -> Prop
  (* Which elements represent which numbers? *)
}.

(* That was a mouthful, but we still need to say what makes one of these
 * reasonable. *)
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

(* Here's a "bonus" condition that we'll sometimes use and sometimes not:
 * [Join] gives a *least* upper bound of its two arguments, such that any other
 * upper bound is also at or above the join. *)
Definition absint_complete (a : absint) :=
  forall x y z n, a.(Represents) n (a.(Join) x y)
                  -> (forall n, a.(Represents) n x -> a.(Represents) n z)
                  -> (forall n, a.(Represents) n y -> a.(Represents) n z)
                  -> a.(Represents) n z.

(* Let's ask [eauto] to try all of the above soundness rules automatically. *)
Hint Resolve TopSound ConstSound AddSound SubtractSound MultiplySound
     AddMonotone SubtractMonotone MultiplyMonotone
     JoinSoundLeft JoinSoundRight : core.


(** * Example: even-odd analysis *)

Inductive parity := Even | Odd | Either.
(* In this interpretation, every value either has known parity or not. *)

Definition isEven (n : nat) := exists k, n = k * 2.
Definition isOdd (n : nat) := exists k, n = k * 2 + 1.
(* Here are some convenient definitions of the parities. *)

(* BEGIN SPAN OF BORING THEOREMS ABOUT PARITY, WHICH WE WON'T EXPLAIN. *)

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

Hint Resolve isEven_0 isEven_1 isEven_S_Even isEven_S_Odd : core.

(* END SPAN OF BORING THEOREMS ABOUT PARITY. *)

(* Next, we are ready to implement the operators of the abstract
 * interpretation. *)

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
  | Odd, Odd => Even
  | _, _ => Either
  end.
(* Note subtleties with [Either]s above, to deal with underflow at zero! *)

Definition parity_multiply (x y : parity) :=
  match x, y with
  | Even, _ => Even
  | Odd, Odd => Odd
  | _, Even => Even
  | _, _ => Either
  end.

Definition parity_join (x y : parity) :=
  match x, y with
  | Even, Even => Even
  | Odd, Odd => Odd
  | _, _ => Either
  end.

(* What does it mean for a parity to classify a number correctly? *)
Inductive parity_rep : nat -> parity -> Prop :=
| PrEven : forall n,
  isEven n
  -> parity_rep n Even
| PrOdd : forall n,
  ~isEven n
  -> parity_rep n Odd
| PrEither : forall n,
  parity_rep n Either.

Hint Constructors parity_rep : core.

(* Putting it all together: *)
Definition parity_absint := {|
  Top := Either;
  Constant := parity_const;
  Add := parity_add;
  Subtract := parity_subtract;
  Multiply := parity_multiply;
  Join := parity_join;
  Represents := parity_rep
|}.

(* Now we prove soundness. *)

Lemma parity_const_sound : forall n,
  parity_rep n (parity_const n).
Proof.
  induct n; simplify; eauto.
  cases (parity_const n); simplify; eauto.
  invert IHn; eauto.
  invert IHn; eauto.
Qed.

Hint Resolve parity_const_sound : core.

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

Hint Resolve even_not_odd odd_not_even : core.

Lemma parity_join_complete : forall n x y,
  parity_rep n (parity_join x y)
  -> parity_rep n x \/ parity_rep n y.
Proof.
  simplify; cases x; cases y; simplify; propositional.
  assert (isEven n \/ isOdd n) by apply decide_parity.
  propositional; eauto using odd_notEven.
  assert (isEven n \/ isOdd n) by apply decide_parity.
  propositional; eauto using odd_notEven.
Qed.

Hint Resolve parity_join_complete : core.

(* The final proof uses some automation that we won't explain, to descend down
 * to the hearts of the interesting cases. *)

Theorem parity_sound : absint_sound parity_absint.
Proof.
  constructor; simplify; eauto;
  repeat match goal with
         | [ H : parity_rep _ _ |- _ ] => invert H
         | [ H : ~isEven _ |- _ ] => apply notEven_odd in H; invert H
         | [ H : isEven _ |- _ ] => invert H
         | [ p : parity |- _ ] => cases p; simplify; try equality
         end; try solve [ exfalso; eauto ]; try (constructor; try apply odd_notEven).

  (* We finish up by instantiating all those existential quantifiers in uses of
   * [isEven] and [isOdd]. *)
  exists (x0 + x); ring.
  exists (x0 + x); ring.
  exists (x0 + x); ring.
  exists (x0 + x + 1); ring.
  exists (x - x0); linear_arithmetic.
  exists (x - x0); linear_arithmetic.
  exists (x * x0 * 2); ring.
  exists ((x * 2 + 1) * x0); ring.
  exists (n * x); ring.
  exists ((x * 2 + 1) * x0); ring.
  exists (2 * x * x0 + x + x0); ring.
  exists (x * m); ring.
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

Theorem parity_complete : absint_complete parity_absint.
Proof.
  unfold absint_complete; simplify; eauto;
  repeat match goal with
         | [ H : parity_rep _ _ |- _ ] => invert H
         | [ H : ~isEven _ |- _ ] => apply notEven_odd in H; invert H
         | [ H : isEven _ |- _ ] => invert H
         | [ p : parity |- _ ] => cases p; simplify; try equality
         end; try solve [ exfalso; eauto ]; try (constructor; try apply odd_notEven).
  exists x0; ring.
  exists x0; ring.
Qed.


(** * Flow-insensitive analysis *)

(* So there's an example of an abstract interpretation, but how do we put it to
 * use to prove a theorem about a program?  Model checking was an example of a
 * *path-sensitive* analysis, where we accumulated a finite set of reachable
 * states of a system.  Abstract interpretation is usually *path-insensitive*,
 * and it may even be *flow-insensitive*, which means that we will find an
 * invariant that *ignores the current command altogether*.  Instead, the
 * invariant talks just about the valuation.  To help us do that, here's a type
 * definition: *)

Definition astate (a : absint) := fmap var a.

(* An abstract state maps variables to abstract elements.  The idea is that each
 * variable should take on a concrete value represented by its associated
 * abstract value.  These are only finite maps, so missing variables are allowed
 * to take arbitrary values. *)

(* An easy thing to do with an [astate] is evaluate an expression into another
 * abstract element. *)
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

(* To automate finding a suitable path-insensitive invariant, it's helpful to
 * compute the set of all assignments in a command. *)
Fixpoint assignmentsOf (c : cmd) : set (var * arith) :=
  match c with
  | Skip => {}
  | Assign x e => {(x, e)}
  | Sequence c1 c2 => assignmentsOf c1 \cup assignmentsOf c2
  | If _ c1 c2 => assignmentsOf c1 \cup assignmentsOf c2
  | While _ c1 => assignmentsOf c1
  end.

(* Any step in a program can be matched by either doing nothing or running one
 * of the assignments. *)
Theorem assignmentsOf_ok : forall v c v' c',
  step (v, c) (v', c')
  -> v' = v \/ exists x e, (x, e) \in assignmentsOf c
                        /\ v' = v $+ (x, interp e v).
Proof.
  induct 1; unfold Sets.In; simplify; eauto 10.
  first_order.
Qed.

(* Taking a step never adds new possible assignments. *)
Theorem assignmentsOf_monotone : forall v c v' c',
  step (v, c) (v', c')
  -> assignmentsOf c' \subseteq assignmentsOf c.
Proof.
  induct 1; simplify; sets.
  (* [sets]: simplify a goal involving set-theory operators. *)
Qed.

(* OK, now we know all the assignments that could happen.  We can start with
 * some initial [astate] and repeatedly pick some assignment and execute it to
 * modify [astate].  The trouble would be if, for instance in our even-odd
 * example, the program had two assignments ["x" <- 0] and ["x" <- 1].  We could
 * alternate between these assignments and waste our time forever, switching
 * ["x"] back and forth between [Even] and [Odd]!  Instead, when we run an
 * assignment, we want to merge the new abstract value with the old, getting a
 * new value guaranteed to overapproximate both of them.  [merge_astate] applies
 * that combination to all variables in two abstract states, using a finite-map
 * function [merge] from the book library.  Any variable found in at most one of
 * the two input maps is absent from the output map, and any variable found in
 * both maps is now mapped to the *join* of the original values, using a crucial
 * component of any abstract interpretation. *)
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

(* With [merge_astate] in place, we can define a new transition system,
 * capturing the essence of flow-insensitive abstract interpretations.  We can
 * either do nothing or we can pick an assignment, run it, and merge the result
 * into our growing candidate invariant. *)
Inductive flow_insensitive_step a (c : cmd) : astate a -> astate a -> Prop :=
| InsensitiveNothing : forall s,
  flow_insensitive_step c s s
| InsensitiveStep : forall x e s,
  (x, e) \in assignmentsOf c
  -> flow_insensitive_step c s (merge_astate s (s $+ (x, absint_interp e s))).

Hint Constructors flow_insensitive_step : core.

Definition flow_insensitive_trsys a (s : astate a) (c : cmd) := {|
  Initial := {s};
  Step := flow_insensitive_step (a := a) c
|}.

(* Now we revisit our studies of *simulation* from model checking.  After all,
 * that abstraction principle worked for transition systems in general,
 * regardless of whether we want to model-check afterward.  To define our
 * simulation relation, let's start with what makes an abstract state compatible
 * with a concrete valuation. *)
Definition insensitive_compatible a (s : astate a) (v : valuation) : Prop :=
  forall x xa, s $? x = Some xa
               -> (exists n, v $? x = Some n
                             /\ a.(Represents) n xa)
                  \/ (forall n, a.(Represents) n xa).
(* That is, when a variable is mapped to some abstract element, either that
 * variable has a compatible concrete value, or the variable has no value and
 * that element actually accepts all values (i.e., is probably [Top]). *)

(* Concrete state matches abstract when:
 * (1) The abstract state and valuation match up.
 * (2) The command's assignment set is contained within the set of the overall
 * program [c]. *)
Inductive Rinsensitive a (c : cmd) : valuation * cmd -> astate a -> Prop :=
| RInsensitive : forall v s c',
  insensitive_compatible s v
  -> assignmentsOf c' \subseteq assignmentsOf c
  -> Rinsensitive c (v, c') s.

Hint Constructors Rinsensitive : core.

(* A helpful decomposition property for compatibility *)
Lemma insensitive_compatible_add : forall a (s : astate a) v x na n,
  insensitive_compatible s v
  -> a.(Represents) n na
  -> insensitive_compatible (s $+ (x, na)) (v $+ (x, n)).
Proof.
  unfold insensitive_compatible; simplify.
  cases (x ==v x0); simplify; eauto.
  invert H1; eauto.
Qed.

(* Interpretation of expressions is compatible with [Represents]. *)
Theorem absint_interp_ok : forall a, absint_sound a
  -> forall (s : astate a) v e,
    insensitive_compatible s v
    -> a.(Represents) (interp e v) (absint_interp e s).
Proof.
  induct e; simplify; eauto.
  cases (s $? x); auto.
  unfold insensitive_compatible in H0.
  apply H0 in Heq.
  invert Heq.
  invert H1.
  propositional.
  rewrite H1.
  assumption.
  eauto.
Qed.

Hint Resolve insensitive_compatible_add absint_interp_ok : core.

(* With that, let's show that the flow-insensitive version of a program
 * *simulates* the original program, w.r.t. any sound abstract
 * interpretation. *)
Theorem insensitive_simulates : forall a (s : astate a) v c,
  absint_sound a
  -> insensitive_compatible s v
  -> simulates (Rinsensitive (a := a) c) (trsys_of v c) (flow_insensitive_trsys s c).
Proof.
  simplify.
  constructor; simplify.

  exists s; propositional.
  subst.
  constructor.
  assumption.
  sets.

  invert H1.
  cases st1'.
  assert (assignmentsOf c0 \subseteq assignmentsOf c).
  apply assignmentsOf_monotone in H2.
  sets.
  apply assignmentsOf_ok in H2.
  propositional; subst.
  eauto.
  invert H5.
  invert H2.
  propositional; subst.
  exists (merge_astate st2 (st2 $+ (x, absint_interp x0 st2))).
  propositional; eauto.
  econstructor; eauto.
  unfold insensitive_compatible in *; simplify.
  unfold merge_astate in *; simplify.
  cases (st2 $? x1); simplify; try equality.
  cases (x ==v x1); simplify; try equality.
  invert H5; eauto 6.
  rewrite Heq in H5.
  invert H5; eauto.
  apply H3 in Heq; propositional; eauto.
  invert H5; propositional; eauto.
Qed.

(* Now we need a way to come up with an invariant, in the form of one unifying
 * [astate].  This predicate formalizes one step from our informal recipe above:
 * run every possible assignment on an [astate] in some order, at each step
 * merging the new state with the old. *)
Inductive runAllAssignments a : set (var * arith) -> astate a -> astate a -> Prop :=
| RunDone : forall s,
  runAllAssignments {} s s
| RunStep : forall x e xes s s',
  runAllAssignments (constant xes) (merge_astate s (s $+ (x, absint_interp e s))) s'
  -> runAllAssignments (constant ((x, e) :: xes)) s s'.

(* Finally, we can iterate that process to take an initial state to a final one
 * that covers all possible executions. *)
Inductive iterate a (c : cmd) : astate a -> astate a -> Prop :=

(* If [runAllAssignments] has no effect, then we're done. *)
| IterateDone : forall s,
  runAllAssignments (assignmentsOf c) s s
  -> iterate c s s

(* Otherwise, use it to evolve one step and continue from there. *)
| IterateStep : forall s s' s'',
  runAllAssignments (assignmentsOf c) s s'
  -> iterate c s' s''
  -> iterate c s s''.

(* What does it mean for [s2] to capture all concrete states captured by
 * [s1]? *)
Definition subsumed a (s1 s2 : astate a) :=
  forall x, match s1 $? x with
            | None => s2 $? x = None
            | Some xa1 =>
              forall xa2, s2 $? x = Some xa2
                          -> forall n, a.(Represents) n xa1
                                       -> a.(Represents) n xa2
            end.

(* A few basic properties of subsumption *)

Theorem subsumed_refl : forall a (s : astate a),
  subsumed s s.
Proof.
  unfold subsumed; simplify.
  cases (s $? x); equality.
Qed.

Hint Resolve subsumed_refl : core.

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

Hint Resolve subsumed_use subsumed_use_empty : core.

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

Lemma subsumed_merge_left : forall a, absint_sound a
  -> forall s1 s2 : astate a,
    subsumed s1 (merge_astate s1 s2).
Proof.
  unfold subsumed, merge_astate; simplify.
  cases (s1 $? x); trivial.
  cases (s2 $? x); simplify; try equality.
  invert H0; eauto.
Qed.

Hint Resolve subsumed_merge_left : core.

Lemma subsumed_merge_both : forall a, absint_sound a
  -> absint_complete a
  -> forall s1 s2 s : astate a,
    subsumed s1 s
    -> subsumed s2 s
    -> subsumed (merge_astate s1 s2) s.
Proof.
  unfold subsumed, merge_astate; simplify.
  specialize (H1 x).
  specialize (H2 x).
  cases (s1 $? x); auto.
  cases (s2 $? x); auto.
  simplify.
  unfold absint_complete in *; eauto.
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

Hint Resolve subsumed_add : core.

(* A key property of interpreting expressions abstractly: it's *monotone*, in
 * the sense that moving up to a less precise [astate] leads to a less precise
 * interpretation result. *)
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

Hint Resolve absint_interp_monotone : core.

(* [runAllAssignments] also respects the subsumption order, in going from inputs
 * to outputs. *)
Lemma runAllAssignments_monotone : forall a, absint_sound a
  -> forall xes (s s' : astate a),
    runAllAssignments xes s s'
    -> subsumed s s'.
Proof.
  induct 2; simplify; eauto using subsumed_trans.
Qed.    

Hint Resolve runAllAssignments_monotone : core.

(* The output of [runAllAssignments] subsumes every state reachable by running a
 * single command. *)
Lemma runAllAssignments_ok : forall a, absint_sound a
  -> forall xes (s s' : astate a),
    runAllAssignments xes s s'
    -> forall x e, (x, e) \in xes
                -> subsumed (s $+ (x, absint_interp e s)) s'.
Proof.
  induct 2; unfold Sets.In; simplify; propositional.

  invert H2.
  apply subsumed_trans with (s2 := merge_astate s (s $+ (x0, absint_interp e0 s))); eauto.
  unfold subsumed, merge_astate; simplify.
  cases (x0 ==v x); subst; simplify.
  cases (s $? x); try equality.
  invert H1; eauto.
  cases (s $? x); try equality.
  invert 1; eauto.

  eapply subsumed_trans; try apply IHrunAllAssignments; eauto.
Qed.

(* Let's skip past this lemma to the theorem it supports. *)
Lemma iterate_ok' : forall a, absint_sound a
  -> absint_complete a
  -> forall c (s0 s s' : astate a),
    iterate c s s'
    -> subsumed s0 s
    -> invariantFor (flow_insensitive_trsys s0 c) (fun s'' => subsumed s'' s').
Proof.
  induct 3; simplify.

  apply invariant_induction; simplify; propositional; subst; auto.

  invert H4; auto.
  eapply runAllAssignments_ok in H5; eauto.
  apply subsumed_merge_both; auto.
  unfold subsumed, merge_astate; simplify.
  assert (subsumed s1 s) by assumption.
  specialize (H4 x0).
  specialize (H5 x0).
  cases (x ==v x0); subst; simplify; eauto.

  eauto using subsumed_trans.
Qed.

(* In a sound and complete abstract interpretation, [iterate] produces a genuine
 * invariant for the flow-insensitive execution of a command, phrased in terms
 * of subsumption. *)
Theorem iterate_ok : forall a, absint_sound a
  -> absint_complete a
  -> forall c (s0 s : astate a),
    iterate c s0 s
    -> invariantFor (flow_insensitive_trsys s0 c) (fun s' => subsumed s' s).
Proof.
  eauto using iterate_ok'.
Qed.

(* Here's our corral of automatic tactics for the day.  These do the boring
 * parts of iteration for us. *)
Ltac insensitive_simpl := unfold merge_astate; simplify; repeat simplify_map.
Ltac runAllAssignments := repeat (constructor; insensitive_simpl).
Ltac iterate1 := eapply IterateStep; [ simplify; runAllAssignments | ].
Ltac iterate_done := eapply IterateDone; simplify; runAllAssignments.

(* Here's a good first program to try our analysis on. *)
Definition straightline :=
  "a" <- 7;;
  "b" <- "b" + 2 * "a";;
  "a" <- "a" + "b".

(* A useful property, capturing the intended meaning of [Even] *)
Lemma final_even : forall (s s' : astate parity_absint) v x,
  insensitive_compatible s v
  -> subsumed s s'
  -> s' $? x = Some Even
  -> exists n, v $? x = Some n /\ isEven n.
Proof.
  unfold insensitive_compatible, subsumed; simplify.
  specialize (H x); specialize (H0 x).
  cases (s $? x); simplify.

  rewrite Heq in *.
  assert (Some d = Some d) by equality.
  apply H in H2.
  first_order.

  eapply H0 in H1.
  invert H1.
  eauto.
  assumption.

  specialize (H2 1).
  invert H2; try (exfalso; eauto).

  rewrite Heq in *.
  equality.
Qed.

(* Now we can verify the example program, saying that, when the program
 * finishes, variable ["b"] holds an even number. *)
Theorem straightline_even :
  invariantFor (trsys_of ($0 $+ ("a", 0) $+ ("b", 0)) straightline)
               (fun p => snd p = Skip
                         -> exists n, fst p $? "b" = Some n /\ isEven n).
Proof.
  (* We start off much as with model checking: strengthening the invariant. *)
  simplify.
  eapply invariant_weaken.

  (* Now we use simulation to switch to analyzing the flow-insensitive
   * program. *)
  unfold straightline.
  eapply invariant_simulates.
  apply insensitive_simulates with (s := $0 $+ ("a", Even) $+ ("b", Even))
                                   (a := parity_absint).
  apply parity_sound.
  unfold insensitive_compatible; simplify.
  cases (x ==v "b"); simplify.
  invert H; eauto.
  cases (x ==v "a"); simplify.
  invert H; eauto.
  equality.

  (* Now we apply the general principle that iteration is a sound way to find an
   * invariant for a flow-insensitive program. *)
  apply iterate_ok.
  apply parity_sound.
  apply parity_complete.

  (* Time to iterate!  It only takes one round of run-all-commands to reach an
   * [astate] that covers all reachable states.  Watch the [astate] change as we
   * iterate. *)
  iterate1.
  iterate_done.

  (* Now the routine step of showing that our calculated invariant implies the
   * original one from the theorem statement. *)
  invert 1.
  invert H0; simplify.
  eapply final_even; eauto; simplify; equality.
Qed.

(* Everything still works with programs that have conditions. *)
Definition less_straightline :=
  "a" <- 7;;
  when "c" then
    "b" <- "b" + 2 * "a"
  else
    "b" <- 18
  done.

Theorem less_straightline_even :
  invariantFor (trsys_of ($0 $+ ("a", 0) $+ ("b", 0)) less_straightline)
               (fun p => snd p = Skip
                         -> exists n, fst p $? "b" = Some n /\ isEven n).
Proof.
  simplify.
  eapply invariant_weaken.

  unfold less_straightline.
  eapply invariant_simulates.
  apply insensitive_simulates with (s := $0 $+ ("a", Even) $+ ("b", Even))
                                   (a := parity_absint).
  apply parity_sound.
  unfold insensitive_compatible; simplify.
  cases (x ==v "b"); simplify.
  invert H; eauto.
  cases (x ==v "a"); simplify.
  invert H; eauto.
  equality.

  apply iterate_ok.
  apply parity_sound.
  apply parity_complete.

  iterate1.
  iterate_done.

  invert 1.
  invert H0; simplify.
  eapply final_even; eauto; simplify; equality.
Qed.

(* It works for loops, too. *)
Definition loopy :=
  "n" <- 100;;
  "a" <- 0;;
  while "n" loop
    "a" <- "a" + "n";;
    "n" <- "n" - 2
  done.

Theorem loopy_even :
  invariantFor (trsys_of ($0 $+ ("n", 0) $+ ("a", 0)) loopy)
               (fun p => snd p = Skip
                         -> exists n, fst p $? "n" = Some n /\ isEven n).
Proof.
  simplify.
  eapply invariant_weaken.

  unfold loopy.
  eapply invariant_simulates.
  apply insensitive_simulates with (s := $0 $+ ("n", Even) $+ ("a", Even))
                                   (a := parity_absint).
  apply parity_sound.
  unfold insensitive_compatible; simplify.
  cases (x ==v "a"); simplify.
  invert H; eauto.
  cases (x ==v "n"); simplify.
  invert H; eauto.
  equality.

  apply iterate_ok.
  apply parity_sound.
  apply parity_complete.

  (* This time, the original [astate] is already fully general. *)
  iterate_done.

  invert 1.
  invert H0; simplify.
  eapply final_even; eauto; simplify; equality.
Qed.


(** * Flow-sensitive analysis *)

(* Flow-insensitive parity analysis will get stuck on a program like this one,
 * assuming, like before, that all variables start out initialized to zero. *)
Definition simple :=
  "a" <- 7;;
  "b" <- 8;;
  "a" <- "a" + "b";;
  "b" <- ("a" + 1) * ("b" + 1).
(* Unfortunately, some variables get assigned odd values in this program.
 * However the parity of a variable is still uniquely determined, given
 * *where we are in the program*!  Flow-sensitive analysis attaches a different
 * [astate] to every intermediate program, allowing us to handle such
 * potentially tricky cases.  We will be able to do a fully accurate
 * flow-sensitive parity analysis on this program. *)

(* Here, we can get away with a simpler definition of compatibility than last
 * time. *)
Definition compatible a (s : astate a) (v : valuation) : Prop :=
  forall x xa, s $? x = Some xa
               -> exists n, v $? x = Some n
                            /\ a.(Represents) n xa.

Lemma compatible_add : forall a (s : astate a) v x na n,
  compatible s v
  -> a.(Represents) n na
  -> compatible (s $+ (x, na)) (v $+ (x, n)).
Proof.
  unfold compatible; simplify.
  cases (x ==v x0); simplify; eauto.
  invert H1; eauto.
Qed.

Hint Resolve compatible_add : core.

(* A similar result follows about soundness of expression interpretation. *)
Theorem absint_interp_ok2 : forall a, absint_sound a
  -> forall (s : astate a) v e,
    compatible s v
    -> a.(Represents) (interp e v) (absint_interp e s).
Proof.
  induct e; simplify; eauto.
  cases (s $? x); auto.
  unfold compatible in H0.
  apply H0 in Heq.
  invert Heq.
  propositional.
  rewrite H2.
  assumption.
Qed.

Hint Resolve absint_interp_ok2 : core.

(* The new type of invariant we calculate as we go: a map from commands to
 * [astate]s.  The idea is that we populate this map with the commands that show
 * up as we step the program through full executions. *)
Definition astates (a : absint) := fmap cmd (astate a).

(* Here's an executable version of executing a command for a single step
 * abstractly.  The function is to return an [astates] capturing all the "places
 * we could end up" after running [c].  A complication is the argument [wrap],
 * which captures the fact that we are actually running [wrap c], which puts
 * some additional context around the command we're focusing on.  Note how
 * [wrap] is extended in the first recursive call for [Sequence].  Also, this
 * function returns [None] when [c] is [Skip], signalling that no step can be
 * taken. *)
Fixpoint absint_step a (s : astate a) (c : cmd) (wrap : cmd -> cmd) : option (astates a) :=
  match c with
  | Skip => None
  | Assign x e => Some ($0 $+ (wrap Skip, s $+ (x, absint_interp e s)))
  | Sequence c1 c2 =>
    match absint_step s c1 (fun c => wrap (Sequence c c2)) with
    | None => Some ($0 $+ (wrap c2, s))
    | v => v
    end
  | If _ then_ else_ => Some ($0 $+ (wrap then_, s) $+ (wrap else_, s))
  | While e body => Some ($0 $+ (wrap Skip, s) $+ (wrap (Sequence body (While e body)), s))
    (* We approximate mercilessly by ignoring the test expressions in
     * conditional control flow! *)
  end.

(* Below, it will be helpful to do case splits on whether two commands are
 * equal.  Here we automatically derive a proof that every pair of commands are
 * equal or aren't. *)
Lemma command_equal : forall c1 c2 : cmd, sumbool (c1 = c2) (c1 <> c2).
Proof.
  repeat decide equality.
Qed.

(* Key correctness property: every concrete step can be matched by one of the
 * choices returned by [absint_step]. *)
Theorem absint_step_ok : forall a, absint_sound a
  -> forall (s : astate a) v, compatible s v
  -> forall c v' c', step (v, c) (v', c')
                     -> forall wrap, exists ss s', absint_step s c wrap = Some ss
                                                   /\ ss $? wrap c' = Some s'
                                                   /\ compatible s' v'.
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

(* Now we can define a flow-sensitive, abstract transition-system version of a
 * program. *)
Inductive abs_step a : astate a * cmd -> astate a * cmd -> Prop :=
| AbsStep : forall s c ss s' c',
  absint_step s c (fun x => x) = Some ss
  -> ss $? c' = Some s'
  -> abs_step (s, c) (s', c').

Hint Constructors abs_step : core.

Definition absint_trsys a (c : cmd) := {|
  Initial := {($0, c)};
  Step := abs_step (a := a)
|}.

(* Now here's the pretty obvious simulation relation to use, to connect the
 * abstract version to the concrete version. *)
Inductive Rabsint a : valuation * cmd -> astate a * cmd -> Prop :=
| RAbsint : forall v s c,
  compatible s v
  -> Rabsint (v, c) (s, c).

Hint Constructors abs_step Rabsint : core.

Theorem absint_simulates : forall a v c,
  absint_sound a
  -> simulates (Rabsint (a := a)) (trsys_of v c) (absint_trsys a c).
Proof.
  simplify.
  constructor; simplify.

  exists ($0, c); propositional.
  subst.
  constructor.
  unfold compatible.
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

(* As before, we will compute candidate invariants iteratively.  This operation
 * helps us merge states as before, except now it works at the level of
 * [astates], which distinguish between commands.  A difference from
 * [merge_astate] is that, when one of the two inputs omits a mapping for some
 * command, we just keep the other map's entry for that command.  When both maps
 * know about a command, we merge their values with [merge_astate]. *)
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

(* This relation captures an iteration process where we consider steps from
 * every command in an [astates], running [absint_step] to proceed onward from
 * each point, using [merge_astates] to combine results. *)
Inductive oneStepClosure a : astates a -> astates a -> Prop :=
| OscNil :
  oneStepClosure $0 $0
| OscCons : forall ss c s ss' ss'',
  oneStepClosure ss ss'
  -> match absint_step s c (fun x => x) with
     | None => ss'
     | Some ss'' => merge_astates ss'' ss'
     end = ss''
  -> oneStepClosure (ss $+ (c, s)) ss''.

(* A derivative of basic subsumption, lifted to flow-sensitive states *)
Definition subsumeds a (ss1 ss2 : astates a) :=
  forall c s1, ss1 $? c = Some s1
               -> exists s2, ss2 $? c = Some s2
                             /\ subsumed s1 s2.

(* A few basic facts about [subsumeds] *)

Theorem subsumeds_refl : forall a (ss : astates a),
  subsumeds ss ss.
Proof.
  unfold subsumeds; simplify; eauto.
Qed.

Hint Resolve subsumeds_refl : core.

Lemma subsumeds_add : forall a (ss1 ss2 : astates a) c s1 s2,
  subsumeds ss1 ss2
  -> subsumed s1 s2
  -> subsumeds (ss1 $+ (c, s1)) (ss2 $+ (c, s2)).
Proof.
  unfold subsumeds; simplify.
  cases (command_equal c c0); subst; simplify; eauto.
  invert H1; eauto.
Qed.

Hint Resolve subsumeds_add : core.

Lemma subsumeds_empty : forall a (ss : astates a),
  subsumeds $0 ss.
Proof.
  unfold subsumeds; simplify.
  equality.
Qed.

Lemma subsumeds_add_left : forall a (ss1 ss2 : astates a) c s,
  ss2 $? c = Some s
  -> subsumeds ss1 ss2
  -> subsumeds (ss1 $+ (c, s)) ss2.
Proof.
  unfold subsumeds; simplify.
  cases (command_equal c c0); subst; simplify; eauto.
  invert H1; eauto.
Qed.

(* Now we just repeat [oneStepClosure] until finding a fixed point.
 * Note the arguments to this predicate, called like
 * [interpret ss worklist ss'].  [ss] is the state we're starting from, and
 * [ss'] is the final invariant we calculate.  [worklist] includes only those
 * command/[astate] pairs that we didn't already explore outward from.  It would
 * be pointless to continually explore from all the points we already
 * processed! *)
Inductive interpret a : astates a -> astates a -> astates a -> Prop :=

(* One-step closure produces a state that is subsumed within the original, so
 * we're done. *)
| InterpretDone : forall ss1 any ss2,
  oneStepClosure ss1 ss2
  -> subsumeds ss2 ss1
  -> interpret ss1 any ss1

(* One-step closure from the worklist produces a frontier of new states.
 * Continue interpreting from there, merging into [ss], but keeping only the new
 * states for the worklist. *)
| InterpretStep : forall ss worklist ss' ss'',
  oneStepClosure worklist ss'
  -> interpret (merge_astates ss ss') ss' ss''
  -> interpret ss worklist ss''.

(* One-step closure really does cover everything that one abstract step could
 * do. *)
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

  invert H2.
  invert H3.
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

  apply IHoneStepClosure in H3; auto.
  invert H3; propositional.
  cases (absint_step s c (fun x => x)); eauto.
  unfold merge_astates; simplify.
  rewrite H3.
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

(* Changing [astate] preserves behavior of [absint_step] on [Skip]. *)
Lemma absint_step_monotone_None : forall a (s : astate a) c wrap,
    absint_step s c wrap = None
    -> forall s' : astate a, absint_step s' c wrap = None.
Proof.
  induct c; simplify; try equality.
  cases (absint_step s c1 (fun c => wrap (c;; c2))); equality.
Qed.

(* Moving to a less specific [astate] preserves behavior of [absint_step] on
 * non-[Skip]. *)
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

(* [abs_step] outputs less specific states when its input gets less specific. *)
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

(* Let's skip describing this lemma, to move to the main event below. *)
Lemma interpret_sound' : forall c a, absint_sound a
  -> forall ss worklist ss' : astates a, interpret ss worklist ss'
    -> ss $? c = Some $0
    -> invariantFor (absint_trsys a c) (fun p => exists s, ss' $? snd p = Some s
                                                           /\ subsumed (fst p) s).
Proof.
  induct 2; simplify; subst.

  apply invariant_induction; simplify; propositional; subst; simplify; eauto.

  invert H3; propositional.
  cases s.
  cases s'.
  simplify.
  eapply abs_step_monotone in H4; eauto.
  invert H4; propositional.
  eapply oneStepClosure_sound in H4; eauto.
  invert H4; propositional.
  eapply H1 in H4.
  invert H4; propositional.
  eauto using subsumed_trans.

  apply IHinterpret.
  unfold merge_astates; simplify.
  rewrite H2.
  cases (ss' $? c); trivial.
  unfold merge_astate; simplify; equality.
Qed.

(* Iterating with a sound abstract interpretation produces an [astates] that
 * gives an invariant for the flow-insensitive abstract system. *)
Theorem interpret_sound : forall c a (ss : astates a),
  absint_sound a
  -> interpret ($0 $+ (c, $0)) ($0 $+ (c, $0)) ss
  -> invariantFor (absint_trsys a c) (fun p => exists s, ss $? snd p = Some s
                                                         /\ subsumed (fst p) s).
Proof.
  simplify.
  eapply interpret_sound'; eauto.
  simplify; equality.
Qed.

(* Now two lemmas that we prove to help the [simplify] tactic reduce uses of
 * [merge_astates]. *)

Lemma merge_astates_fok_parity : forall x : option (astate parity_absint),
  match x with Some x' => Some x' | None => None end = x.
Proof.
  simplify; cases x; equality.
Qed.

Lemma merge_astates_fok2_parity : forall x (y : option (astate parity_absint)),
    match y with
    | Some y' => Some (merge_astate x y')
    | None => Some x
    end = None -> False.
Proof.
  simplify; cases y; equality.
Qed.

Hint Resolve merge_astates_fok_parity merge_astates_fok2_parity : core.

(* Our second corral of tactics for the day, automating iteration *)
Ltac interpret_simpl := unfold merge_astates, merge_astate;
                       simplify; repeat simplify_map.
Ltac oneStepClosure := apply OscNil
                       || (eapply OscCons; [ oneStepClosure
                                           | interpret_simpl; reflexivity ]).
Ltac interpret1 := eapply InterpretStep; [ oneStepClosure | interpret_simpl ].
Ltac interpret_done := eapply InterpretDone; [ oneStepClosure
  | repeat (apply subsumeds_add_left || apply subsumeds_empty); (simplify; equality) ].

(* A flow-sensitive variant of [final_even] from before *)
Lemma final_even2 : forall (s s' : astate parity_absint) v x,
  compatible s v
  -> subsumed s s'
  -> s' $? x = Some Even
  -> exists n, v $? x = Some n /\ isEven n.
Proof.
  unfold insensitive_compatible, subsumed; simplify.
  specialize (H x); specialize (H0 x).
  cases (s $? x); simplify.

  rewrite Heq in *.
  assert (Some d = Some d) by equality.
  apply H in H2.
  first_order.

  eapply H0 in H1.
  invert H1.
  eauto.
  assumption.

  rewrite Heq in *.
  equality.
Qed.

(* Finally, we can analyze that simple program we started with! *)
Theorem simple_even : forall v,
  invariantFor (trsys_of v simple) (fun p => snd p = Skip
                                             -> exists n, fst p $? "b" = Some n /\ isEven n).
Proof.
  (* The beginning of the proof is just as before, using a flow-sensitive
   * simulation in place of flow-insensitive. *)
  simplify.
  eapply invariant_weaken.

  unfold simple.
  eapply invariant_simulates.
  apply absint_simulates with (a := parity_absint).
  apply parity_sound.

  apply interpret_sound.
  apply parity_sound.

  (* Time to iterate!  Note how steps are modifying [interpret]'s first argument
   * both by extending its domain and by generalizing the mappings of existing
   * commands. *)
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret_done.

  invert 1.
  first_order.
  invert H0; simplify.
  invert H1.
  eapply final_even2; eauto; simplify; try equality.
Qed.

(* This tricky program gives ["b"] different parity on different branches, but ["a"]
 * stays even. *)
Definition branchy :=
  "a" <- 8;;
  when "c" then
    "b" <- "a" + 4;;
    "a" <- "b"
  else
    "b" <- 7;;
    "a" <- "b" + 3
  done.

Theorem branchy_even : forall v,
  invariantFor (trsys_of v branchy) (fun p => snd p = Skip
                                              -> exists n, fst p $? "a" = Some n /\ isEven n).
Proof.
  simplify.
  eapply invariant_weaken.

  unfold branchy.
  eapply invariant_simulates.
  apply absint_simulates with (a := parity_absint).
  apply parity_sound.

  apply interpret_sound.
  apply parity_sound.

  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret_done.

  invert 1.
  first_order.
  invert H0; simplify.
  invert H1.
  eapply final_even2; eauto; simplify; equality.
Qed.

(* Here's a simple loop to analyze for evenness. *)
Definition easy :=
  "n" <- 10;;
  while "n" loop
    "n" <- "n" - 2
  done.

Theorem easy_even : forall v,
  invariantFor (trsys_of v easy) (fun p => snd p = Skip
                                           -> exists n, fst p $? "n" = Some n /\ isEven n).
Proof.
  simplify.
  eapply invariant_weaken.

  unfold easy.
  eapply invariant_simulates.
  apply absint_simulates with (a := parity_absint).
  apply parity_sound.

  apply interpret_sound.
  apply parity_sound.

  interpret1.
  interpret1.
  interpret1.
  interpret_done.

  invert 1.
  first_order.
  invert H0; simplify.
  invert H1.
  eapply final_even2; eauto; simplify; equality.
Qed.

(* We can also tackle the loop we handled with flow-insensitive analysis. *)
Theorem loopy_even_again : forall v,
  invariantFor (trsys_of v loopy) (fun p => snd p = Skip
                                            -> exists n, fst p $? "n" = Some n /\ isEven n).
Proof.
  simplify.
  eapply invariant_weaken.

  unfold loopy.
  eapply invariant_simulates.
  apply absint_simulates with (a := parity_absint).
  apply parity_sound.

  apply interpret_sound.
  apply parity_sound.

  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret_done.

  invert 1.
  first_order.
  invert H0; simplify.
  invert H1.
  eapply final_even2; eauto; simplify; equality.
Qed.


(** * Another abstract interpretation: intervals *)

(* We might also want to track intervals of natural numbers that a variable's
 * value must fall within. *)

Record interval := {
  Lower : nat;
  Upper : option nat
}.

Record interval_rep (n : nat) (i : interval) : Prop := {
  BoundedBelow : i.(Lower) <= n;
  BoundedAbove : match i.(Upper) with
                 | None => True
                 | Some n2 => n <= n2
                 end
}.

Hint Constructors interval_rep : core.

(* Test if an interval contains any values. *)
Definition impossible (x : interval) :=
  match x.(Upper) with
  | None => false
  | Some u => if x.(Lower) <=? u then false else true
  end.

(* To join two intervals, we check explicitly if either one is impossible.
 * Otherwise, we might join an impossible interval with a possible interval and
 * get a different, less precise possible interval, which can't be the *least*
 * upper bound of the two.  Rather, that least bound would need to be the
 * original possible interval.  Similarly, without this check, we could join two
 * impossible intervals and get a possible interval, when the least upper bound
 * must be impossible. *)
Definition interval_join (x y : interval) :=
  if impossible x then y
  else if impossible y then x
       else {| Lower := min x.(Lower) y.(Lower);
               Upper := match x.(Upper) with
                        | None => None
                        | Some x2 =>
                          match y.(Upper) with
                          | None => None
                          | Some y2 => Some (max x2 y2)
                          end
                        end |}.

Lemma interval_join_impossible1 : forall x y,
  impossible x = true
  -> interval_join x y = y.
Proof.
  unfold interval_join; simplify.
  rewrite H; equality.
Qed.

Lemma interval_join_impossible2 : forall x y,
  impossible x = false
  -> impossible y = true
  -> interval_join x y = x.
Proof.
  unfold interval_join; simplify.
  rewrite H, H0; equality.
Qed.

Lemma interval_join_possible : forall x y,
  impossible x = false
  -> impossible y = false
  -> interval_join x y = {| Lower := min x.(Lower) y.(Lower);
                            Upper := match x.(Upper) with
                                     | None => None
                                     | Some x2 =>
                                       match y.(Upper) with
                                       | None => None
                                       | Some y2 => Some (max x2 y2)
                                       end
                                     end |}.
Proof.
  unfold interval_join; simplify.
  rewrite H, H0; equality.
Qed.

Hint Rewrite interval_join_impossible1 interval_join_impossible2 interval_join_possible
     using assumption.

(* We'll reuse this function to define both addition and multiplication.
 * [f] gets filled in with either underlying operation. *)
Definition interval_combine (f : nat -> nat -> nat) (x y : interval) :=
  if impossible x || impossible y then
    {| Lower := 1; Upper := Some 0 |}
    (* Why this special case?  Otherwise, we might encounter the
     * counterintuitive result of adding an impossible interval to a possible
     * one to get a possible one.  Then we'd continue exploring out from the new
     * interval, wasting our time when, actually, that state is inherently
     * contradictory.  Note that we return a particular impossible interval in
     * this case. *)
  else {| Lower := f x.(Lower) y.(Lower);
          Upper := match x.(Upper) with
                   | None => None
                   | Some x2 =>
                     match y.(Upper) with
                     | None => None
                     | Some y2 => Some (f x2 y2)
                     end
                   end |}.

Lemma interval_combine_possible_fwd : forall f x y,
  impossible x = false
  -> impossible y = false
  -> interval_combine f x y
     = {| Lower := f x.(Lower) y.(Lower);
          Upper := match x.(Upper) with
                   | None => None
                   | Some x2 =>
                     match y.(Upper) with
                     | None => None
                     | Some y2 => Some (f x2 y2)
                     end
                   end |}.
Proof.
  unfold interval_combine; simplify.
  rewrite H, H0; simplify; equality.
Qed.

Lemma interval_combine_possible_bwd : forall f x y,
  impossible (interval_combine f x y) = false
  -> impossible x = false /\ impossible y = false.
Proof.
  unfold interval_combine; simplify.
  cases (impossible x); simplify.
  unfold impossible in H; simplify; equality.
  cases (impossible y); simplify; equality.
Qed.

Hint Rewrite interval_combine_possible_fwd using assumption.

Definition interval_subtract (x y : interval) :=
  if impossible x || impossible y then
    {| Lower := 1; Upper := Some 0 |}
  else
    {| Lower := match y.(Upper) with
                | None => 0
                | Some y2 => x.(Lower) - y2
                end;
       Upper := match x.(Upper) with
                | None => None
                | Some x2 => Some (x2 - y.(Lower))
                end |}.

Lemma interval_subtract_possible_fwd : forall x y,
  impossible x = false
  -> impossible y = false
  -> interval_subtract x y
     = {| Lower := match y.(Upper) with
                   | None => 0
                   | Some y2 => x.(Lower) - y2
                   end;
          Upper := match x.(Upper) with
                   | None => None
                   | Some x2 => Some (x2 - y.(Lower))
                   end |}.
Proof.
  unfold interval_subtract; simplify.
  rewrite H, H0; simplify; equality.
Qed.

Lemma interval_subtract_possible_bwd : forall x y,
  impossible (interval_subtract x y) = false
  -> impossible x = false /\ impossible y = false.
Proof.
  unfold interval_subtract; simplify.
  cases (impossible x); simplify.
  unfold impossible in H; simplify; equality.
  cases (impossible y); simplify; equality.
Qed.

Hint Rewrite interval_subtract_possible_fwd using assumption.

Definition interval_absint := {|
  Top := {| Lower := 0; Upper := None |};
  Constant := fun n => {| Lower := n;
                          Upper := Some n |};
  Add := interval_combine plus;
  Subtract := interval_subtract;
  Multiply := interval_combine mult;
  Join := interval_join;
  Represents := interval_rep
|}.

Hint Resolve mult_le_compat : core. (* Theorem from Coq standard library *)

(* When one interval implies another, and the first is possible, we can deduce
 * arithmetic relationships betwen their respective bounds. *)
Lemma interval_imply : forall k1 k2 u1 u2,
    impossible {| Lower := k1; Upper := u1 |} = false
    -> (forall n,
           interval_rep n {| Lower := k1; Upper := u1 |}
           -> interval_rep n {| Lower := k2; Upper := u2 |})
    -> k1 >= k2
       /\ match u2 with
          | None => True
          | Some u2' => match u1 with
                        | None => False
                        | Some u1' => u1' <= u2'
                        end
          end
       /\ impossible {| Lower := k2; Upper := u2 |} = false.
Proof.
  simplify.
  assert (k1 >= k2 \/ k1 < k2) by linear_arithmetic.
  invert H1.
  propositional.

  cases u2; auto.
  cases u1.
  assert (n >= n0 \/ n < n0) by linear_arithmetic.
  propositional.
  exfalso.
  assert (interval_rep n0 {| Lower := k2; Upper := Some n |}).
  apply H0.
  constructor; simplify; auto.
  unfold impossible in H; simplify.
  cases (k1 <=? n0); equality.
  invert H1; simplify; auto.
  linear_arithmetic.
  assert (interval_rep (S (max k1 n)) {| Lower := k2; Upper := Some n |}).
  apply H0.
  constructor; simplify; auto.
  linear_arithmetic.
  invert H1; simplify; linear_arithmetic.

  unfold impossible; simplify.
  cases u2; try equality.
  cases (k2 <=? n); try equality; try linear_arithmetic.
  exfalso.
  assert (interval_rep k1 {| Lower := k2; Upper := Some n |}).
  apply H0.
  unfold impossible in H; simplify.
  cases u1.
  cases (k1 <=? n0); try equality.
  constructor; simplify; linear_arithmetic.
  constructor; simplify; auto; linear_arithmetic.
  invert H1; simplify.
  linear_arithmetic.

  exfalso.
  assert (interval_rep k1 {| Lower := k2; Upper := u2 |}).
  apply H0.
  unfold impossible in H; simplify.
  cases u1.
  cases (k1 <=? n); try equality.
  constructor; simplify; linear_arithmetic.
  constructor; simplify; auto; linear_arithmetic.
  invert H1; simplify; try linear_arithmetic.
Qed.

Lemma impossible_sound : forall n x,
  interval_rep n x
  -> impossible x = true
  -> False.
Proof.
  invert 1.
  unfold impossible.
  cases (Upper x); simplify; try equality.
  cases (Lower x <=? n0); try equality.
  linear_arithmetic.
Qed.

Lemma mult_bound1 : forall a b n a' b',
  a' * b' <= n
  -> a <= a'
  -> b <= b'
  -> a * b <= n.
Proof.
  simplify.
  transitivity (a' * b'); eauto.
Qed.

Lemma mult_bound2 : forall a b n a' b',
  n <= a' * b'
  -> a' <= a
  -> b' <= b
  -> n <= a * b.
Proof.
  simplify.
  transitivity (a' * b'); eauto.
Qed.

Hint Immediate mult_bound1 mult_bound2 : core.

(* Now a bruiser of an automated proof, covering all the cases to show that this
 * abstraction is sound. *)
Theorem interval_sound : absint_sound interval_absint.
Proof.
  constructor; simplify; eauto;
  repeat match goal with
         | [ x : interval |- _ ] => cases x
         end; simplify;
  (repeat match goal with
          | [ _ : interval_rep _ (interval_join ?x ?y) |- _ ] =>
            cases (impossible x); simplify; eauto;
            cases (impossible y); simplify; eauto
          | [ H : interval_rep _ ?x |- _ ] =>
            cases (impossible x); [ exfalso; solve [ eauto using impossible_sound ] | invert H ]
          | [ H : impossible _ = _ |- _ ] => apply interval_combine_possible_bwd in H; propositional; simplify
          | [ H : impossible _ = _ |- _ ] => apply interval_subtract_possible_bwd in H; propositional; simplify
          | [ H : forall x, _ |- _ ] => apply interval_imply in H; auto
          | [ |- context[interval_join ?x _] ] =>
            match goal with
            | [ _ : impossible x = _ |- _ ] => fail 1
            | _ => cases (impossible x); simplify
            end
          | [ |- context[interval_join _ ?x] ] =>
            match goal with
            | [ _ : impossible x = _ |- _ ] => fail 1
            | _ => cases (impossible x); simplify
            end
          end; propositional; try constructor; simplify;
   repeat match goal with
          | [ H : Some _ = Some _ |- _] => invert H
          | [ _ : context[match ?X with _ => _ end] |- _ ] => cases X
          | [ |- context[match ?X with _ => _ end] ] => cases X
          end; eauto; try equality; try linear_arithmetic).
Qed.

(* As before, two helpful lemmas to feed the book library's automation about
 * [merge] *)

Lemma merge_astates_fok_interval : forall x : option (astate interval_absint),
  match x with Some x' => Some x' | None => None end = x.
Proof.
  simplify; cases x; equality.
Qed.

Lemma merge_astates_fok2_interval : forall x (y : option (astate interval_absint)),
    match y with
    | Some y' => Some (merge_astate x y')
    | None => Some x
    end = None -> False.
Proof.
  simplify; cases y; equality.
Qed.

Hint Resolve merge_astates_fok_interval merge_astates_fok2_interval : core.

(* The same kind of lemma we've proved for finishing off each proof by abstract
 * interpretation so far *)
Lemma final_upper : forall (s s' : astate interval_absint) v x l u,
  compatible s v
  -> subsumed s s'
  -> s' $? x = Some {| Lower := l; Upper := Some u |}
  -> exists n, v $? x = Some n /\ n <= u.
Proof.
  unfold compatible, subsumed; simplify.
  specialize (H x); specialize (H0 x).
  cases (s $? x); simplify.

  rewrite Heq in *.
  assert (Some d = Some d) by equality.
  apply H in H2.
  first_order.

  rewrite Heq in *.
  equality.
Qed.

Hint Rewrite min_l min_r max_l max_r using linear_arithmetic.

(* Let's see which intervals are computed for this program. *)
Definition interval_test :=
  "a" <- 6;;
  "b" <- 7;;
  when "c" then
    "a" <- "a" + "b"
  else
    "b" <- "a" * "b"
  done.

Theorem interval_test_ok : forall v,
  invariantFor (trsys_of v interval_test)
               (fun p => snd p = Skip
                         -> exists n, fst p $? "b" = Some n /\ n <= 42).
Proof.
  simplify.
  eapply invariant_weaken.

  unfold interval_test.
  eapply invariant_simulates.
  apply absint_simulates with (a := interval_absint).
  apply interval_sound.

  apply interpret_sound.
  apply interval_sound.

  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  interpret1.
  unfold interval_join, interval_combine; simplify.
  interpret_done.

  invert 1.
  first_order.
  invert H0; simplify.
  invert H1.
  eapply final_upper; eauto; simplify; equality.
Qed.


(** * Widening *)

(* Imagine analyzing this program with the previous abstract interpretation. *)
Definition ge7 :=
  "a" <- 7;;
  while "a" loop
    "a" <- "a" + 3
  done.
(* The inferred upper bound for ["a"] will keep going up forever, and the
 * iteration will never terminate!  An idea called *widening* will save us,
 * where for certain join operations we intentionally return an element less
 * precise than we really could.  For this example, let's say that when a new
 * interval has a higher upper bound than an old interval, we push the upper
 * bound to infinity for the joined interval.  Now there are no infinite
 * sequences of joins where the result is different each time. *)

(* It turns out that this operation is used so that, when combining "old" and
 * "new" elements, [x] is always old and [y] is always new. *)
Definition interval_widen (x y : interval) :=
  if impossible x then y
  else if impossible y then x
       else {| Lower := if x.(Lower) <=? y.(Lower) then x.(Lower) else 0;
               Upper := match x.(Upper) with
                        | None => None
                        | Some x2 =>
                          match y.(Upper) with
                          | None => None
                          | Some y2 => if y2 <=? x2 then Some x2 else None
                          end
                        end |}.

Lemma interval_widen_impossible1 : forall x y,
  impossible x = true
  -> interval_widen x y = y.
Proof.
  unfold interval_widen; simplify.
  rewrite H; equality.
Qed.

Lemma interval_widen_impossible2 : forall x y,
  impossible x = false
  -> impossible y = true
  -> interval_widen x y = x.
Proof.
  unfold interval_widen; simplify.
  rewrite H, H0; equality.
Qed.

Lemma interval_widen_possible : forall x y,
  impossible x = false
  -> impossible y = false
  -> interval_widen x y = {| Lower := if x.(Lower) <=? y.(Lower) then x.(Lower) else 0;
                             Upper := match x.(Upper) with
                                      | None => None
                                      | Some x2 =>
                                        match y.(Upper) with
                                        | None => None
                                        | Some y2 => if y2 <=? x2 then Some x2 else None
                                        end
                                      end |}.
Proof.
  unfold interval_widen; simplify.
  rewrite H, H0; equality.
Qed.

Hint Rewrite interval_widen_impossible1 interval_widen_impossible2 interval_widen_possible
     using assumption.

Definition interval_absint_widening := {|
  Top := {| Lower := 0; Upper := None |};
  Constant := fun n => {| Lower := n;
                          Upper := Some n |};
  Add := interval_combine plus;
  Subtract := interval_subtract;
  Multiply := interval_combine mult;
  Join := interval_widen;
  Represents := interval_rep
|}.

Theorem interval_widening_sound : absint_sound interval_absint_widening.
Proof.
  constructor; simplify; eauto;
  repeat match goal with
         | [ x : interval |- _ ] => cases x
         end; simplify;
  (repeat match goal with
          | [ _ : interval_rep _ (interval_widen ?x ?y) |- _ ] =>
            cases (impossible x); simplify; eauto;
            cases (impossible y); simplify; eauto
          | [ H : interval_rep _ ?x |- _ ] =>
            cases (impossible x); [ exfalso; solve [ eauto using impossible_sound ] | invert H ]
          | [ H : impossible _ = _ |- _ ] => apply interval_combine_possible_bwd in H; propositional; simplify
          | [ H : impossible _ = _ |- _ ] => apply interval_subtract_possible_bwd in H; propositional; simplify
          | [ H : forall x, _ |- _ ] => apply interval_imply in H; auto
          | [ |- context[interval_widen ?x _] ] =>
            match goal with
            | [ _ : impossible x = _ |- _ ] => fail 1
            | _ => cases (impossible x); simplify
            end
          | [ |- context[interval_widen _ ?x] ] =>
            match goal with
            | [ _ : impossible x = _ |- _ ] => fail 1
            | _ => cases (impossible x); simplify
            end
          end; propositional; try constructor; simplify;
   repeat match goal with
          | [ H : Some _ = Some _ |- _] => invert H
          | [ _ : context[match ?X with _ => _ end] |- _ ] => cases X
          | [ |- context[match ?X with _ => _ end] ] => cases X
          end; eauto; try equality; linear_arithmetic).
Qed.

Lemma merge_astates_fok_interval_widening : forall x : option (astate interval_absint_widening),
  match x with Some x' => Some x' | None => None end = x.
Proof.
  simplify; cases x; equality.
Qed.

Lemma merge_astates_fok2_interval_widening : forall x (y : option (astate interval_absint_widening)),
    match y with
    | Some y' => Some (merge_astate x y')
    | None => Some x
    end = None -> False.
Proof.
  simplify; cases y; equality.
Qed.

Hint Resolve merge_astates_fok_interval_widening merge_astates_fok2_interval_widening : core.

Lemma final_lower_widening : forall (s s' : astate interval_absint_widening) v x l,
  compatible s v
  -> subsumed s s'
  -> s' $? x = Some {| Lower := l; Upper := None |}
  -> exists n, v $? x = Some n /\ n >= l.
Proof.
  unfold compatible, subsumed; simplify.
  specialize (H x); specialize (H0 x).
  cases (s $? x); simplify.

  rewrite Heq in *.
  assert (Some d = Some d) by equality.
  apply H in H2.
  first_order.

  rewrite Heq in *.
  equality.
Qed.

(* Now, behold our quite-terminating analysis of this infinite-looping
 * program! *)
Theorem ge7_ok : forall v,
  invariantFor (trsys_of v ge7)
               (fun p => snd p = (while "a" loop "a" <- "a" + 3 done)
                         -> exists n, fst p $? "a" = Some n /\ n >= 7).
Proof.
  simplify.
  eapply invariant_weaken.

  unfold ge7.
  eapply invariant_simulates.
  apply absint_simulates with (a := interval_absint_widening).
  apply interval_widening_sound.

  apply interpret_sound.
  apply interval_widening_sound.

  interpret1.
  interpret1.
  interpret1.
  interpret1.
  unfold interval_combine, interval_widen; simplify.
  interpret1.
  unfold interval_combine, interval_widen; simplify.
  interpret1.
  unfold interval_combine, interval_widen; simplify.
  interpret_done.

  invert 1.
  first_order.
  invert H0; simplify.
  invert H1.
  eapply final_lower_widening; eauto; simplify; equality.
Qed.
