(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Coq material: unification and logic programming
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/
  * Much of the material comes from CPDT <http://adam.chlipala.net/cpdt/> by the same author. *)

Require Import Frap.

Set Implicit Arguments.


(** * Introducing Logic Programming *)

(* Recall the definition of addition from the standard library. *)

Definition real_plus := Eval compute in plus.
Print real_plus.

(* This is a recursive definition, in the style of functional programming.  We
 * might also follow the style of logic programming, which corresponds to the
 * inductive relations we have defined in previous chapters. *)

Inductive plusR : nat -> nat -> nat -> Prop :=
| PlusO : forall m, plusR O m m
| PlusS : forall n m r, plusR n m r
  -> plusR (S n) m (S r).

(* Intuitively, a fact [plusR n m r] only holds when [plus n m = r].  It is not
 * hard to prove this correspondence formally. *)

Theorem plus_plusR : forall n m,
  plusR n m (n + m).
Proof.
  induct n; simplify.

  constructor.

  constructor.
  apply IHn.
Qed.

(* We see here another instance of the very mechanical proof pattern that came
 * up before: keep trying constructors and hypotheses.  The tactic [auto] will
 * automate searching through sequences of that kind, when we prime it with good
 * suggestions of single proof steps to try, as with this command: *)

Hint Constructors plusR : core.

(* That is, every constructor of [plusR] should be considered as an atomic proof
 * step, from which we enumerate step sequences. *)

Theorem plus_plusR_snazzy : forall n m,
  plusR n m (n + m).
Proof.
  induct n; simplify; auto.
Qed.

Theorem plusR_plus : forall n m r,
  plusR n m r
  -> r = n + m.
Proof.
  induct 1; simplify; linear_arithmetic.
Qed.

(* With the functional definition of [plus], simple equalities about arithmetic
 * follow by computation. *)

Example four_plus_three : 4 + 3 = 7.
Proof.
  reflexivity.
Qed.

Print four_plus_three.

(* With the relational definition, the same equalities take more steps to prove,
 * but the process is completely mechanical.  For example, consider this
 * simple-minded manual proof search strategy.  The steps prefaced by [Fail] are
 * intended to fail; they're included for explanatory value, to mimic a
 * simple-minded try-everything strategy. *)

Example four_plus_three' : plusR 4 3 7.
Proof.
  Fail apply PlusO.
  apply PlusS.
  Fail apply PlusO.
  apply PlusS.
  Fail apply PlusO.
  apply PlusS.
  Fail apply PlusO.
  apply PlusS.
  apply PlusO.

  (* At this point the proof is completed.  It is no doubt clear that a simple
   * procedure could find all proofs of this kind for us.  We are just exploring
   * all possible proof trees, built from the two candidate steps [apply PlusO]
   * and [apply PlusS].  Thus, [auto] is another great match! *)
Restart.
  auto.
Qed.

Print four_plus_three'.

(* Let us try the same approach on a slightly more complex goal. *)

Example five_plus_three : plusR 5 3 8.
Proof.
  auto.

  (* This time, [auto] is not enough to make any progress.  Since even a single
   * candidate step may lead to an infinite space of possible proof trees,
   * [auto] is parameterized on the maximum depth of trees to consider.  The
   * default depth is 5, and it turns out that we need depth 6 to prove the
   * goal. *)

  auto 6.

  (* Sometimes it is useful to see a description of the proof tree that [auto]
   * finds, with the [info_auto] variant. *)

Restart.
  info_auto 6.
Qed.

(* The two key components of logic programming are _backtracking_ and
 * _unification_.  To see these techniques in action, consider this further
 * silly example.  Here our candidate proof steps will be reflexivity and
 * quantifier instantiation. *)

Example seven_minus_three : exists x, x + 3 = 7.
Proof.
  (* For explanatory purposes, let us simulate a user with minimal understanding
   * of arithmetic.  We start by choosing an instantiation for the quantifier.
   * It is relevant that [ex_intro] is the proof rule for existential-quantifier
   * instantiation. *)

  apply ex_intro with 0.
  Fail reflexivity.

  (* This seems to be a dead end.  Let us _backtrack_ to the point where we ran
   * [apply] and make a better alternative choice. *)

Restart.
  apply ex_intro with 4.
  reflexivity.
Qed.

(* The above was a fairly tame example of backtracking.  In general, any node in
 * an under-construction proof tree may be the destination of backtracking an
 * arbitrarily large number of times, as different candidate proof steps are
 * found not to lead to full proof trees, within the depth bound passed to [auto].
 *
 * Next we demonstrate unification, which will be easier when we switch to the
 * relational formulation of addition. *)

Example seven_minus_three' : exists x, plusR x 3 7.
Proof.
  (* We could attempt to guess the quantifier instantiation manually as before,
   * but here there is no need.  Instead of [apply], we use [eapply], which
   * proceeds with placeholder _unification variables_ standing in for those
   * parameters we wish to postpone guessing. *)

  eapply ex_intro.

  (* Now we can finish the proof with the right applications of [plusR]'s
   * constructors.  Note that new unification variables are being generated to
   * stand for new unknowns. *)

  apply PlusS.
  apply PlusS. apply PlusS. apply PlusS.
  apply PlusO.

  (* The [auto] tactic will not perform these sorts of steps that introduce
   * unification variables, but the [eauto] tactic will.  It is helpful to work
   * with two separate tactics, because proof search in the [eauto] style can
   * uncover many more potential proof trees and hence take much longer to
   * run. *)

Restart.
  info_eauto 6.
Qed.

(* This proof gives us our first example where logic programming simplifies
 * proof search compared to functional programming.  In general, functional
 * programs are only meant to be run in a single direction; a function has
 * disjoint sets of inputs and outputs.  In the last example, we effectively ran
 * a logic program backwards, deducing an input that gives rise to a certain
 * output.  The same works for deducing an unknown value of the other input. *)

Example seven_minus_four' : exists x, plusR 4 x 7.
Proof.
  eauto 6.
Qed.

(* By proving the right auxiliary facts, we can reason about specific functional
 * programs in the same way as we did above for a logic program.  Let us prove
 * that the constructors of [plusR] have natural interpretations as lemmas about
 * [plus].  We can find the first such lemma already proved in the standard
 * library, using the [SearchRewrite] command to find a library function proving
 * an equality whose lefthand or righthand side matches a pattern with
 * wildcards. *)

SearchRewrite (O + _).

(* The command [Hint Immediate] asks [auto] and [eauto] to consider this lemma
 * as a candidate step for any leaf of a proof tree, meaning that all premises
 * of the rule need to match hypotheses. *)

Hint Immediate plus_O_n : core.

(* The counterpart to [PlusS] we will prove ourselves. *)

Lemma plusS : forall n m r,
  n + m = r
  -> S n + m = S r.
Proof.
  linear_arithmetic.
Qed.

(* The command [Hint Resolve] adds a new candidate proof step, to be attempted
 * at any level of a proof tree, not just at leaves. *)

Hint Resolve plusS : core.

(* Now that we have registered the proper hints, we can replicate our previous
 * examples with the normal, functional addition [plus]. *)

Example seven_minus_three'' : exists x, x + 3 = 7.
Proof.
  eauto 6.
Qed.

Example seven_minus_four : exists x, 4 + x = 7.
Proof.
  eauto 6.
Qed.

(* This new hint database is far from a complete decision procedure, as we see in
 * a further example that [eauto] does not finish. *)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
Proof.
  eauto 6.
Abort.

(* A further lemma will be helpful. *)

Lemma plusO : forall n m,
  n = m
  -> n + 0 = m.
Proof.
  linear_arithmetic.
Qed.

Hint Resolve plusO : core.

(* Note that, if we consider the inputs to [plus] as the inputs of a
 * corresponding logic program, the new rule [plusO] introduces an ambiguity.
 * For instance, a sum [0 + 0] would match both of [plus_O_n] and [plusO],
 * depending on which operand we focus on.  This ambiguity may increase the
 * number of potential search trees, slowing proof search, but semantically it
 * presents no problems, and in fact it leads to an automated proof of the
 * present example. *)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
Proof.
  eauto 7.
Qed.

(* Just how much damage can be done by adding hints that grow the space of
 * possible proof trees?  A classic gotcha comes from unrestricted use of
 * transitivity, as embodied in this library theorem about equality: *)

Check eq_trans.

(* Hints are scoped over sections, so let us enter a section to contain the
 * effects of an unfortunate hint choice. *)

Section slow.
  Hint Resolve eq_trans : core.

  (* The following fact is false, but that does not stop [eauto] from taking a
   * very long time to search for proofs of it.  We use the handy [Time] command
   * to measure how long a proof step takes to run.  None of the following steps
   * make any progress. *)

  Example zero_minus_one : exists x, 1 + x = 0.
    Time eauto 1.
    Time eauto 2.
    Time eauto 3.
    Time eauto 4.
    Time eauto 5.

    (* We see worrying exponential growth in running time, and the [debug]
     * tactical helps us see where [eauto] is wasting its time, outputting a
     * trace of every proof step that is attempted.  The rule [eq_trans] applies
     * at every node of a proof tree, and [eauto] tries all such positions. *)

    debug eauto 3.
  Abort.
End slow.

(* Sometimes, though, transitivity is just what is needed to get a proof to go
 * through automatically with [eauto].  For those cases, we can use named
 * _hint databases_ to segregate hints into different groups that may be called
 * on as needed.  Here we put [eq_trans] into the database [slow]. *)

Hint Resolve eq_trans : slow.

Example from_one_to_zero : exists x, 1 + x = 0.
Proof.
  Time eauto.
  (* This [eauto] fails to prove the goal, but at least it takes substantially
   * less than the 2 seconds required above! *)
Abort.

(* One simple example from before runs in the same amount of time, avoiding
 * pollution by transitivity. *)

Example seven_minus_three_again : exists x, x + 3 = 7.
Proof.
  Time eauto 6.
Qed.

(* When we _do_ need transitivity, we ask for it explicitly. *)

Example needs_trans : forall x y, 1 + x = y
  -> y = 2
  -> exists z, z + x = 3.
Proof.
  info_eauto with slow.
Qed.

(* The [info] trace shows that [eq_trans] was used in just the position where it
 * is needed to complete the proof.  We also see that [auto] and [eauto] always
 * perform [intro] steps without counting them toward the bound on proof-tree
 * depth. *)


(** * Searching for Underconstrained Values *)

(* Recall the definition of the list length function. *)

Print Datatypes.length.

(* This function is easy to reason about in the forward direction, computing
 * output from input. *)

Example length_1_2 : length (1 :: 2 :: nil) = 2.
Proof.
  auto.
Qed.

Print length_1_2.

(* As in the last section, we will prove some lemmas to recast [length] in
 * logic-programming style, to help us compute inputs from outputs. *)

Theorem length_O : forall A, length (nil (A := A)) = O.
Proof.
  simplify; equality.
Qed.

Theorem length_S : forall A (h : A) t n,
  length t = n
  -> length (h :: t) = S n.
Proof.
  simplify; equality.
Qed.

Hint Resolve length_O length_S : core.

(* Let us apply these hints to prove that a [list nat] of length 2 exists.
 * (Here we register [length_O] with [Hint Resolve] instead of [Hint Immediate]
 * merely as a convenience to use the same command as for [length_S]; [Resolve]
 * and [Immediate] have the same meaning for a premise-free hint.) *)

Example length_is_2 : exists ls : list nat, length ls = 2.
Proof.
  eauto.

  (* Coq leaves for us two subgoals to prove... [nat]?!  We are being asked to
   * show that natural numbers exists.  Why?  Some unification variables of that
   * type were left undetermined, by the end of the proof.  Specifically, these
   * variables stand for the 2 elements of the list we find.  Of course it makes
   * sense that the list length follows without knowing the data values.  In Coq
   * 8.6 and up, the [Unshelve] command brings these goals to the forefront,
   * where we can solve each one with [exact O], but usually it is better to
   * avoid getting to such a point.
   *
   * To debug such situations, it can be helpful to print the current internal
   * representation of the proof, so we can see where the unification variables
   * show up. *)

  Show Proof.
Abort.

(* Paradoxically, we can make the proof-search process easier by constraining
 * the list further, so that proof search naturally locates appropriate data
 * elements by unification.  The library predicate [Forall] will be helpful. *)

Print Forall.

Example length_is_2 : exists ls : list nat, length ls = 2
  /\ Forall (fun n => n >= 1) ls.
Proof.
  eauto 9.
Qed.

(* We can see which list [eauto] found by printing the proof term. *)

Print length_is_2.

(* Let us try one more, fancier example.  First, we use a standard higher-order
 * function to define a function for summing all data elements of a list. *)

Definition sum := fold_right plus O.

(* Another basic lemma will be helpful to guide proof search. *)

Lemma plusO' : forall n m,
  n = m
  -> 0 + n = m.
Proof.
  linear_arithmetic.
Qed.

Hint Resolve plusO' : core.

(* Finally, we meet [Hint Extern], the command to register a custom hint.  That
 * is, we provide a pattern to match against goals during proof search.
 * Whenever the pattern matches, a tactic (given to the right of an arrow [=>])
 * is attempted.  Below, the number [1] gives a priority for this step.  Lower
 * priorities are tried before higher priorities, which can have a significant
 * effect on proof-search time, i.e. when we manage to give lower priorities to
 * the cheaper rules. *)

Hint Extern 1 (sum _ = _) => simplify : core.

(* Now we can find a length-2 list whose sum is 0. *)

Example length_and_sum : exists ls : list nat, length ls = 2
  /\ sum ls = O.
Proof.
  eauto 7.
Qed.

Print length_and_sum.

(* Printing the proof term shows the unsurprising list that is found.  Here is
 * an example where it is less obvious which list will be used.  Can you guess
 * which list [eauto] will choose? *)

Example length_and_sum' : exists ls : list nat, length ls = 5
  /\ sum ls = 42.
Proof.
  eauto 15.
Qed.

Print length_and_sum'.

(* We will give away part of the answer and say that the above list is less
 * interesting than we would like, because it contains too many zeroes.  A
 * further constraint forces a different solution for a smaller instance of the
 * problem. *)

Example length_and_sum'' : exists ls : list nat, length ls = 2
  /\ sum ls = 3
  /\ Forall (fun n => n <> 0) ls.
Proof.
  eauto 11.
Qed.

Print length_and_sum''.

(* We could continue through exercises of this kind, but even more interesting
 * than finding lists automatically is finding _programs_ automatically. *)


(** * Synthesizing Programs *)

(* Here is a simple syntax type for arithmetic expressions, similar to those we
 * have used several times before.  In this case, we allow expressions to
 * mention exactly one distinguished variable. *)

Inductive exp : Set :=
| Const (n : nat)
| Var
| Plus (e1 e2 : exp).

(* An inductive relation specifies the semantics of an expression, relating a
 * variable value and an expression to the expression value. *)

Inductive eval (var : nat) : exp -> nat -> Prop :=
| EvalConst : forall n, eval var (Const n) n
| EvalVar : eval var Var var
| EvalPlus : forall e1 e2 n1 n2, eval var e1 n1
  -> eval var e2 n2
  -> eval var (Plus e1 e2) (n1 + n2).

Hint Constructors eval : core.

(* We can use [auto] to execute the semantics for specific expressions. *)

Example eval1 : forall var, eval var (Plus Var (Plus (Const 8) Var)) (var + (8 + var)).
Proof.
  auto.
Qed.

(* Unfortunately, just the constructors of [eval] are not enough to prove
 * theorems like the following, which depends on an arithmetic identity. *)

Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
Proof.
  eauto.
Abort.

(* To help prove [eval1'], we prove an alternative version of [EvalPlus] that
 * inserts an extra equality premise.  This sort of staging is helpful to get
 * around limitations of [eauto]'s unification: [EvalPlus] as a direct hint will
 * only match goals whose results are already expressed as additions, rather
 * than as constants.  With the alternative version below, to prove the first
 * two premises, [eauto] is given free reign in deciding the values of [n1] and
 * [n2], while the third premise can then be proved by [reflexivity], no matter
 * how each of its sides is decomposed as a tree of additions. *)

Theorem EvalPlus' : forall var e1 e2 n1 n2 n, eval var e1 n1
  -> eval var e2 n2
  -> n1 + n2 = n
  -> eval var (Plus e1 e2) n.
Proof.
  simplify; subst; auto.
Qed.

Hint Resolve EvalPlus' : core.

(* Further, we instruct [eauto] to apply [ring], via [Hint Extern].  We should
 * try this step for any equality goal. *)

Section use_ring.
  Hint Extern 1 (_ = _) => ring : core.

  (* Now we can return to [eval1'] and prove it automatically. *)

  Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
  Proof.
    eauto.
  Qed.

  (* Now we are ready to take advantage of logic programming's flexibility by
   * searching for a program (arithmetic expression) that always evaluates to a
   * particular symbolic value. *)

  Example synthesize1 : exists e, forall var, eval var e (var + 7).
  Proof.
    eauto.
  Qed.

  Print synthesize1.

  (* Here are two more examples showing off our program-synthesis abilities. *)

  Example synthesize2 : exists e, forall var, eval var e (2 * var + 8).
  Proof.
    eauto.
  Qed.

  Print synthesize2.

  Example synthesize3 : exists e, forall var, eval var e (3 * var + 42).
  Proof.
    eauto.
  Qed.

  Print synthesize3.
End use_ring.

(* These examples show linear expressions over the variable [var].  Any such
 * expression is equivalent to [k * var + n] for some [k] and [n].  It is
 * probably not so surprising that we can prove that any expression's semantics
 * is equivalent to some such linear expression, but it is tedious to prove such
 * a fact manually.  To finish this section, we will use [eauto] to complete the
 * proof, finding [k] and [n] values automatically.
 *
 * We prove a series of lemmas and add them as hints.  We have alternate [eval]
 * constructor lemmas and some facts about arithmetic. *)

Theorem EvalConst' : forall var n m, n = m
  -> eval var (Const n) m.
Proof.
  simplify; subst; auto.
Qed.

Theorem EvalVar' : forall var n,
  var = n
  -> eval var Var n.
Proof.
  simplify; subst; auto.
Qed.

Hint Resolve EvalConst' EvalVar' : core.

(* Next, we prove a few hints that feel a bit like cheating, as they telegraph
 * the procedure for choosing values of [k] and [n].  Nonetheless, with these
 * lemmas in place, we achieve an automated proof without explicitly
 * orchestrating the lemmas' composition. *)
Section cheap_hints.
  Theorem zero_times : forall n m r,
    r = m
    -> r = 0 * n + m.
  Proof.
    linear_arithmetic.
  Qed.

  Theorem plus_0 : forall n r,
    r = n
    -> r = n + 0.
  Proof.
    linear_arithmetic.
  Qed.

  Theorem times_1 : forall n, n = 1 * n.
  Proof.
    linear_arithmetic.
  Qed.

  Theorem combine : forall x k1 k2 n1 n2,
    (k1 * x + n1) + (k2 * x + n2) = (k1 + k2) * x + (n1 + n2).
  Proof.
    simplify; ring.
  Qed.

  Hint Resolve zero_times plus_0 times_1 combine : core.

  Theorem linear : forall e, exists k n,
    forall var, eval var e (k * var + n).
  Proof.
    induct e; first_order; eauto.
  Qed.
End cheap_hints.

(* Let's try that again, without using those hints that give away the answer.
 * We should be able to coerce Coq into doing more of the thinking for us. *)

(* First, we will want to be able to use built-in tactic [ring_simplify] on
 * goals that contain unification variables, which will be the case at
 * intermediate points in our proof search.  We also want a bit more
 * standardization on ordering of variables within multiplications, to increase
 * the odds that different calculations can unify with each other.  Here is a
 * tactic that realizes those wishes. *)

Ltac robust_ring_simplify :=
  (* First, introduce regular names for all unification variables, because
   * [ring_simplify] freaks out when it meets a unification variable. *)
  repeat match goal with
         | [ |- context[?v] ] => is_evar v; remember v
         end;

  (* Now call the standard tactic. *)
  ring_simplify;

  (* Replace uses of the new variables with the original unification
   * variables. *)
  subst;

  (* Find and correct cases where commutativity doesn't agree across subterms of
   * the goal. *)
  repeat match goal with
         | [ |- context[?X * ?Y] ] =>
           match goal with
           | [ |- context[?Z * X] ] => rewrite (mult_comm Z X)
           end
         end.

(* This tactic is pretty expensive, but let's try it eventually whenever the
 * goal is an equality. *)
Hint Extern 5 (_ = _) => robust_ring_simplify : core.

(* The only other missing ingredient is priming Coq with some good ideas for
 * instantiating existential quantifiers.  These will all be tried in some
 * order, in a particular proof search. *)
Hint Extern 1 (exists n : nat, _) => exists 0 : core.
Hint Extern 1 (exists n : nat, _) => exists 1 : core.
Hint Extern 1 (exists n : nat, _) => eexists (_ + _) : core.
(* Note how this last hint uses [eexists] to provide an instantiation with
 * wildcards inside it.  Each underscore is replaced with a fresh unification
 * variable. *)

(* Now Coq figures out the recipe for us, and quite quickly, at that! *)
Theorem linear_snazzy : forall e, exists k n,
  forall var, eval var e (k * var + n).
Proof.
  induct e; first_order; eauto.
Qed.

(* Here's a quick tease using a feature that we'll explore fully in a later
 * class.  Let's use a mysterious construct [sigT] instead of [exists]. *)

Hint Extern 1 (sigT (fun n : nat => _)) => exists 0 : core.
Hint Extern 1 (sigT (fun n : nat => _)) => exists 1 : core.
Hint Extern 1 (sigT (fun n : nat => _)) => eexists (_ + _) : core.

Theorem linear_computable : forall e, sigT (fun k => sigT (fun n =>
  forall var, eval var e (k * var + n))).
Proof.
  induct e; first_order; eauto.
Defined.

(* Essentially the same proof search has completed.  This time, though, we ended
 * the proof with [Defined], which saves it as _transparent_, so details of the
 * "proof" can be consulted from the outside.  Actually, this "proof" is more
 * like a recursive program that finds [k] and [n], given [e]!  Let's add a
 * wrapper to make that idea more concrete. *)

Definition params (e : exp) : nat * nat :=
  let '(existT _ k (existT _ n _)) := linear_computable e in
  (k, n).

(* Now we can actually _run our proof_ to get normalized versions of particular
 * expressions. *)

Compute params (Plus (Const 7) (Plus Var (Plus (Const 8) Var))).


(* With Coq doing so much of the proof-search work for us, we might get
 * complacent and consider that any successful [eauto] invocation is as good as
 * any other.  However, because introduced unification variables may wind up
 * spread across multiple subgoals, running [eauto] can have a surprising kind
 * of _side effect_ across goals!  When a proof isn't solved completely by one
 * [eauto] call, the cross-subgoal side effects can break proofs that used to
 * work, when we introduce new premises or hints.  Here's an illustrative
 * example. *)
Section side_effect_sideshow.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable x : A.

  Hypothesis Px : P x.
  Hypothesis Qx : Q x.

  Theorem double_threat : exists y, P y /\ Q y.
  Proof.
    eexists; propositional.
    eauto.
    eauto.
  Qed.

  (* That was easy enough.  [eauto] could have solved the whole thing, but humor
   * me by considering this slightly less-automated proof.  Watch what happens
   * when we add a new premise. *)

  Variable z : A.
  Hypothesis Pz : P z.

  Theorem double_threat' : exists y, P y /\ Q y.
  Proof.
    eexists; propositional.
    eauto.
    eauto.
    (* Oh no!  The second subgoal isn't true anymore, because the first [eauto]
     * now matched [Pz] instead of [Px]. *)
  Restart.
    eauto.
    (* [eauto] can still find the whole proof, though. *)
  Qed.
End side_effect_sideshow.

(* Again, the moral of the story is: while proof search in Coq often feels
 * purely functional, unification variables allow imperative side effects to
 * reach across subgoals.  That's a tremendously useful feature for effective
 * proof automation, but it can also sneak up on you at times. *)


(** * More on [auto] Hints *)

(* Let us stop at this point and take stock of the possibilities for [auto] and
 * [eauto] hints.  Hints are contained within _hint databases_, which we have
 * seen extended in many examples so far.  When no hint database is specified, a
 * default database is used.  Hints in the default database are always used by
 * [auto] or [eauto].  The chance to extend hint databases imperatively is
 * important, because, in Ltac programming, we cannot create "global variables"
 * whose values can be extended seamlessly by different modules in different
 * source files.  We have seen the advantages of hints so far, where a proof
 * script using [auto] or [eauto] can automatically adapt to presence of new
 * hints.
 *
 * The basic hints for [auto] and [eauto] are: 
 * - [Hint Immediate lemma], asking to try solving a goal immediately by
 *   applying a lemma and discharging any hypotheses with a single proof step
 *   each
 * - [Hint Resolve lemma], which does the same but may add new premises that are
 *   themselves to be subjects of nested proof search
 * - [Hint Constructors pred], which acts like [Resolve] applied to every
 *   constructor of an inductive predicate
 * - [Hint Unfold ident], which tries unfolding [ident] when it appears at the
 *   head of a proof goal
 * Each of these [Hint] commands may be used with a suffix, as in
 * [Hint Resolve lemma : my_db], to add the hint only to the specified database,
 * so that it would only be used by, for instance, [auto with my_db].  An
 * additional argument to [auto] specifies the maximum depth of proof trees to
 * search in depth-first order, as in [auto 8] or [auto 8 with my_db].  The
 * default depth is 5.
 *
 * All of these [Hint] commands can be expressed with a more primitive hint
 * kind, [Extern].  A few more examples of [Hint Extern] should illustrate more
 * of the possibilities. *)

Theorem bool_neq : true <> false.
Proof.
  auto.
  (* No luck so far. *)
Abort.

(* It is hard to come up with a [bool]-specific hint that is not just a
 * restatement of the theorem we mean to prove.  Luckily, a simpler form
 * suffices, by appealing to the [equality] tactic. *)

Hint Extern 1 (_ <> _) => equality : core.

Theorem bool_neq : true <> false.
Proof.
  auto.
Qed.

(* A [Hint Extern] may be implemented with the full Ltac language.  This example
 * shows a case where a hint uses a [match]. *)

Section forall_and.
  Variable A : Set.
  Variables P Q : A -> Prop.

  Hypothesis both : forall x, P x /\ Q x.

  Theorem forall_and : forall z, P z.
  Proof.
    auto.

    (* The [auto] invocation makes no progress beyond what [intros] would have
     * accomplished.  An [auto] call will not apply the hypothesis [both] to
     * prove the goal, because the conclusion of [both] does not unify with the
     * conclusion of the goal.  However, we can teach [auto] to handle this
     * kind of goal. *)

    Hint Extern 1 (P ?X) =>
      match goal with
        | [ H : forall x, P x /\ _ |- _ ] => apply (proj1 (H X))
      end : core.

    auto.
  Qed.

  (* We see that an [Extern] pattern may bind unification variables that we use
   * in the associated tactic.  The function [proj1] is from the standard
   * library, for extracting a proof of [U] from a proof of [U /\ V]. *)

End forall_and.

(* After our success on this example, we might get more ambitious and seek to
 * generalize the hint to all possible predicates [P]. *)
Fail Hint Extern 1 (?P ?X) =>
  match goal with
    | [ H : forall x, P x /\ _ |- _ ] => apply (proj1 (H X))
  end : core.

(* Coq's [auto] hint databases work as tables mapping _head symbols_ to lists of
 * tactics to try.  Because of this, the constant head of an [Extern] pattern
 * must be determinable statically.  In our first [Extern] hint, the head symbol
 * was [not], since [x <> y] desugars to [not (x = y)]; and, in the second
 * example, the head symbol was [P].
 *
 * Fortunately, a more basic form of [Hint Extern] also applies.  We may simply
 * leave out the pattern to the left of the [=>], incorporating the
 * corresponding logic into the Ltac script. *)

Hint Extern 1 =>
  match goal with
    | [ H : forall x, ?P x /\ _ |- ?P ?X ] => apply (proj1 (H X))
  end : core.

(* Be forewarned that a [Hint Extern] of this kind will be applied at _every_
 * node of a proof tree, so an expensive Ltac script may slow proof search
 * significantly. *)


(** * Rewrite Hints *)

(* Another dimension of extensibility with hints is rewriting with quantified
 * equalities.  We have used the associated command [Hint Rewrite] in several
 * examples so far.  The [simplify] tactic uses these hints by calling the
 * built-in tactic [autorewrite].  Our rewrite hints have taken the form
 * [Hint Rewrite lemma], which by default adds them to the default hint database
 * [core]; but alternate hint databases may also be specified just as with,
 * e.g., [Hint Resolve].
 *
 * The next example shows a direct use of [autorewrite].  Note that, while
 * [Hint Rewrite] uses a default database, [autorewrite] requires that a
 * database be named. *)

Section autorewrite.
  Variable A : Set.
  Variable f : A -> A.

  Hypothesis f_f : forall x, f (f x) = f x.

  Hint Rewrite f_f.

  Lemma f_f_f : forall x, f (f (f x)) = f x.
  Proof.
    intros; autorewrite with core; reflexivity.
  Qed.

  (* There are a few ways in which [autorewrite] can lead to trouble when
   * insufficient care is taken in choosing hints.  First, the set of hints may
   * define a nonterminating rewrite system, in which case invocations to
   * [autorewrite] may not terminate.  Second, we may add hints that "lead
   * [autorewrite] down the wrong path."  For instance: *)

  Section garden_path.
    Variable g : A -> A.
    Hypothesis f_g : forall x, f x = g x.
    Hint Rewrite f_g.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
    Proof.
      intros; autorewrite with core.
    Abort.

    (* Our new hint was used to rewrite the goal into a form where the old hint
     * could no longer be applied.  This "non-monotonicity" of rewrite hints
     * contrasts with the situation for [auto], where new hints may slow down
     * proof search but can never "break" old proofs.  The key difference is
     * that [auto] either solves a goal or makes no changes to it, while
     * [autorewrite] may change goals without solving them.  The situation for
     * [eauto] is slightly more complicated, as changes to hint databases may
     * change the proof found for a particular goal, and that proof may
     * influence the settings of unification variables that appear elsewhere in
     * the proof state. *)

  Reset garden_path.

  (* The [autorewrite] tactic also works with quantified equalities that include
   * additional premises, but we must be careful to avoid similar incorrect
   * rewritings. *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
    Hint Rewrite f_g.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
    Proof.
      intros; autorewrite with core.
    Abort.

    (* The inappropriate rule fired the same three times as before, even though
     * we know we will not be able to prove the premises. *)

  Reset garden_path.

  (* Our final, successful attempt uses an extra argument to [Hint Rewrite] that
   * specifies a tactic to apply to generated premises.  Such a hint is only
   * used when the tactic succeeds for all premises, possibly leaving further
   * subgoals for some premises. *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
    Hint Rewrite f_g using assumption.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
    Proof.
      intros; autorewrite with core; reflexivity.
    Qed.

    (* We may still use [autorewrite] to apply [f_g] when the generated premise
     * is among our assumptions. *)

    Lemma f_f_f_g : forall x, P x -> f (f x) = g x.
    Proof.
      intros; autorewrite with core; reflexivity.
    Qed.
  End garden_path.

  (* It can also be useful to apply the [autorewrite with db in *] form, which
   * does rewriting in hypotheses, as well as in the conclusion. *)

  Lemma in_star : forall x y, f (f (f (f x))) = f (f y)
    -> f x = f (f (f y)).
  Proof.
    intros; autorewrite with core in *; assumption.
  Qed.

End autorewrite.

(* Many proofs can be automated in pleasantly modular ways with deft
 * combinations of [auto] and [autorewrite]. *)
