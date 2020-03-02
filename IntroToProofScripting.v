(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Coq material: introduction to proof scripting and the Ltac language
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/
  * Much of the material comes from CPDT <http://adam.chlipala.net/cpdt/> by the same author. *)

Require Import Frap.

Set Implicit Arguments.


(** * Ltac Programming Basics *)

(* We have already seen a few examples of Ltac programs, without much explanation.
 * Ltac is the proof scripting language built into Coq.  Actually, every
 * primitive step in our proofs has been a (degenerate, small) Ltac program.
 * Let's take a bottom-up look at more Ltac features.
 *
 * We've seen [match goal] tactics a few times so far.  They allow syntactic
 * inspection of hypothesis and conclusion formulas of current goals, where we
 * pick tactics to run based on what we find.  Here's a simple example to
 * find an [if] and do a case split based on its test expression. *)

Ltac find_if :=
  match goal with
    | [ |- if ?X then _ else _ ] => cases X
  end.

(* Here's a proof that becomes trivial, given [find_if].  You can imagine a
 * whole family of similar theorems that also become trivial. *)

Theorem hmm : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
Proof.
  simplify.
  repeat find_if. (* Note [repeat] for "run over and over until you can't
                   * progress." *)
  trivial. (* A fun tactic that consults a database of really boring steps. *)
  trivial.
  trivial.
  trivial.

  (* Let's write that again with more automation. *)
  Restart.
  simplify; repeat find_if; trivial.
Qed.

(* Another very useful Ltac building block is *context patterns*. *)

Ltac find_if_inside :=
  match goal with
    | [ |- context[if ?X then _ else _] ] => cases X
  end.

(* The behavior of this tactic is to find any subterm of the conclusion that is
 * an [if] and then [cases] the test expression.  This version subsumes
 * [find_if].  The general behavior of [context] (an Ltac keyword) is to allow
 * matching in arbitrary subterms. *)

Theorem hmm' : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
Proof.
  simplify; repeat find_if_inside; trivial.
Qed.

(* We can also use [find_if_inside] to prove goals that [find_if] does not
 * simplify sufficiently. *)

Theorem hmm2 : forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
Proof.
  simplify; repeat find_if_inside; equality.
Qed.


(** * Automating the two-thread locked-increment example from TransitionSystems *)

(* Let's experience the process of gradually automating the proof we finished
 * the last lecture with.  Here's the system-definition code, stripped of
 * comments. *)

Inductive increment_program :=
| Lock
| Read
| Write (local : nat)
| Unlock
| Done.

Record inc_state := {
  Locked : bool;
  Global : nat
}.

Record threaded_state shared private := {
  Shared : shared;
  Private : private
}.

Definition increment_state := threaded_state inc_state increment_program.

Inductive increment_init : increment_state -> Prop :=
| IncInit :
  increment_init {| Shared := {| Locked := false; Global := O |};
                    Private := Lock |}.

Inductive increment_step : increment_state -> increment_state -> Prop :=
| IncLock : forall g,
  increment_step {| Shared := {| Locked := false; Global := g |};
                    Private := Lock |}
                 {| Shared := {| Locked := true; Global := g |};
                    Private := Read |}
| IncRead : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Read |}
                 {| Shared := {| Locked := l; Global := g |};
                    Private := Write g |}
| IncWrite : forall l g v,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Write v |}
                 {| Shared := {| Locked := l; Global := S v |};
                    Private := Unlock |}
| IncUnlock : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Unlock |}
                 {| Shared := {| Locked := false; Global := g |};
                    Private := Done |}.

Definition increment_sys := {|
  Initial := increment_init;
  Step := increment_step
|}.

Inductive parallel1 shared private1 private2
  (init1 : threaded_state shared private1 -> Prop)
  (init2 : threaded_state shared private2 -> Prop)
  : threaded_state shared (private1 * private2) -> Prop :=
| Pinit : forall sh pr1 pr2,
  init1 {| Shared := sh; Private := pr1 |}
  -> init2 {| Shared := sh; Private := pr2 |}
  -> parallel1 init1 init2 {| Shared := sh; Private := (pr1, pr2) |}.

Inductive parallel2 shared private1 private2
          (step1 : threaded_state shared private1 -> threaded_state shared private1 -> Prop)
          (step2 : threaded_state shared private2 -> threaded_state shared private2 -> Prop)
          : threaded_state shared (private1 * private2)
            -> threaded_state shared (private1 * private2) -> Prop :=
| Pstep1 : forall sh pr1 pr2 sh' pr1',
  step1 {| Shared := sh; Private := pr1 |} {| Shared := sh'; Private := pr1' |}
  -> parallel2 step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1', pr2) |}
| Pstep2 : forall sh pr1 pr2 sh' pr2',
  step2 {| Shared := sh; Private := pr2 |} {| Shared := sh'; Private := pr2' |}
  -> parallel2 step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1, pr2') |}.

Definition parallel shared private1 private2
           (sys1 : trsys (threaded_state shared private1))
           (sys2 : trsys (threaded_state shared private2)) := {|
  Initial := parallel1 sys1.(Initial) sys2.(Initial);
  Step := parallel2 sys1.(Step) sys2.(Step)
|}.

Definition increment2_sys := parallel increment_sys increment_sys.

Definition contribution_from (pr : increment_program) : nat :=
  match pr with
  | Unlock => 1
  | Done => 1
  | _ => 0
  end.

Definition has_lock (pr : increment_program) : bool :=
  match pr with
  | Read => true
  | Write _ => true
  | Unlock => true
  | _ => false
  end.

Definition shared_from_private (pr1 pr2 : increment_program) :=
  {| Locked := has_lock pr1 || has_lock pr2;
     Global := contribution_from pr1 + contribution_from pr2 |}.

Definition instruction_ok (self other : increment_program) :=
  match self with
  | Lock => True
  | Read => has_lock other = false
  | Write n => has_lock other = false /\ n = contribution_from other
  | Unlock => has_lock other = false
  | Done => True
  end.

Inductive increment2_invariant :
  threaded_state inc_state (increment_program * increment_program) -> Prop :=
| Inc2Inv : forall pr1 pr2,
  instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> increment2_invariant {| Shared := shared_from_private pr1 pr2; Private := (pr1, pr2) |}.

Lemma Inc2Inv' : forall sh pr1 pr2,
  sh = shared_from_private pr1 pr2
  -> instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> increment2_invariant {| Shared := sh; Private := (pr1, pr2) |}.
Proof.
  simplify.
  rewrite H.
  apply Inc2Inv; assumption.
Qed.

(* OK, HERE is where prove the main theorem.  This source file doesn't leave a
 * record of the trail of intermediate, less-automated versions, but we develop
 * it step-by-step in class. *)

Theorem increment2_invariant_ok : invariantFor increment2_sys increment2_invariant.
Proof.
  apply invariant_induction; simplify;
    repeat (match goal with
            | [ H : parallel1 _ _ _ |- _ ] => invert H
            | [ H : parallel2 _ _ _ _ |- _ ] => invert H
            | [ H : increment_init _ |- _ ] => invert H
            | [ H : increment2_invariant _ |- _ ] => invert H
            | [ H : increment_step _ _ |- _ ] => invert H
            | [ H : instruction_ok ?pr _ |- _ ] => cases pr
            | [ |- increment2_invariant _ ] => apply Inc2Inv'
            | [ |- context[shared_from_private] ] => unfold shared_from_private
            end; simplify; try equality).
Qed.


(** * Implementing some of [propositional] ourselves *)

(* In class, we develop our own implementation of [propositional] one feature
 * at a time, but here's just the final product.  To understand it, we print
 * the definitions of the logical connectives.  Interestingly enough, they are
 * special cases of the machinery we met last time for inductive relations! *)

Print True.
Print False.
Locate "/\".
Print and.
Locate "\/".
Print or.
(* Implication ([->]) is built into Coq, so nothing to look up there. *)

Ltac my_tauto :=
  repeat match goal with
	   | [ H : ?P |- ?P ] => exact H

	   | [ |- True ] => constructor
	   | [ |- _ /\ _ ] => constructor
	   | [ |- _ -> _ ] => intro

	   | [ H : False |- _ ] => cases H
	   | [ H : _ /\ _ |- _ ] => cases H
	   | [ H : _ \/ _ |- _ ] => cases H

	   | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => specialize (H1 H2)
	 end.

(* Note on some new tactics:
 * - [intro]: goes from proving [P1 -> P2] to proving [P2] with [P1] as a
 *   hypothesis.
 * - [specialize (H e1 .. eN)]: replace a hypothesis with a version that is
 *   specialized to a provided set of arguments (for quantified variables or
 *   local hypotheses from implications).  By convention, when the argument to
 *   [specialize] is an application of a hypothesis [H] to a set of arguments,
 *   the result of the specialization replaces [H]. *)

Section propositional.
  Variables P Q R : Prop.

  Theorem propositional : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
  Proof.
    my_tauto.
  Qed.
End propositional.

(* [match goal] has useful backtracking semantics.  When one rule fails, we
 * backtrack automatically to the next one. *)

(* For instance, this (unnecessarily verbose) proof script works: *)

Theorem m1 : True.
Proof.
  match goal with
    | [ |- _ ] => intro
    | [ |- True ] => constructor
  end.
Qed.

(* The example shows how failure can move to a different pattern within a
 * [match].  Failure can also trigger an attempt to find _a different way of
 * matching a single pattern_.  Consider another example: *)

Theorem m2 : forall P Q R : Prop, P -> Q -> R -> Q.
Proof.
  intros; match goal with
            | [ H : _ |- _ ] => idtac H
          end.

  (* Coq prints "[H1]".  By applying [idtac] with an argument, a convenient
   * debugging tool for "leaking information out of [match]es," we see that
   * this [match] first tries binding [H] to [H1], which cannot be used to prove
   * [Q].  Nonetheless, the following variation on the tactic succeeds at
   * proving the goal: *)

  match goal with
    | [ H : _ |- _ ] => idtac H; exact H
  end.
Qed.

(* The tactic first unifies [H] with [H1], as before, but [exact H] fails in
 * that case, so the tactic engine searches for more possible values of [H].
 * Eventually, it arrives at the correct value, so that [exact H] and the
 * overall tactic succeed. *)

(* Let's try some more ambitious reasoning, with quantifiers.  We'll be
 * instantiating quantified facts heuristically.  If we're not careful, we get
 * in a loop repeating the same instantiation forever.  We'll need a way to
 * check that a fact is not already known.  Here's a tactic: *)

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
      (* A hypothesis already asserts this fact. *)
    | _ =>
      match P with
        | ?P1 /\ ?P2 =>
          (* Check each conjunct of [P] separately, since they might be known by
           * different means. *)
          first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
          (* If we manage to get this far, then we found no redundancy, so
           * declare success. *)
      end
  end.

(* The number for [fail N] indicates failing at the backtracking point [N]
 * levels out from where we are.  [first] applies the first tactic that does not
 * fail. *)

(* This tactic adds a fact to the context, only if it is not not already
 * present. *)

Ltac extend pf :=
  let t := type of pf in
    notHyp t; pose proof pf.

(* With these tactics defined, we can write a tactic [completer] for, among
 * other things, adding to the context all consequences of a set of simple
 * first-order formulas. *)

Ltac completer :=
  repeat match goal with
	   | [ H : _ /\ _ |- _ ] => cases H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')

           | [ |- _ /\ _ ] => constructor
           | [ |- forall x, _ ] => intro
           | [ |- _ -> _ ] => intro
             (* Interestingly, the last rule is redundant with the second-last.
              * See CPDT for details.... *)
         end.

Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo : forall (y x : A), P x -> S x.
  Proof.
    completer.
    assumption.
  Qed.
End firstorder.


(** * Functional Programming in Ltac *)

(* Let's write a list-length function in Ltac rather than Gallina.  In class,
 * we'll muddle through some intermediate versions before getting to the first
 * version that at least parses. *)

Module Import FirstTry.
  Ltac length ls :=
    match ls with
    | nil => O
    | _ :: ?ls' => constr:(S (length ls'))
    end.
End FirstTry.

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
Abort.

(* Something went wrong there. *)

Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' =>
      let ls'' := length ls' in
        constr:(S ls'')
  end.

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
Abort.

(* Here's a [map] implementation in Ltac.  Strangely, it needs to be passed the
 * type of the new list explicitly. *)

Ltac map T f :=
  let rec map' ls :=
    match ls with
      | nil => constr:(@nil T)
      | ?x :: ?ls' =>
        let x' := f x in
          let ls'' := map' ls' in
            constr:(x' :: ls'')
    end in
  map'.

Goal False.
  let ls := map (nat * nat)%type ltac:(fun x => constr:((x, x))) (1 :: 2 :: 3 :: nil) in
    pose ls.
Abort.

(* Now let's revisit [length] and see how we might implement "printf debugging"
 * for it. *)

Module Import WithPrinting.
  Ltac length ls :=
    idtac ls;
    match ls with
    | nil => O
    | _ :: ?ls' =>
      let ls'' := length ls' in
      constr:(S ls'')
    end.
End WithPrinting.

Goal False.
  (*let n := length (1 :: 2 :: 3 :: nil) in
    pose n.*)
  (* Oh, that has a dynamic type error. *)
Abort.

(* The problem is that Ltac as a language contains several datatypes.  One of
 * them is "tactic sequence," which can't be mixed with other datatypes like
 * "term in the logic."  Tactic sequences don't return results.  We can use
 * continuation-passing style as a mitigation. *)

Module Import WithPrintingFixed.
  Ltac length ls k :=
    idtac ls;
    match ls with
    | nil => k O
    | _ :: ?ls' => length ls' ltac:(fun n => k (S n))
    end.
End WithPrintingFixed.

Goal False.
  length (1 :: 2 :: 3 :: nil) ltac:(fun n => pose n).
Abort.

(* However, it's not always convenient to use continuation passing style
 * everywhere, so cool kids use the following hack to sneak side effects
 * into otherwise functional Ltac code: *)
Module Import WithPrintingFixedWithoutContinuations.
  Ltac length ls :=
    let __ := match constr:(Set) with
              | _ => (* put all your side effects here:*)
                     idtac ls; assert (ls = ls) by equality
              end in
    match ls with
    | nil => constr:(O)
    | _ :: ?ls' => let L := length ls' in constr:(S L)
    end.
End WithPrintingFixedWithoutContinuations.

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
  pose n.
Abort.

(** * Recursive Proof Search *)

(* Let's work on a tactic to try all possible instantiations of quantified
 * hypotheses, attempting to find out where the goal becomes obvious. *)

Ltac inster n :=
  intuition; (* <-- A fancier version of [propositional] whose details we won't
              *     dwell on *)
    match n with
      | S ?n' =>
        match goal with
          | [ H : forall x : ?T, _, y : ?T |- _ ] => pose proof (H y); inster n'
        end
    end.

(* Important: when one recursive call fails (happens when [n] reaches zero and
 * [intuition] leaves some open goals), the backtracking semantics of
 * [match goal] cause us to try the next instantiation! *)

Section test_inster.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable f : A -> A.
  Variable g : A -> A -> A.

  Hypothesis H1 : forall x y, P (g x y) -> Q (f x).

  Theorem test_inster : forall x, P (g x x) -> Q (f x).
  Proof.
    inster 2.
  Qed.

  Hypothesis H3 : forall u v, P u /\ P v /\ u <> v -> P (g u v).
  Hypothesis H4 : forall u, Q (f u) -> P u /\ P (f u).

  Theorem test_inster2 : forall x y, x <> y -> P x -> Q (f y) -> Q (f x).
  Proof.
    inster 3.
  Qed.
End test_inster.

(** ** A fancier example of proof search (probably skipped on first
       reading/run-through) *)

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).
Ltac imp := unfold imp; firstorder.

(** These lemmas about [imp] will be useful in the tactic that we will write. *)

Theorem and_True_prem : forall P Q,
  (P /\ True --> Q)
  -> (P --> Q).
Proof.
  imp.
Qed.

Theorem and_True_conc : forall P Q,
  (P --> Q /\ True)
  -> (P --> Q).
Proof.
  imp.
Qed.

Theorem pick_prem1 : forall P Q R S,
  (P /\ (Q /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
Proof.
  imp.
Qed.

Theorem pick_prem2 : forall P Q R S,
  (Q /\ (P /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
Proof.
  imp.
Qed.

Theorem comm_prem : forall P Q R,
  (P /\ Q --> R)
  -> (Q /\ P --> R).
Proof.
  imp.
Qed.

Theorem pick_conc1 : forall P Q R S,
  (S --> P /\ (Q /\ R))
  -> (S --> (P /\ Q) /\ R).
Proof.
  imp.
Qed.

Theorem pick_conc2 : forall P Q R S,
  (S --> Q /\ (P /\ R))
  -> (S --> (P /\ Q) /\ R).
Proof.
  imp.
Qed.

Theorem comm_conc : forall P Q R,
  (R --> P /\ Q)
  -> (R --> Q /\ P).
Proof.
  imp.
Qed.

Ltac search_prem tac :=
  let rec search P :=
    tac
    || (apply and_True_prem; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply pick_prem1; search P1)
           || (apply pick_prem2; search P2)
       end
  in match goal with
       | [ |- ?P /\ _ --> _ ] => search P
       | [ |- _ /\ ?P --> _ ] => apply comm_prem; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_prem; tac))
     end.

Ltac search_conc tac :=
  let rec search P :=
    tac
    || (apply and_True_conc; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply pick_conc1; search P1)
           || (apply pick_conc2; search P2)
       end
  in match goal with
       | [ |- _ --> ?P /\ _ ] => search P
       | [ |- _ --> _ /\ ?P ] => apply comm_conc; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_conc; tac))
     end.

Theorem False_prem : forall P Q,
  False /\ P --> Q.
Proof.
  imp.
Qed.

Theorem True_conc : forall P Q : Prop,
  (P --> Q)
  -> (P --> True /\ Q).
Proof.
  imp.
Qed.

Theorem Match : forall P Q R : Prop,
  (Q --> R)
  -> (P /\ Q --> P /\ R).
Proof.
  imp.
Qed.

Theorem ex_prem : forall (T : Type) (P : T -> Prop) (Q R : Prop),
  (forall x, P x /\ Q --> R)
  -> (ex P /\ Q --> R).
Proof.
  imp.
Qed.

Theorem ex_conc : forall (T : Type) (P : T -> Prop) (Q R : Prop) x,
  (Q --> P x /\ R)
  -> (Q --> ex P /\ R).
Proof.
  imp.
Qed.

Theorem imp_True : forall P,
  P --> True.
Proof.
  imp.
Qed.

Ltac matcher :=
  intros;
    repeat search_prem ltac:(simple apply False_prem || (simple apply ex_prem; intro));
      repeat search_conc ltac:(simple apply True_conc || simple eapply ex_conc
        || search_prem ltac:(simple apply Match));
      try simple apply imp_True.

(* Our tactic succeeds at proving a simple example. *)

Theorem t2 : forall P Q : Prop,
  Q /\ (P /\ False) /\ P --> P /\ Q.
Proof.
  matcher.
Qed.

(* In the generated proof, we find a trace of the workings of the search tactics. *)

Print t2.

(* We can also see that [matcher] is well-suited for cases where some human
 * intervention is needed after the automation finishes. *)

Theorem t3 : forall P Q R : Prop,
  P /\ Q --> Q /\ R /\ P.
Proof.
  matcher.
Abort.

(* The [matcher] tactic even succeeds at guessing quantifier instantiations.  It
 * is the unification that occurs in uses of the [Match] lemma that does the
 * real work here. *)

Theorem t4 : forall (P : nat -> Prop) Q, (exists x, P x /\ Q) --> Q /\ (exists x, P x).
Proof.
  matcher.
Qed.

Print t4.


(** * Creating Unification Variables *)

(* A final useful ingredient in tactic crafting is the ability to allocate new
 * unification variables explicitly.  Before we are ready to write a tactic, we
 * can try out its ingredients one at a time. *)

Theorem t5 : (forall x : nat, S x > x) -> 2 > 1.
Proof.
  intros.

  evar (y : nat).

  let y' := eval unfold y in y in
    clear y; specialize (H y').

  apply H.
Qed.

Ltac newEvar T k :=
  let x := fresh "x" in
  evar (x : T);
  let x' := eval unfold x in x in
    clear x; k x'.

Ltac insterU H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             newEvar T ltac:(fun y => specialize (H y))
         end.

Theorem t5' : (forall x : nat, S x > x) -> 2 > 1.
Proof.
  intro H.
  insterU H.
  apply H.
Qed.

(* This particular example is somewhat silly, since [apply] by itself would have
 * solved the goal originally.  Separate forward reasoning is more useful on
 * hypotheses that end in existential quantifications.  Before we go through an
 * example, it is useful to define a variant of [insterU] that does not clear
 * the base hypothesis we pass to it. *)

Ltac insterKeep H :=
  let H' := fresh "H'" in
    pose proof H as H'; insterU H'.

Section t6.
  Variables A B : Type.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros.

    do 2 insterKeep H1.

    repeat match goal with
             | [ H : ex _ |- _ ] => destruct H
           end.

    eexists.
    eexists.
    apply H2.
    exact H.
    exact p.
    (* In two weeks, we'll meet [eauto], which can do these last steps
     * automatically. *)
  Qed.
End t6.

(* Here's an example where something bad happens. *)

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros; do 2 insterKeep H1;
      repeat match goal with
               | [ H : ex _ |- _ ] => destruct H
             end; eauto.

    (* Oh, two trivial goals remain. *)
    Unshelve.
    assumption.
    assumption.
  Qed.
End t7.

(* Why did we need to do that extra work?  The [forall] rule was also matching
 * implications! *)

Module Import FixedInster.
  Ltac insterU tac H :=
    repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
             | Prop =>
               (let H' := fresh "H'" in
                assert (H' : T) by solve [ tac ];
                specialize (H H'); clear H')
               || fail 1
             | _ =>
               newEvar T ltac:(fun y => specialize (H y))
             end
           end.

  Ltac insterKeep tac H :=
    let H' := fresh "H'" in
      pose proof H as H'; insterU tac H'.
End FixedInster.

Section t7'.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7' : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros.
    do 2 insterKeep ltac:(idtac; match goal with
                                 | [ H : Q ?v |- _ ] =>
                                   match goal with
                                   | [ _ : context[P v _] |- _ ] => fail 1
                                   | _ => apply H
                                   end
                                 end) H1;
    repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
           end; eauto.
  Qed.
End t7'.

(* One more example of working with existentials: *)

Theorem t8 : exists p : nat * nat, fst p = 3.
Proof.
  econstructor.
  instantiate (1 := (3, 2)).
  (* ^-- We use [instantiate] to plug in a value for one of the "question-mark
   * variables" in the conclusion.  The [1 :=] part says "first such variable
   * mentioned in the conclusion, counting from right to left." *)
  equality.
Qed.

(* A way that plays better with automation: *)

Theorem t9 : exists p : nat * nat, fst p = 3.
Proof.
  econstructor; match goal with
                  | [ |- fst ?x = 3 ] => unify x (3, 2)
                end; equality.
Qed.
