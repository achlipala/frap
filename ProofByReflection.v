(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Supplementary Coq material: proof by reflection
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/
  * Much of the material comes from CPDT <http://adam.chlipala.net/cpdt/> by the same author. *)

Require Import Frap.

Set Implicit Arguments.
Set Asymmetric Patterns.


(* Our last "aside" on effective Coq use (in IntroToProofScripting.v)
 * highlighted a very heuristic approach to proving.  As an alternative, we will
 * study a technique called proof by reflection.  We will write, in Gallina (the
 * logical functional-programming language of Coq), decision procedures with
 * proofs of correctness, and we will appeal to these procedures in writing very
 * short proofs.  Such a proof is checked by running the decision procedure.
 * The term _reflection_ applies because we will need to translate Gallina
 * propositions into values of inductive types representing syntax, so that
 * Gallina programs may analyze them, and translating such a term back to the
 * original form is called _reflecting_ it. *)


(** * Proving Evenness *)

(* Proving that particular natural-number constants are even is certainly
 * something we would rather have happen automatically.  The Ltac-programming
 * techniques that we learned last week make it easy to implement such a
 * procedure. *)

Inductive isEven : nat -> Prop :=
| Even_O : isEven O
| Even_SS : forall n, isEven n -> isEven (S (S n)).

Ltac prove_even := repeat constructor.

Theorem even_256 : isEven 256.
Proof.
  prove_even.
Qed.

Set Printing All.
Print even_256.
Unset Printing All.

(* Here we see a term of Coq's core proof language, which we don't explain in
 * detail, but roughly speaking such a term is a syntax tree recording which
 * lemmas were used, and how their quantifiers were instantiated, to prove a
 * theorem.  This Ltac procedure always works (at least on machines with
 * infinite resources), but it has a serious drawback, which we see when we
 * print the proof it generates that 256 is even.  The final proof term has
 * length super-linear in the input value, which we reveal with
 * [Set Printing All], to disable all syntactic niceties and show every node of
 * the internal proof AST.  The problem is that each [Even_SS] application needs
 * a choice of [n], and we wind up giving every even number from 0 to 254 in
 * that position, at some point or another, for quadratic proof-term size.
 *
 * It is also unfortunate not to have static-typing guarantees that our tactic
 * always behaves appropriately.  Other invocations of similar tactics might
 * fail with dynamic type errors, and we would not know about the bugs behind
 * these errors until we happened to attempt to prove complex enough goals.
 *
 * The techniques of proof by reflection address both complaints.  We will be
 * able to write proofs like in the example above with constant size overhead
 * beyond the size of the input, and we will do it with verified decision
 * procedures written in Gallina. *)

Fixpoint check_even (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n') => check_even n'
  end.

(* To prove [check_even] sound, we need two IH strengthenings:
 * - Effectively switch to _strong induction_ with an extra numeric variable,
 *   asserted to be less than the one we induct on.
 * - Express both cases for how a [check_even] test might turn out. *)
Lemma check_even_ok' : forall n n', n' < n
  -> if check_even n' then isEven n' else ~isEven n'.
Proof.
  induct n; simplify.

  linear_arithmetic.

  cases n'; simplify.
  constructor.
  cases n'; simplify.
  propositional.
  invert H0.
  specialize (IHn n').
  cases (check_even n').
  constructor.
  apply IHn.
  linear_arithmetic.
  propositional.
  invert H0.
  apply IHn.
  linear_arithmetic.
  assumption.
Qed.

Theorem check_even_ok : forall n, check_even n = true -> isEven n.
Proof.
  simplify.
  assert (n < S n) by linear_arithmetic.
  apply check_even_ok' in H0.
  rewrite H in H0.
  assumption.
Qed.

(* As this theorem establishes, the function [check_even] may be viewed as a
 * _verified decision procedure_.  It is now trivial to write a tactic to prove
 * evenness. *)

Ltac prove_even_reflective :=
  match goal with
    | [ |- isEven _ ] => apply check_even_ok; reflexivity
  end.

Theorem even_256' : isEven 256.
Proof.
  prove_even_reflective.
Qed.

Set Printing All.
Print even_256'.
Unset Printing All.

(* Notice that only one [nat] appears as an argument to an applied lemma, and
 * that's the original number to test for evenness.  Proof-term size scales
 * linearly.
 *
 * What happens if we try the tactic with an odd number? *)

Theorem even_255 : isEven 255.
Proof.
  (*prove_even_reflective.*)
Abort.
(* Coq reports that [reflexivity] can't prove [false = true], which makes
 * perfect sense! *)

(* Our tactic [prove_even_reflective] is reflective because it performs a
 * proof-search process (a trivial one, in this case) wholly within Gallina. *)


(** * Reifying the Syntax of a Trivial Tautology Language *)

(* We might also like to have reflective proofs of trivial tautologies like
 * this one: *)

Theorem true_galore : (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof.
  tauto.
Qed.

Print true_galore.

(* As we might expect, the proof that [tauto] builds contains explicit
 * applications of deduction rules.  For large formulas, this can add a linear
 * amount of proof-size overhead, beyond the size of the input.
 *
 * To write a reflective procedure for this class of goals, we will need to get
 * into the actual "reflection" part of "proof by reflection."  It is impossible
 * to case-analyze a [Prop] in any way in Gallina.  We must _reify_ [Prop] into
 * some type that we _can_ analyze.  This inductive type is a good candidate: *)

(* begin thide *)
Inductive taut : Set :=
| TautTrue : taut
| TautAnd : taut -> taut -> taut
| TautOr : taut -> taut -> taut
| TautImp : taut -> taut -> taut.

(* We write a recursive function to _reflect_ this syntax back to [Prop].  Such
 * functions are also called _interpretation functions_, and we have used them
 * in previous examples to give semantics to small programming languages. *)

Fixpoint tautDenote (t : taut) : Prop :=
  match t with
    | TautTrue => True
    | TautAnd t1 t2 => tautDenote t1 /\ tautDenote t2
    | TautOr t1 t2 => tautDenote t1 \/ tautDenote t2
    | TautImp t1 t2 => tautDenote t1 -> tautDenote t2
  end.

(* It is easy to prove that every formula in the range of [tautDenote] is
 * true. *)

Theorem tautTrue : forall t, tautDenote t.
Proof.
  induct t; simplify; propositional.
Qed.

(* To use [tautTrue] to prove particular formulas, we need to implement the
 * syntax-reification process.  A recursive Ltac function does the job. *)

Ltac tautReify P :=
  match P with
    | True => TautTrue
    | ?P1 /\ ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautAnd t1 t2)
    | ?P1 \/ ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautOr t1 t2)
    | ?P1 -> ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautImp t1 t2)
  end.

(* With [tautReify] available, it is easy to finish our reflective tactic.  We
 * look at the goal formula, reify it, and apply [tautTrue] to the reified
 * formula.  Recall that the [change] tactic replaces a conclusion formula with
 * another that is equal to it, as shown by partial execution of terms. *)

Ltac obvious :=
  match goal with
    | [ |- ?P ] =>
      let t := tautReify P in
      change (tautDenote t); apply tautTrue
  end.

(* We can verify that [obvious] solves our original example, with a proof term
 * that does not mention details of the proof. *)

Theorem true_galore' : (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof.
  obvious.
Qed.

Set Printing All.
Print true_galore'.
Unset Printing All.

(* It is worth considering how the reflective tactic improves on a pure-Ltac
 * implementation.  The formula-reification process is just as ad-hoc as before,
 * so we gain little there.  In general, proofs will be more complicated than
 * formula translation, and the "generic proof rule" that we apply here _is_ on
 * much better formal footing than a recursive Ltac function.  The dependent
 * type of the proof guarantees that it "works" on any input formula.  This
 * benefit is in addition to the proof-size improvement that we have already
 * seen.
 *
 * It may also be worth pointing out that our previous example of evenness
 * testing used a test [check_even] that could sometimes fail, while here we
 * avoid the extra Boolean test by identifying a syntactic class of formulas
 * that are always true by construction.  Of course, many interesting proof
 * steps don't have that structure, so let's look at an example that still
 * requires extra proving after the reflective step. *)


(** * A Monoid Expression Simplifier *)

(* Proof by reflection does not require encoding of all of the syntax in a goal.
 * We can insert "variables" in our syntax types to allow injection of arbitrary
 * pieces, even if we cannot apply specialized reasoning to them.  In this
 * section, we explore that possibility by writing a tactic for normalizing
 * monoid equations. *)

Section monoid.
  Variable A : Set.
  Variable e : A.
  Variable f : A -> A -> A.

  Infix "+" := f.

  Hypothesis assoc : forall a b c, (a + b) + c = a + (b + c).
  Hypothesis identl : forall a, e + a = a.
  Hypothesis identr : forall a, a + e = a.

  (* We add variables and hypotheses characterizing an arbitrary instance of the
   * algebraic structure of monoids.  We have an associative binary operator and
   * an identity element for it.
   *
   * It is easy to define an expression-tree type for monoid expressions.  A
   * [Var] constructor is a "catch-all" case for subexpressions that we cannot
   * model.  These subexpressions could be actual Gallina variables, or they
   * could just use functions that our tactic is unable to understand. *)

  Inductive mexp : Set :=
  | Ident : mexp
  | Var : A -> mexp
  | Op : mexp -> mexp -> mexp.

  (* Next, we write an interpretation function. *)

  Fixpoint mdenote (me : mexp) : A :=
    match me with
      | Ident => e
      | Var v => v
      | Op me1 me2 => mdenote me1 + mdenote me2
    end.

  (* We will normalize expressions by flattening them into lists, via
   * associativity, so it is helpful to have a denotation function for lists of
   * monoid values. *)

  Fixpoint mldenote (ls : list A) : A :=
    match ls with
      | nil => e
      | x :: ls' => x + mldenote ls'
    end.

  (* The flattening function itself is easy to implement. *)

  Fixpoint flatten (me : mexp) : list A :=
    match me with
      | Ident => []
      | Var x => [x]
      | Op me1 me2 => flatten me1 ++ flatten me2
    end.

  (* This function has a straightforward correctness proof in terms of our
   * [denote] functions. *)

  Lemma flatten_correct' : forall ml2 ml1,
    mldenote (ml1 ++ ml2) = mldenote ml1 + mldenote ml2.
  Proof.
    induction ml1; simplify; equality.
  Qed.

  Hint Rewrite flatten_correct'.

  Theorem flatten_correct : forall me, mdenote me = mldenote (flatten me).
  Proof.
    induction me; simplify; equality.
  Qed.

  (* Now it is easy to prove a theorem that will be the main tool behind our
   * simplification tactic. *)

  Theorem monoid_reflect : forall me1 me2,
    mldenote (flatten me1) = mldenote (flatten me2)
    -> mdenote me1 = mdenote me2.
  Proof.
    simplify; repeat rewrite flatten_correct; assumption.
  Qed.

  (* We implement reification into the [mexp] type. *)

  Ltac reify me :=
    match me with
      | e => Ident
      | ?me1 + ?me2 =>
        let r1 := reify me1 in
        let r2 := reify me2 in
          constr:(Op r1 r2)
      | _ => constr:(Var me)
    end.

  (* The final [monoid] tactic works on goals that equate two monoid terms.  We
   * reify each and change the goal to refer to the reified versions, finishing
   * off by applying [monoid_reflect] and simplifying uses of [mldenote]. *)

  Ltac monoid :=
    match goal with
      | [ |- ?me1 = ?me2 ] =>
        let r1 := reify me1 in
        let r2 := reify me2 in
          change (mdenote r1 = mdenote r2);
            apply monoid_reflect; simplify
    end.

  (* We can make short work of theorems like this one: *)

  Theorem t1 : forall a b c d, a + b + c + d = a + (b + c) + d.
  Proof.
    simplify; monoid.

    (* Our tactic has canonicalized both sides of the equality, such that we can
     * finish the proof by reflexivity. *)

    reflexivity.
  Qed.

  (* It is interesting to look at the form of the proof. *)

  Set Printing All.
  Print t1.
  Unset Printing All.

  (* The proof term contains only restatements of the equality operands in
   * reified form, followed by a use of reflexivity on the shared canonical
   * form. *)
End monoid.

(* Extensions of this basic approach are used in the implementations of the
 * [ring] and [field] tactics that come packaged with Coq. *)


(** * Set Simplification for Model Checking *)

(* Let's take a closer look at model-checking proofs like from an earlier class. *)

(* Here's a simple transition system, where state is just a [nat], and where
 * each step subtracts 1 or 2. *)

Inductive subtract_step : nat -> nat -> Prop :=
| Subtract1 : forall n, subtract_step (S n) n
| Subtract2 : forall n, subtract_step (S (S n)) n.

Definition subtract_sys (n : nat) : trsys nat := {|
  Initial := {n};
  Step := subtract_step
|}.

Lemma subtract_ok :
  invariantFor (subtract_sys 5)
               (fun n => n <= 5).
Proof.
  eapply invariant_weaken.

  apply multiStepClosure_ok.
  simplify.
  (* Here we'll see that the Frap libary uses slightly different, optimized
   * versions of the model-checking relations.  For instance, [multiStepClosure]
   * takes an extra set argument, the _worklist_ recording newly discovered
   * states.  There is no point in following edges out of states that were
   * already known at previous steps. *)

  (* Now, some more manual iterations: *)
  eapply MscStep.
  closure.
  (* Ew.  What a big, ugly set expression.  Let's shrink it down to something
   * more readable, with duplicates removed, etc. *)
  simplify.
  (* How does the Frap library do that?  Proof by reflection is a big part of
   * it!  Let's develop a baby version of that automation.  The full-scale
   * version is in file Sets.v. *)
Abort.

(* We'll specialize our representation to unions of set literals, whose elements
 * are constant [nat]s.  The full-scale version in the library is more
 * flexible. *)
Inductive setexpr :=
| Literal (ns : list nat)
| Union (e1 e2 : setexpr).

(* Here's what our expressions mean. *)
Fixpoint setexprDenote (e : setexpr) : set nat :=
  match e with
  | Literal ns => constant ns
  | Union e1 e2 => setexprDenote e1 \cup setexprDenote e2
  end.

(* Simplification reduces all expressions to flat, duplicate-free set
 * literals. *)
Fixpoint normalize (e : setexpr) : list nat :=
  match e with
  | Literal ns => dedup ns
  | Union e1 e2 => setmerge (normalize e1) (normalize e2)
  end.
(* Here we use functions [dedup] and [setmerge] from the Sets module, which is
 * especially handy because that module has proved some key theorems about
 * them. *)

(* Let's prove that normalization doesn't change meaning. *)
Theorem normalize_ok : forall e,
    setexprDenote e = constant (normalize e).
Proof.
  induct e; simpl. (* Here we use the more primitive [simpl], because [simplify]
                    * calls the fancier set automation from the book library,
                    * which would be "cheating." *)

  pose proof (constant_dedup (fun x => x) ns).
  repeat rewrite map_id in H.
  equality.

  rewrite IHe1, IHe2.
  pose proof (constant_map_setmerge (fun x => x) (normalize e2) (normalize e1)).
  repeat rewrite map_id in H.
  equality.
Qed.

(* Reification works as before, with one twist. *)
Ltac reify_set E :=
  match E with
  | constant ?ns => constr:(Literal ns)
  | ?E1 \cup ?E2 =>
    let e1 := reify_set E1 in
    let e2 := reify_set E2 in
    constr:(Union e1 e2)
  | _ => let pf := constr:(E = {}) in constr:(Literal [])
    (* The twist is in this case: we instantiate all unification variables with
     * the empty set.  It's a sound proof step, and it so happens that we only
     * call this tactic in spots where this heuristic makes sense. *)
  end.

(* Now the usual recipe for a reflective tactic, this time using rewriting
 * instead of [apply] for the key step, to allow simplification deep within the
 * structure of a goal. *)
Ltac simplify_set :=
  match goal with
  | [ |- context[?X \cup ?Y] ] =>
    let e := reify_set (X \cup Y) in
    let Heq := fresh in
    assert (Heq : X \cup Y = setexprDenote e) by reflexivity;
    rewrite Heq; clear Heq;
    rewrite normalize_ok; simpl
  end.

(* Back to our example, which we can now finish without calling [simplify] to
 * reduce trees of union operations. *)
Lemma subtract_ok :
  invariantFor (subtract_sys 5)
               (fun n => n <= 5).
Proof.
  eapply invariant_weaken.

  apply multiStepClosure_ok.
  simplify.

  (* Now, some more manual iterations: *)
  eapply MscStep.
  closure.
  simplify_set.
  (* Success!  One subexpression shrunk.  Now for the other. *)
  simplify_set.
  (* Our automation doesn't handle set difference, so we finish up calling the
   * library tactic. *)
  simplify.

  eapply MscStep.
  closure.
  simplify_set.
  simplify_set.
  simplify.

  eapply MscStep.
  closure.
  simplify_set.
  simplify_set.
  simplify.

  eapply MscStep.
  closure.
  simplify_set.
  simplify_set.
  simplify.

  model_check_done.

  simplify.
  linear_arithmetic.
Qed.


(** * A Smarter Tautology Solver *)

(* Now we are ready to revisit our earlier tautology-solver example.  We want to
 * broaden the scope of the tactic to include formulas whose truth is not
 * syntactically apparent.  We will want to allow injection of arbitrary
 * formulas, like we allowed arbitrary monoid expressions in the last example.
 * Since we are working in a richer theory, it is important to be able to use
 * equalities between different injected formulas.  For instance, we cannot
 * prove [P -> P] by translating the formula into a value like
 * [Imp (Var P) (Var P)], because a Gallina function has no way of comparing the
 * two [P]s for equality. *)

(* We introduce a synonym for how we name variables: natural numbers. *)
Definition propvar := nat.

Inductive formula : Set :=
| Atomic : propvar -> formula
| Truth : formula
| Falsehood : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imp : formula -> formula -> formula.

(* Now we can define our denotation function.  First, a type of truth-value
 * assignments to propositional variables: *)
Definition asgn := nat -> Prop.

Fixpoint formulaDenote (atomics : asgn) (f : formula) : Prop :=
  match f with
    | Atomic v => atomics v
    | Truth => True
    | Falsehood => False
    | And f1 f2 => formulaDenote atomics f1 /\ formulaDenote atomics f2
    | Or f1 f2 => formulaDenote atomics f1 \/ formulaDenote atomics f2
    | Imp f1 f2 => formulaDenote atomics f1 -> formulaDenote atomics f2
  end.

Require Import ListSet.

Section my_tauto.
  Variable atomics : asgn.

  (* Now we are ready to define some helpful functions based on the [ListSet]
   * module of the standard library, which (unsurprisingly) presents a view of
   * lists as sets. *)

  (* The [eq_nat_dec] below is a richly typed equality test on [nat]s.  We'll
   * get to the ideas behind it in a later class. *)
  Definition add (s : set propvar) (v : propvar) := set_add eq_nat_dec v s.

  (* We define what it means for all members of a variable set to represent
   * true propositions, and we prove some lemmas about this notion. *)

  Fixpoint allTrue (s : set propvar) : Prop :=
    match s with
      | nil => True
      | v :: s' => atomics v /\ allTrue s'
    end.

  Theorem allTrue_add : forall v s,
    allTrue s
    -> atomics v
    -> allTrue (add s v).
  Proof.
    induct s; simplify; propositional;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; simplify; propositional.
  Qed.

  Theorem allTrue_In : forall v s,
    allTrue s
    -> set_In v s
    -> atomics v.
  Proof.
    induct s; simplify; equality.
  Qed.

  (* Now we can write a function [forward] that implements deconstruction of
   * hypotheses, expanding a compound formula into a set of sets of atomic
   * formulas covering all possible cases introduced with use of [Or].  To
   * handle consideration of multiple cases, the function takes in a
   * continuation argument (advanced functional-programming feature that often
   * puzzles novices, so don't worry if it takes a while to digest!), which will
   * be called once for each case. *)

  Fixpoint forward (known : set propvar) (hyp : formula)
           (cont : set propvar -> bool) : bool :=
    match hyp with
    | Atomic v => cont (add known v)
    | Truth => cont known
    | Falsehood => true
    | And h1 h2 => forward known h1 (fun known' =>
                     forward known' h2 cont)
    | Or h1 h2 => forward known h1 cont && forward known h2 cont
    | Imp _ _ => cont known
    end.

  (* Some examples might help get the idea across. *)
  Compute fun cont => forward [] (Atomic 0) cont.
  Compute fun cont => forward [] (Or (Atomic 0) (Atomic 1)) cont.
  Compute fun cont => forward [] (Or (Atomic 0) (And (Atomic 1) (Atomic 2))) cont.
  
  (* A [backward] function implements analysis of the final goal.  It calls
   * [forward] to handle implications. *)

  Fixpoint backward (known : set propvar) (f : formula) : bool :=
    match f with
    | Atomic v => if In_dec eq_nat_dec v known then true else false
    | Truth => true
    | Falsehood => false
    | And f1 f2 => backward known f1 && backward known f2
    | Or f1 f2 => backward known f1 || backward known f2
    | Imp f1 f2 => forward known f1 (fun known' => backward known' f2)
    end.

  (* Examples: *)
  Compute backward [] (Atomic 0).
  Compute backward [0] (Atomic 0).
  Compute backward [0; 2] (Or (Atomic 0) (Atomic 1)).
  Compute backward [2] (Or (Atomic 0) (Atomic 1)).
  Compute backward [2] (Imp (Atomic 0) (Or (Atomic 0) (Atomic 1))).
  Compute backward [2] (Imp (Or (Atomic 0) (Atomic 3)) (Or (Atomic 0) (Atomic 1))).
  Compute backward [2] (Imp (Or (Atomic 1) (Atomic 0)) (Or (Atomic 0) (Atomic 1))).
End my_tauto.

Lemma forward_ok : forall atomics hyp f known cont,
    forward known hyp cont = true
    -> (forall known', allTrue atomics known'
                       -> cont known' = true
                       -> formulaDenote atomics f)
    -> allTrue atomics known
    -> formulaDenote atomics hyp
    -> formulaDenote atomics f.
Proof.
  induct hyp; simplify; propositional.

  apply H0 with (known' := add known p).
  apply allTrue_add.
  assumption.
  assumption.
  assumption.

  eapply H0.
  eassumption.
  assumption.

  eapply IHhyp1.
  eassumption.
  simplify.
  eauto.
  assumption.
  assumption.

  apply andb_true_iff in H; propositional.
  eapply IHhyp1.
  eassumption.
  assumption.
  assumption.
  assumption.

  apply andb_true_iff in H; propositional.
  eapply IHhyp2.
  eassumption.
  assumption.
  assumption.
  assumption.

  eapply H0.
  eassumption.
  assumption.
Qed.

Lemma backward_ok' : forall atomics f known,
    backward known f = true
    -> allTrue atomics known
    -> formulaDenote atomics f.
Proof.
  induct f; simplify; propositional.

  cases (in_dec Nat.eq_dec p known); propositional.
  eapply allTrue_In.
  eassumption.
  unfold set_In.
  assumption.
  equality.

  equality.

  apply andb_true_iff in H; propositional.
  eapply IHf1.
  eassumption.
  assumption.

  apply andb_true_iff in H; propositional.
  eapply IHf2.
  eassumption.
  assumption.

  apply orb_true_iff in H; propositional.
  left.
  eapply IHf1.
  eassumption.
  assumption.
  right.
  eapply IHf2.
  eassumption.
  assumption.

  eapply forward_ok.
  eassumption.
  simplify.
  eapply IHf2.
  eassumption.
  assumption.
  assumption.
  assumption.
Qed.

Theorem backward_ok : forall f,
    backward [] f = true
    -> forall atomics, formulaDenote atomics f.
Proof.
  simplify.
  apply backward_ok' with (known := []).
  assumption.
  simplify.
  propositional.
Qed.

(* Find the position of an element in a list. *)
Ltac position x ls :=
  match ls with
  | [] => constr:(@None nat)
  | x :: _ => constr:(Some 0)
  | _ :: ?ls' =>
    let p := position x ls' in
    match p with
    | None => p
    | Some ?n => constr:(Some (S n))
    end
  end.

(* Compute a duplicate-free list of all variables in [P], combining it with
 * [acc]. *)
Ltac vars_in P acc :=
  match P with
  | True => acc
  | False => acc
  | ?Q1 /\ ?Q2 =>
    let acc' := vars_in Q1 acc in
    vars_in Q2 acc'
  | ?Q1 \/ ?Q2 =>
    let acc' := vars_in Q1 acc in
    vars_in Q2 acc'
  | ?Q1 -> ?Q2 =>
    let acc' := vars_in Q1 acc in
    vars_in Q2 acc'
  | _ =>
    let pos := position P acc in
    match pos with
    | Some _ => acc
    | None => constr:(P :: acc)
    end
  end.

(* Reification of formula [P], with a pregenerated list [vars] of variables it
 * may mention *)
Ltac reify_tauto' P vars :=
  match P with
  | True => Truth
  | False => Falsehood
  | ?Q1 /\ ?Q2 =>
    let q1 := reify_tauto' Q1 vars in
    let q2 := reify_tauto' Q2 vars in
    constr:(And q1 q2)
  | ?Q1 \/ ?Q2 =>
    let q1 := reify_tauto' Q1 vars in
    let q2 := reify_tauto' Q2 vars in
    constr:(Or q1 q2)
  | ?Q1 -> ?Q2 =>
    let q1 := reify_tauto' Q1 vars in
    let q2 := reify_tauto' Q2 vars in
    constr:(Imp q1 q2)
  | _ =>
    let pos := position P vars in
    match pos with
    | Some ?pos' => constr:(Atomic pos')
    end
  end.

(* Our final tactic implementation is now fairly straightforward.  First, we
 * [intro] all quantifiers that do not bind [Prop]s.  Then we reify.  Finally,
 * we call the verified procedure through a lemma. *)

Ltac my_tauto :=
  repeat match goal with
           | [ |- forall x : ?P, _ ] =>
             match type of P with
               | Prop => fail 1
               | _ => intro
             end
         end;
  match goal with
    | [ |- ?P ] =>
      let vars := vars_in P (@nil Prop) in
      let p := reify_tauto' P vars in
      change (formulaDenote (nth_default False vars) p)
  end;
  apply backward_ok; reflexivity.

(* A few examples demonstrate how the tactic works: *)

Theorem mt1 : True.
Proof.
  my_tauto.
Qed.

Print mt1.

Theorem mt2 : forall x y : nat, x = y -> x = y.
Proof.
  my_tauto.
Qed.

Print mt2.

(* Crucially, both instances of [x = y] are represented with the same variable
 * 0. *)

Theorem mt3 : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  -> y > z /\ (x < y \/ x < S y).
Proof.
  my_tauto.
Qed.

Print mt3.

(* Our goal contained three distinct atomic formulas, and we see that a
 * three-element environment is generated.
 *
 * It can be interesting to observe differences between the level of repetition
 * in proof terms generated by [my_tauto] and [tauto] for especially trivial
 * theorems. *)

Theorem mt4 : True /\ True /\ True /\ True /\ True /\ True /\ False -> False.
Proof.
  my_tauto.
Qed.

Print mt4.

Theorem mt4' : True /\ True /\ True /\ True /\ True /\ True /\ False -> False.
Proof.
  tauto.
Qed.

Print mt4'.

(* The traditional [tauto] tactic introduces a quadratic blow-up in the size of
 * the proof term, whereas proofs produced by [my_tauto] always have linear
 * size. *)
