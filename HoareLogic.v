(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 12: Hoare Logic: Verifying Imperative Programs
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.




(** * Syntax and semantics of a simple imperative language *)

(* Here's some appropriate syntax for expressions (side-effect-free) of a simple
 * imperative language with a mutable memory. *)
Inductive exp :=
| Const (n : nat)
| Var (x : string)
| Read (e1 : exp)
| Plus (e1 e2 : exp)
| Minus (e1 e2 : exp)
| Mult (e1 e2 : exp).

(* Those were the expressions of numeric type.  Here are the Boolean
 * expressions. *)
Inductive bexp :=
| Equal (e1 e2 : exp)
| Less (e1 e2 : exp).

Definition heap := fmap nat nat.
Definition valuation := fmap var nat.
Definition assertion := heap -> valuation -> Prop.

(* Here's the syntax of side-effecting commands, where we attach an assertion to
 * every "while" loop, for reasons that should become clear later.  The
 * assertion is ignored in the operational semantics! *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : exp)
| Write (e1 e2 : exp)
| Seq (c1 c2 : cmd)
| If_ (be : bexp) (then_ else_ : cmd)
| While_ (inv : assertion) (be : bexp) (body : cmd)

(* And one more, which we'll use to characterize program correctness more
 * simply: *)
| Assert (a : assertion).

(* Shorthand notation for looking up in a finite map, returning zero if the key
 * is not found *)
Notation "m $! k" := (match m $? k with Some n => n | None => O end) (at level 30).

(* Start of expression semantics: meaning of expressions *)
Fixpoint eval (e : exp) (h : heap) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => v $! x
  | Read e1 => h $! eval e1 h v
  | Plus e1 e2 => eval e1 h v + eval e2 h v
  | Minus e1 e2 => eval e1 h v - eval e2 h v
  | Mult e1 e2 => eval e1 h v * eval e2 h v
  end.

(* Meaning of Boolean expressions *)
Fixpoint beval (b : bexp) (h : heap) (v : valuation) : bool :=
  match b with
  | Equal e1 e2 => if eval e1 h v ==n eval e2 h v then true else false
  | Less e1 e2 => if eval e2 h v <=? eval e1 h v then false else true
  end.

(* A big-step operational semantics for commands *)
Inductive exec : heap -> valuation -> cmd -> heap -> valuation -> Prop :=
| ExSkip : forall h v,
  exec h v Skip h v
| ExAssign : forall h v x e,
  exec h v (Assign x e) h (v $+ (x, eval e h v))
| ExWrite : forall h v e1 e2,
  exec h v (Write e1 e2) (h $+ (eval e1 h v, eval e2 h v)) v
| ExSeq : forall h1 v1 c1 h2 v2 c2 h3 v3,
  exec h1 v1 c1 h2 v2
  -> exec h2 v2 c2 h3 v3
  -> exec h1 v1 (Seq c1 c2) h3 v3
| ExIfTrue : forall h1 v1 b c1 c2 h2 v2,
  beval b h1 v1 = true
  -> exec h1 v1 c1 h2 v2
  -> exec h1 v1 (If_ b c1 c2) h2 v2
| ExIfFalse : forall h1 v1 b c1 c2 h2 v2,
  beval b h1 v1 = false
  -> exec h1 v1 c2 h2 v2
  -> exec h1 v1 (If_ b c1 c2) h2 v2
| ExWhileFalse : forall I h v b c,
  beval b h v = false
  -> exec h v (While_ I b c) h v
| ExWhileTrue : forall I h1 v1 b c h2 v2 h3 v3,
  beval b h1 v1 = true
  -> exec h1 v1 c h2 v2
  -> exec h2 v2 (While_ I b c) h3 v3
  -> exec h1 v1 (While_ I b c) h3 v3

(* Assertions execute only when they are true.  They provide a way to embed
 * proof obligations within programs. *)
| ExAssert : forall h v (a : assertion),
  a h v
  -> exec h v (Assert a) h v.


(** * Hoare logic *)

(* Here's an inductive predicate capturing a class of *proved* specifications
 * for commands.  The intuition is that, when [hoare_triple P c Q], we know
 * that, when we start [c] in a state satisfying [P], if [c] finishes, its final
 * state satisfies [Q]. *)

Inductive hoare_triple : assertion -> cmd -> assertion -> Prop :=
| HtSkip : forall P, hoare_triple P Skip P
| HtAssign : forall (P : assertion) x e,
  hoare_triple P (Assign x e) (fun h v => exists v', P h v' /\ v = v' $+ (x, eval e h v'))
| HtWrite : forall (P : assertion) (e1 e2 : exp),
  hoare_triple P (Write e1 e2) (fun h v => exists h', P h' v /\ h = h' $+ (eval e1 h' v, eval e2 h' v))
| HtSeq : forall (P Q R : assertion) c1 c2,
  hoare_triple P c1 Q
  -> hoare_triple Q c2 R
  -> hoare_triple P (Seq c1 c2) R
| HtIf : forall (P Q1 Q2 : assertion) b c1 c2,
  hoare_triple (fun h v => P h v /\ beval b h v = true) c1 Q1
  -> hoare_triple (fun h v => P h v /\ beval b h v = false) c2 Q2
  -> hoare_triple P (If_ b c1 c2) (fun h v => Q1 h v \/ Q2 h v)
| HtWhile : forall (I P : assertion) b c,
  (forall h v, P h v -> I h v)
  -> hoare_triple (fun h v => I h v /\ beval b h v = true) c I
  -> hoare_triple P (While_ I b c) (fun h v => I h v /\ beval b h v = false)
| HtAssert : forall P I : assertion,
  (forall h v, P h v -> I h v)
  -> hoare_triple P (Assert I) P
| HtConsequence : forall (P Q P' Q' : assertion) c,
  hoare_triple P c Q
  -> (forall h v, P' h v -> P h v)
  -> (forall h v, Q h v -> Q' h v)
  -> hoare_triple P' c Q'.

(* Let's prove that the intuitive description given above really applies to this
 * predicate.  First, a lemma, which is difficult to summarize intuitively!
 * More or less precisely this obligation shows up in the main proof below. *)
Lemma hoare_triple_big_step_while: forall (I : assertion) b c,
  (forall h v h' v', exec h v c h' v'
                     -> I h v
                     -> beval b h v = true
                     -> I h' v')
  -> forall h v h' v', exec h v (While_ I b c) h' v'
                       -> I h v
                       -> I h' v' /\ beval b h' v' = false.
Proof.
  induct 2; eauto.
Qed.

(* That main theorem statement literally translates our intuitive description of
 * [hoare_triple] from above. *)
Theorem hoare_triple_big_step : forall pre c post,
    hoare_triple pre c post
    -> forall h v h' v', exec h v c h' v'
                         -> pre h v
                         -> post h' v'.
Proof.
  induct 1; eauto; invert 1; eauto.

  simplify.
  eapply hoare_triple_big_step_while; eauto.
Qed.


(* BEGIN syntax macros that won't be explained *)
Coercion Const : nat >-> exp.
Coercion Var : string >-> exp.
Notation "*[ e ]" := (Read e) : cmd_scope.
Infix "+" := Plus : cmd_scope.
Infix "-" := Minus : cmd_scope.
Infix "*" := Mult : cmd_scope.
Infix "=" := Equal : cmd_scope.
Infix "<" := Less : cmd_scope.
Definition set (dst src : exp) : cmd :=
  match dst with
  | Read dst' => Write dst' src
  | Var dst' => Assign dst' src
  | _ => Assign "Bad LHS" 0
  end.
Infix "<-" := set (no associativity, at level 70) : cmd_scope.
Infix ";;" := Seq (right associativity, at level 75) : cmd_scope.
Notation "'when' b 'then' then_ 'else' else_ 'done'" := (If_ b then_ else_) (at level 75, b at level 0).
Notation "{{ I }} 'while' b 'loop' body 'done'" := (While_ I b body) (at level 75).
Notation "'assert' {{ I }}" := (Assert I) (at level 75).
Delimit Scope cmd_scope with cmd.

Infix "+" := plus : reset_scope.
Infix "-" := Init.Nat.sub : reset_scope.
Infix "*" := mult : reset_scope.
Infix "=" := eq : reset_scope.
Infix "<" := lt : reset_scope.
Delimit Scope reset_scope with reset.
Open Scope reset_scope.
(* END macros *)

(* We should draw some attention to the next notation, which defines special
 * lambdas for writing assertions. *)
Notation "h & v ~> e" := (fun h v => e%reset) (at level 85, v at level 0).

(* And here's the classic notation for Hoare triples. *)
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c%cmd Q) (at level 90, c at next level).

(* Special case of consequence: keeping the precondition; only changing the
 * postcondition. *)
Lemma HtStrengthenPost : forall (P Q Q' : assertion) c,
  hoare_triple P c Q
  -> (forall h v, Q h v -> Q' h v)
  -> hoare_triple P c Q'.
Proof.
  simplify; eapply HtConsequence; eauto.
Qed.

(* Finally, three tactic definitions that we won't explain.  The overall tactic
 * [ht] tries to prove Hoare triples, essentially by rote application of the
 * rules.  Some other obligations are generated, generally of implications
 * between assertions, and [ht] also makes a best effort to solve those. *)

Ltac ht1 := apply HtSkip || apply HtAssign || apply HtWrite || eapply HtSeq
            || eapply HtIf || eapply HtWhile || eapply HtAssert
            || eapply HtStrengthenPost.

Ltac t := cbv beta; propositional; subst;
          repeat match goal with
                 | [ H : ex _ |- _ ] => invert H; propositional; subst
                 end;
          simplify;
          repeat match goal with
                 | [ _ : context[?a <=? ?b] |- _ ] => destruct (a <=? b); try discriminate
                 | [ H : ?E = ?E |- _ ] => clear H
                 end; simplify; propositional; auto; try equality; try linear_arithmetic.

Ltac ht := simplify; repeat ht1; t.


(** * Some examples of verified programs *)

(** ** Swapping the values in two variables *)

(* First, let's prove it with more manual applications of the Hoare-logic
 * rules. *)
Theorem swap_ok : forall a b,
  {{_&v ~> v $! "x" = a /\ v $! "y" = b}}
    "tmp" <- "x";;
    "x" <- "y";;
    "y" <- "tmp"
  {{_&v ~> v $! "x" = b /\ v $! "y" = a}}.
Proof.
  simplify.
  eapply HtSeq.
  apply HtAssign.
  eapply HtSeq.
  apply HtAssign.
  eapply HtStrengthenPost.
  apply HtAssign.
  simplify.
  t.
Qed.

(* We can also automate the proof easily. *)
Theorem swap_ok_snazzy : forall a b,
  {{_&v ~> v $! "x" = a /\ v $! "y" = b}}
    "tmp" <- "x";;
    "x" <- "y";;
    "y" <- "tmp"
  {{_&v ~> v $! "x" = b /\ v $! "y" = a}}.
Proof.
  ht.
Qed.

(** ** Computing the maximum of two variables *)

Theorem max_ok : forall a b,
  {{_&v ~> v $! "x" = a /\ v $! "y" = b}}
    when "x" < "y" then
      "m" <- "y"
    else
      "m" <- "x"
    done
  {{_&v ~> v $! "m" = max a b}}.
Proof.
  simplify.
  eapply HtStrengthenPost.
  apply HtIf.
  apply HtAssign.
  apply HtAssign.
  simplify.
  t.
Qed.

Theorem max_ok_snazzy : forall a b,
  {{_&v ~> v $! "x" = a /\ v $! "y" = b}}
    when "x" < "y" then
      "m" <- "y"
    else
      "m" <- "x"
    done
  {{_&v ~> v $! "m" = max a b}}.
Proof.
  ht.
Qed.

(** ** Iterative factorial *)

(* These two rewrite rules capture the definition of functional [fact], in
 * exactly the form useful in our Hoare-logic proof. *)
Lemma fact_base : forall n,
  n = 0
  -> fact n = 1.
Proof.
  simplify; subst; auto.
Qed.

Hint Rewrite <- minus_n_O.

Lemma fact_rec : forall n,
  n > 0
  -> fact n = n * fact (n - 1).
Proof.
  simplify; cases n; simplify; linear_arithmetic.
Qed.

Hint Rewrite fact_base fact_rec using linear_arithmetic.

(* Note the careful choice of loop invariant below.  It may look familiar from
 * earlier chapters' proofs! *)
Theorem fact_ok : forall n,
  {{_&v ~> v $! "n" = n}}
    "acc" <- 1;;
    {{_&v ~> v $! "acc" * fact (v $! "n") = fact n}}
    while 0 < "n" loop
      "acc" <- "acc" * "n";;
      "n" <- "n" - 1
    done
  {{_&v ~> v $! "acc" = fact n}}.
Proof.
  simplify.
  eapply HtSeq.
  apply HtAssign.
  eapply HtStrengthenPost.
  eapply HtWhile.
  simplify.
  t.
  eapply HtSeq.
  apply HtAssign.
  eapply HtStrengthenPost.
  apply HtAssign.
  simplify.
  t.
  ring [H0].
  (* This variant of [ring] suggests a hypothesis to use in the proof. *)
  simplify.
  t.
Qed.

Theorem fact_ok_snazzy : forall n,
  {{_&v ~> v $! "n" = n}}
    "acc" <- 1;;
    {{_&v ~> v $! "acc" * fact (v $! "n") = fact n}}
    while 0 < "n" loop
      "acc" <- "acc" * "n";;
      "n" <- "n" - 1
    done
  {{_&v ~> v $! "acc" = fact n}}.
Proof.
  ht.
  ring [H0].
Qed.

(** ** Selection sort *)

(* This is our one example of a program reading/writing memory, which holds the
 * representation of an array that we want to sort in-place. *)

(* One simple lemma turns out to be helpful to guide [eauto] properly. *)
Lemma leq_f : forall A (m : fmap A nat) x y,
  x = y
  -> m $! x <= m $! y.
Proof.
  ht.
Qed.

Hint Resolve leq_f.
Hint Extern 1 (@eq nat _ _) => linear_arithmetic.
Hint Extern 1 (_ < _) => linear_arithmetic.
Hint Extern 1 (_ <= _) => linear_arithmetic.
(* We also register [linear_arithmetic] as a step to try during proof search. *)

(* These invariants are fairly hairy, but probably the best way to understand
 * them is just to spend a while reading them.  They generally talk about
 * sortedness of subsets of the array.  See the final postcondition for how we
 * interpret a part of memory as an array.  Also note that we only prove here
 * that the final array is sorted, *not* that it's a permutation of the original
 * array!  (Exercise for the reader?  I'm not sure how much work it would
 * take.) *)
Theorem selectionSort_ok :
  {{_&_ ~> True}}
    "i" <- 0;;
    {{h&v ~> v $! "i" <= v $! "n"
        /\ (forall i j, i < j < v $! "i" -> h $! (v $! "a" + i) <= h $! (v $! "a" + j))
        /\ (forall i j, i < v $! "i" -> v $! "i" <= j < v $! "n" -> h $! (v $! "a" + i) <= h $! (v $! "a" + j)) }}
    while "i" < "n" loop
      "j" <- "i"+1;;
      "best" <- "i";;
      {{h&v ~> v $! "i" < v $! "j" <= v $! "n"
         /\ v $! "i" <= v $! "best" < v $! "n"
         /\ (forall k, v $! "i" <= k < v $! "j" -> h $! (v $! "a" + v $! "best") <= h $! (v $! "a" + k))
         /\ (forall i j, i < j < v $! "i" -> h $! (v $! "a" + i) <= h $! (v $! "a" + j))
         /\ (forall i j, i < v $! "i" -> v $! "i" <= j < v $! "n" -> h $! (v $! "a" + i) <= h $! (v $! "a" + j)) }}
      while "j" < "n" loop
        when *["a" + "j"] < *["a" + "best"] then
          "best" <- "j"
        else
          Skip
        done;;
        "j" <- "j" + 1
      done;;
      "tmp" <- *["a" + "best"];;
      *["a" + "best"] <- *["a" + "i"];;
      *["a" + "i"] <- "tmp";;
      "i" <- "i" + 1
    done
  {{h&v ~> forall i j, i < j < v $! "n" -> h $! (v $! "a" + i) <= h $! (v $! "a" + j)}}.
Proof.
  ht; repeat match goal with
             | [ |- context[_ $+ (?a + ?x, _) $! (?a + ?y)] ] =>
               cases (x ==n y); ht
             end.

  cases (k ==n x0 $! "j"); ht.
  specialize (H k); ht.

  cases (k ==n x $! "j"); ht.
Qed.


(** * An alternative correctness theorem for Hoare logic, with small-step semantics *)

(* In case you were worried that this chapter is too far removed from the
 * pattern of program reasoning we've seen recur again and again, help is here!
 * We can also characterize Hoare triples in terms of invariants of transition
 * systems.  To start with, here's a small-step semantics for our running
 * language. *)
Inductive step : heap * valuation * cmd -> heap * valuation * cmd -> Prop :=
| StAssign : forall h v x e,
  step (h, v, Assign x e) (h, v $+ (x, eval e h v), Skip)
| StWrite : forall h v e1 e2,
  step (h, v, Write e1 e2) (h $+ (eval e1 h v, eval e2 h v), v, Skip)
| StStepSkip : forall h v c,
  step (h, v, Seq Skip c) (h, v, c)
| StStepRec : forall h1 v1 c1 h2 v2 c1' c2,
  step (h1, v1, c1) (h2, v2, c1')
  -> step (h1, v1, Seq c1 c2) (h2, v2, Seq c1' c2)
| StIfTrue : forall h v b c1 c2,
  beval b h v = true
  -> step (h, v, If_ b c1 c2) (h, v, c1)
| StIfFalse : forall h v b c1 c2,
  beval b h v = false
  -> step (h, v, If_ b c1 c2) (h, v, c2)
| StWhileFalse : forall I h v b c,
  beval b h v = false
  -> step (h, v, While_ I b c) (h, v, Skip)
| StWhileTrue : forall I h v b c,
  beval b h v = true
  -> step (h, v, While_ I b c) (h, v, Seq c (While_ I b c))
| StAssert : forall h v (a : assertion),
  a h v
  -> step (h, v, Assert a) (h, v, Skip).

Hint Constructors step.

Definition trsys_of (st : heap * valuation * cmd) := {|
  Initial := {st};
  Step := step
|}.

(* We'll characterize *unstuckness* in roughly the same way as we did for
 * lambda-calculus type soundness: the program is done (reached [Skip]) or can
 * take a step. *)
Definition unstuck (st : heap * valuation * cmd) :=
  snd st = Skip
  \/ exists st', step st st'.

(* A convenient property of Hoare triples: they rule out stuckness, regardless
 * of the specs we choose, so long as the precondition accurately describes the
 * real execution state!  Note that the only real possibility for stuckness in
 * the semantics is via [Assert], which is why we included it.  We reduce
 * arbitrary correctness checks, on intermediate program states, to stuckness or
 * lack thereof in program execution. *)
Lemma hoare_triple_unstuck : forall P c Q,
  {{P}} c {{Q}}
  -> forall h v, P h v
                 -> unstuck (h, v, c).
Proof.
  induct 1; unfold unstuck; simplify; propositional; eauto.

  apply IHhoare_triple1 in H1.
  unfold unstuck in H1; simplify; first_order; subst; eauto.
  cases x.
  cases p.
  eauto.

  cases (beval b h v); eauto.

  cases (beval b h v); eauto.

  apply H0 in H2.
  apply IHhoare_triple in H2.
  unfold unstuck in H2; simplify; first_order.
Qed.

(* Another basic property: [Skip] has no effect on program state, and the set of
 * derivable specs for [Skip] reflects that fact. *)
Lemma hoare_triple_Skip : forall P Q,
  {{P}} Skip {{Q}}
  -> forall h v, P h v -> Q h v.
Proof.
  induct 1; auto.
Qed.

(* Finally, our main inductive proof: small steps preserve the existence of
 * Hoare triples.  We even give the concrete specification for the new command
 * [c'] that was stepped to.  It keeps the old postcondition, and we give it a
 * very specific precondition saying "the state is exactly this." *)
Lemma hoare_triple_step : forall P c Q,
  {{P}} c {{Q}}
  -> forall h v h' v' c',
      step (h, v, c) (h', v', c')
      -> P h v
      -> {{h''&v'' ~> h'' = h' /\ v'' = v'}} c' {{Q}}.
Proof.
  induct 1.

  invert 1.

  invert 1; ht; eauto.

  invert 1; ht; eauto.

  invert 1; simplify.

  eapply HtConsequence; eauto.
  propositional; subst.
  eapply hoare_triple_Skip; eauto.

  econstructor; eauto.

  invert 1; simplify.
  eapply HtConsequence; eauto; equality.
  eapply HtConsequence; eauto; equality.

  invert 1; simplify.
  eapply HtConsequence with (P := h'' & v'' ~> h'' = h' /\ v'' = v').
  apply HtSkip.
  auto.
  simplify; propositional; subst; eauto.

  econstructor.
  eapply HtConsequence; eauto.
  simplify; propositional; subst; eauto.
  econstructor; eauto.

  invert 1; simplify.
  eapply HtConsequence; eauto.
  econstructor.
  simplify; propositional; subst; eauto.

  simplify.
  eapply HtConsequence.
  eapply IHhoare_triple; eauto.
  simplify; propositional; subst; eauto.
  auto.
Qed.

(* Oh, what a coincidence! ;-)  As with type-safety proofs, we find that the
 * reasonably intuitive properties we just proved are precisely the hard parts
 * of a standard proof by invariant strengthening and invariant induction. *)
Theorem hoare_triple_invariant : forall P c Q h v,
  {{P}} c {{Q}}
  -> P h v
  -> invariantFor (trsys_of (h, v, c)) unstuck.
Proof.
  simplify.
  apply invariant_weaken with (invariant1 := fun st => {{h&v ~> h = fst (fst st)
                                                           /\ v = snd (fst st)}}
                                                         snd st
                                                       {{_&_ ~> True}}).

  apply invariant_induction; simplify.

  propositional; subst; simplify.
  eapply HtConsequence; eauto.
  equality.

  cases s.
  cases s'.
  cases p.
  cases p0.
  simplify.
  eapply hoare_triple_step; eauto.
  simplify; auto.

  simplify.
  cases s.
  cases p.
  simplify.
  eapply hoare_triple_unstuck; eauto.
  simplify; auto.
Qed.

(* A very simple example, just to show all this in action *)
Definition forever := (
  "i" <- 1;;
  "n" <- 1;;
  {{h&v ~> v $! "i" > 0}}
  while 0 < "i" loop
    "i" <- "i" * 2;;
    "n" <- "n" + "i";;
    assert {{h&v ~> v $! "n" >= 1}}
  done;;

  assert {{_&_ ~> False}}
  (* Note that this last assertion implies that the program never terminates! *)
)%cmd.

Theorem forever_ok : {{_&_ ~> True}} forever {{_&_ ~> False}}.
Proof.
  ht.
Qed.

Theorem forever_invariant : invariantFor (trsys_of ($0, $0, forever)) unstuck.
Proof.
  eapply hoare_triple_invariant.
  apply forever_ok.
  simplify; trivial.
Qed.
