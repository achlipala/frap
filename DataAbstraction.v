(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 3: Data Abstraction
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.


(* Perhaps the essence of effective programming is division of large tasks into
 * smaller ones, and *data abstraction* is a key technique to that end.
 * We provide a clear separation between *interfaces* and *implementations*.
 * The author of a library can take responsibility for making it implement an
 * interface faithfully, *encapsulating* private state and other implementation
 * details in a way that client code can't observe.  Then that client code can
 * mix and match implementations of some well-specified functionality.
 *
 * As part of our quick tour through effective Coq programming, we will dwell on
 * patterns for data abstraction, including how to state it formally, from the
 * perspectives of both libraries and client code. *)


(** * Specification styles for data abstraction *)

(* One of the classic formalisms for data abstraction is the *algebraic* style,
 * where requirements on implementations are written out as quantified
 * equalities.  Any implementation must satisfy these equalities, but we grant
 * implementations freedom in internal details. *)
Module Algebraic.
  (* Here's an example of an algebraic interface or *specification* ("spec" for
   * short).  It's for purely functional queues, which follow first-in-first-out
   * disciplines. *)
  Module Type QUEUE.
    Parameter t : Set -> Set.
    (* An implementation must include some data type [t].
     * Actually, it's more of a *type family*, e.g. like [list] and some other
     * polymorphic container types we looked at last time. *)

    Parameter empty : forall A, t A.
    (* For any type [A] of data, we can build a queue for that element type. *)
    Parameter enqueue : forall A, t A -> A -> t A.
    (* Enqueue a new element, in the functional style, where we build a new
     * queue instead of modifying the original. *)
    Parameter dequeue : forall A, t A -> option (t A * A).
    (* Given a queue, either return [None] if it is empty or [Some (q', v)] for
     * the result of dequeuing one element, where [q'] is the new queue (now
     * one element shorter) and [v] is the element we dequeue. *)

    (* Which algebraic properties characterize correct queues? *)

    (* First, [dequeue] returns [None] exactly on empty queues. *)
    Axiom dequeue_empty : forall A,
        dequeue (empty A) = None.
    Axiom empty_dequeue : forall A (q : t A),
        dequeue q = None -> q = empty A.

    (* Second, [dequeue] forms a kind of inverse for [enqueue]. *)
    Axiom dequeue_enqueue : forall A (q : t A) x,
        dequeue (enqueue q x) = Some (match dequeue q with
                                      | None => (empty A, x)
                                      | Some (q', y) => (enqueue q' x, y)
                                      end).

    (* These properties turn out to be enough to prove interesting properties
     * about client code that uses queues.  Before we get there, we should
     * define some concrete queue implementations.  (If we don't give an
     * implementation, we often realize that the spec is *unrealizable*!) *)
  End QUEUE.

  (* First, there is a fairly straightforward implementation with lists. *)
  Module ListQueue : QUEUE.
    Definition t : Set -> Set := list.
    (* Note that we use identifier [list] alone as a first-class type family,
     * without specifying a parameter explicitly. *)

    (* We follow the convention of enqueuing onto the front of lists and
     * dequeuing from the back, so the first two operations are just the first
     * two constructors of [list]. *)
    Definition empty A : t A := nil.
    Definition enqueue A (q : t A) (x : A) : t A := x :: q.

    (* [dequeue] is a little more work: we use recursion to step down to the
     * last element of a list. *)
    Fixpoint dequeue A (q : t A) : option (t A * A) :=
      match q with
      | [] => None
      | x :: q' =>
        match dequeue q' with
        | None => Some ([], x)
        | Some (q'', y) => Some (x :: q'', y)
        end
      end.

    (* Applying our experience so far with Coq proofs, the algebraic laws are
     * unremarkable to establish. *)

    Theorem dequeue_empty : forall A, dequeue (empty A) = None.
    Proof.
      simplify.
      equality.
    Qed.

    Theorem empty_dequeue : forall A (q : t A),
        dequeue q = None -> q = empty A.
    Proof.
      simplify.
      cases q.

      simplify.
      equality.

      simplify.
      cases (dequeue q).
      cases p.
      equality.
      equality.
    Qed.

    Theorem dequeue_enqueue : forall A (q : t A) x,
        dequeue (enqueue q x) = Some (match dequeue q with
                                      | None => (empty A, x)
                                      | Some (q', y) => (enqueue q' x, y)
                                      end).
    Proof.
      simplify.
      cases (dequeue q).

      cases p.
      equality.

      equality.
    Qed.
  End ListQueue.

  (* There are software-engineering benefits to interface-implementation
   * separation even when one only bothers to build a single implementation.
   * However, often there are naive and clever optimized versions of a single
   * interface.  Queues are no exception.  Before we get to a truly clever
   * version, we'll demonstrate with a less obviously better version:
   * enqueuing at the back and dequeuing from the front. *)
  Module ReversedListQueue : QUEUE.
    Definition t : Set -> Set := list.
    (* Still the same internal queue type, but note that Coq's type system
     * prevents client code from knowing that fact!  [t] appears *opaque*
     * or *abstract* from the outside, as we'll see shortly. *)

    (* The first two operations are similar, but now we enqueue at the
     * list end. *)
    Definition empty A : t A := [].
    Definition enqueue A (q : t A) (x : A) : t A := q ++ [x].

    (* [dequeue] is now constant-time, with no recursion and just a single
     * pattern match. *)
    Definition dequeue A (q : t A) : option (t A * A) :=
      match q with
      | [] => None
      | x :: q' => Some (q', x)
      end.

    (* The proofs of the laws are still boring. *)

    Theorem dequeue_empty : forall A, dequeue (empty A) = None.
    Proof.
      simplify.
      equality.
    Qed.

    Theorem empty_dequeue : forall A (q : t A),
        dequeue q = None -> q = empty A.
    Proof.
      simplify.
      cases q.

      simplify.
      equality.

      simplify.
      equality.
    Qed.

    Theorem dequeue_enqueue : forall A (q : t A) x,
        dequeue (enqueue q x) = Some (match dequeue q with
                                      | None => (empty A, x)
                                      | Some (q', y) => (enqueue q' x, y)
                                      end).
    Proof.
      simplify.
      unfold dequeue, enqueue.
      cases q; simplify.
      equality.
      equality.
    Qed.
  End ReversedListQueue.

  (* Let's take a look at some client code that is agnostic to queue
   * implementation details.  We have been using Coq's *module system*, inspired
   * by those of the ML programming languages, to encode interfaces and
   * implementations.  Coq also adopts from ML the idea of *functors*, or
   * functions from modules to modules. *)
  Module DelayedSum (Q : QUEUE).
    (* The code in this scope may refer to some unknown implementation [Q] of
     * the [QUEUE] interface. *)

    (* We will only use a simple example here: enqueue the first [n] natural
     * numbers and then successively dequeue them, computing the sum as we
     * go. *)

    (* First, the function to enqueue the first [n] natural numbers. *)
    Fixpoint makeQueue (n : nat) (q : Q.t nat) : Q.t nat :=
      match n with
      | 0 => q
      | S n' => makeQueue n' (Q.enqueue q n')
      end.

    (* Next, the function to dequeue repeatedly, keeping a sum. *)
    Fixpoint computeSum (n : nat) (q : Q.t nat) : nat :=
      match n with
      | 0 => 0
      | S n' => match Q.dequeue q with
                | None => 0
                | Some (q', v) => v + computeSum n' q'
                end
      end.

    (* This function gives the expected answer, in a simpler form, of
     * [computeSum] after [makeQueue]. *)
    Fixpoint sumUpto (n : nat) : nat :=
      match n with
      | 0 => 0
      | S n' => n' + sumUpto n'
      end.

    (* A crucial lemma: what results from dequeuing out of a [makeQueue]
     * call?  The answer depends on whether the initial queue [q] has anything
     * to dequeue. *)
    Lemma dequeue_makeQueue : forall n q,
        Q.dequeue (makeQueue n q)
        = match Q.dequeue q with
          | Some (q', v) =>
            (* The queue we started with had content.  We dequeue from it. *)
            Some (makeQueue n q', v)
          | None =>
            (* No content in initial queue.  We get [n-1] (unless [n = 0]). *)
            match n with
            | 0 => None
            | S n' => Some (makeQueue n' q, n')
            end
          end.
    Proof.
      induct n.

      simplify.
      cases (Q.dequeue q).
      cases p.
      equality.
      equality.

      simplify.
      rewrite IHn.
      rewrite Q.dequeue_enqueue.
      (* ^-- Crucial step!  First use of a law from the interface. *)
      cases (Q.dequeue q).
      cases p.
      equality.

      rewrite (Q.empty_dequeue (q := q)).
      (* ^-- Another law! *)
      equality.
      assumption.
    Qed.

    (* Now we can tackle the final property directly by induction. *)
    Theorem computeSum_ok : forall n,
        computeSum n (makeQueue n (Q.empty nat)) = sumUpto n.
    Proof.
      induct n.

      simplify.
      equality.

      simplify.
      rewrite dequeue_makeQueue.
      rewrite Q.dequeue_enqueue.
      rewrite Q.dequeue_empty.
      rewrite IHn.
      equality.
    Qed.
  End DelayedSum.
End Algebraic.

(* There is a famous implementation of queues with two stacks, achieving
 * amortized constant time for all operations, in contrast to the worst-case
 * quadratic time of both queue implementations we just saw.  However, to
 * justify this fancy implementation, we will need to choose a more permissive
 * interface, based on the idea of parameterizing over an arbitrary *equivalence
 * relation* between queues, which need not be simple equality. *)
Module AlgebraicWithEquivalenceRelation.
  Module Type QUEUE.
    (* We still have a type family of queues, plus the same three operations. *)
    Parameter t : Set -> Set.


    Parameter empty : forall A, t A.
    Parameter enqueue : forall A, t A -> A -> t A.
    Parameter dequeue : forall A, t A -> option (t A * A).

    (* What's new?  This equivalence relation.  The type [Prop] stands for
     * logical truth values, so a function returning it can be seen as a
     * relation in the usual mathematical sense.  This is a *binary* relation,
     * in particular, since it takes two arguments. *)
    Parameter equiv : forall A, t A -> t A -> Prop.

    (* Let's declare convenient syntax for the relation. *)
    Infix "~=" := equiv (at level 70).

    (* It really is an equivalence relation, as formalized by the usual three
     * laws. *)
    Axiom equiv_refl : forall A (a : t A), a ~= a.
    Axiom equiv_sym : forall A (a b : t A), a ~= b -> b ~= a.
    Axiom equiv_trans : forall A (a b c : t A), a ~= b -> b ~= c -> a ~= c.

    (* It must be the case that enqueuing elements preserves the relation. *)
    Axiom equiv_enqueue : forall A (a b : t A) (x : A),
        a ~= b
        -> enqueue a x ~= enqueue b x.

    (* We define a derived relation for results of [dequeue]: either both
     * [dequeue]s failed to return anything, or both returned the same data
     * value along with new queues that are themselves related. *)
    Definition dequeue_equiv A (a b : option (t A * A)) :=
      match a, b with
      | None, None => True
      | Some (qa, xa), Some (qb, xb) => qa ~= qb /\ xa = xb
      | _, _ => False
      end.

    Infix "~~=" := dequeue_equiv (at level 70).

    Axiom equiv_dequeue : forall A (a b : t A),
        a ~= b
        -> dequeue a ~~= dequeue b.

    (* We retain the three axioms from the prior interface, using our fancy
     * relation instead of equality on queues. *)

    Axiom dequeue_empty : forall A,
        dequeue (empty A) = None.
    Axiom empty_dequeue : forall A (q : t A),
        dequeue q = None -> q ~= empty A.

    Axiom dequeue_enqueue : forall A (q : t A) x,
        dequeue (enqueue q x)
        ~~= match dequeue q with
            | None => Some (empty A, x)
            | Some (q', y) => Some (enqueue q' x, y)
            end.
  End QUEUE.

  (* It's easy to redo [ListQueue], specifying normal equality for the
   * equivalence relation. *)
  Module ListQueue : QUEUE.
    Definition t : Set -> Set := list.

    Definition empty A : t A := nil.
    Definition enqueue A (q : t A) (x : A) : t A := x :: q.
    Fixpoint dequeue A (q : t A) : option (t A * A) :=
      match q with
      | [] => None
      | x :: q' =>
        match dequeue q' with
        | None => Some ([], x)
        | Some (q'', y) => Some (x :: q'', y)
        end
      end.

    Definition equiv A (a b : t A) := a = b.
    Infix "~=" := equiv (at level 70).

    Theorem equiv_refl : forall A (a : t A), a ~= a.
    Proof.
      equality.
    Qed.

    Theorem equiv_sym : forall A (a b : t A), a ~= b -> b ~= a.
    Proof.
      equality.
    Qed.

    Theorem equiv_trans : forall A (a b c : t A), a ~= b -> b ~= c -> a ~= c.
    Proof.
      equality.
    Qed.

    Theorem equiv_enqueue : forall A (a b : t A) (x : A),
        a ~= b
        -> enqueue a x ~= enqueue b x.
    Proof.
      unfold equiv; equality.
    Qed.

    Definition dequeue_equiv A (a b : option (t A * A)) :=
      match a, b with
      | None, None => True
      | Some (qa, xa), Some (qb, xb) => qa ~= qb /\ xa = xb
      | _, _ => False
      end.

    Infix "~~=" := dequeue_equiv (at level 70).

    Theorem equiv_dequeue : forall A (a b : t A),
        a ~= b
        -> dequeue a ~~= dequeue b.
    Proof.
      unfold equiv, dequeue_equiv; simplify.
      rewrite H.
      cases (dequeue b).

      cases p.
      equality.

      propositional.
    Qed.

    Theorem dequeue_empty : forall A, dequeue (empty A) = None.
    Proof.
      simplify.
      equality.
    Qed.

    Theorem empty_dequeue : forall A (q : t A),
        dequeue q = None -> q ~= empty A.
    Proof.
      simplify.
      cases q.

      simplify.
      unfold equiv.
      equality.

      simplify.
      cases (dequeue q).
      cases p.
      equality.
      equality.
    Qed.

    Theorem dequeue_enqueue : forall A (q : t A) x,
        dequeue (enqueue q x)
        ~~= match dequeue q with
            | None => Some (empty A, x)
            | Some (q', y) => Some (enqueue q' x, y)
            end.
    Proof.
      unfold dequeue_equiv, equiv.
      induct q; simplify.

      equality.

      cases (dequeue q).

      cases p.
      equality.
      equality.
    Qed.
  End ListQueue.

  (* However, now we can implement the classic two-stacks optimized queue! *)
  Module TwoStacksQueue : QUEUE.
    (* Every queue is a pair of stacks: one for enqueuing and one for
     * dequeuing. *)
    Record stackpair (A : Set) := {
      EnqueueHere : list A;
      (* This stack has more recently enqueued elements closer to the front,
       * making enqueuing constant-time. *)

      DequeueHere : list A
      (* This stack has least recently enqueued elements closer to the front,
       * making dequeuing constant-time. *)
    }.
    (* What's the catch?  Sometimes we need to reverse [EnqueueHere] and
     * transfer it to [DequeueHere], or otherwise there would never be anything
     * to dequeue!  Luckily, the work we do in transfering is bounded
     * asymptotically by the total number of enqueue/dequeue operations, so
     * we get *amortized* constant time. *)

    (* By the way, the [Record] feature we used above is similar to e.g. structs
     * in C. *)

    Definition t := stackpair.

    Definition empty A : t A := {|
      EnqueueHere := [];
      DequeueHere := []
    |}.
    Definition enqueue A (q : t A) (x : A) : t A := {|
      EnqueueHere := x :: q.(EnqueueHere);
      DequeueHere := q.(DequeueHere)
    |}.
    Definition dequeue A (q : t A) : option (t A * A) :=
      match q.(DequeueHere) with
      | x :: dq => Some ({| EnqueueHere := q.(EnqueueHere);
                            DequeueHere := dq |}, x)
      | [] =>
        (* Out of dequeuable elements.  Reverse enqueued elements
         * and transfer to the other stack. *)
        match rev q.(EnqueueHere) with
        | [] => None
        | x :: eq => Some ({| EnqueueHere := [];
                              DequeueHere := eq |}, x)
        end
      end.

    (* This function explains which simple queue representation we have in mind,
     * for each fancy two-stack representation. *)
    Definition elements A (q : t A) : list A :=
      q.(EnqueueHere) ++ rev q.(DequeueHere).

    (* That function is useful to define our equivalence relation. *)
    Definition equiv A (a b : t A) :=
      elements a = elements b.
    Infix "~=" := equiv (at level 70).

    Theorem equiv_refl : forall A (a : t A), a ~= a.
    Proof.
      equality.
    Qed.

    Theorem equiv_sym : forall A (a b : t A), a ~= b -> b ~= a.
    Proof.
      equality.
    Qed.

    Theorem equiv_trans : forall A (a b c : t A), a ~= b -> b ~= c -> a ~= c.
    Proof.
      equality.
    Qed.

    (* Now it is mostly routine to prove the laws, though a few tricks may
     * be worth reading through. *)

    Theorem equiv_enqueue : forall A (a b : t A) (x : A),
        a ~= b
        -> enqueue a x ~= enqueue b x.
    Proof.
      unfold equiv, elements; simplify.
      equality.
    Qed.

    Definition dequeue_equiv A (a b : option (t A * A)) :=
      match a, b with
      | None, None => True
      | Some (qa, xa), Some (qb, xb) => qa ~= qb /\ xa = xb
      | _, _ => False
      end.

    Infix "~~=" := dequeue_equiv (at level 70).

    Theorem equiv_dequeue : forall A (a b : t A),
        a ~= b
        -> dequeue a ~~= dequeue b.
    Proof.
      unfold equiv, dequeue_equiv, elements, dequeue; simplify.
      cases (DequeueHere a); simplify.
      cases (rev (EnqueueHere a)); simplify.
      cases (DequeueHere b); simplify.
      cases (rev (EnqueueHere b)); simplify.
      propositional.
      SearchRewrite (_ ++ []).
      rewrite app_nil_r in H.
      rewrite app_nil_r in H.
      equality.
      cases (EnqueueHere a); simplify.
      cases (EnqueueHere b); simplify.
      cases (rev l); simplify.
      equality.
      equality.
      equality.
      cases (rev l0); simplify.
      equality.
      equality.
      cases (DequeueHere b); simplify.
      cases (rev (EnqueueHere b)); simplify.
      rewrite app_nil_r in H.
      rewrite app_nil_r in H.
      equality.
      rewrite app_nil_r in H.
      rewrite app_nil_r in H.
      equality.
      rewrite app_nil_r in H.
      rewrite H in Heq0.
      SearchRewrite (rev (_ ++ _)).
      rewrite rev_app_distr in Heq0.
      rewrite rev_app_distr in Heq0.
      simplify.
      invert Heq0.
      unfold equiv, elements.
      simplify.
      rewrite rev_app_distr.
      SearchRewrite (rev (rev _)).
      rewrite rev_involutive.
      rewrite rev_involutive.
      equality.
      cases (DequeueHere b); simplify.
      cases (rev (EnqueueHere b)); simplify.
      rewrite app_nil_r in H.
      rewrite <- H in Heq1.
      cases (EnqueueHere a); simplify.
      cases (rev l); simplify.
      equality.
      rewrite rev_app_distr in Heq1.
      simplify.
      equality.
      rewrite rev_app_distr in Heq1.
      rewrite rev_app_distr in Heq1.
      simplify.
      equality.
      unfold equiv, elements.
      simplify.
      rewrite app_nil_r in H.
      rewrite <- H in Heq1.
      rewrite rev_app_distr in Heq1.
      rewrite rev_app_distr in Heq1.
      simplify.
      invert Heq1.
      rewrite rev_involutive.
      rewrite rev_app_distr.
      rewrite rev_involutive.
      equality.
      unfold equiv, elements.
      simplify.
      SearchAbout app cons nil.
      apply app_inj_tail.
      rewrite <- app_assoc.
      rewrite <- app_assoc.
      assumption.
    Qed.

    Theorem dequeue_empty : forall A, dequeue (empty A) = None.
    Proof.
      simplify.
      equality.
    Qed.

    Theorem empty_dequeue : forall A (q : t A),
        dequeue q = None -> q ~= empty A.
    Proof.
      simplify.
      cases q.
      unfold dequeue in *.
      simplify.
      cases DequeueHere0.
      cases (rev EnqueueHere0).
      cases EnqueueHere0.
      equality.
      simplify.
      cases (rev EnqueueHere0); simplify.
      equality.
      equality.
      equality.
      equality.
    Qed.

    Theorem dequeue_enqueue : forall A (q : t A) x,
        dequeue (enqueue q x)
        ~~= match dequeue q with
            | None => Some (empty A, x)
            | Some (q', y) => Some (enqueue q' x, y)
            end.
    Proof.
      unfold dequeue_equiv, equiv; simplify.
      cases q; simplify.
      unfold dequeue, enqueue; simplify.
      cases DequeueHere0; simplify.

      cases (rev EnqueueHere0); simplify.

      equality.

      unfold elements; simplify.
      SearchRewrite (rev (_ ++ _)).
      rewrite rev_app_distr.
      simplify.
      equality.

      equality.
    Qed.
  End TwoStacksQueue.

  (* The exercise of the generic delayed sum may be repeated with equivalence
   * relations. *)

  Module DelayedSum (Q : QUEUE).
    Fixpoint makeQueue (n : nat) (q : Q.t nat) : Q.t nat :=
      match n with
      | 0 => q
      | S n' => makeQueue n' (Q.enqueue q n')
      end.

    Fixpoint computeSum (n : nat) (q : Q.t nat) : nat :=
      match n with
      | 0 => 0
      | S n' => match Q.dequeue q with
                | None => 0
                | Some (q', v) => v + computeSum n' q'
                end
      end.

    Fixpoint sumUpto (n : nat) : nat :=
      match n with
      | 0 => 0
      | S n' => n' + sumUpto n'
      end.

    Infix "~=" := Q.equiv (at level 70).
    Infix "~~=" := Q.dequeue_equiv (at level 70).

    Lemma makeQueue_congruence : forall n a b,
        a ~= b
        -> makeQueue n a ~= makeQueue n b.
    Proof.
      induct n; simplify.

      assumption.

      apply IHn.
      apply Q.equiv_enqueue.
      assumption.
    Qed.

    Lemma dequeue_makeQueue : forall n q,
        Q.dequeue (makeQueue n q)
        ~~= match Q.dequeue q with
            | Some (q', v) => Some (makeQueue n q', v)
            | None =>
              match n with
              | 0 => None
              | S n' => Some (makeQueue n' q, n')
              end
            end.
    Proof.
      induct n.

      simplify.
      cases (Q.dequeue q).
      cases p.
      unfold Q.dequeue_equiv.
      propositional.
      apply Q.equiv_refl.
      unfold Q.dequeue_equiv.
      propositional.

      simplify.
      unfold Q.dequeue_equiv in *.
      specialize (IHn (Q.enqueue q n)).
      cases (Q.dequeue (makeQueue n (Q.enqueue q n))).

      cases p.
      pose proof (Q.dequeue_enqueue q n).
      unfold Q.dequeue_equiv in *.
      cases (Q.dequeue (Q.enqueue q n)).

      cases p.
      cases (Q.dequeue q).

      cases p.
      propositional.
      apply Q.equiv_trans with (b := makeQueue n t0).
      assumption.
      apply makeQueue_congruence.
      assumption.
      equality.

      propositional.
      apply Q.equiv_trans with (b := makeQueue n t0).
      assumption.
      apply makeQueue_congruence.
      apply Q.equiv_trans with (b := Q.empty nat).
      assumption.
      apply Q.equiv_sym.
      apply Q.empty_dequeue.
      assumption.
      equality.

      cases (Q.dequeue q).

      cases p.
      propositional.

      propositional.

      pose proof (Q.dequeue_enqueue q n).
      unfold Q.dequeue_equiv in H.
      cases (Q.dequeue (Q.enqueue q n)).

      cases p.
      propositional.

      cases (Q.dequeue q).

      cases p.
      propositional.

      propositional.
    Qed.

    Theorem computeSum_congruence : forall n a b,
        a ~= b
        -> computeSum n a = computeSum n b.
    Proof.
      induct n.

      simplify.
      equality.

      simplify.
      pose proof (Q.equiv_dequeue H).
      unfold Q.dequeue_equiv in H0.
      cases (Q.dequeue a).

      cases p.
      cases (Q.dequeue b).
      cases p.
      rewrite IHn with (b := t0).
      equality.
      equality.
      propositional.

      cases (Q.dequeue b).
      propositional.
      equality.
    Qed.

    Theorem computeSum_ok : forall n,
        computeSum n (makeQueue n (Q.empty nat)) = sumUpto n.
    Proof.
      induct n.

      simplify.
      equality.

      simplify.
      pose proof (dequeue_makeQueue n (Q.enqueue (Q.empty nat) n)).
      unfold Q.dequeue_equiv in H.
      cases (Q.dequeue (makeQueue n (Q.enqueue (Q.empty nat) n))).

      cases p.
      pose proof (Q.dequeue_enqueue (Q.empty nat) n).
      unfold Q.dequeue_equiv in H0.
      cases (Q.dequeue (Q.enqueue (Q.empty nat) n)).

      cases p.
      rewrite Q.dequeue_empty in H0.
      propositional.
      f_equal.
      equality.
      rewrite <- IHn.
      
      apply computeSum_congruence.
      apply Q.equiv_trans with (b := makeQueue n t0).
      assumption.
      apply makeQueue_congruence.
      assumption.

      rewrite Q.dequeue_empty in H0.
      propositional.

      pose proof (Q.dequeue_enqueue (Q.empty nat) n).
      unfold Q.dequeue_equiv in H0.
      cases (Q.dequeue (Q.enqueue (Q.empty nat) n)).

      cases p.
      propositional.

      rewrite Q.dequeue_empty in H0.
      propositional.
    Qed.
  End DelayedSum.
End AlgebraicWithEquivalenceRelation.

(* It's worth presenting one final style of data-abstraction formalism: we
 * introduce *representation functions* in the interface, to map the internal
 * representation to some standard one that is easy to reason about.  We don't
 * expect "real code" to call the representation function.  Instead, it's just a
 * proof device to let us write convincing laws.  Here's the previous example
 * redone in this manner, without comment. *)
Module RepFunction.
  Module Type QUEUE.
    Parameter t : Set -> Set.

    Parameter empty : forall A, t A.
    Parameter enqueue : forall A, t A -> A -> t A.
    Parameter dequeue : forall A, t A -> option (t A * A).

    Parameter rep : forall A, t A -> list A.

    Axiom empty_rep : forall A,
        rep (empty A) = [].

    Axiom enqueue_rep : forall A (q : t A) x,
        rep (enqueue q x) = x :: rep q.

    Axiom dequeue_empty : forall A (q : t A),
        rep q = []
        -> dequeue q = None.

    Axiom dequeue_nonempty : forall A (q : t A) xs x,
        rep q = xs ++ [x]
        -> exists q', dequeue q = Some (q', x) /\ rep q' = xs.
  End QUEUE.

  Module ListQueue : QUEUE.
    Definition t : Set -> Set := list.

    Definition empty A : t A := nil.
    Definition enqueue A (q : t A) (x : A) : t A := x :: q.
    Fixpoint dequeue A (q : t A) : option (t A * A) :=
      match q with
      | [] => None
      | x :: q' =>
        match dequeue q' with
        | None => Some ([], x)
        | Some (q'', y) => Some (x :: q'', y)
        end
      end.

    Definition rep A (q : t A) := q.

    Theorem empty_rep : forall A,
        rep (empty A) = [].
    Proof.
      equality.
    Qed.

    Theorem enqueue_rep : forall A (q : t A) x,
        rep (enqueue q x) = x :: rep q.
    Proof.
      equality.
    Qed.

    Theorem dequeue_empty : forall A (q : t A),
        rep q = []
        -> dequeue q = None.
    Proof.
      unfold rep; simplify.
      rewrite H.
      equality.
    Qed.

    Theorem dequeue_nonempty : forall A (q : t A) xs x,
        rep q = xs ++ [x]
        -> exists q', dequeue q = Some (q', x) /\ rep q' = xs.
    Proof.
      unfold rep; induct q.

      simplify.
      cases xs; simplify.
      equality.
      equality.

      simplify.
      cases xs; simplify.
      invert H; simplify.
      exists [].
      equality.

      invert H.
      assert (exists q' : t A, dequeue (xs ++ [x]) = Some (q', x) /\ q' = xs).
      apply IHq.
      equality.
      first_order.
      rewrite H.
      exists (a0 :: x0).
      equality.
    Qed.
  End ListQueue.

  Module TwoStacksQueue : QUEUE.
    Record stackpair (A : Set) := {
      EnqueueHere : list A;
      DequeueHere : list A
    }.

    Definition t := stackpair.

    Definition empty A : t A := {|
      EnqueueHere := [];
      DequeueHere := []
    |}.
    Definition enqueue A (q : t A) (x : A) : t A := {|
      EnqueueHere := x :: q.(EnqueueHere);
      DequeueHere := q.(DequeueHere)
    |}.
    Definition dequeue A (q : t A) : option (t A * A) :=
      match q.(DequeueHere) with
      | x :: dq => Some ({| EnqueueHere := q.(EnqueueHere);
                            DequeueHere := dq |}, x)
      | [] =>
        match rev q.(EnqueueHere) with
        | [] => None
        | x :: eq => Some ({| EnqueueHere := [];
                              DequeueHere := eq |}, x)
        end
      end.

    Definition rep A (q : t A) : list A :=
      q.(EnqueueHere) ++ rev q.(DequeueHere).

    Theorem empty_rep : forall A,
        rep (empty A) = [].
    Proof.
      equality.
    Qed.

    Theorem enqueue_rep : forall A (q : t A) x,
        rep (enqueue q x) = x :: rep q.
    Proof.
      equality.
    Qed.

    Theorem dequeue_empty : forall A (q : t A),
        rep q = []
        -> dequeue q = None.
    Proof.
      unfold rep, dequeue; simplify.
      cases (DequeueHere q); simplify.
      rewrite app_nil_r in H.
      rewrite H.
      simplify.
      equality.
      cases (EnqueueHere q); simplify.
      cases (rev l); simplify.
      equality.
      equality.
      equality.
    Qed.

    Theorem dequeue_nonempty : forall A (q : t A) xs x,
        rep q = xs ++ [x]
        -> exists q', dequeue q = Some (q', x) /\ rep q' = xs.
    Proof.
      unfold rep, dequeue; simplify.

      cases (DequeueHere q); simplify.

      rewrite app_nil_r in H.
      rewrite H.
      rewrite rev_app_distr; simplify.
      exists {| EnqueueHere := []; DequeueHere := rev xs |}.
      simplify.
      rewrite rev_involutive.
      equality.

      exists {| EnqueueHere := EnqueueHere q; DequeueHere := l |}.
      simplify.
      rewrite app_assoc in H.
      apply app_inj_tail in H.
      propositional.
      rewrite H1.
      equality.
    Qed.
  End TwoStacksQueue.

  Module DelayedSum (Q : QUEUE).
    Fixpoint makeQueue (n : nat) (q : Q.t nat) : Q.t nat :=
      match n with
      | 0 => q
      | S n' => makeQueue n' (Q.enqueue q n')
      end.

    Fixpoint computeSum (n : nat) (q : Q.t nat) : nat :=
      match n with
      | 0 => 0
      | S n' => match Q.dequeue q with
                | None => 0
                | Some (q', v) => v + computeSum n' q'
                end
      end.

    Fixpoint sumUpto (n : nat) : nat :=
      match n with
      | 0 => 0
      | S n' => n' + sumUpto n'
      end.

    Fixpoint upto (n : nat) : list nat :=
      match n with
      | 0 => []
      | S n' => upto n' ++ [n']
      end.

    Lemma makeQueue_rep : forall n q,
        Q.rep (makeQueue n q) = upto n ++ Q.rep q.
    Proof.
      induct n.

      simplify.
      equality.

      simplify.
      rewrite IHn.
      rewrite Q.enqueue_rep.
      rewrite <- app_assoc.
      simplify.
      equality.
    Qed.

    Lemma computeSum_makeQueue' : forall n q,
        Q.rep q = upto n
        -> computeSum n q = sumUpto n.
    Proof.
      induct n.

      simplify.
      equality.

      simplify.
      pose proof (Q.dequeue_nonempty _ _ H).
      first_order.
      rewrite H0.
      rewrite IHn.
      equality.
      assumption.
    Qed.

    Theorem computeSum_ok : forall n,
        computeSum n (makeQueue n (Q.empty nat)) = sumUpto n.
    Proof.
      simplify.
      apply computeSum_makeQueue'.
      rewrite makeQueue_rep.
      rewrite Q.empty_rep.
      apply app_nil_r.
    Qed.
  End DelayedSum.
End RepFunction.


(** * Data abstraction with fixed parameter types *)

(* Finite sets are another classic *abstract data type*, another name for what
 * we have been defining so far with modules.  Here's a generic finite-set
 * interface, following the first algebraic style we saw above. *)
Module Type FINITE_SET.
  Parameter key : Set. (* What type of data may be added to these sets? *)
  Parameter t : Set.   (* What is the type of sets themselves? *)

  Parameter empty : t.
  Parameter add : t -> key -> t.
  Parameter member : t -> key -> bool.

  Axiom member_empty : forall k, member empty k = false.

  Axiom member_add_eq : forall k s,
      member (add s k) k = true.
  Axiom member_add_noteq : forall k1 k2 s,
      k1 <> k2
      -> member (add s k1) k2 = member s k2.

  Axiom decidable_equality : forall a b : key, a = b \/ a <> b.
  (* This last axiom may be a bit surprising.  Coq is so oriented toward
   * computation that we don't assume the *law of the excluded middle*, which
   * says that every proposition is either true or false.  Instead, we prove
   * specific instances as needed.  But feel free to ignore this point for
   * the purposes of this class. *)
End FINITE_SET.

(* We want a generic implementation of finite sets, as found in the standard
 * libaries of languages like Java.  However, not just any key set will do.
 * We need enough computable operations.  One sufficient operation is an
 * equality test. *)
Module Type SET_WITH_EQUALITY.
  Parameter t : Set.
  Parameter equal : t -> t -> bool.

  Axiom equal_ok : forall a b, if equal a b then a = b else a <> b.
End SET_WITH_EQUALITY.

(* Here's a generic implementation of finite sets, parameterized over an
 * arbitrary set with a correct equality operation.  Note the use of the [with]
 * operator to *refine* the result signature [FINITE_SET]: we reveal that the
 * [key] type is actually [SE.T], that is, the key type from the parameter module
 * [SE]. *)
Module ListSet(SE : SET_WITH_EQUALITY) <: FINITE_SET with Definition key := SE.t.
  Definition key := SE.t.
  Definition t := list SE.t.

  Definition empty : t := [].
  Definition add (s : t) (k : key) : t := k :: s.
  Fixpoint member (s : t) (k : key) : bool :=
    match s with
    | [] => false
    | k' :: s' => SE.equal k' k || member s' k
    end.

  Theorem member_empty : forall k, member empty k = false.
  Proof.
    simplify.
    equality.
  Qed.

  Theorem member_add_eq : forall k s,
      member (add s k) k = true.
  Proof.
    simplify.
    pose proof (SE.equal_ok k k).
    cases (SE.equal k k); simplify.
    equality.
    equality.
  Qed.

  Theorem member_add_noteq : forall k1 k2 s,
      k1 <> k2
      -> member (add s k1) k2 = member s k2.
  Proof.
    simplify.
    pose proof (SE.equal_ok k1 k2).
    cases (SE.equal k1 k2); simplify.
    equality.
    equality.
  Qed.

  Theorem decidable_equality : forall a b : key, a = b \/ a <> b.
  Proof.
    simplify.
    pose proof (SE.equal_ok a b).
    cases (SE.equal a b); propositional.
  Qed.
End ListSet.

(* Here's an example decidable-equality type for natural numbers. *)
Module NatWithEquality <: SET_WITH_EQUALITY with Definition t := nat.
  Definition t := nat.

  Fixpoint equal (a b : nat) : bool :=
    match a, b with
    | 0, 0 => true
    | S a', S b' => equal a' b'
    | _, _ => false
    end.

  Theorem equal_ok : forall a b, if equal a b then a = b else a <> b.
  Proof.
    induct a; simplify.

    cases b.
    equality.
    equality.

    cases b.
    equality.
    specialize (IHa b).
    cases (equal a b).
    equality.
    equality.
  Qed.
End NatWithEquality.

(* And here's how to instantiate the generic set for the naturals. *)
Module NatSet := ListSet(NatWithEquality).

(* Now, some generic client code, for testing duplicate-freeness of lists. *)
Module FindDuplicates (FS : FINITE_SET).
  Fixpoint noDuplicates' (ls : list FS.key) (s : FS.t) : bool :=
    match ls with
    | [] => true
    | x :: ls' => negb (FS.member s x) && noDuplicates' ls' (FS.add s x)
    end.

  Definition noDuplicates (ls : list FS.key) := noDuplicates' ls FS.empty.

  (* A characterization of having a duplicate: the list can be partitioned into
   * pieces revealing the same element [a] at two boundaries. *)
  Definition hasDuplicate (ls : list FS.key) :=
    exists ls1 a ls2 ls3, ls = ls1 ++ a :: ls2 ++ a :: ls3.

  (* A characterization of containing an element [a]: the list can be
   * partitioned into two pieces, with [a] at the boundary. *)
  Definition contains (a : FS.key) (ls : list FS.key) :=
    exists ls1 ls2, ls = ls1 ++ a :: ls2.

  Lemma noDuplicates'_ok : forall ls s, if noDuplicates' ls s
                                        then ~(hasDuplicate ls
                                               \/ exists a, FS.member s a = true
                                                            /\ contains a ls)
                                        else (hasDuplicate ls
                                              \/ exists a, FS.member s a = true
                                                           /\ contains a ls).
  Proof.
    induct ls; simplify.

    unfold hasDuplicate, contains.
    propositional.
    first_order.
    cases x; simplify.
    equality.
    equality.

    first_order.
    cases x0; simplify.
    equality.
    equality.
    cases (FS.member s a); simplify.
    right.
    exists a.
    propositional.
    unfold contains.
    exists [].
    exists ls.
    simplify.
    equality.

    specialize (IHls (FS.add s a)).
    cases (noDuplicates' ls (FS.add s a)).
    propositional.

    apply H1.
    exists a.
    propositional.
    apply FS.member_add_eq.
    unfold hasDuplicate, contains in *.
    first_order.
    cases x; simplify.
    invert H0.
    exists x1.
    exists x2.
    equality.

    invert H0.
    exfalso.
    apply H with (x3 := x).
    exists x0.
    exists x1.
    exists x2.
    equality.

    first_order.
    apply H1 with x.
    propositional.
    pose proof (FS.decidable_equality a x).
    propositional.
    rewrite H4.
    apply FS.member_add_eq.
    rewrite FS.member_add_noteq.
    assumption.
    assumption.
    cases x0; simplify.
    equality.
    invert H2.
    exists x0.
    exists x1.
    equality.

    first_order.
    left.
    exists (a :: x).
    exists x0.
    exists x1.
    exists x2.
    simplify.
    equality.
    cases (FS.member s x).

    right.
    exists x.
    propositional.
    exists (a :: x0).
    exists x1.
    simplify.
    equality.

    left.
    pose proof (FS.decidable_equality a x).
    propositional.

    exists nil.
    exists a.
    exists x0.
    exists x1.
    simplify.
    equality.
    rewrite FS.member_add_noteq in H.
    equality.
    assumption.
  Qed.

  Theorem noDuplicates_ok : forall ls, if noDuplicates ls
                                       then ~hasDuplicate ls 
                                       else hasDuplicate ls.
  Proof.
    simplify.
    pose proof (noDuplicates'_ok ls FS.empty).
    unfold noDuplicates.
    cases (noDuplicates' ls FS.empty); first_order.
    rewrite FS.member_empty in H.
    equality.
  Qed.
End FindDuplicates.

Module NatDuplicateFinder := FindDuplicates(NatSet).

Compute NatDuplicateFinder.noDuplicates [].
Compute NatDuplicateFinder.noDuplicates [1].
Compute NatDuplicateFinder.noDuplicates [1; 2].
Compute NatDuplicateFinder.noDuplicates [1; 2; 3].
Compute NatDuplicateFinder.noDuplicates [1; 2; 1; 3].


(** * Custom implementations of abstract data types *)

(* Sometimes we want to write custom implementations of polymorphic data types.
 * Our last example of duplicate detection is a good one: we can make it much
 * faster when we know something about how the lists will be built.  In
 * particular, finite sets of natural numbers can be made compact when we know
 * that the common case is *intervals*, sets of consecutive numbers. *)
Module NatRangeSet <: FINITE_SET with Definition key := nat.
  Definition key := nat.

  Inductive rangeSet : Set :=
  | Empty
    (* Set has no elements. *)
  | Range (from to : nat)
    (* Set contains exactly the numbers from [from] to [to], inclusive. *)
  | AdHoc (s : NatSet.t)
    (* Set isn't an interval, so fall back on the list-based version. *).

  Definition t := rangeSet.

  (* When we realize that a freshly formed set isn't an interval, we often need
   * to convert an interval to an ad-hoc set.  These functions accomplish
   * that. *)

  Fixpoint fromRange' (from to : nat) : NatSet.t :=
    match to with
    | 0 => NatSet.add NatSet.empty 0
    | S to' => if NatWithEquality.equal to from
               then NatSet.add NatSet.empty to
               else NatSet.add (fromRange' from to') (S to')
    end.

  Definition fromRange (from to : nat) : NatSet.t :=
    if Compare_dec.leb from to
    then fromRange' from to
    else NatSet.empty.

  Definition empty : t := Empty.
  Definition add (s : t) (k : key) : t :=
    match s with
    | Empty => Range k k
    | Range from to =>
      if Compare_dec.leb from k && Compare_dec.leb k to
      then s
      else if NatWithEquality.equal k (from - 1) && Compare_dec.leb from to
           then Range k to
           else if NatWithEquality.equal k (to + 1) && Compare_dec.leb from to
                then Range from k
                else AdHoc (NatSet.add (fromRange from to) k)
    | AdHoc s' => AdHoc (NatSet.add s' k)
    end.

  Definition member (s : t) (k : key) : bool :=
    match s with
    | Empty => false
    | Range from to => Compare_dec.leb from to && Compare_dec.leb from k && Compare_dec.leb k to
    | AdHoc s' => NatSet.member s' k
    end.

  Theorem member_empty : forall k, member empty k = false.
  Proof.
    simplify.
    equality.
  Qed.

  Lemma member_fromRange' : forall k from to,
      from <= to
      -> NatSet.member (fromRange' from to) k = Compare_dec.leb from k && Compare_dec.leb k to.
  Proof.
    induct to; simplify.

    cases k; simplify.
    rewrite Compare_dec.leb_correct by assumption.
    equality.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.

    cases from; simplify.
    cases k; simplify.
    apply IHto.
    linear_arithmetic.
    pose proof (NatWithEquality.equal_ok to k).
    cases (NatWithEquality.equal to k); simplify.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.
    rewrite IHto by linear_arithmetic.
    cases to.
    rewrite Compare_dec.leb_correct_conv by linear_arithmetic.
    equality.
    cases (Compare_dec.leb k to).
    apply Compare_dec.leb_complete in Heq0.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.
    apply Compare_dec.leb_complete_conv in Heq0.
    rewrite Compare_dec.leb_correct_conv by linear_arithmetic.
    equality.
    
    pose proof (NatWithEquality.equal_ok to from).
    cases (NatWithEquality.equal to from); simplify.

    cases k; simplify.
    equality.
    pose proof (NatWithEquality.equal_ok to k).
    cases (NatWithEquality.equal to k); simplify.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.
    cases (Compare_dec.leb from k); simplify.
    apply Compare_dec.leb_complete in Heq1.
    rewrite Compare_dec.leb_correct_conv by linear_arithmetic.
    equality.
    equality.

    cases k; simplify.
    apply IHto.
    linear_arithmetic.
    rewrite IHto by linear_arithmetic.
    pose proof (NatWithEquality.equal_ok to k).
    cases (NatWithEquality.equal to k); simplify.    
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.

    cases to.
    rewrite (Compare_dec.leb_correct_conv 0 k) by linear_arithmetic.
    equality.
    cases (Compare_dec.leb k to).
    apply Compare_dec.leb_complete in Heq1.
    rewrite (Compare_dec.leb_correct k (S to)) by linear_arithmetic.
    equality.
    apply Compare_dec.leb_complete_conv in Heq1.
    rewrite (Compare_dec.leb_correct_conv (S to) k) by linear_arithmetic.
    equality.
  Qed.

  Theorem member_add_eq : forall k s,
      member (add s k) k = true.
  Proof.
    unfold member, add; simplify.
    cases s.

    SearchAbout Compare_dec.leb.
    rewrite Compare_dec.leb_correct.
    equality.
    linear_arithmetic.

    cases (Compare_dec.leb from k); simplify.
    cases (Compare_dec.leb k to); simplify.
    rewrite Heq.
    rewrite Heq0.
    apply Compare_dec.leb_complete in Heq.
    apply Compare_dec.leb_complete in Heq0.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.

    pose proof (NatWithEquality.equal_ok k (from - 1)).
    cases (NatWithEquality.equal k (from - 1)).
    apply leb_complete in Heq.
    apply leb_complete_conv in Heq0.
    linear_arithmetic.
    simplify.
    pose proof (NatWithEquality.equal_ok k (to + 1)).
    cases (NatWithEquality.equal k (to + 1)); simplify.
    cases (Compare_dec.leb from to).
    rewrite Heq.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.
    apply NatSet.member_add_eq.
    pose proof (NatWithEquality.equal_ok k k).
    cases (NatWithEquality.equal k k); simplify.
    equality.
    equality.

    pose proof (NatWithEquality.equal_ok k (from - 1)).
    cases (NatWithEquality.equal k (from - 1)); simplify.
    cases (Compare_dec.leb from to).
    apply Compare_dec.leb_complete in Heq1.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.
    pose proof (NatWithEquality.equal_ok k (to + 1)).
    cases (NatWithEquality.equal k (to + 1)); simplify.
    pose proof (NatWithEquality.equal_ok k k).
    cases (NatWithEquality.equal k k); simplify.
    equality.
    equality.
    pose proof (NatWithEquality.equal_ok k k).
    cases (NatWithEquality.equal k k); simplify.
    equality.
    equality.
    pose proof (NatWithEquality.equal_ok k (to + 1)).
    cases (NatWithEquality.equal k (to + 1)); simplify.
    cases (Compare_dec.leb from to).
    apply Compare_dec.leb_complete in Heq2.
    apply Compare_dec.leb_complete_conv in Heq.
    linear_arithmetic.
    apply NatSet.member_add_eq.
    pose proof (NatWithEquality.equal_ok k k).
    cases (NatWithEquality.equal k k); simplify.
    equality.
    equality.    

    apply NatSet.member_add_eq.
  Qed.

  Theorem member_add_noteq : forall k1 k2 s,
      k1 <> k2
      -> member (add s k1) k2 = member s k2.
  Proof.
    simplify.
    unfold member, add.
    cases s.

    cases (Compare_dec.leb k1 k2); simplify.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    apply Compare_dec.leb_complete in Heq.
    rewrite Compare_dec.leb_correct_conv.
    equality.
    unfold key in *. (* Tricky step!  Coq needs to see that we are really working with numbers. *)
    linear_arithmetic.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.

    cases (Compare_dec.leb from k1); simplify.
    cases (Compare_dec.leb k1 to); simplify.
    equality.

    pose proof (NatWithEquality.equal_ok k1 (from - 1)).
    cases (NatWithEquality.equal k1 (from - 1)); simplify.
    apply leb_complete in Heq.
    apply leb_complete_conv in Heq0.
    linear_arithmetic.
    pose proof (NatWithEquality.equal_ok k1 (to + 1)).
    cases (NatWithEquality.equal k1 (to + 1)); simplify.
    cases (Compare_dec.leb from to).
    rewrite H1.
    cases (Compare_dec.leb from k2); simplify.
    cases (Compare_dec.leb k2 to).
    apply Compare_dec.leb_complete in Heq5.
    apply Compare_dec.leb_complete in Heq3.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.
    apply Compare_dec.leb_complete in Heq3.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    apply Compare_dec.leb_complete_conv in Heq5.
    unfold key in *.
    rewrite Compare_dec.leb_correct_conv by linear_arithmetic.
    equality.
    rewrite andb_false_r.
    equality.
    simplify.
    pose proof (NatWithEquality.equal_ok k1 k2).
    cases (NatWithEquality.equal k1 k2); simplify.
    equality.
    unfold fromRange.
    rewrite Heq3.
    apply NatSet.member_empty.
    pose proof (NatWithEquality.equal_ok k1 k2).
    cases (NatWithEquality.equal k1 k2); simplify.
    equality.
    unfold fromRange.
    cases (Compare_dec.leb from to); simplify.
    apply member_fromRange'.
    apply Compare_dec.leb_complete.
    assumption.
    equality.

    pose proof (NatWithEquality.equal_ok k1 (from - 1)).
    cases (NatWithEquality.equal k1 (from - 1)); simplify.
    cases (Compare_dec.leb from to).
    apply Compare_dec.leb_complete in Heq1.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    f_equal.
    f_equal.
    cases (Compare_dec.leb k1 k2).
    apply Compare_dec.leb_complete in Heq2.
    apply Compare_dec.leb_complete_conv in Heq.
    unfold key in *.
    rewrite Compare_dec.leb_correct by linear_arithmetic.
    equality.
    apply Compare_dec.leb_complete_conv in Heq2.
    apply Compare_dec.leb_complete_conv in Heq.
    unfold key in *.
    rewrite Compare_dec.leb_correct_conv by linear_arithmetic.
    equality.
    pose proof (NatWithEquality.equal_ok k1 (to + 1)).
    cases (NatWithEquality.equal k1 (to + 1)); simplify.
    pose proof (NatWithEquality.equal_ok k1 k2).
    cases (NatWithEquality.equal k1 k2); simplify.
    unfold key in *; linear_arithmetic.
    unfold fromRange.
    rewrite Heq1.
    apply NatSet.member_empty. 
    pose proof (NatWithEquality.equal_ok k1 k2).
    cases (NatWithEquality.equal k1 k2); simplify.
    equality.
    unfold fromRange.
    rewrite Heq1.
    apply NatSet.member_empty. 
    pose proof (NatWithEquality.equal_ok k1 (to + 1)).
    cases (NatWithEquality.equal k1 (to + 1)); simplify.
    cases (Compare_dec.leb from to).
    rewrite Heq; simplify.
    apply Compare_dec.leb_complete in Heq2.
    apply Compare_dec.leb_complete_conv in Heq.
    linear_arithmetic.
    rewrite NatSet.member_add_noteq by assumption; simplify.
    unfold fromRange.
    rewrite Heq2.
    apply NatSet.member_empty. 
    pose proof (NatWithEquality.equal_ok k1 k2).
    cases (NatWithEquality.equal k1 k2); simplify.
    equality.
    unfold fromRange.
    cases (Compare_dec.leb from to); simplify.
    apply member_fromRange'.
    apply Compare_dec.leb_complete; assumption.
    equality.
    apply NatSet.member_add_noteq.
    assumption.
  Qed.

  Theorem decidable_equality : forall a b : key, a = b \/ a <> b.
  Proof.
    simplify.
    pose proof (NatWithEquality.equal_ok a b).
    cases (NatWithEquality.equal a b); propositional.
  Qed.
End NatRangeSet.

(* Time for a head-to-head performance contest between our naive and clever
 * sets! *)

Module FasterNatDuplicateFinder := FindDuplicates(NatRangeSet).

Fixpoint upto (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => n' :: upto n'
  end.

Compute upto 10.

Time Compute NatDuplicateFinder.noDuplicates (upto 1000).
Time Compute FasterNatDuplicateFinder.noDuplicates (upto 1000).
