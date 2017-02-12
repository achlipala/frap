(** Formal Reasoning About Programs <http://adam.chlipala.net/frap/>
  * Chapter 3: Data Abstraction
  * Author: Adam Chlipala
  * License: https://creativecommons.org/licenses/by-nc-nd/4.0/ *)

Require Import Frap.

Set Implicit Arguments.


Module Algebraic.
  Module Type QUEUE.
    Parameter t : Set -> Set.

    Parameter empty : forall A, t A.
    Parameter enqueue : forall A, t A -> A -> t A.
    Parameter dequeue : forall A, t A -> option (t A * A).

    Axiom dequeue_empty : forall A,
        dequeue (empty A) = None.
    Axiom empty_dequeue : forall A (q : t A),
        dequeue q = None -> q = empty A.
    Axiom dequeue_enqueue : forall A (q : t A) x,
        dequeue (enqueue q x) = Some (match dequeue q with
                                      | None => (empty A, x)
                                      | Some (q', y) => (enqueue q' x, y)
                                      end).
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

  Module ReversedListQueue : QUEUE.
    Definition t : Set -> Set := list.

    Definition empty A : t A := [].
    Definition enqueue A (q : t A) (x : A) : t A := q ++ [x].
    Definition dequeue A (q : t A) : option (t A * A) :=
      match q with
      | [] => None
      | x :: q' => Some (q', x)
      end.

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

    Lemma dequeue_makeQueue : forall n q,
        Q.dequeue (makeQueue n q)
        = match Q.dequeue q with
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
      equality.
      equality.

      simplify.
      rewrite IHn.
      rewrite Q.dequeue_enqueue.
      cases (Q.dequeue q).
      cases p.
      equality.

      rewrite (Q.empty_dequeue (q := q)).
      equality.
      assumption.
    Qed.

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

Module AlgebraicWithEquivalenceRelation.
  Module Type QUEUE.
    Parameter t : Set -> Set.

    Parameter empty : forall A, t A.
    Parameter enqueue : forall A, t A -> A -> t A.
    Parameter dequeue : forall A, t A -> option (t A * A).

    Parameter equiv : forall A, t A -> t A -> Prop.

    Infix "~=" := equiv (at level 70).

    Axiom equiv_refl : forall A (a : t A), a ~= a.
    Axiom equiv_sym : forall A (a b : t A), a ~= b -> b ~= a.
    Axiom equiv_trans : forall A (a b c : t A), a ~= b -> b ~= c -> a ~= c.

    Axiom equiv_enqueue : forall A (a b : t A) (x : A),
        a ~= b
        -> enqueue a x ~= enqueue b x.

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

    Definition elements A (q : t A) : list A :=
      q.(EnqueueHere) ++ rev q.(DequeueHere).

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
      rewrite rev_app_distr in Heq1.      rewrite rev_app_distr in Heq1.
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
