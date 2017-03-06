Theorem factorial_ok_2 :
  invariantFor (factorial_sys 2) (fact_correct 2).
Proof.
  simplify.
  eapply invariant_weaken.
  (* We begin like in last chapter, by strengthening to an inductive
   * invariant. *)

  apply multiStepClosure_ok.
  (* The difference is that we will use multi-step closure to find the invariant
   * automatically.  Note that the invariant appears as an existential variable,
   * whose name begins with a question mark. *)
  simplify.
  rewrite fact_init_is.
  (* It's important to phrase the current candidate invariant explicitly as a
   * finite set, before continuing.  Otherwise, it won't be obvious how to take
   * the one-step closure. *)

  (* Compute which states are reachable after one step. *)
  eapply MscStep.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  (* Compute which states are reachable after two steps. *)
  eapply MscStep.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  (* Compute which states are reachable after three steps. *)
  eapply MscStep.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_split; simplify.
  invert H; simplify.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  (* Now the candidate invariatn is closed under single steps.  Let's prove
   * it. *)
  apply MscDone.
  apply prove_oneStepClosure; simplify.
  propositional.
  propositional; invert H0; try equality.
  invert H; equality.
  invert H1; equality.

  (* Finally, we prove that our new invariant implies the simpler, noninductive
   * one that we started with. *)
  simplify.
  propositional; subst; simplify; propositional.
  (* [subst]: remove all hypotheses like [x = e] for variables [x], simply
   *   replacing all uses of [x] by [e]. *)
Qed.

Theorem twoadd2_ok :
  invariantFor (parallel twoadd_sys twoadd_sys) (twoadd_correct (private := _)).
Proof.
  eapply invariant_weaken.
  eapply invariant_simulates.
  apply withInterference_abstracts.
  apply withInterference_parallel.
  apply twoadd_ok.
  apply twoadd_ok.

  unfold twoadd_correct.
  invert 1.
  assumption.
Qed.
