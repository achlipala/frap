Require Import FrapWithoutSets SubsetTypes.

Set Implicit Arguments.
Set Asymmetric Patterns.


(** * Length-Indexed Lists *)

Section ilist.
  Variable A : Set.
  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

  Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 with
      | Nil => ls2
      | Cons _ x ls1' => Cons x (app ls1' ls2)
    end.

  Fixpoint inject (ls : list A) : ilist (length ls) :=
    match ls with
      | nil => Nil
      | h :: t => Cons h (inject t)
    end.

  Fixpoint unject n (ls : ilist n) : list A :=
    match ls with
      | Nil => nil
      | Cons _ h t => h :: unject t
    end.

  Theorem inject_inverse : forall ls, unject (inject ls) = ls.
  Proof.
    induct ls; simplify; equality.
  Qed.

  Fail Definition hd n (ls : ilist (S n)) : A :=
    match ls with
    | Nil => _
    | Cons _ h _ => h
    end.
End ilist.


(** * A Tagless Interpreter *)

Inductive type : Set :=
| Nat : type
| Bool : type
| Prod : type -> type -> type.

Inductive exp : type -> Set :=
| NConst : nat -> exp Nat
| Plus : exp Nat -> exp Nat -> exp Nat
| Eq : exp Nat -> exp Nat -> exp Bool

| BConst : bool -> exp Bool
| And : exp Bool -> exp Bool -> exp Bool
| If : forall t, exp Bool -> exp t -> exp t -> exp t

| Pair : forall t1 t2, exp t1 -> exp t2 -> exp (Prod t1 t2)
| Fst : forall t1 t2, exp (Prod t1 t2) -> exp t1
| Snd : forall t1 t2, exp (Prod t1 t2) -> exp t2.

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
    | Prod t1 t2 => typeDenote t1 * typeDenote t2
  end%type.

Fixpoint expDenote t (e : exp t) : typeDenote t :=
  match e with
    | NConst n => n
    | Plus e1 e2 => expDenote e1 + expDenote e2
    | Eq e1 e2 => if eq_nat_dec (expDenote e1) (expDenote e2) then true else false

    | BConst b => b
    | And e1 e2 => expDenote e1 && expDenote e2
    | If _ e' e1 e2 => if expDenote e' then expDenote e1 else expDenote e2

    | Pair _ _ e1 e2 => (expDenote e1, expDenote e2)
    | Fst _ _ e' => fst (expDenote e')
    | Snd _ _ e' => snd (expDenote e')
  end.

Fixpoint cfold t (e : exp t) : exp t :=
  match e with
    | NConst n => NConst n
    | Plus e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | NConst n1, NConst n2 => NConst (n1 + n2)
        | _, _ => Plus e1' e2'
      end
    | Eq e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | NConst n1, NConst n2 => BConst (if eq_nat_dec n1 n2 then true else false)
        | _, _ => Eq e1' e2'
      end

    | BConst b => BConst b
    | And e1 e2 =>
      let e1' := cfold e1 in
      let e2' := cfold e2 in
      match e1', e2' with
        | BConst b1, BConst b2 => BConst (b1 && b2)
        | _, _ => And e1' e2'
      end
    | If _ e e1 e2 =>
      let e' := cfold e in
      match e' with
        | BConst true => cfold e1
        | BConst false => cfold e2
        | _ => If e' (cfold e1) (cfold e2)
      end

    | Pair _ _ e1 e2 => Pair (cfold e1) (cfold e2)
    | Fst _ _ e => Fst e
    | Snd _ _ e => Snd e
  end.

Theorem cfold_correct : forall t (e : exp t), expDenote e = expDenote (cfold e).
Proof.

























Admitted.
  (*induct e; simplify;
    repeat (match goal with
              | [ |- context[match cfold ?E with NConst _ => _ | _ => _ end] ] =>
                dep_cases (cfold E)
              | [ |- context[match pairOut (cfold ?E) with Some _ => _
                               | None => _ end] ] =>
                dep_cases (cfold E)
              | [ |- context[if ?E then _ else _] ] => cases E
              | [ H : _ = _ |- _ ] => rewrite H
            end; simplify); try equality.
Qed.*)


(** * Interlude: The Convoy Pattern *)

Fail Definition firstElements n A B (ls1 : ilist A n) (ls2 : ilist B n) : option (A * B) :=
  match ls1 with
  | Cons _ v1 _ =>
    Some (v1,
          match ls2 in ilist _ N return match N with O => unit | S _ => B end with
          | Cons _ v2 _ => v2
          | Nil => tt
          end)
  | Nil => None
  end.

Fail Fixpoint zip n A B (ls1 : ilist A n) (ls2 : ilist B n) {struct ls1} : ilist (A * B) n :=
  match ls1 in ilist _ N return ilist B N -> ilist (A * B) N with
  | Cons _ v1 ls1' => 
    fun ls2 =>
      match ls2 in ilist _ N return match N with
                                    | O => unit
                                    | S N' => ilist A N' -> ilist (A * B) N
                                    end with
      | Cons _ v2 ls2' => fun ls1' => Cons (v1, v2) (zip ls1' ls2')
      | Nll => tt
      end ls1'
  | Nil => fun _ => Nil _
  end ls2.


(** * Dependently Typed Red-Black Trees *)

Inductive color : Set := Red | Black.

Inductive rbtree : color -> nat -> Set :=
| Leaf : rbtree Black 0
| RedNode : forall n, rbtree Black n -> nat -> rbtree Black n -> rbtree Red n
| BlackNode : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rbtree Black (S n).

Section depth.
  Variable f : nat -> nat -> nat.

  Fixpoint depth c n (t : rbtree c n) : nat :=
    match t with
      | Leaf => 0
      | RedNode _ t1 _ t2 => S (f (depth t1) (depth t2))
      | BlackNode _ _ _ t1 _ t2 => S (f (depth t1) (depth t2))
    end.
End depth.

Theorem depth_min : forall c n (t : rbtree c n), depth min t >= 0.
Proof.
Admitted.

Theorem depth_max : forall c n (t : rbtree c n), depth max t <= 0.
Proof.
Admitted.

Theorem balanced : forall c n (t : rbtree c n), t = t.
Proof.
Admitted.

Inductive rtree : nat -> Set :=
| RedNode' : forall c1 c2 n, rbtree c1 n -> nat -> rbtree c2 n -> rtree n.

Section present.
  Variable x : nat.

  Fixpoint present c n (t : rbtree c n) : Prop :=
    match t with
      | Leaf => False
      | RedNode _ a y b => present a \/ x = y \/ present b
      | BlackNode _ _ _ a y b => present a \/ x = y \/ present b
    end.

  Definition rpresent n (t : rtree n) : Prop :=
    match t with
      | RedNode' _ _ _ a y b => present a \/ x = y \/ present b
    end.
End present.

Locate "{ _ : _ & _ }".
Print sigT.

Notation "{< x >}" := (existT _ _ x).

Definition balance1 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n
    -> { c : color & rbtree c (S n) } with
    | RedNode' _ c0 _ t1 y t2 =>
      match t1 in rbtree c n return rbtree c0 n -> rbtree c2 n
        -> { c : color & rbtree c (S n) } with
        | RedNode _ a x b => fun c d =>
          {<RedNode (BlackNode a x b) y (BlackNode c data d)>}
        | t1' => fun t2 =>
          match t2 in rbtree c n return rbtree Black n -> rbtree c2 n
            -> { c : color & rbtree c (S n) } with
            | RedNode _ b x c => fun a d =>
              {<RedNode (BlackNode a y b) x (BlackNode c data d)>}
            | b => fun a t => {<BlackNode (RedNode a y b) data t>}
          end t1'
      end t2
  end.

Definition balance2 n (a : rtree n) (data : nat) c2 :=
  match a in rtree n return rbtree c2 n -> { c : color & rbtree c (S n) } with
    | RedNode' _ c0 _ t1 z t2 =>
      match t1 in rbtree c n return rbtree c0 n -> rbtree c2 n
        -> { c : color & rbtree c (S n) } with
        | RedNode _ b y c => fun d a =>
          {<RedNode (BlackNode a data b) y (BlackNode c z d)>}
        | t1' => fun t2 =>
          match t2 in rbtree c n return rbtree Black n -> rbtree c2 n
            -> { c : color & rbtree c (S n) } with
            | RedNode _ c z' d => fun b a =>
              {<RedNode (BlackNode a data b) z (BlackNode c z' d)>}
            | b => fun a t => {<BlackNode t data (RedNode a z b)>}
          end t1'
      end t2
  end.

Section insert.
  Variable x : nat.

  Definition insResult c n :=
    match c with
      | Red => rtree n
      | Black => { c' : color & rbtree c' n }
    end.

  Fixpoint ins c n (t : rbtree c n) : insResult c n :=
    match t with
      | Leaf => {< RedNode Leaf x Leaf >}
      | RedNode _ a y b =>
        if le_lt_dec x y
          then RedNode' (projT2 (ins a)) y b
          else RedNode' a y (projT2 (ins b))
      | BlackNode c1 c2 _ a y b =>
        if le_lt_dec x y
          then
            match c1 return insResult c1 _ -> _ with
              | Red => fun ins_a => balance1 ins_a y b
              | _ => fun ins_a => {< BlackNode (projT2 ins_a) y b >}
            end (ins a)
          else
            match c2 return insResult c2 _ -> _ with
              | Red => fun ins_b => balance2 ins_b y a
              | _ => fun ins_b => {< BlackNode a y (projT2 ins_b) >}
            end (ins b)
    end.

  Definition insertResult c n :=
    match c with
      | Red => rbtree Black (S n)
      | Black => { c' : color & rbtree c' n }
    end.

  Definition makeRbtree {c n} : insResult c n -> insertResult c n :=
    match c with
      | Red => fun r =>
        match r with
          | RedNode' _ _ _ a x b => BlackNode a x b
        end
      | Black => fun r => r
    end.

  Definition insert c n (t : rbtree c n) : insertResult c n :=
    makeRbtree (ins t).

  Section present.
    Variable z : nat.

    Ltac present_balance :=
      simplify;
      repeat (match goal with
                | [ _ : context[match ?T with Leaf => _ | _ => _ end] |- _ ] =>
                  dep_cases T
                | [ |- context[match ?T with Leaf => _ | _ => _ end] ] => dep_cases T
              end; simplify); propositional.

    Lemma present_balance1 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
      present z (projT2 (balance1 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
    Proof.
      simplify; cases a; present_balance.
    Qed.

    Lemma present_balance2 : forall n (a : rtree n) (y : nat) c2 (b : rbtree c2 n),
      present z (projT2 (balance2 a y b))
      <-> rpresent z a \/ z = y \/ present z b.
    Proof.
      simplify; cases a; present_balance.
    Qed.

    Definition present_insResult c n :=
      match c return (rbtree c n -> insResult c n -> Prop) with
        | Red => fun t r => rpresent z r <-> z = x \/ present z t
        | Black => fun t r => present z (projT2 r) <-> z = x \/ present z t
      end.

    Theorem present_ins : forall c n (t : rbtree c n),
      present_insResult t (ins t).
    Proof.
      induct t; simplify;
        repeat (match goal with
                  | [ _ : context[if ?E then _ else _] |- _ ] => cases E
                  | [ |- context[if ?E then _ else _] ] => cases E
                  | [ _ : context[match ?C with Red => _ | Black => _ end]
                      |- _ ] => cases C
                end; simplify);
        try match goal with
              | [ _ : context[balance1 ?A ?B ?C] |- _ ] =>
                pose proof (present_balance1 A B C)
            end;
        try match goal with
              | [ _ : context[balance2 ?A ?B ?C] |- _ ] =>
                pose proof (present_balance2 A B C)
            end;
        try match goal with
              | [ |- context[balance1 ?A ?B ?C] ] =>
                pose proof (present_balance1 A B C)
            end;
        try match goal with
              | [ |- context[balance2 ?A ?B ?C] ] =>
                pose proof (present_balance2 A B C)
            end;
        simplify; propositional.
    Qed.

    Ltac present_insert :=
      unfold insert; intros n t;
        pose proof (present_ins t); simplify;
          cases (ins t); propositional.

    Theorem present_insert_Red : forall n (t : rbtree Red n),
      present z (insert t)
      <-> (z = x \/ present z t).
    Proof.
      present_insert.
    Qed.

    Theorem present_insert_Black : forall n (t : rbtree Black n),
      present z (projT2 (insert t))
      <-> (z = x \/ present z t).
    Proof.
      present_insert.
    Qed.
  End present.
End insert.

Recursive Extraction insert.


(** * A Certified Regular Expression Matcher *)

Require Import Ascii String.
Open Scope string_scope.

Section star.
  Variable P : string -> Prop.

  Inductive star : string -> Prop :=
  | Empty : star ""
  | Iter : forall s1 s2,
    P s1
    -> star s2
    -> star (s1 ++ s2).
End star.

Fail Inductive regexp : (string -> Prop) -> Set :=
| Char : forall ch : ascii,
  regexp (fun s => s = String ch "")
| Concat : forall (P1 P2 : string -> Prop) (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2).



















Inductive regexp : (string -> Prop) -> Type :=
| Char : forall ch : ascii,
  regexp (fun s => s = String ch "")
| Concat : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2)
| Or : forall P1 P2 (r1 : regexp P1) (r2 : regexp P2),
  regexp (fun s => P1 s \/ P2 s)
| Star : forall P (r : regexp P),
  regexp (star P).

(* Many theorems about strings are useful for implementing a certified regexp
 * matcher, and few of them are in the [String] library.  Here they are.  Feel
 * free to resume reading at "BOREDOM'S END". *)

Lemma length_emp : length "" <= 0.
Proof.
  auto.
Qed.

Lemma append_emp : forall s, s = "" ++ s.
Proof.
  auto.
Qed.

Ltac substring :=
  simplify;
  repeat match goal with
           | [ |- context[match ?N with O => _ | S _ => _ end] ] =>
             destruct N; simplify
         end; try linear_arithmetic; eauto; try equality.

Local Hint Resolve le_n_S : core.

Lemma substring_le : forall s n m,
  length (substring n m s) <= m.
Proof.
  induct s; substring.
Qed.

Lemma substring_all : forall s,
  substring 0 (length s) s = s.
Proof.
  induct s; substring.
Qed.

Lemma substring_none : forall s n,
  substring n 0 s = "".
Proof.
  induct s; substring.
Qed.

Local Hint Rewrite substring_all substring_none.

Lemma substring_split : forall s m,
  substring 0 m s ++ substring m (length s - m) s = s.
Proof.
  induct s; substring.
Qed.

Lemma length_app1 : forall s1 s2,
  length s1 <= length (s1 ++ s2).
Proof.
  induct s1; substring.
Qed.

Local Hint Resolve length_emp append_emp substring_le substring_split length_app1 : core.

Lemma substring_app_fst : forall s2 s1 n,
  length s1 = n
  -> substring 0 n (s1 ++ s2) = s1.
Proof.
  induct s1; simplify; subst; simplify; try equality.
  rewrite IHs1; auto.
Qed.

Local Hint Rewrite <- minus_n_O.

Lemma substring_app_snd : forall s2 s1 n,
  length s1 = n
  -> substring n (length (s1 ++ s2) - n) (s1 ++ s2) = s2.
Proof.
  induct s1; simplify; subst; simplify; auto.
Qed.

Local Hint Rewrite substring_app_fst substring_app_snd using solve [trivial].

(* BOREDOM'S END! *)

Section sumbool_and.
  Variables P1 Q1 P2 Q2 : Prop.

  Variable x1 : {P1} + {Q1}.
  Variable x2 : {P2} + {Q2}.

  Definition sumbool_and : {P1 /\ P2} + {Q1 \/ Q2} :=
    match x1 with
      | left HP1 =>
        match x2 with
          | left HP2 => left _ (conj HP1 HP2)
          | right HQ2 => right _ (or_intror _ HQ2)
        end
      | right HQ1 => right _ (or_introl _ HQ1)
    end.
End sumbool_and.

Infix "&&" := sumbool_and (at level 40, left associativity).

Local Hint Extern 1 (_ <= _) => linear_arithmetic : core.

Section split.
  Variables P1 P2 : string -> Prop.
  Variable P1_dec : forall s, {P1 s} + {~ P1 s}.
  Variable P2_dec : forall s, {P2 s} + {~ P2 s}.

  Variable s : string.

  Definition split' : forall n : nat, n <= length s
    -> {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2}
    + {forall s1 s2, length s1 <= n -> s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2}.
    refine (fix F (n : nat) : n <= length s
      -> {exists s1, exists s2, length s1 <= n /\ s1 ++ s2 = s /\ P1 s1 /\ P2 s2}
      + {forall s1 s2, length s1 <= n -> s1 ++ s2 = s -> ~ P1 s1 \/ ~ P2 s2} :=
      match n with
        | O => fun _ => Reduce (P1_dec "" && P2_dec s)
        | S n' => fun _ => (P1_dec (substring 0 (S n') s)
            && P2_dec (substring (S n') (length s - S n') s))
          || F n' _
      end); clear F; simplify;
      repeat match goal with
             | [ H : exists x, _ |- _ ] => invert H
             end; propositional; eauto 7;
      try match goal with
          | [ _ : length ?S <= 0 |- _ ] => cases S; simplify
          | [ _ : length ?S' <= S ?N |- _ ] => cases (length S' ==n S N)
          end; subst; simplify; try equality; try linear_arithmetic; eauto.
  Defined.

  Definition split : {exists s1, exists s2, s = s1 ++ s2 /\ P1 s1 /\ P2 s2}
    + {forall s1 s2, s = s1 ++ s2 -> ~ P1 s1 \/ ~ P2 s2}.
    refine (Reduce (split' (n := length s) _)); simplify; auto; first_order; subst; eauto.
  Defined.
End split.

Arguments split {P1 P2}.

(* And now, a few more boring lemmas.  Rejoin at "BOREDOM VANQUISHED", if you
 * like. *)

Lemma app_empty_end : forall s, s ++ "" = s.
Proof.
  induct s; substring.
Qed.

Local Hint Rewrite app_empty_end.

Lemma substring_self : forall s n,
  n <= 0
  -> substring n (length s - n) s = s.
Proof.
  induct s; substring.
Qed.

Lemma substring_empty : forall s n m,
  m <= 0
  -> substring n m s = "".
Proof.
  induct s; substring.
Qed.

Local Hint Rewrite substring_self substring_empty using linear_arithmetic.
Local Hint Rewrite substring_split.

Lemma substring_split' : forall s n m,
  substring n m s ++ substring (n + m) (length s - (n + m)) s
  = substring n (length s - n) s.
Proof.
  induct s; substring.
Qed.

Local Hint Extern 1 (String _ _ = String _ _) => f_equal : core.

Lemma substring_stack : forall s n2 m1 m2,
  m1 <= m2
  -> substring 0 m1 (substring n2 m2 s)
  = substring n2 m1 s.
Proof.
  induct s; substring.
Qed.

Ltac substring' :=
  simplify;
  repeat match goal with
           | [ |- context[match ?N with O => _ | S _ => _ end] ] => cases N; simplify
         end; try equality; try linear_arithmetic.

Lemma substring_stack' : forall s n1 n2 m1 m2,
  n1 + m1 <= m2
  -> substring n1 m1 (substring n2 m2 s)
  = substring (n1 + n2) m1 s.
Proof.
  induct s; substring';
    match goal with
    | [ H : _ |- _ ] => rewrite H by linear_arithmetic; f_equal; linear_arithmetic
    end.
Qed.

Lemma substring_suffix : forall s n,
  n <= length s
  -> length (substring n (length s - n) s) = length s - n.
Proof.
  induct s; substring.
Qed.

Lemma substring_suffix_emp' : forall s n m,
  substring n (S m) s = ""
  -> n >= length s.
Proof.
  induct s; simplify; auto;
    match goal with
      | [ |- ?N >= _ ] => cases N; simplify; try equality
    end;
    match goal with
      [ |- S ?N >= S ?E ] => assert (N >= E) by eauto; linear_arithmetic
    end.
Qed.

Lemma substring_suffix_emp : forall s n m,
  substring n m s = ""
  -> m > 0
  -> n >= length s.
Proof.
  simplify; cases m; simplify; eauto using substring_suffix_emp'.
Qed.

Local Hint Rewrite substring_stack substring_stack' substring_suffix using linear_arithmetic.

Lemma minus_minus : forall n m1 m2,
  m1 + m2 <= n
  -> n - m1 - m2 = n - (m1 + m2).
Proof.
  linear_arithmetic.
Qed.

Lemma plus_n_Sm' : forall n m : nat, S (n + m) = m + S n.
Proof.
  linear_arithmetic.
Qed.

Local Hint Rewrite minus_minus plus_n_Sm' using linear_arithmetic.

(* BOREDOM VANQUISHED! *)

Section dec_star.
  Variable P : string -> Prop.
  Variable P_dec : forall s, {P s} + {~ P s}.

  (* Some new lemmas and hints about the [star] type family are useful.  Rejoin
   * at BOREDOM DEMOLISHED to skip the details. *)

  Hint Constructors star : core.

  Lemma star_empty : forall s,
    length s = 0
    -> star P s.
  Proof.
    simplify; cases s; simplify; try equality; eauto.
  Qed.

  Lemma star_singleton : forall s, P s -> star P s.
  Proof.
    simplify.
    rewrite <- (app_empty_end s); auto.
  Qed.

  Lemma star_app : forall s n m,
    P (substring n m s)
    -> star P (substring (n + m) (length s - (n + m)) s)
    -> star P (substring n (length s - n) s).
  Proof.
    induct n; substring;
      match goal with
        | [ H : P (substring ?N ?M ?S) |- _ ] =>
          solve [ rewrite <- (substring_split S M); auto
            | rewrite <- (substring_split' S N M); simplify; auto ]
      end.
  Qed.

  Hint Resolve star_empty star_singleton star_app : core.

  Variable s : string.

  Hint Extern 1 (exists i : nat, _) =>
    match goal with
    | [ H : P (String _ ?S) |- _ ] => exists (length S); simplify
    end : core.

  Lemma star_inv : forall s,
    star P s
    -> s = ""
    \/ exists i, i < length s
      /\ P (substring 0 (S i) s)
      /\ star P (substring (S i) (length s - S i) s).
  Proof.
    induct 1; simplify; first_order; subst.
    cases s1; simplify; propositional; eauto 10.
    cases s1; simplify; propositional; eauto 10.
  Qed.

  Lemma star_substring_inv : forall n,
    n <= length s
    -> star P (substring n (length s - n) s)
    -> substring n (length s - n) s = ""
    \/ exists l, l < length s - n
      /\ P (substring n (S l) s)
      /\ star P (substring (n + S l) (length s - (n + S l)) s).
  Proof.
    simplify;
      match goal with
        | [ H : star _ _ |- _ ] => pose proof (star_inv H); simplify;
                                     first_order; simplify; eauto
      end.
  Qed.

  (* BOREDOM DEMOLISHED! *)

  Section dec_star''.
    Variable n : nat.

    Variable P' : string -> Prop.
    Variable P'_dec : forall n' : nat, n' > n
      -> {P' (substring n' (length s - n') s)}
      + {~ P' (substring n' (length s - n') s)}.

    Hint Extern 1 (_ \/ _) => linear_arithmetic : core.

    Definition dec_star'' : forall l : nat,
      {exists l', S l' <= l
        /\ P (substring n (S l') s) /\ P' (substring (n + S l') (length s - (n + S l')) s)}
      + {forall l', S l' <= l
        -> ~ P (substring n (S l') s)
        \/ ~ P' (substring (n + S l') (length s - (n + S l')) s)}.
      refine (fix F (l : nat) : {exists l', S l' <= l
          /\ P (substring n (S l') s) /\ P' (substring (n + S l') (length s - (n + S l')) s)}
        + {forall l', S l' <= l
          -> ~ P (substring n (S l') s)
          \/ ~ P' (substring (n + S l') (length s - (n + S l')) s)} :=
        match l with
          | O => _
          | S l' =>
            (P_dec (substring n (S l') s) && P'_dec (n' := n + S l') _)
            || F l'
        end); clear F; simplify; first_order; eauto 7;
        match goal with
        | [ H : ?X <= S ?Y |- _ ] => destruct (eq_nat_dec X (S Y)); simplify; eauto; equality
        end.
    Defined.
  End dec_star''.

  Lemma star_length_contra : forall n,
    length s > n
    -> n >= length s
    -> False.
  Proof.
    linear_arithmetic.
  Qed.

  Lemma star_length_flip : forall n n',
    length s - n <= S n'
    -> length s > n
    -> length s - n > 0.
  Proof.
    linear_arithmetic.
  Qed.

  Hint Resolve star_length_contra star_length_flip substring_suffix_emp : core.

  Definition dec_star' : forall n n' : nat, length s - n' <= n
    -> {star P (substring n' (length s - n') s)}
    + {~ star P (substring n' (length s - n') s)}.
    refine (fix F (n n' : nat) : length s - n' <= n
      -> {star P (substring n' (length s - n') s)}
      + {~ star P (substring n' (length s - n') s)} :=
      match n with
        | O => fun _ => Yes
        | S n'' => fun _ =>
          le_gt_dec (length s) n'
          || dec_star'' (n := n') (star P)
            (fun n0 _ => Reduce (F n'' n0 _)) (length s - n')
      end); clear F; simplify; first_order; propositional; eauto;
    match goal with
      | [ H : star _ _ |- _ ] => apply star_substring_inv in H; simplify; eauto
    end; first_order; eauto.
  Defined.

  Definition dec_star : {star P s} + {~ star P s}.
    refine (Reduce (dec_star' (n := length s) 0 _)); simplify; auto.
  Defined.
End dec_star.

Lemma app_cong : forall x1 y1 x2 y2,
  x1 = x2
  -> y1 = y2
  -> x1 ++ y1 = x2 ++ y2.
Proof.
  equality.
Qed.

Local Hint Resolve app_cong : core.

Definition matches : forall P (r : regexp P) s, {P s} + {~ P s}.
  refine (fix F P (r : regexp P) s : {P s} + {~ P s} :=
    match r with
      | Char ch => string_dec s (String ch "")
      | Concat _ _ r1 r2 => Reduce (split (F _ r1) (F _ r2) s)
      | Or _ _ r1 r2 => F _ r1 s || F _ r2 s
      | Star _ r => dec_star _ _ _
    end); simplify; first_order.
Defined.

Definition toBool A B (x : {A} + {B}) :=
  if x then true else false.

Example hi := Concat (Char "h"%char) (Char "i"%char).
Compute toBool (matches hi "hi").
Compute toBool (matches hi "bye").

Example a_b := Or (Char "a"%char) (Char "b"%char).
Compute toBool (matches a_b "").
Compute toBool (matches a_b "a").
Compute toBool (matches a_b "aa").
Compute toBool (matches a_b "b").

Example a_star := Star (Char "a"%char).
Compute toBool (matches a_star "").
Compute toBool (matches a_star "a").
Compute toBool (matches a_star "b").
Compute toBool (matches a_star "aa").
