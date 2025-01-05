Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).
End NatPlayground.

Check (S O).

Fixpoint odd (n : nat) : bool :=
  match n with
  | O => false
  | S O => true
  | S (S n) => odd n
  end.

Compute (odd 3).

Module NatPlayground2.
  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S k => S (plus k m)
    end.

  Example test_plus : plus 1 2 = 3.
  Proof.
    simpl.
    reflexivity.
  Qed.
End NatPlayground2.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S O => S O
  | S k => mult n (factorial k)
  end.

Example test_factorial : factorial 3 = 6.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem plus_0 : forall (n : nat), 0 + n = n.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Theorem plus_id : forall (n m : nat), n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_ex : forall (n m o : nat), n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H.
  intros H'.
  rewrite -> H.
  rewrite -> H'.
  reflexivity.
Qed.

Theorem mult_n_1 : forall (p : nat), p * S O = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match (n, m) with
  | (S k, S q) => eqb k q
  | (O, O) => true
  | _ => false
  end.

Theorem plus_1_neq_0 : forall (n : nat), eqb (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [ | n'] eqn:E.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
Qed.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Theorem andb_true_elim2 : forall (b c : bool), andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b eqn:E.
    - simpl.
      intros H.
      rewrite -> H.
      reflexivity.
    - simpl.
      intros H.
      destruct c.
        * reflexivity.
        * rewrite -> H.
          reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = negb x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H.
  intros b.
  rewrite -> H.
  rewrite -> H.
  destruct b.
    - reflexivity.
    - reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c : bool), andb b c = orb b c -> b = c.
Proof.
  intros b c.
  destruct b eqn:B, c eqn:C.
    - simpl.
      reflexivity.
    - simpl.
      intros H.
      rewrite -> H.
      reflexivity.
    - simpl.
      intros H.
      rewrite -> H.
      reflexivity.
    - simpl.
      reflexivity.
Qed.


