Require Import PeanoNat.

Set Printing Parentheses.

Theorem add_0_r : forall (n : nat), n + 0 = n.
Proof.
  intros n.
  induction n as [ | n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
Qed.

Theorem mul_0_r : forall (n : nat), n * 0 = 0.
Proof.
  induction n as [ | n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
Qed.

Theorem plus_n_Sm : forall (n m : nat), S (n + m) = n + S m.
Proof.
  intros.
  induction n as [ | n' IHn'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite <- IHn'.
      reflexivity.
Qed.

Theorem add_comm : forall (n m : nat), n + m = m + n.
Proof.
  intros.
  induction n as [ | n' IHn'].
    - simpl.
      rewrite -> add_0_r.
      reflexivity.
    - simpl.
      rewrite -> IHn'.
      rewrite -> plus_n_Sm.
      reflexivity.
Qed.

Theorem add_assoc : forall (n m p : nat), n + (m + p) = n + m + p.
Proof.
  intros.
  induction n as [ | n' IHn'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite <- IHn'.
      reflexivity.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | S n' => S (S (double n'))
  | O => O
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros.
  induction n as [ | n' IHn'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite -> IHn'.
      rewrite -> plus_n_Sm.
      reflexivity.
Qed.

Theorem eqb_refl : forall (n : nat), (n =? n) = true.
Proof.
  intros.
  induction n.
    - simpl.
      reflexivity.
    - simpl.
      rewrite -> IHn.
      reflexivity.
Qed.

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S n' => negb (even n')
  end.

Theorem even_S : forall (n : nat), even (S n) = negb (even n).
Proof.
  intros.
  induction n as [ | n' IHn'].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
Qed.

Theorem mult_0_plus' : forall (n m : nat), (n + 0 + 0) * m = n * m.
Proof.
  intros.
  assert (H : n + 0 + 0 = n).
  {
    induction n as [ | n' IHn'].
    {
      simpl.
      reflexivity.
    }
    {
      simpl.
      rewrite -> IHn'.
      reflexivity.
    }
  }
  rewrite -> H.
  reflexivity.
Qed.

Theorem add_shuffle3 : forall (n m p : nat), n + (m + p) = m + (n + p).
Proof.
  intros.
  induction p as [ | p' IHp'].
    - rewrite -> add_0_r.
      rewrite -> add_0_r.
      rewrite -> add_comm.
      reflexivity.
    - rewrite <- plus_n_Sm.
      rewrite <- plus_n_Sm.
      rewrite <- plus_n_Sm.
      rewrite <- plus_n_Sm.
      rewrite -> IHp'.
      reflexivity.
Qed.

Theorem add_shuffle3' : forall (n m p : nat), n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> add_assoc.
  assert (H : n + m = m + n).
  {
    rewrite -> add_comm.
    reflexivity.
  }
  rewrite -> H.
  rewrite -> add_assoc.
  reflexivity.
Qed.

Lemma add3_swap_2_3 : forall (n m k : nat), n + m + k = n + k + m.
Proof.
  intros.
  assert (H : m + k = k + m).
  {
    rewrite -> add_comm.
    reflexivity.
  }
  rewrite <- add_assoc.
  rewrite -> H.
  rewrite -> add_assoc.
  reflexivity.
Qed.

Theorem mul_distr : forall (n m p : nat), n * (m + p) = n * m + n * p.
Proof.
  intros.
  induction n.
    - reflexivity.
    - simpl.
      rewrite -> IHn.
      rewrite -> add_assoc.
      rewrite -> add_assoc.
      assert (H : forall x, m + x + p = m + p + x).
      {
        intros.
        assert (test : x + p = p + x).
        {
          rewrite -> add_comm.
          reflexivity.
        }
        rewrite <- add_assoc.
        rewrite -> test.
        rewrite -> add_assoc.
        reflexivity.
      }
      rewrite -> H.
      reflexivity.
Qed.

Theorem mul_1_r : forall (m : nat), m * 1 = m.
Proof.
  intros.
  induction m as [ | m' IHm'].
    * reflexivity.
    * simpl.
      rewrite -> IHm'.
      reflexivity.
Qed.

Theorem mul_comm : forall (m n : nat), m * n = n * m.
Proof.
  intros.
  induction n as [ | n' IHn'].
    - rewrite -> mul_0_r.
      reflexivity.
    - simpl.
      rewrite <- IHn'.
      assert (H : m * S n' = m * (1 + n')).
      {
        reflexivity.
      }
      rewrite -> H.
      rewrite -> mul_distr.
      rewrite -> mul_1_r.
      reflexivity.
Qed.

Theorem mul_comm' : forall (m n : nat), m * n = n * m.
Proof.
  intros.
  induction m as [ | m' IHm'].
    * simpl.
      rewrite -> mul_0_r.
      reflexivity.
    * simpl.
      assert (H : n * S m' = n * (1 + m')).
      {
        simpl.
        reflexivity.
      }
      rewrite -> H.
      rewrite -> mul_distr.
      rewrite -> mul_1_r.
      rewrite -> IHm'.
      reflexivity.
Qed.

Theorem plus_leb_compat_l :
  forall (n m p : nat), (n <=? m) = true -> (p + n <=? p + m) = true.
Proof.
  intros.
  induction p as [ | p' IHp'].
    - simpl.
      rewrite -> H.
      reflexivity.
    - simpl.
      rewrite -> IHp'.
      reflexivity.
Qed.

Theorem leb_refl : forall (n : nat), (n <=? n) = true.
Proof.
  intros.
  induction n as [ | n' IHn'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite -> IHn'.
      reflexivity.
Qed.

Theorem zero_neqb_S : forall (n : nat), (0 =? S n) = false.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem andb_false_r : forall (b : bool), andb b false = false.
Proof.
  intros.
  assert (H : forall x y,
    andb x y =
    match y with
    | true => x
    | false => false
    end).
  {
    intros.
    destruct x, y.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
  }
  rewrite -> H.
  reflexivity.
Qed.

Theorem S_neqb_0 : forall (n : nat), (S n =? 0) = false.
Proof.
  intros.
  reflexivity.
Qed.

Theorem mult_1_l : forall (n : nat), 1 * n = n.
Proof.
  intros.
  simpl.
  rewrite -> add_comm.
  simpl.
  reflexivity.
Qed.

Theorem all3_spec :
  forall (b c : bool), orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros.
  destruct b.
    - simpl.
      destruct c.
        * reflexivity.
        * reflexivity.
    - simpl.
      reflexivity.
Qed.

Lemma add3_shuffle_2_3 : forall (n m k : nat), n + m + k = n + k + m.
Proof.
  intros.
  rewrite <- add_assoc.
  rewrite -> add_comm.
  assert (H : m + k = k + m).
  {
    rewrite -> add_comm.
    reflexivity.
  }
  rewrite -> H.
  rewrite -> add_comm.
  rewrite -> add_assoc.
  reflexivity.
Qed.

Theorem mult_plus_distr_r : forall (n m p : nat), (n + m) * p = n * p + m * p.
Proof.
  intros.
  induction p as [ | p' AHp'].
    - rewrite -> mul_0_r.
      rewrite -> mul_0_r.
      rewrite -> mul_0_r.
      reflexivity.
    - simpl.
      rewrite -> mul_comm.
      simpl.
      rewrite -> mul_comm.
      rewrite -> AHp'.
      rewrite -> add_assoc.
      simpl.
      assert (H0 : n * S p' = S p' * n).
      {
        rewrite -> mul_comm.
        reflexivity.
      }
      rewrite -> H0.
      assert (H1 : m * S p' = S p' * m).
      {
        rewrite -> mul_comm.
        reflexivity.
      }
      rewrite -> H1.
      simpl.
      assert (H2 : n + p' * n + (m + p' * m) = n + p' * n + (m + p' * m)).
      {
        reflexivity.
      }
      assert (Q : n + p' * n + (m + p' * m) = n + m + p' * n + p' * m).
      {
        rewrite -> add3_shuffle_2_3.
        rewrite -> add_assoc.
        rewrite -> add3_shuffle_2_3.
        reflexivity.
      }
      rewrite -> Q.
      rewrite -> mul_comm.
      assert (Q1 : m * p' = p' * m).
      {
        rewrite -> mul_comm.
        reflexivity.
      }
      rewrite -> Q1.
      reflexivity.
Qed.

Theorem mult_assoc : forall (n m p : nat), n * (m * p) = n * m * p.
Proof.
  intros.
  induction n as [ | n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> IHn'.
      rewrite -> mult_plus_distr_r.
      reflexivity.
Qed.

Theorem add_shuffle3'' : forall (n m p : nat), n + (m + p) = m + (n + p).
Proof.
  intros.
  rewrite -> add_assoc.
  replace (n + m) with (m + n).
    - rewrite <- add_assoc.
      reflexivity.
    - rewrite -> add_comm.
      reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => 0
  | B0 n => double (bin_to_nat n)
  | B1 n => 1 + double (bin_to_nat n)
  end.

Theorem bin_to_nat_pres_incr :
  forall (b : bin), bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros.
  induction b.
    - reflexivity.
    - reflexivity.
    - simpl.
      rewrite -> IHb.
      simpl.
      reflexivity.
Qed.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z
  | S k => incr (nat_to_bin k)
  end.

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros.
  induction n as [ | n' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> bin_to_nat_pres_incr.
      rewrite -> IHn'.
      reflexivity.
Qed.

Lemma double_incr : forall (n : nat), double (S n) = S (S (double n)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Definition double_bin (b : bin) : bin :=
  match b with
  | Z => Z
  | B0 n => B0 (B0 n)
  | B1 n => B0 (B1 n)
  end.

Theorem double_bin_def: forall b: bin, double_bin b = 
  match b with
  | Z => Z
  | B0 n => B0 (B0 n)
  | B1 n => B0 (B1 n)
  end.
Proof.
  simpl.
  reflexivity.
Qed.

Example double_bin_zero : double_bin Z = Z.
Proof.
  reflexivity.
Qed.

Lemma double_incr_bin :
  forall b, double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  destruct b.
    - reflexivity.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
Qed.

Fixpoint normalize (b : bin) : bin :=
  match b with
  | Z => Z
  | B0 b' =>
    match normalize b' with
    | Z => Z
    | other => double_bin other
    end
  | B1 b => B1 (normalize b)
  end.

Example normalize_trimms_zeros : normalize (B1 (B0 (B0 (B0 Z)))) = B1 Z.
Proof.
  simpl.
  reflexivity.
Qed.

Example normalize_preserves_zeros :
  normalize (B1 (B0 (B0 (B1 Z)))) = B1 (B0 (B0 (B1 Z))).
Proof.
  reflexivity.
Qed.

Example normalize_zero : normalize (B0 (B0 Z)) = Z.
Proof.
  reflexivity.
Qed.

Lemma double_Sn : forall (n : nat), double (S n) = S (S (double n)).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma Sn_to_bin : forall (n : nat), nat_to_bin (S n) = incr (nat_to_bin n).
Proof.
  reflexivity.
Qed.

Lemma double_preserved_after_nat_to_bin :
  forall n, nat_to_bin (double n) = double_bin (nat_to_bin n).
Proof.
  induction n.
    * reflexivity.
    * simpl.
      rewrite -> IHn.
      assert (H : forall (m : bin),
        double_bin (incr m) = incr (incr (double_bin m))).
      {
        intros.
        destruct m.
          * reflexivity.
          * reflexivity.
          * reflexivity.
      }
      rewrite -> H.
      reflexivity.
Qed.

Lemma incr_double_bin: forall b : bin, incr (double_bin b) = B1 b.
Proof.
  intros.
  destruct b.
  * reflexivity.
  * reflexivity.
  * reflexivity.
Qed.
    

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros.
  induction b.
    - simpl.
      reflexivity.
    - simpl.
      rewrite double_preserved_after_nat_to_bin.
      rewrite IHb.
      rewrite double_bin_def.
      reflexivity.
    - simpl.
      rewrite double_preserved_after_nat_to_bin.
      rewrite incr_double_bin.
      rewrite IHb.
      reflexivity.
Qed.
