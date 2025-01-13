Require Import PeanoNat.

Module LateDays.
  Inductive letter : Type :=
    | A
    | B
    | C
    | D
    | F.

  Inductive modifier : Type :=
    | Plus
    | Natural
    | Minus.

  Inductive grade : Type :=
    | Grade (l : letter) (m : modifier).

  Definition letter_comparison (l1 l2 : letter) : comparison :=
    match l1, l2 with
    | A, A => Eq
    | A, _ => Gt
    | B, A => Lt
    | B, B => Eq
    | B, _ => Gt
    | C, (A | B) => Lt
    | C, C => Eq
    | C, _ => Gt
    | D, (A | B | C) => Lt
    | D, D => Eq
    | D, _ => Gt
    | F, (A | B | C | D) => Lt
    | F, F => Eq
    end.

  Theorem letter_comparison_Eq : forall l, letter_comparison l l = Eq.
  Proof.
    intros l.
    destruct l eqn:E.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
  Qed.

  Definition modifier_comparison (m1 m2 : modifier) : comparison :=
    match m1, m2 with
    | Plus, Plus => Eq
    | Plus, _ => Gt
    | Natural, Plus => Lt
    | Natural, Natural => Eq
    | Natural, _ => Gt
    | Minus, (Plus | Natural) => Lt
    | Minus, Minus => Eq
    end.

  Definition grade_comparison (l r : grade) : comparison :=
    match l, r with
    | Grade ll lm, Grade rl rm =>
      match letter_comparison ll rl with
      | Eq => modifier_comparison lm rm
      | other => other
      end
    end.

  Example test_grade_comparison1 :
    grade_comparison (Grade A Minus) (Grade B Plus) = Gt.
  Proof.
    reflexivity.
  Qed.

  Example test_grade_comparison2 :
    grade_comparison (Grade A Minus) (Grade A Plus) = Lt.
  Proof.
    reflexivity.
  Qed.

  Example test_grade_comparison3 :
    grade_comparison (Grade F Plus) (Grade F Plus) = Eq.
  Proof.
    reflexivity.
  Qed.

  Example test_grade_comparison4 :
    grade_comparison (Grade B Minus) (Grade C Plus) = Gt.
  Proof.
    reflexivity.
  Qed.

  Theorem grade_letter_cmp_works :
    forall (letter_1 letter_2 : letter) (modifier_1 modifier_2 : modifier),
      letter_comparison letter_1 letter_2 = Lt ->
      grade_comparison (Grade letter_1 modifier_1) (Grade letter_2 modifier_2) =
      Lt.
  Proof.
    intros letter_1 letter_2.
    intros mod_1 mod_2.
    intros H.
    simpl.
    rewrite -> H.
    reflexivity.
  Qed.

  Definition lower_letter (l : letter) : letter :=
    match l with
    | A => B
    | B => C
    | C => D
    | D => F
    | F => F
    end.

  Theorem lower_letter_lowers :
    forall (l : letter),
      letter_comparison F l = Lt -> letter_comparison (lower_letter l) l = Lt.
  Proof.
    intros l.
    destruct l.
      - simpl.
        reflexivity.
      - simpl.
        reflexivity.
      - simpl.
        reflexivity.
      - simpl.
        reflexivity.
      - simpl.
        intros H.
        rewrite -> H.
        reflexivity.
  Qed.

  Definition lower_grade (g : grade) : grade :=
    match g with
    | Grade letter modifier =>
      match modifier with
      | Plus => Grade letter Natural
      | Natural => Grade letter Minus
      | Minus =>
        match letter with
        | F => Grade F Minus
        | other => Grade (lower_letter other) Plus
        end
      end
    end.

  Example lower_grade_A_Plus : lower_grade (Grade A Plus) = Grade A Natural.
  Proof.
    reflexivity.
  Qed.

  Example lower_grade_A_Natural : lower_grade (Grade A Natural) = Grade A Minus.
  Proof.
    reflexivity.
  Qed.

  Example lower_grade_A_Minus : lower_grade (Grade A Minus) = Grade B Plus.
  Proof.
    reflexivity.
  Qed.

  Example lower_grade_B_Plus : lower_grade (Grade B Plus) = Grade B Natural.
  Proof.
    reflexivity.
  Qed.

  Example lower_grade_F_Natural : lower_grade (Grade F Natural) = Grade F Minus.
  Proof.
    reflexivity.
  Qed.

  Example lower_grade_twice :
    lower_grade (lower_grade (Grade B Minus)) = Grade C Natural.
  Proof.
    reflexivity.
  Qed.

  Example lower_grade_thrice :
    lower_grade (lower_grade (lower_grade (Grade B Minus))) = Grade C Minus.
  Proof.
    reflexivity.
  Qed.

  Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = Grade F Minus.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem lower_grade_lowers :
    forall (g : grade),
      grade_comparison (Grade F Minus) g = Lt ->
      grade_comparison (lower_grade g) g = Lt.
  Proof.
    intros g.
    destruct g.
    intros H.
    simpl.
    destruct m eqn:E.
      - simpl.
        rewrite -> letter_comparison_Eq.
        reflexivity.
      - simpl.
        rewrite -> letter_comparison_Eq.
        reflexivity.
      - destruct l.
          * reflexivity.
          * reflexivity.
          * reflexivity.
          * reflexivity.
          * rewrite -> H.
            reflexivity.
  Qed.

  Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
    if late_days <? 9
      then g
      else if late_days <? 17
             then lower_grade g
             else if late_days <? 21
                    then lower_grade (lower_grade g)
                    else lower_grade (lower_grade (lower_grade g)).

  Theorem apply_late_policy_unfold :
    forall (late_days : nat) (g : grade),
      apply_late_policy late_days g =
      (if late_days <? 9
         then g
         else if late_days <? 17
                then lower_grade g
                else if late_days <? 21
                       then lower_grade (lower_grade g)
                       else lower_grade (lower_grade (lower_grade g))).
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem no_penalty_for_mostly_on_time :
    forall (late_days : nat) (g : grade),
      (late_days <? 9) = true -> apply_late_policy late_days g = g.
  Proof.
    intros.
    rewrite -> apply_late_policy_unfold.
    rewrite -> H.
    reflexivity.
  Qed.

  Theorem grade_lowered_once :
    forall (late_days : nat) (g : grade),
      (late_days <? 9) = false ->
      (late_days <? 17) = true ->
      grade_comparison (Grade F Minus) g = Lt ->
      apply_late_policy late_days g = lower_grade g.
  Proof.
    intros.
    rewrite -> apply_late_policy_unfold.
    rewrite -> H.
    rewrite -> H0.
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
    | B0 n => 2 * bin_to_nat n
    | B1 n => 2 * bin_to_nat n + 1
    end.

  Example test_bin_incr1 : incr (B1 Z) = B0 (B1 Z).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_bin_incr2 : incr (B0 (B1 Z)) = B1 (B1 Z).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_bin_incr3 : incr (B1 (B1 Z)) = B0 (B0 (B1 Z)).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_bin_incr6 :
    bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
  Proof.
    reflexivity.
  Qed.
End LateDays.
