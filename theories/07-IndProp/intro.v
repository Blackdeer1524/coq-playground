Require Import List PeanoNat.

From Coq Require Import Unicode.Utf8.

Import ListNotations.

Set Printing Parentheses.
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".

Fixpoint div2 (n : nat) :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if Nat.even n
    then div2 n
    else 3 * n + 1.

Inductive Collatz_holds_for : nat → Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more : ∀ (n : nat), Collatz_holds_for (f n) → Collatz_holds_for n.

Example Collatz_holds_for_12 : Collatz_holds_for 12.
Proof.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_more. unfold f. simpl.
  apply Chf_done.
Qed.

Conjecture collatz : ∀ n, Collatz_holds_for n.

Reserved Notation "n <= m" (at level 70).

(* Inductive le : nat → nat → Prop := *)
(*   | le_n : ∀ (n : nat), n <= n *)
(*   | le_S : ∀ (n m : nat), n <= m → n <= S m *)
(* where "n <= m" := (le n m). *)

Check @le_ind.

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Inductive clos_trans {X : Type} (R : X → X → Prop) : X → X → Prop :=
  | t_step : ∀ (x y : X), R x y → clos_trans R x y
  | t_trans :
      ∀ (x y z : X),
        clos_trans R x y → clos_trans R y z → clos_trans R x z.

Inductive Person : Type :=
  | Sage
  | Cleo
  | Ridley
  | Moss.

Inductive parent_of : Person → Person → Prop :=
  | po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss.

Definition ancestor_of : Person → Person → Prop := clos_trans parent_of.

Example ancestor_of1 : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of.
  apply t_trans with Cleo.
    - apply t_step.
      apply po_SC.
    - apply t_step.
      apply po_CM.
Qed.

Inductive Perm3 {X : Type} : list X → list X → Prop :=
  | perm3_swap12 (a b c : X) : Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) : Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 → Perm3 l2 l3 → Perm3 l1 l3.


Example Perm3_example1 : Perm3 [1;2;3] [2;3;1].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap23. 
Qed.

Example Per3_self: Perm3 [1;2;3] [1;2;3].
Proof.
  apply perm3_trans with [2;1;3].
  - apply perm3_swap12.
  - apply perm3_swap12.
Qed.

Inductive ev : nat → Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).
  
Theorem ev_4 : ev 4.
Proof. 
  apply ev_SS. 
  apply ev_SS. 
  apply ev_0. 
Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : ∀ n, ev n → ev (4 + n).
Proof.
  intros n. 
  simpl. 
  intros Hn. 
  apply ev_SS. 
  apply ev_SS. 
  apply Hn.
Qed.


Lemma double_def: 
  ∀ n, 
    Nat.double n = match n with
                    | O => O
                    | S n' => S (S (Nat.double n'))
                    end.
Proof.
  intro.
  induction n.
  * reflexivity.
  * simpl.
    unfold Nat.double.
    simpl.
    rewrite Nat.add_comm.
    simpl.
    reflexivity.
Qed.

Lemma double_S_n: 
  ∀ n, Nat.double (S n) = S (S (Nat.double n)).
Proof.
  intro.
  apply double_def.
Qed.
  
Theorem ev_double : 
  ∀ n, ev (Nat.double n).
Proof.
  intro.
  induction n as [|n' IHn'].
  * apply ev_0.
  * rewrite double_S_n.
    destruct IHn' as [| n E'] eqn:E.
    + apply ev_SS. apply ev_0.
    + apply ev_SS. apply IHn'.
Qed.

Theorem ev_inversion : 
  ∀ (n : nat), 
    ev n → (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. 
  destruct E as [ | n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'. split. 
    + reflexivity. 
    + apply E'.
Qed.

Theorem evSS_ev : ∀ n, ev (S (S n)) → ev n.
Proof.
  intros n H. 
  apply ev_inversion in H. 
  destruct H as [H0|H1].
  - discriminate H0.
  - destruct H1 as [n' [Hnm Hev]].
    injection Hnm as Heq.
    rewrite Heq. 
    apply Hev.
Qed.

Theorem evSS_ev' : 
  ∀ n, ev (S (S n)) → ev n.
Proof.
  intros n E. 
  inversion E as [| n' E' Heq].
  apply E'.
Qed.


Theorem one_not_even : ~ ev 1.
Proof.
  intros H. 
  apply ev_inversion in H. 
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. 
  inversion H. 
Qed.

Search (S ?n = S ?m → ?n = ?m).

Theorem SSSSev__even : ∀ n,
  ev (S (S (S (S n)))) → ev n.
Proof.
  intros.
  apply ev_inversion in H.
  destruct H as [HL | HR].
  * discriminate HL.
  * destruct HR as [n' E].
    destruct E.
    + injection H as Q.
      rewrite <- Q in H0.
      apply evSS_ev in H0.
      apply H0.
Qed.
      
Theorem SSSSev__even' : ∀ n,
  ev (S (S (S (S n)))) → ev n.
Proof.
  intros.
  inversion H as [Heq | n' E' Heq].
  inversion E' as [|n'' E'' Heq'].
  apply E''.
Qed.

Theorem ev5_nonsense :
  ev 5 → 2 + 2 = 9.
Proof.
  intro.
  simpl.
  inversion H as [Heq | n' E' Heq].
  inversion E' as [Heq' | n'' E'' Heq'].
  inversion E'' as [Heq'' | n''' E''' Heq''].
Qed.

Theorem ev5_nonsense' :
  ev 5 → 2 + 2 = 9.
Proof.
  intros.
  simpl.
  apply ev_inversion in H.
  destruct H as [HL | HR].
  * discriminate HL.
  * destruct HR as [n' [HL HR]].
    + injection HL as E.
      apply ev_inversion in HR.
      destruct HR as [HL | [n'' [HL HR]]].
      - rewrite HL in E. discriminate E.
      - rewrite <- E in HL.
        injection HL as E'.
        rewrite <- E' in HR.
        apply ev_inversion in HR.
        destruct HR as [HL | [n''' [HL HR]]].
        **discriminate HL.
        **discriminate HL.
Qed.


Theorem inversion_ex1 : ∀ (n m o : nat),
  [n; m] = [o; o] → [n] = [m].
Proof.
  intros n m o H. 
  inversion H.
  reflexivity. 
Qed.

Theorem inversion_ex2 : ∀ (n : nat),
  S n = O → 2 + 2 = 5.
Proof.
  intros n contra. 
  inversion contra. 
Qed.

Definition Even (n : nat) : Prop := 
  exists k, n = Nat.double k.

Lemma ev_Even_firsttry' : ∀ n,
  ev n → Even n.
Proof.
  unfold Even.
  intros n E. 
  inversion E as [EQ' | n' E' EQ'].
  - exists 0. reflexivity.
  - rewrite EQ'. 
Abort.
    
Lemma ev_Even : 
  ∀ n, ev n → Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - unfold Even. exists 0. reflexivity.
  - unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. 
    exists (S k). 
    rewrite double_S_n. 
    reflexivity.
Qed.  

Theorem ev_Even_iff : 
  ∀ n, ev n ↔ Even n.
Proof.
  intros n. split.
  - apply ev_Even.
  - unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : ∀ n m, ev n → ev m → ev (n + m).
Proof.
  intros.
  generalize dependent m.
  induction H as [| n' E' IH].
  * intros m Em. simpl. apply Em.
  * intros m Em.
    assert (H: (S (S n')) + m = n' + (S (S m))). {
      rewrite (Nat.add_comm n' (S (S m))).
      simpl.
      rewrite Nat.add_comm.
      reflexivity.
    }
    rewrite H.
    apply IH.
    apply ev_SS.
    apply Em.
Qed.

Inductive ev' : nat → Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Lemma ev_implies_ev': ∀ n, ev n → ev' n.
Proof.
  intros.
  induction H as [| n' E' IH].
  * apply ev'_0.
  * apply (ev'_sum 2 n'). 
    - apply ev'_2. 
    - apply IH.
Qed.

Lemma ev'_implies_ev': ∀ n, ev' n → ev n.
Proof.
  intros.
  induction H as [| | n' m' En' Em' Q].
  * apply ev_0.
  * apply ev_SS. apply ev_0.
  * apply ev_sum.
    apply Em'.
    apply IHQ.
Qed.

Theorem ev'_ev : ∀ n, ev' n ↔ ev n.
Proof.
  intro.
  split.
  * apply ev'_implies_ev'.
  * apply ev_implies_ev'.
Qed.

Theorem ev_ev__ev : ∀ n m,
  ev (n + m) → ev n → ev m.
Proof.
  intros n m HNM HN.
  induction HN as [| n' E' IH].
  * apply HNM.
  * simpl in HNM. 
    inversion HNM.
    apply IH in H0.
    apply H0.
Qed.

Lemma ev_inversion': ∀ n: nat,
  ev n → ev 0 \/ exists k, n = S (S k) /\ ev k.
Proof.
  intros.
  destruct H.
  * left. apply ev_0.
  * right. exists n.
    split.
    - reflexivity.
    - apply H.
Qed.

Lemma n_eq_S_k: ∀ n m, n = S m → exists n', n = S n' /\ n' = m.
Proof.
  intros.
  exists m.
  split.
  * apply H.
  * reflexivity.
Qed.
  
Lemma Ev_ev: ∀ n, Even n → ev n.
Proof. 
  intros.
  unfold Even in H.
  destruct H.
  generalize dependent n.
  induction x.
  * intros.
    rewrite double_def in H.
    rewrite H.
    apply ev_0.
  * intros.
    rewrite double_S_n in H.
    apply n_eq_S_k in H.
    destruct H as [n' [HL HR]].
    apply n_eq_S_k in HR.
    destruct HR as [n'' [HL' HR]].
    apply IHx in HR as E.
    apply ev_SS in E.
    rewrite <- HL' in E.
    rewrite <- HL in E.
    apply E.
Qed.

Theorem Ev_iff_ev: ∀ n, Even n <-> ev n.
Proof.
  intro.
  split.
  * apply Ev_ev.
  * apply ev_Even.
Qed.

Lemma fadsfa: 
  ∀ (n m : nat), ev (n + m) → ((ev n → ev m) \/ ((~ (ev n)) → (~(ev m)))).
Proof.
  intros.
  left.
  apply ev_ev__ev.
  apply H.
Qed.

Lemma n_minus_n: ∀ n, n - n = 0.
Proof.
  intros.
  induction n.
  * reflexivity.
  * simpl. apply IHn.
Qed.

Lemma S_n_minus_n: ∀ n, S n - n = 1.
Proof.
  induction n.
  * reflexivity.
  * simpl.
    simpl in IHn.
    apply IHn.
Qed.

Lemma dljnlvjnklads: ∀ n m k,
  k <=? m = true → (n + m) - k = n + (m - k).
Proof.
  intros n.
  induction n.
  * admit.
  * intros.
Admitted.
    

Lemma vlilhjerf: ∀ n m, 
  ((n + (S m)) - m) = S n.
Proof.
  intros.


  induction n.
  * simpl (0 + (S m)).
    apply S_n_minus_n.
  * replace ((S n) + (S m)) with (n + (S (S m))).
    - admit.
    - admit.
Admitted.

Lemma adfdgafg: ∀ n m R, n + m = R → n = R - m.
Proof.
  intros n.
  induction n.
  * intros.
    simpl in H.
    rewrite H.
    symmetry.
    apply n_minus_n.
  * intros.
    replace ((S n) + m) with (n + (S m)) in H.
    - apply IHn in H as E.
      rewrite <- H.
Admitted.

Theorem ev_plus_plus : ∀ n m p,
  ev (n+m) → ev (n+p) → ev (m+p).
Proof.
Admitted.

Module Playground.
  Inductive le : nat → nat → Prop :=
    | le_n (n : nat) : le n n
    | le_S (n m : nat) (H : le n m) : le n (S m).

  Notation "n <= m" := (le n m).

  Theorem test_le1 :
    3 <= 3.
  Proof.
    apply le_n.
  Qed.

  Theorem test_le2 :
    3 <= 6.
  Proof.
    apply le_S. 
    apply le_S. 
    apply le_S. 
    apply le_n. 
  Qed.

  Theorem test_le3 :
    (2 <= 1) → 2 + 2 = 5.
  Proof.
    intros H. 
    inversion H. 
    inversion H2. 
  Qed.
End Playground.

Inductive total_relation : nat → nat → Prop :=
  | Useless (n : nat) (m : nat) : total_relation n m.
  
 Theorem total_relation_is_total : ∀ n m, total_relation n m.
  Proof.
  intros.
  apply Useless.
Qed.

Inductive empty_relation : nat → nat → Prop := .
  
Theorem empty_relation_is_empty : ∀ n m, ~ empty_relation n m.
Proof.
  intros.
  unfold not.
  intro.
  destruct H.
Qed.

Lemma n_le_m__m_eq_n_plus_k:
  ∀ n m, n <= m → exists k, m = n + k.
Proof.
  intros.
  induction H as [| m E IH].
  * exists 0. rewrite Nat.add_0_r. reflexivity.
  * destruct IH as [n' H].
    rewrite H.
    exists (S n').
    rewrite (Nat.add_comm n (S n')).
    simpl.
    rewrite Nat.add_comm.
    reflexivity.
Qed.

Lemma S_n_le_m: 
  ∀ n m, S n <= m → n <= m.
Proof.
  intros.
  induction H as [| m' E' IH].
  * apply le_S.
    apply le_n.
  * apply le_S in IH.
    apply IH.
Qed.

Lemma m_eq_n_plus_k__n_le_m:
  ∀ n m k, m = n + k → n <= m.
Proof.
  intros n m k.
  generalize dependent n.
  induction k.
  * intros.
    rewrite Nat.add_0_r in H.
    rewrite H.
    apply le_n.
  * intros.
    replace ((S n) + k) with (n + (S k)) in H.
    - replace (n + (S k)) with (S n + k) in H.
      + apply IHk in H.
        apply S_n_le_m in H.
        apply H.
      + simpl.
        rewrite (Nat.add_comm n (S k)).
        simpl.
        rewrite Nat.add_comm.
        reflexivity.
    - simpl.
      rewrite (Nat.add_comm n (S k)).
      simpl.
      rewrite Nat.add_comm.
      reflexivity.
Qed.

Lemma n_le_n_plus_k:
  ∀ n k, n <= n + k.
Proof.
  intros n.
  induction k.
  * simpl. 
    rewrite Nat.add_0_r.
    apply le_n.
  * apply le_S in IHk.
    rewrite Nat.add_succ_r.
    apply IHk.
Qed.

Lemma m_eq_n_plus_some_k__n_le_m:
  ∀ n m, (exists k, m = n + k) → n <= m.
Proof.
  intros n m H.
  destruct H as [k' E].
  rewrite E.
  apply n_le_n_plus_k.
Qed.

Lemma le_trans : ∀ m n o, m <= n → n <= o → m <= o.
Proof.
  intros.
  apply n_le_m__m_eq_n_plus_k in H.
  apply n_le_m__m_eq_n_plus_k in H0.
  destruct H as [k E].
  destruct H0 as [k' E'].
  rewrite E in E'.
  rewrite <- Nat.add_assoc in E'.
  apply m_eq_n_plus_k__n_le_m in E'.
  apply E'.
Qed.

Theorem O_le_n : ∀ n,
  0 <= n.
Proof.
  intros n.
  induction n as [| n' IH].
  * apply le_n.
  * apply le_S.
    apply IH.
Qed.

Theorem n_le_m__Sn_le_Sm : ∀ n m,
  n <= m → S n <= S m.
Proof.
  intros n m H.
  induction H as [| m' E' IH].
  * apply le_n.
  * apply le_S. apply IH.      
Qed.

Theorem Sn_le_Sm__n_le_m : ∀ n m,
  S n <= S m → n <= m.
Proof.
  intros.
  apply n_le_m__m_eq_n_plus_k in H.
  destruct H.
  simpl in H.
  injection H as K.
  symmetry in K.
  symmetry in K.
  apply m_eq_n_plus_k__n_le_m in K.
  apply K.
Qed.

Theorem lt_ge_cases : ∀ n m,
  n < m \/ n >= m.
Proof.
  intros n.
  unfold lt,ge.
  induction n.
  * intros.
    destruct m.
    - right. apply le_n.
    - left. 
      apply n_le_m__Sn_le_Sm.
      apply O_le_n.
  * intros.
    specialize IHn with (pred m).
    destruct IHn as [HL | HR].
    - destruct m.
      + inversion HL.
      + simpl in HL.
        left.
        apply n_le_m__Sn_le_Sm.
        apply HL.
    - destruct m.
      + right.
        apply O_le_n.
      + simpl in HR.
        right.
        apply n_le_m__Sn_le_Sm.
        apply HR.
Qed.

Theorem le_plus_l : ∀ a b,
  a <= a + b.
Proof.
  intro a.
  induction a.
  * intros.
    simpl.
    apply O_le_n.
  * intros.
    simpl.
    apply n_le_m__Sn_le_Sm.
    apply IHa.
Qed.

Theorem plus_le : ∀ n1 n2 m,
  n1 + n2 <= m →
  n1 <= m /\ n2 <= m.
Proof.
  intros.
  split.
  - apply n_le_m__m_eq_n_plus_k in H.
    destruct H.
    rewrite <- Nat.add_assoc in H.
    apply m_eq_n_plus_k__n_le_m in H.
    apply H.
  - apply n_le_m__m_eq_n_plus_k in H.
    destruct H.
    rewrite (Nat.add_comm n1 n2) in H.
    rewrite <- Nat.add_assoc in H.
    apply m_eq_n_plus_k__n_le_m in H.
    apply H.
Qed.

Lemma sum_le_m__term_le_m: 
  ∀ a b n, a + b <= n → a <= n.
Proof.
  intros.
  apply n_le_m__m_eq_n_plus_k in H.
  destruct H.
  rewrite <- Nat.add_assoc in H.
  apply m_eq_n_plus_k__n_le_m  in H.
  apply H.
Qed.

Theorem add_le_cases : 
  ∀ n m p q, 
    n + m <= p + q → n <= p \/ m <= q.
Proof.
  intros n.
  induction n.
  * intros.
    simpl in H.
    left.
    apply O_le_n.
  * intros.
    destruct p.
    - right.
      simpl (0 + q) in H.
      rewrite Nat.add_comm in H.
      apply sum_le_m__term_le_m in H.
      apply H.
    - simpl in H.
      apply Sn_le_Sm__n_le_m in H.
      apply IHn in H.
      destruct H.
      + left.
        apply n_le_m__Sn_le_Sm.
        apply H.
      + right.
        apply H.
Qed.

Theorem plus_le_compat_l : ∀ n m p,
  n ≤ m → p + n ≤ p + m.
Proof.
  intros.
  induction p.
  * simpl. 
    apply H.
  * simpl. 
    apply n_le_m__Sn_le_Sm. 
    apply IHp.
Qed.

Theorem plus_le_compat_r : ∀ n m p,
  n ≤ m → n + p ≤ m + p.
Proof.
  intros.
  induction p.
  * simpl. 
    rewrite! Nat.add_0_r.
    apply H.
  * rewrite! Nat.add_succ_r.
    apply n_le_m__Sn_le_Sm. 
    apply IHp.
Qed.
  
Theorem le_plus_trans : ∀ n m p,
  n ≤ m → n ≤ m + p.
Proof.
  intros.
  induction p.
  * rewrite Nat.add_0_r.
    apply H.
  * rewrite Nat.add_succ_r.
    apply le_S.
    apply IHp.
Qed.

Theorem n_lt_m__n_le_m : ∀ n m,
  n < m → n ≤ m.
Proof.
  unfold lt.
  intros.
  apply S_n_le_m in H.
  apply H.
Qed.
  
Theorem plus_lt : ∀ n1 n2 m,
  n1 + n2 < m → n1 < m ∧ n2 < m.
Proof.
  unfold lt.
  intros.
  generalize dependent n2.
  generalize dependent n1.
  induction m.
  * intros.
    inversion H.
  * split.
    - apply n_le_m__Sn_le_Sm.
      apply Sn_le_Sm__n_le_m in H.
      destruct n2.
      + rewrite Nat.add_0_r in H.
        apply H.
      + rewrite Nat.add_succ_r in H.
        apply IHm in H.
        destruct H.
        apply S_n_le_m in H.
        apply H.
    - apply n_le_m__Sn_le_Sm.
      apply Sn_le_Sm__n_le_m in H. 
      destruct n1.
      + simpl.
        apply H.
      + simpl.
        apply IHm in H.
        destruct H.
        apply S_n_le_m in H0.
        apply H0.
Qed.

Theorem leb_complete : ∀ n m,
  n <=? m = true → n ≤ m.
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  * intros.
    destruct n.
    - apply O_le_n.
    - discriminate H.
  * intros.
    destruct n.
    - apply O_le_n.
    - simpl in H.
      apply IHm in H.
      apply n_le_m__Sn_le_Sm.
      apply H.
Qed.

Theorem leb_correct : ∀ n m,
  n ≤ m → n <=? m = true.
Proof.
  intros.
  generalize dependent n.
  induction m.
  * intros.
    inversion H.
    reflexivity.
  * intros.
    destruct n.
    - reflexivity.
    - apply Sn_le_Sm__n_le_m in H.
      apply IHm in H.
      apply H.
Qed.

Theorem leb_iff : ∀ n m,
  n <=? m = true ↔ n ≤ m.
Proof.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Theorem leb_true_trans : ∀ n m o,
  n <=? m = true → m <=? o = true → n <=? o = true.
Proof.
  intros.
  rewrite leb_iff in *.
  apply (le_trans n m o).
  * apply H.
  * apply H0.
Qed.

Module R.
  Inductive R : nat → nat → nat → Prop :=
    | c1 : R 0 0 0
    | c2 m n o (H : R m n o ) : R (S m) n (S o)
    | c3 m n o (H : R m n o ) : R m (S n) (S o)
    | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
    | c5 m n o (H : R m n o ) : R n m o.

  Definition fR : nat → nat → nat := 
    fun a => fun b => a + b.
    
  Search ((S ?n) = (S ?m)).
  
  Lemma R_O_N_N: ∀ n, R 0 n n.
  Proof.
    induction n.
    * apply c1.
    * apply c3 in IHn.
      apply IHn.
  Qed.

  
  Theorem R_equiv_fR : ∀ m n o, R m n o ↔ fR m n = o.
  Proof.
    intros.
    split.
    - intro.
      unfold fR in *.
      induction H.
      * reflexivity.
      * simpl. rewrite IHR. reflexivity.
      * rewrite Nat.add_succ_r.
        rewrite IHR.
        reflexivity.
      * simpl in IHR.
        rewrite Nat.add_succ_r in IHR.
        injection IHR.
        intros.
        apply H0.
      * rewrite Nat.add_comm.
        apply IHR.
    - intro.
      unfold fR in H.
      generalize dependent n.
      generalize dependent o.
      induction m.
      * intros.
        simpl in H.
        rewrite H.
        apply R_O_N_N.
      * intros.
        simpl in H.
        rewrite <- Nat.add_succ_r in H.
        apply IHm in H.
        apply c4.
        apply c2.
        apply c2.
        apply H.
  Qed.
End R.

Inductive subseq : list nat → list nat → Prop :=
  | ss_nil l : subseq [] l
  | ss_pref s m (E: subseq s m) h p: subseq (h :: s) (p ++ [h] ++ m).


Theorem ss_refl: ∀ (l : list nat), subseq l l.
Proof.
  intros.
  induction l.
  * apply ss_nil.
  * assert (Q:subseq (a :: l) (a :: l) = subseq (a :: l) ([] ++ [a] ++ l)). {
      reflexivity.
    }
    rewrite Q.
    apply ss_pref.
    apply IHl.
  (* intro l. *)
  (* assert (Q: subseq l l = subseq (l ++ []) ([] ++ l ++ [])). { *)
  (*     rewrite! app_nil_r. *)
  (*     reflexivity. *)
  (* } *)
  (* rewrite Q. *)
  (* apply (ss_pref l [] [] []).  *)
  (* apply ss_nil. *)
Qed.

Lemma app_is_nil:
  ∀ T (l : list T) r, (l ++ r) = [] -> l = [] ∧ r = [].
Proof.
  intros.
  destruct l,r.
  * split.
    - reflexivity.
    - reflexivity.
  * simpl in H. 
    discriminate H.
  * rewrite app_nil_r in H. 
    discriminate H.
  * discriminate H.
Qed.

Lemma ss_of_nil : 
  ∀ l1, subseq (l1) [] → (l1) = [].
Proof.
  intros.
  remember [] as e.
  induction H.
  * rewrite Heqe. 
    reflexivity.
  * apply app_is_nil in Heqe.
    destruct Heqe as [Hp Hhm].
    apply app_is_nil in Hhm.
    destruct Hhm as [Hh Hm].
    discriminate Hh.
  (* intros. *)
  (* remember [] as e. *)
  (* induction H. *)
  (* * reflexivity. *)
  (* * apply app_is_nil in Heqe. *)
  (*   destruct Heqe as [Hp Hslmr]. *)
  (*   apply app_is_nil in Hslmr. *)
  (*   destruct Hslmr as [Hsl Hmr]. *)
  (*   apply IHsubseq in Hmr as E. *)
  (*   rewrite E. *)
  (*   rewrite Hsl. *)
  (*   rewrite Hp. *)
  (*   reflexivity. *)
Qed.

Lemma cons_is_app : forall X (a : X) l, a :: l = [a] ++ l.
Proof.
  intros.
  reflexivity.
Qed.

Theorem ss_l_app: 
  ∀ l m, subseq l m -> ∀ p, subseq l (p ++ m).
Proof.
  intros l m.
  intro H.
  induction H.
  * intros.
    apply ss_nil.
  * intros.
    rewrite app_assoc.
    specialize IHsubseq with [].
    apply (ss_pref s m IHsubseq h (p0 ++ p)).
Qed.

Lemma ss_cons_l:
  ∀ p s m, subseq (p :: s) m -> subseq s m.
Proof.
  intros.
  inversion H.
  rewrite app_assoc.
  apply ss_l_app.
  apply E.
Qed.
   
Theorem ss_app_l: 
  ∀ p s m, subseq (p ++ s) m -> subseq s m.
Proof.
  intros.
  induction p.
  * simpl in H. 
    apply H.
  * simpl in H.
    apply ss_cons_l in H.
    apply IHp in H.
    apply H.
Qed.

Theorem ss_trans : ∀ (l1 l2 l3 : list nat),
  subseq l1 l2 →
  subseq l2 l3 →
  subseq l1 l3.
Proof.
  intros l1 l2 l3 H.
  generalize dependent l3.
  induction H.
  * intros.
    apply ss_nil.
  * intros.
    apply ss_app_l in H0 as H'.
    simpl in H'.
    inversion H'.
    apply ss_pref.
    apply IHsubseq.
    apply E.
Qed.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T → reg_exp T → Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
        (H1 : s1 =~ re1) 
        (H2 : s2 =~ re2)
        : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
        (H1 : s1 =~ re1)
        : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
        (H2 : s2 =~ re2)
        : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
        (H1 : s1 =~ re)
        (H2 : s2 =~ (Star re))
        : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ¬ ([1; 2] =~ Char 1).
Proof.
  intros H. 
  inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl.
  apply (MApp [1]). { apply MChar. }
  apply (MApp [2]). { apply MChar. }
  apply (MApp [3]). { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  ∀ T s (re : reg_exp T) ,
    s =~ re →
    s =~ Star re.
Proof.
  intros.
  replace s with (s ++ []).
  - apply MStarApp.
    * apply H.
    * apply MStar0.
  - rewrite app_nil_r.
    reflexivity.
Qed.

Lemma empty_is_empty : ∀ T (s : list T),
  ¬ (s =~ EmptySet).
Proof.
  intros.
  intro.
  inversion H.
Qed.

Lemma MUnion' : ∀ T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 ∨ s =~ re2 →
  s =~ Union re1 re2.
Proof.
  intros.
  destruct H as [HL | HR].
  * apply MUnionL. apply HL.
  * apply MUnionR. apply HR.
Qed.

Fixpoint fold {X Y: Type} (f : X→Y→Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Lemma MStar' : ∀ T (ss : list (list T)) (re : reg_exp T),
  (∀ s, In s ss → s =~ re) →
  fold (@app T) ss [] =~ Star re.
Proof.
  intros.
  induction ss.
  * simpl.
    apply MStar0.
  * simpl.
    apply MStarApp.
    - simpl in H.
      apply H.
      left.
      reflexivity.
    - apply IHss.
      simpl in H.
      intros.
      apply H.
      right.
      apply H0.
Qed.

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : ∀ T (s : list T) (re : reg_exp T) (x : T),
  s =~ re →
  In x s →
  In x (re_chars re).
Proof.
  intros T s re x HMatch.
  generalize dependent x.
  induction HMatch as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  * intros. 
    simpl in H. 
    destruct H.
  * intros. 
    simpl in H. 
    destruct H as [HL | HR].
    - rewrite HL. 
      simpl. 
      left. 
      reflexivity.
    - destruct HR.
  * intros.
    apply in_app_iff in H.
    destruct H as [HL | HR].
    - apply IH1 in HL. 
      simpl. 
      apply in_app_iff. 
      left. 
      apply HL.
    - apply IH2 in HR. 
      simpl. 
      apply in_app_iff. 
      right. 
      apply HR.
  * intros. 
    simpl. 
    apply IH in H. 
    apply in_app_iff. 
    left. 
    apply H.
  * intros. 
    apply IH in H. 
    simpl. 
    apply in_app_iff. 
    right. 
    apply H.
  * intros. 
    simpl in H. 
    destruct H.
  * intros. 
    apply in_app_iff in H. 
    destruct H.
    - simpl. 
      apply IH1 in H. 
      apply H.
    - apply IH2 in H. 
      apply H.
Qed.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char t => true
  | App r1 r2 => re_not_empty r1 && re_not_empty r2
  | Union r1 r2  => re_not_empty r1 || re_not_empty r2
  | Star r => true
  end.

Lemma re_not_empty_forward : ∀ T (re : reg_exp T),
  (exists s, s =~ re) → re_not_empty re = true.
Proof.
  intros.
  destruct H as [s H].
  induction H.
  * reflexivity.
  * reflexivity.
  * simpl.
    rewrite IHexp_match1.
    rewrite IHexp_match2.
    reflexivity.
  * simpl.
    rewrite IHexp_match.
    reflexivity.
  * simpl.
    rewrite IHexp_match.
    apply Bool.orb_true_r.
  * reflexivity.
  * reflexivity.
Qed.

Lemma orb_prop : ∀ b1 b2, (orb b1 b2) = true → b1 = true \/ b2 = true.
Proof.
  intros.
  destruct b1,b2.
  * left. reflexivity.
  * left. reflexivity.
  * right. reflexivity.
  * discriminate H.
Qed.

Lemma re_not_empty_backward : ∀ T (re : reg_exp T),
  re_not_empty re = true → (exists s, s =~ re).
Proof.
  intros.
  induction re.
  * simpl in H.
    discriminate H.
  * exists []. apply MEmpty.
  * exists [t]. apply MChar.
  * simpl in H.
    apply andb_prop in H.
    destruct H.
    apply IHre1 in H.
    apply IHre2 in H0.
    destruct H as [s1 H].
    destruct H0 as [s2 H'].
    exists (s1 ++ s2).
    apply MApp.
    - apply H.
    - apply H'.
  * simpl in H.
    apply orb_prop in H.
    destruct H as [H | H].
    - apply IHre1 in H. 
      destruct H as [s H].
      exists s.
      apply MUnionL.
      apply H.
    - apply IHre2 in H.
      destruct H as [s H].
      exists s.
      apply MUnionR.
      apply H.
  * exists [].
    apply MStar0.
Qed.
      
Lemma re_not_empty_correct : ∀ T (re : reg_exp T),
  (exists s, s =~ re) ↔ re_not_empty re = true.
Proof.
  intros.
  split.
  - apply re_not_empty_forward.
  - apply re_not_empty_backward.
Qed.

Lemma star_app: ∀ T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re →
  s2 =~ Star re →
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  * discriminate Heqre'.
  * discriminate Heqre'.
  * discriminate Heqre'.
  * discriminate Heqre'.
  * discriminate Heqre'.
  * intros.
    apply H.
  * intros.
    apply IH2 in Heqre' as R.
    rewrite <- app_assoc.
    apply MStarApp.
    - apply Hmatch1.
    - apply IH2.
      apply Heqre'.
      apply H.
    - apply H.
Qed.

Lemma MStar'' : ∀ T (s : list T) (re : reg_exp T),
  s =~ Star re →
    ∃ ss : list (list T), s = fold (@app T) ss [] ∧ ∀ s', In s' ss → s' =~ re.
Proof.
  intros T s re H.
  remember (Star re) as r'.
  induction H
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  * discriminate Heqr'.
  * discriminate Heqr'.
  * discriminate Heqr'.
  * discriminate Heqr'.
  * discriminate Heqr'.
  * simpl.
    exists [].
    simpl.
    split.
    - reflexivity.
    - intros.
      destruct H.
  * apply IH2 in Heqr' as H.
    destruct H as [ss [HL HR]].
    exists (s1::ss).
    split.
    - simpl.
      apply app_inv_head_iff.
      apply HL.
    - simpl.
      intros.
      destruct H as [H | H].
      + rewrite H in Hmatch1.
        injection Heqr'.
        intros.
        rewrite <- H0.
        apply Hmatch1.
      + apply HR in H.
        apply H.
Qed.

Module Pumping.
  Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
    match re with
    | EmptySet => 1
    | EmptyStr => 1
    | Char _ => 2
    | App re1 re2 => pumping_constant re1 + pumping_constant re2
    | Union re1 re2 => pumping_constant re1 + pumping_constant re2
    | Star r => pumping_constant r
    end.

  Lemma pumping_constant_ge_1 :
    ∀ T (re : reg_exp T),
      pumping_constant re ≥ 1.
  Proof.
    intros T re. 
    induction re.
    - (* EmptySet *)
      apply le_n.
    - (* EmptyStr *)
      apply le_n.
    - (* Char *)
      apply le_S. apply le_n.
    - (* App *)
      simpl.
      unfold ge in *.
      apply le_trans with (n:=pumping_constant re1).
      * apply IHre1. 
      * apply le_plus_l.
    - (* Union *)
      simpl.
      apply le_trans with (n:=pumping_constant re1).
      apply IHre1. apply le_plus_l.
    - (* Star *)
      simpl. apply IHre.
  Qed.
  
  Lemma pumping_constant_0_false :
    ∀ T (re : reg_exp T),
      pumping_constant re = 0 → False.
  Proof.
    intros T re H.
    assert (Hp1 : pumping_constant re ≥ 1).
    { apply pumping_constant_ge_1. }
    rewrite H in Hp1. inversion Hp1.
  Qed.
  
  Fixpoint napp {T} (n : nat) (l : list T) : list T :=
    match n with
    | 0 => []
    | S n' => l ++ napp n' l
    end.
    
  Lemma napp_plus: ∀ T (n m : nat) (l : list T),
    napp (n + m) l = napp n l ++ napp m l.
  Proof.
    intros T n m l.
    induction n.
    * reflexivity.
    * simpl.
      rewrite IHn.
      rewrite app_assoc.
      reflexivity.
  Qed.
  
  Lemma napp_star :
    ∀ T m s1 s2 (re : reg_exp T),
      s1 =~ re → s2 =~ Star re →
        napp m s1 ++ s2 =~ Star re.
  Proof.
    intros T m s1 s2 re.
    intros.
    induction m.
    * simpl.
      apply H0.
    * simpl.
      rewrite <- app_assoc.
      apply MStarApp.
      - apply H.
      - apply IHm.
  Qed.
  
  Lemma star_star__app_star : 
    ∀ T s1 s2 (re : reg_exp T),
      s1 =~ Star re → s2 =~ Star re → (s1 ++ s2) =~ Star re.
  Proof.
    intros.
    remember (Star re) as r'.
    induction H.
    * discriminate Heqr'.
    * discriminate Heqr'.
    * discriminate Heqr'.
    * discriminate Heqr'.
    * discriminate Heqr'.
    * simpl. apply H0.
    * apply IHexp_match2 in Heqr'.
      rewrite <- app_assoc.
      apply MStarApp.
      - apply H.
      - apply Heqr'.
      - apply H0.
  Qed.

  Lemma star__napp_star : 
    ∀ T m s1 (re : reg_exp T),
      s1 =~ Star re → napp m s1 =~ Star re.
  Proof.
    intros.
    induction m.
    * simpl.
      apply MStar0.
    * simpl.
      apply star_star__app_star.
      - apply H.
      - apply IHm.
  Qed.
  
  Lemma weak_pumping : ∀ T (re : reg_exp T) s,
    s =~ re →
      pumping_constant re ≤ length s →
        ∃ s1 s2 s3,
          s = s1 ++ s2 ++ s3 ∧
          s2 ≠ [] ∧
          ∀ m, s1 ++ napp m s2 ++ s3 =~ re.
  Proof.
    intros T re s Hmatch.
    induction Hmatch
      as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
         | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
         | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
    * simpl. 
      intros contra. 
      inversion contra. 
    * intro.
      simpl in H.
      inversion H.
      inversion H1.
    * intros HPC.
      simpl in HPC.
      rewrite length_app in HPC.
      apply add_le_cases in HPC.
      destruct HPC as [HPC | HPC].
      apply IH1 in HPC as R.
      destruct R as [x [y [z [Hs1 [Hy HPump]]]]].
      exists x,y,(z++s2).
      split.
      - rewrite Hs1.
        rewrite (app_assoc y z s2).
        rewrite (app_assoc x (y ++ z) s2).
        reflexivity.
      - split.
        + apply Hy.
        + intros.
          rewrite (app_assoc (napp m y) z s2).
          rewrite app_assoc.
          apply MApp.
          apply HPump.
          apply Hmatch2.
      - apply IH2 in HPC.
        destruct HPC as [x [y [z [Hs2 [Hy HPump]]]]].
        exists (s1++x),y,z.
        split.
        + rewrite Hs2.
          rewrite app_assoc.
          reflexivity.
        + split.
          **apply Hy.
          **intros.
            rewrite <- (app_assoc s1 x _).
            apply MApp.
            --apply Hmatch1.
            --apply HPump.
    * intros.
      simpl in H.
      apply sum_le_m__term_le_m in H as H'.
      apply IH in H'.
      destruct H' as [x [y [z [Hs1 [Hy HPump]]]]].
      exists x,y,z.
      split.
      - apply Hs1.
      - split.
        + apply Hy.
        + intros.
          apply MUnionL.
          apply HPump.
    * intros.
      simpl in H.
      rewrite Nat.add_comm in H.
      apply sum_le_m__term_le_m in H as H'.
      apply IH in H'.
      destruct H' as [x [y [z [Hs1 [Hy HPump]]]]].
      exists x,y,z.
      split.
      - apply Hs1.
      - split.
        + apply Hy.
        + intros.
          apply MUnionR.
          apply HPump.
    * intros.
      simpl in H.
      apply Nat.le_0_r in H.
      apply pumping_constant_0_false in H.
      destruct H.
    * intros.
      rewrite length_app in H.
      simpl in *.
      destruct s2.
      - simpl in H.
        rewrite Nat.add_0_r in H.
        apply IH1 in H.
        destruct H as [x [y [z [Hs1 [Hs2 HPump]]]]].
        exists x,y,z.
        split.
        + rewrite app_nil_r.
          apply Hs1.
        + split.
          **apply Hs2.
          **intros.
            rewrite <- (app_nil_r (x ++ ((napp m y) ++ z))).
            apply MStarApp.
            apply HPump.
            apply MStar0.
      - exists s1,(t::s2),[].
        split.
        + simpl.
          rewrite app_nil_r.
          reflexivity.
        + split.
          **unfold "<>".
            intro.
            discriminate H0.
          **intro.
            rewrite app_nil_r.
            apply MStarApp.
            --apply Hmatch1.
            --apply star__napp_star.
              apply Hmatch2.
  Qed.
  
  Lemma add_le_cases_smarter:
    ∀ a b c d, (a + b) <= (c + d) → 
      (a <= c) \/ (a > c /\ b <= d).
  Proof.
    intros.
    unfold gt,lt.
    apply Nat.add_le_cases in H.
    assert (R:(a ≤ c) ∨ (b ≤ d) → (a <=? c = true) \/ (b <=? d = true)). {
      intros.
      destruct H.
      - apply leb_correct in H.
        left.
        apply H.
      - right.
        apply leb_correct in H.
        apply H.
    }
    apply R in H.
    destruct (a <=? c) eqn:Q.
    * left.
      apply leb_iff.
      apply Q.
    * right.
      split.
      - rewrite Nat.leb_gt in Q.
        unfold lt in Q.
        apply Q.
      - destruct H.
        + discriminate H.
        + apply leb_iff.
          apply H.
  Qed.
  
  Lemma re_matcher_then_star_matches:
    ∀ T (s : list T) re, s =~ re → s =~ (Star re).
  Proof.
    intros.
    rewrite <- (app_nil_r s).
    apply MStarApp.
    * apply H.
    * apply MStar0.
  Qed.

  Lemma pumping : ∀ T (re : reg_exp T) s,
    s =~ re →
      pumping_constant re ≤ length s →
      ∃ s1 s2 s3,
        s = s1 ++ s2 ++ s3 ∧
        s2 ≠ [] ∧
        length s1 + length s2 ≤ pumping_constant re ∧
        ∀ m, s1 ++ napp m s2 ++ s3 =~ re.
  Proof.
    intros T re s Hmatch.
    induction Hmatch
      as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
         | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
         | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
    * intros.
      simpl in H.
      inversion H.
    * simpl.
      intros.
      inversion H.
      inversion H1.
    * simpl.
      intros.
      rewrite length_app in H.
      apply add_le_cases_smarter in H.
      destruct H as [EL | [NEL ER]].
      - apply IH1 in EL as IH'.
        destruct IH' as [x [y[z [Hs1 [Hy [Hpc HPump]]]]]].
        exists x,y,(z++s2).
        split. {
          rewrite Hs1.
          rewrite <- (app_assoc x (y ++ z) s2).
          rewrite <- (app_assoc y z s2).
          reflexivity.
        }
        split. {
          apply Hy.
        }
        split. {
          apply (le_trans (length x + length y) (pumping_constant re1) (pumping_constant re1 + pumping_constant re2)).
          apply Hpc.
          apply le_plus_l.
        }
        intros.
        rewrite app_assoc.
        rewrite app_assoc.
        apply MApp.
        + rewrite <- app_assoc.
          apply HPump.
        + apply Hmatch2.
      - apply IH2 in ER as IH'.
        destruct IH' as [x [y [z [Hs2 [Hy [Hpc HPump]]]]]].
        exists (s1 ++ x), y ,z.
        split. {
          rewrite <- app_assoc.
          rewrite <- Hs2.
          reflexivity.
        }
        split. {
          apply Hy.
        }
        split. {
          rewrite length_app.
          rewrite <- Nat.add_assoc. 
          apply Nat.add_le_mono.
          unfold gt,lt in NEL.
          apply S_n_le_m.
          apply NEL.
          apply Hpc.
        }
        intros.
        rewrite <- app_assoc.
        apply MApp.
        + apply Hmatch1.
        + apply HPump.
    * simpl.
      intros.
      apply sum_le_m__term_le_m in H as E.
      apply IH in E.
      destruct E as [x [y [z [Hs1 [Hy [Hpc HPump]]]]]].
      exists x, y, z.
      split. {
        apply Hs1.
      }
      split. {
        apply Hy.
      }
      split. {
        apply (le_trans _ (pumping_constant re1) _).
        apply Hpc.
        apply Nat.le_add_r.
      }
      intros.
      apply MUnionL.
      apply HPump.
    * simpl.
      intros.
      rewrite Nat.add_comm in H.
      apply sum_le_m__term_le_m in H as E.
      apply IH in E.
      destruct E as [x [y [z [Hs1 [Hy [Hpc HPump]]]]]].
      exists x, y, z.
      split. {
        apply Hs1.
      }
      split. {
        apply Hy.
      }
      split. {
        apply (le_trans _ (pumping_constant re2) _).
        apply Hpc.
        rewrite Nat.add_comm.
        apply Nat.le_add_r.
      }
      intros.
      apply MUnionR.
      apply HPump.
    * simpl.
      intros.
      inversion H.
      apply pumping_constant_0_false in H1.
      destruct H1.
    * intros.
      rewrite length_app in H.
      destruct s1.
      - simpl in *.
        apply IH2 in H.
        apply H.
      - destruct (length (t::s1) <=? pumping_constant re) eqn:Q.
        + apply leb_iff in Q.
          exists [],(t::s1),(s2).
          split. {
            reflexivity.
          }
          split. {
            intro.
            discriminate.
          }
          split. {
            simpl in *.
            apply Q.
          }
          intro.
          simpl.
          apply napp_star.
          apply Hmatch1.
          apply Hmatch2.
        + apply Nat.leb_gt in Q.
          apply Nat.lt_le_incl in Q.
          apply IH1 in Q.
          destruct Q as [x [y [z [Hs1 [Hy [HPC HPump]]]]]].
          exists x,y,(z ++ s2).
          split. {
            rewrite Hs1.
            rewrite <-app_assoc.
            rewrite <-app_assoc.
            reflexivity.
          }
          split. {
            apply Hy.
          }
          split. {
            simpl.
            apply HPC.
          }
          intros.
          rewrite app_assoc.
          rewrite app_assoc.
          apply MStarApp.
          **rewrite <- app_assoc.
            apply HPump.
          **apply Hmatch2.
  Qed.
End Pumping.

Inductive nostutter {X:Type} : list X → Prop :=
  | ns_nil : nostutter []
  | ns_singl (a: X) : nostutter [a]
  | ns_a (h : X) (t : list X) (H : nostutter (h :: t)) (a : X) (I: a <> h): nostutter (a :: (h :: t)).
  
Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof. 
  repeat constructor; apply Nat.eqb_neq; auto.
Qed.

Example test_nostutter_2: nostutter (@nil nat).
Proof. 
  repeat constructor; apply Nat.eqb_neq; auto.
Qed.

Example test_nostutter_3: nostutter [5].
Proof. 
  repeat constructor; auto. 
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof. 
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. 
Qed.

Inductive merge {X:Type} : list X → list X → list X → Prop :=
  | merge_nil : merge [] [] []
  | merge_pref l l' r r' m (H1 : merge l' r' m) : 
                merge (l ++ l') (r ++ r') (l ++ r ++ m)
  .

Lemma merge_pref_l: 
  ∀ T (l': list T) l r m, merge l r m → merge (l' ++ l) r (l' ++ m).
Proof.
  intros.
  replace r with ([] ++ r). {
    replace (l' ++ m) with (l' ++ [] ++ m). {
      apply merge_pref.
      apply H.
    }
    reflexivity.
  }
  reflexivity.
Qed.

Lemma merge_pref_r:
  ∀ T l (r': list T) r m, merge l r m → merge l (r' ++ r) (r' ++ m).
Proof.
  intros.
  replace l with ([] ++ l). {
    replace (r' ++ m) with ([] ++ r' ++ m). {
      apply merge_pref.
      apply H.
    }
    reflexivity.
  }
  reflexivity.
Qed.
    
Lemma merge_symm: 
  ∀ T (l : list T) r m, merge l r m → merge r l m.
Proof.
  intros.
  induction H.
  * apply merge_nil.
  * apply (merge_pref [] (r ++ r') l l' _).
    apply (merge_pref r r' [] l' _).
    apply IHmerge.
Qed.

Lemma merge_nil_l: 
  ∀ T (l : list T), merge [] l l.
Proof.
  intros.
  assert (Q: merge [] l l = merge ([] ++ []) (l ++ []) ([] ++ l ++ [])). {
    rewrite! app_nil_r.
    reflexivity.
  }
  rewrite Q.
  apply merge_pref.
  apply merge_nil.
Qed.

Lemma merge_app: 
  ∀ T (l1 : list T) l2, merge l1 l2 (l1 ++ l2).
Proof.
  intros.
  assert (Q: merge l1 l2 (l1 ++ l2) = merge (l1 ++ []) (l2 ++ []) (l1 ++ l2 ++ [])). {
    rewrite! app_nil_r.
    reflexivity.
  }
  rewrite Q.
  apply merge_pref.
  apply merge_nil.
Qed.

Example merge_test_1 : merge [1;6;2] [4;3] [1;4;6;2;3].
Proof.
  replace ([1;6;2]) with ([1] ++ [6;2]). {
    replace ([4;3]) with ([4] ++ [3]). {
      replace ([1;4;6;2;3]) with ([1] ++ [4] ++ [6;2] ++ [3]). {
        apply merge_pref_l.
        apply merge_pref_r.
        apply merge_app.
      } 
      reflexivity.
    }
    reflexivity.
  }
  reflexivity.
Qed.

Fixpoint All {T : Type} (P : T → Prop) (l : list T) : Prop :=
  match l with
  | nil => True
  | h :: t => P h ∧ All P t
  end.

Lemma All_distr: ∀ (X: Type) (test : X → Prop) l1 l2,
  All test (l1 ++ l2) → All test l1 ∧ All test l2.
Proof.
  intros X test l1.
  induction l1.
  * intros.
    simpl in *.
    split.
    - apply I.
    - apply H.
  * simpl in *.
    intros.
    destruct H as [HL HR].  
    apply IHl1 in HR.
    destruct HR as [Hl1 Hl2].
    split.
    - split.
      + apply HL.
      + apply Hl1.
    - apply Hl2.
Qed.


Lemma filter_with_all_true : 
  ∀ X l test, All (λ n : X, ((test n) = true)) l → filter test l = l.
Proof.
  intros.
  induction l.
  * reflexivity.
  * simpl in *.
    destruct H as [Ha Hl].
    apply IHl in Hl.
    rewrite Ha.
    rewrite Hl.
    reflexivity.
Qed.


Lemma filter_with_all_false : 
  ∀ X l test, All (λ n : X, ((test n) = false)) l → filter test l = [].
Proof.
  intros.
  induction l.
  * reflexivity.
  * simpl in *.
    destruct H as [Ha Hl]. 
    apply IHl in Hl.
    rewrite Ha.
    apply Hl.
Qed.

Theorem merge_filter : ∀ (X : Set) (test: X → bool) (l l1 l2 : list X),
  merge l1 l2 l →
    All (λ n, test n = true) l1 →
      All (λ n, test n = false) l2 →
        filter test l = l1.
Proof.
  intros X test l l1 l2 HMerge HL1 HL2.
  induction HMerge.
  * reflexivity.
  * apply All_distr in HL1.
    apply All_distr in HL2.
    destruct HL1 as [Hl Hl'].
    destruct HL2 as [Hr Hr'].
    apply IHHMerge in Hl'.
    - rewrite! filter_app.
      rewrite Hl'.
      apply filter_with_all_false in Hr.
      rewrite Hr.
      apply filter_with_all_true in Hl.
      rewrite Hl.
      reflexivity.
    - apply Hr'.
Qed.

Fixpoint check_subseq (l' : list nat) (l : list nat) : bool :=
  match (l', l) with
  | ([], _) => true
  | (h :: t, []) => false
  | (h' :: t', h :: t) => 
    if h' =? h 
        then check_subseq t' t 
        else false 
  end.
  
Lemma check_subseq_nil:
  ∀ l, (check_subseq l [] = true) → l = [].
Proof.
  intros.
  destruct l.
  * reflexivity.
  * simpl in H.
    discriminate.
Qed.

Lemma a_le_b__a_le_b_plus_c:
  ∀a b, a ≤ b → ∀ c, a ≤ b + c.
Proof.
  intros.
  induction c.
  * rewrite Nat.add_0_r. 
    apply H.
  * rewrite Nat.add_succ_r.
    apply le_S.
    apply IHc.
Qed.

Theorem filter_challenge_2:
  ∀ l l' (H : subseq l' l) test (H': All (λ n, test n = true) l'), 
    length l' <= length (filter test l).
Proof.
  intros l l' Hsub.
  intro test.
  induction Hsub.
  * intros.
    simpl.
    apply O_le_n.
  * intros.
    simpl in H'.
    destruct H' as [Hh HA].
    apply IHHsub in HA.
    simpl.
    rewrite cons_is_app.
    rewrite! filter_app.
    simpl.
    rewrite Hh.
    rewrite! length_app.
    simpl.
    rewrite Nat.add_succ_r.
    apply n_le_m__Sn_le_Sm.
    rewrite Nat.add_comm.
    apply a_le_b__a_le_b_plus_c.
    apply HA.
Qed.

Inductive pal {X: Type} : list X -> Prop :=
  | pal_e : pal []
  | pal_s (x : X) : pal [x]
  | pal_m (x : X) q (P : pal q) : pal ([x] ++ q ++ [x]).
  
Theorem pal_app_rev : ∀ (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros X l.
  induction l.
  * simpl.
    apply pal_e.
  * simpl.
    rewrite cons_is_app.
    assert (Q: [a] ++ (l ++ ((rev l) ++ [a])) = [a] ++ (l ++ (rev l)) ++ [a]). {
      rewrite! app_assoc.
      reflexivity.
    }
    rewrite Q.
    apply pal_m.
    apply IHl.
Qed.

Theorem pal_rev : ∀ (X:Type) (l: list X) , pal l → l = rev l.
Proof.
  intros.
  induction H.
  * reflexivity.
  * reflexivity.
  * simpl.
    rewrite rev_app_distr.
    simpl.
    rewrite <- IHpal.
    reflexivity.
Qed.

Lemma nil_len : ∀ X (l : list X), length l = 0 -> l = [].
Proof.
  destruct l.
  * intros.
    reflexivity.
  * intro.
    simpl in H.
    discriminate H.
Qed.

Lemma S_len : 
  ∀ X (l : list X), length l = 1 -> ∃a, l = [a].
Proof.
  intros.
  destruct l.
  * discriminate H.
  * simpl in H.
    injection H.
    intros.
    apply nil_len in H0.
    rewrite H0.
    exists x.
    reflexivity.
Qed.

Fixpoint drop_tail (X : Type) (l : list X) : option (list X * X) :=
  match l with
  | nil => None
  | h :: t => match drop_tail X t with
              | None => Some ([],h)
              | Some (r,q) => Some (h::r,q)
              end
  end.

Lemma drop_tail_add_cons:
  ∀ X (a : X) l l' t x, 
    (drop_tail X (a :: l)) = (Some (l', t)) →
      (drop_tail X (x :: a :: l)) = Some (x :: l', t).
Proof.
  intros.
  simpl in *.
  rewrite H.
  reflexivity.
Qed.

Lemma drop_tail_on_non_nil:
  ∀ X (l : list X), length l >= 1 -> ∃l' t, drop_tail X l = Some (l',t).
Proof.
  intros.
  destruct l.
  * inversion H.
  * generalize dependent x. 
    induction l.
    - exists [], x.
      reflexivity.
    - assert (Q: forall x, (length (x :: l)) >= 1). {
        intro. 
        simpl.
        apply n_le_m__Sn_le_Sm.
        apply O_le_n.
      }
      apply (IHl a) in Q.
      destruct Q as [l' [t H']].
      intros.
      apply (drop_tail_add_cons X a l l' t x) in H'.
      exists (x::l'),t.
      apply H'.
Qed.

Lemma destruct_list_tail:
  ∀ X (l : list X), (l = []) ∨ (∃l' a, l = l' ++ [a]).
Proof.
  intros.
  destruct l.
  * left. 
    reflexivity.
  * right.
    generalize dependent x.
    induction l.
    - intro.
      exists [], x.
      reflexivity.
    - intros.
      specialize IHl with a.
      destruct IHl as [l' [a' H]].
      rewrite H.
      exists (x::l'), a'.
      reflexivity.
Qed.
      
Lemma list_len_2_plus: 
  ∀ X (l : list X), length l >= 2 -> ∃a b l', l = [a] ++ l' ++ [b].
Proof.
  intros.
  destruct l.
  * inversion H.
  * destruct l.
    - inversion H.
      inversion H1.
    - destruct (destruct_list_tail X (x0 :: l)) as [HE | HT].
      + discriminate HE.
      + destruct HT as [l' [a HT]].
        rewrite HT.
        exists x,a,l'.
        reflexivity.
Qed.

Lemma asdfas:
  ∀ X (h : X) t a b, [h] ++ a ++ [t] = [t] ++ b ++ [h] -> h = t.
Proof.
  intros.
  injection H.
  intros.
  apply H1.
Qed.

Theorem l_eq_rev_l:
  ∀ X l, l = rev l -> 
    (l = []) 
  ∨ (∃a, l = [a]) 
  ∨ (∃ (a : X) l', (l = [a] ++ l' ++ [a]) ∧ l' = rev l').
Proof.
  intros X l H.
  destruct (length l) eqn:E.
  * apply nil_len in E.
    left.
    apply E.
  * destruct n.
    - apply S_len in E.
      destruct E as [a E].
      right.
      left.
      exists a.
      apply E.
    - right. 
      right.
      assert (Q: length l >= 2). {
        rewrite E.
        apply n_le_m__Sn_le_Sm.
        apply n_le_m__Sn_le_Sm.
        apply O_le_n.
      }
      apply list_len_2_plus in Q.
      destruct Q as [h [t [l' Hl]]].
      exists h,l'.
      rewrite Hl in H.
      simpl in H.
      rewrite rev_app_distr in H.
      simpl in H.
      injection H.
      intros.
      rewrite <- H1 in Hl.
      rewrite H1 in H0.
      apply app_inv_tail in H0.
      split.
      + apply Hl.
      + apply H0.
Qed.

Theorem palindrome_converse: ∀ {X: Type} (l: list X),
  l = rev l → pal l.
Proof.
  intros.
  apply l_eq_rev_l in H as E.
  destruct E as [E | [E | E]].
  * rewrite E. 
    apply pal_e.
  * destruct E as [a E].
    rewrite E.
    apply pal_s.
  * destruct E as [a [l' [HL E]]].
    

    
    
    

    

    

    
  

  
