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

Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more : forall (n : nat), Collatz_holds_for (f n) -> Collatz_holds_for n.

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

Conjecture collatz : forall n, Collatz_holds_for n.

Reserved Notation "n <= m" (at level 70).

(* Inductive le : nat -> nat -> Prop := *)
(*   | le_n : forall (n : nat), n <= n *)
(*   | le_S : forall (n m : nat), n <= m -> n <= S m *)
(* where "n <= m" := (le n m). *)

Check @le_ind.

Example le_3_5 : 3 <= 5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step : forall (x y : X), R x y -> clos_trans R x y
  | t_trans :
      forall (x y z : X),
        clos_trans R x y -> clos_trans R y z -> clos_trans R x z.

Inductive Person : Type :=
  | Sage
  | Cleo
  | Ridley
  | Moss.

Inductive parent_of : Person -> Person -> Prop :=
  | po_SC : parent_of Sage Cleo
  | po_SR : parent_of Sage Ridley
  | po_CM : parent_of Cleo Moss.

Definition ancestor_of : Person -> Person -> Prop := clos_trans parent_of.

Example ancestor_of1 : ancestor_of Sage Moss.
Proof.
  unfold ancestor_of.
  apply t_trans with Cleo.
    - apply t_step.
      apply po_SC.
    - apply t_step.
      apply po_CM.
Qed.

Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) : Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) : Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.


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

Inductive ev : nat -> Prop :=
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

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. 
  simpl. 
  intros Hn. 
  apply ev_SS. 
  apply ev_SS. 
  apply Hn.
Qed.


Lemma double_def: 
  forall n, 
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
  forall n, Nat.double (S n) = S (S (Nat.double n)).
Proof.
  intro.
  apply double_def.
Qed.
  
Theorem ev_double : 
  forall n, ev (Nat.double n).
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
  forall (n : nat), 
    ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E. 
  destruct E as [ | n' E'] eqn:EE.
  - left. reflexivity.
  - right. exists n'. split. 
    + reflexivity. 
    + apply E'.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
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
  forall n, ev (S (S n)) -> ev n.
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

Search (S ?n = S ?m -> ?n = ?m).

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
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
      
Theorem SSSSev__even' : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros.
  inversion H as [Heq | n' E' Heq].
  inversion E' as [|n'' E'' Heq'].
  apply E''.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intro.
  simpl.
  inversion H as [Heq | n' E' Heq].
  inversion E' as [Heq' | n'' E'' Heq'].
  inversion E'' as [Heq'' | n''' E''' Heq''].
Qed.

Theorem ev5_nonsense' :
  ev 5 -> 2 + 2 = 9.
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


Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. 
  inversion H.
  reflexivity. 
Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. 
  inversion contra. 
Qed.

Definition Even (n : nat) : Prop := 
  exists k, n = Nat.double k.

Lemma ev_Even_firsttry' : forall n,
  ev n -> Even n.
Proof.
  unfold Even.
  intros n E. 
  inversion E as [EQ' | n' E' EQ'].
  - exists 0. reflexivity.
  - rewrite EQ'. 
Abort.
    
Lemma ev_Even : 
  forall n, ev n -> Even n.
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
  forall n, ev n <-> Even n.
Proof.
  intros n. split.
  - apply ev_Even.
  - unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
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

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Lemma ev_implies_ev': forall n, ev n -> ev' n.
Proof.
  intros.
  induction H as [| n' E' IH].
  * apply ev'_0.
  * apply (ev'_sum 2 n'). 
    - apply ev'_2. 
    - apply IH.
Qed.

Lemma ev'_implies_ev': forall n, ev' n -> ev n.
Proof.
  intros.
  induction H as [| | n' m' En' Em' Q].
  * apply ev_0.
  * apply ev_SS. apply ev_0.
  * apply ev_sum.
    apply Em'.
    apply IHQ.
Qed.

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intro.
  split.
  * apply ev'_implies_ev'.
  * apply ev_implies_ev'.
Qed.

Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m HNM HN.
  induction HN as [| n' E' IH].
  * apply HNM.
  * simpl in HNM. 
    inversion HNM.
    apply IH in H0.
    apply H0.
Qed.

Lemma ev_inversion': forall n: nat,
  ev n -> ev 0 \/ exists k, n = S (S k) /\ ev k.
Proof.
  intros.
  destruct H.
  * left. apply ev_0.
  * right. exists n.
    split.
    - reflexivity.
    - apply H.
Qed.

(* Lemma dflajafsj: forall n k, *)
(*   n = Nat.double (S k) -> exists n', n = (S (S n')) /\ n' = Nat.double k. *)
(* Proof. *)
(*   intros. *)


Lemma n_eq_S_k: forall n m, n = S m -> exists n', n = S n' /\ n' = m.
Proof.
  intros.
  exists m.
  split.
  * apply H.
  * reflexivity.
Qed.
  
Lemma Ev_ev: forall n, Even n -> ev n.
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

Theorem Ev_iff_ev: forall n, Even n <-> ev n.
Proof.
  intro.
  split.
  * apply Ev_ev.
  * apply ev_Even.
Qed.

Lemma fadsfa: 
  forall (n m : nat), ev (n + m) -> ((ev n -> ev m) \/ ((~ (ev n)) -> (~(ev m)))).
Proof.
  intros.
  left.
  apply ev_ev__ev.
  apply H.
Qed.

Lemma n_minus_n: forall n, n - n = 0.
Proof.
  intros.
  induction n.
  * reflexivity.
  * simpl. apply IHn.
Qed.

Lemma S_n_minus_n: forall n, S n - n = 1.
Proof.
  induction n.
  * reflexivity.
  * simpl.
    simpl in IHn.
    apply IHn.
Qed.

Lemma dljnlvjnklads: forall n m k,
  k <=? m = true -> (n + m) - k = n + (m - k).
Proof.
  intros n.
  induction n.
  * admit.
  * intros.
Admitted.
    

Lemma vlilhjerf: forall n m, 
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

Lemma adfdgafg: forall n m R, n + m = R -> n = R - m.
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

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
Admitted.

Module Playground.
  Inductive le : nat -> nat -> Prop :=
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
    (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intros H. 
    inversion H. 
    inversion H2. 
  Qed.
End Playground.

Inductive total_relation : nat -> nat -> Prop :=
  | Useless (n : nat) (m : nat) : total_relation n m.
  
 Theorem total_relation_is_total : forall n m, total_relation n m.
  Proof.
  intros.
  apply Useless.
Qed.

Inductive empty_relation : nat -> nat -> Prop := .
  
Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
Proof.
  intros.
  unfold not.
  intro.
  destruct H.
Qed.

Lemma n_le_m__m_eq_n_plus_k:
  forall n m, n <= m -> exists k, m = n + k.
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
  forall n m, S n <= m -> n <= m.
Proof.
  intros.
  induction H as [| m' E' IH].
  * apply le_S.
    apply le_n.
  * apply le_S in IH.
    apply IH.
Qed.

Lemma m_eq_n_plus_k__n_le_m:
  forall n m k, m = n + k -> n <= m.
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
  forall n k, n <= n + k.
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
  forall n m, (exists k, m = n + k) -> n <= m.
Proof.
  intros n m H.
  destruct H as [k' E].
  rewrite E.
  apply n_le_n_plus_k.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
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

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n as [| n' IH].
  * apply le_n.
  * apply le_S.
    apply IH.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [| m' E' IH].
  * apply le_n.
  * apply le_S. apply IH.      
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros.
  apply n_le_m__m_eq_n_plus_k in H.
  destruct H.
  simpl in H.
  injection H as K.
  symmetry in K.
  apply m_eq_n_plus_k__n_le_m in K.
  apply K.
Qed.

Theorem lt_ge_cases : forall n m,
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

Theorem le_plus_l : forall a b,
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

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
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
  forall a b n, a + b <= n -> a <= n.
Proof.
  intros.
  apply n_le_m__m_eq_n_plus_k in H.
  destruct H.
  rewrite <- Nat.add_assoc in H.
  apply m_eq_n_plus_k__n_le_m  in H.
  apply H.
Qed.

Theorem add_le_cases : 
  forall n m p q, 
    n + m <= p + q -> n <= p \/ m <= q.
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
  
  Lemma R_O_N_N: forall n, R 0 n n.
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
  | ss_r (l : list nat) : subseq l l 
  | ss_ins (l' l m r : list nat) (E: subseq l' m) : subseq l' (l ++ m ++ r)
  | ss_inn (l m r l' : list nat) (E: subseq (l ++ m ++ r) l') : subseq m l'.

Theorem ss_refl : ∀ (l : list nat), subseq l l.
Proof.
  intros.
  apply ss_r.
Qed.

Theorem ss_app : ∀ (l1 l2 l3 : list nat),
  subseq l1 l2 → subseq l1 (l2 ++ l3).
Proof.
  intros.
  rewrite <- app_nil_l.
  rewrite app_assoc.
  apply (ss_ins l1 [] l2 l3).
  apply H.
Qed.

Search (?l1 ++ ?l2 = []).

Lemma ss_nil : forall l1, subseq (l1) [] -> (l1) = [].
Proof.
  intros l1 l2.
  remember [] as e.
  induction l2.
  * reflexivity.
  * apply app_eq_nil in Heqe as E.
    destruct E.
    apply app_eq_nil in H0 as E.
    destruct E.
    apply IHl2 in H1 as R.
    rewrite R.
    rewrite H2.
    rewrite H.
    rewrite app_nil_r.
    reflexivity.
  * apply IHl2 in Heqe as R.
    rewrite Heqe in R.
    apply app_eq_nil in R.
    destruct R.
    apply app_eq_nil in H0.
    destruct H0.
    rewrite H0.
    rewrite Heqe.
    reflexivity.
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
    apply H.
  * intros.
    apply IHsubseq.
    apply ss_inn in H0.
    apply H0.
  * intros.
    apply IHsubseq in H0.
    apply ss_inn in H0.
    apply H0.
Qed.