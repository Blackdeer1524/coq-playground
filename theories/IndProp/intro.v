Require Import List PeanoNat.

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
  apply Chf_more.
  unfold f.
  simpl.
  apply Chf_more.
  unfold f.
  simpl.
  apply Chf_more.
  unfold f.
  simpl.
  apply Chf_more.
  unfold f.
  simpl.
  apply Chf_more.
  unfold f.
  simpl.
  apply Chf_more.
  unfold f.
  simpl.
  apply Chf_more.
  unfold f.
  simpl.
  apply Chf_more.
  unfold f.
  simpl.
  apply Chf_more.
  unfold f.
  simpl.
  apply Chf_done.
Qed.

Conjecture collatz : forall n, Collatz_holds_for n.

Reserved Notation "n <= m" (at level 70).

Inductive le : nat -> nat -> Prop :=
  | le_n : forall (n : nat), n <= n
  | le_S : forall (n m : nat), n <= m -> n <= S m
where "n <= m" := (le n m).

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
    destruct IHn'.
    + apply ev_SS. apply ev_0.
    + apply ev_SS. apply ev_SS. apply IHn'.
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
  (* We are in the E = ev_SS n' E' case now. *)
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

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  unfold Even.
  intros n E. 
  inversion E as [EQ' | n' E' EQ'].
  - exists 0. reflexivity.
  - rewrite EQ'. 
    
    