Require Import PeanoNat.
Require Import List.
Import ListNotations.

Set Printing Parentheses.
Set Warnings "-notation-overridden,-parsing".
Set Warnings "-deprecated-hint-without-locality".

Definition injective {A : _} {B : _} (f : A -> B) :=
  forall (x y : A), f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H.
  injection H as H1.
  apply H1.
Qed.

Check @eq : forall (A : Type), A -> A -> Prop.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
    - reflexivity.
    - reflexivity.
Qed.

Example and_exercise : forall (n m : nat), n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  split.
    - destruct n.
        * reflexivity.
        * discriminate H.
    - destruct m.
        * reflexivity.
        * rewrite -> Nat.add_comm in H.
          discriminate H.
Qed.

Lemma and_example2 : forall (n m : nat), n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite -> Hn.
  rewrite -> Hm.
  reflexivity.
Qed.

Lemma and_example2' : forall (n m : nat), n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite -> !Hn.
  rewrite -> Hm.
  reflexivity.
Qed.

Lemma and_example3 : forall (n m : nat), n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite -> Hn.
  reflexivity.
Qed.

Lemma proj2 : forall (P Q : Prop), P /\ Q -> Q.
Proof.
  intros.
  destruct H as [_ HR].
  apply HR.
Qed.

Theorem and_commut : forall (P Q : Prop), P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - apply HQ.
    - apply HP.
Qed.

Theorem and_assoc : forall (P Q R : Prop), P /\ Q /\ R -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
    * split.
        - apply HP.
        - apply HQ.
    * apply HR.
Qed.

Lemma factor_is_O : forall (n m : nat), n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.
  destruct H as [Hn | Hm].
    - rewrite -> Hn.
      reflexivity.
    - rewrite -> Hm.
      rewrite <- mult_n_O.
      reflexivity.
Qed.

Lemma or_intro_l : forall (A B : Prop), A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma or_intro_r : forall (A B : Prop), B -> A \/ B.
Proof.
  intros A B HB.
  right.
  apply HB.
Qed.

Lemma zero_or_succ : forall (n : nat), n = 0 \/ n = S (pred n).
Proof.
  intros [ | n'].
    - left.
      reflexivity.
    - right.
      reflexivity.
Qed.

Lemma test : forall (n : nat), (forall (m : nat), n * m = 0) -> n = 0.
Proof.
  intros.
  specialize H with 1.
  rewrite -> Nat.mul_1_r in H.
  apply H.
Qed.

Lemma mult_is_O : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n eqn:N, m eqn:M.
    * left.
      reflexivity.
    * left.
      reflexivity.
    * right.
      reflexivity.
    * left.
      simpl in H.
      discriminate H.
Qed.

Theorem or_commut : forall (P Q : Prop), P \/ Q -> Q \/ P.
Proof.
  intros.
  destruct H as [HP | HQ].
    * right.
      apply HP.
    * left.
      apply HQ.
Qed.

Check not : Prop -> Prop.

Notation "~ x" := (not x) : type_scope.

Theorem ex_falso_quodlibet : forall (P : Prop), False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Theorem not_implies_our_not :
  forall (P : Prop), ~ P -> forall (Q : Prop), P -> Q.
Proof.
  intros P H Q H2.
  unfold not in H.
  destruct H.
  apply H2.
Qed.

Notation "x <> y" := (~ x = y).

Theorem zero_not_one : 0 <> 1.
Proof.
  intro.
  discriminate H.
Qed.

Theorem not_False : ~ False.
Proof.
  unfold not.
  intro.
  apply H.
Qed.

Theorem contradiction_implies_anything : forall (P Q : Prop), P /\ ~ P -> Q.
Proof.
  intros.
  destruct H as [HP HNP].
  unfold not in HNP.
  destruct HNP.
  apply HP.
Qed.

Theorem double_neg : forall (P : Prop), P -> ~ ~ P.
Proof.
  intros.
  unfold not.
  intros.
  destruct H0.
  apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop), (P -> Q) -> ~ Q -> ~ P.
Proof.
  intros P Q H HnQ.
  unfold not in *.
  intro HP.
  destruct HnQ.
  apply H.
  apply HP.
Qed.

Theorem not_both_true_and_false : forall (P : Prop), ~ (P /\ ~ P).
Proof.
  intros.
  unfold not.
  intro.
  destruct H as [Hl Hr].
  destruct Hr.
  apply Hl.
Qed.

Theorem de_morgan_not_or : forall (P Q : Prop), ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  unfold not.
  intros.
  split.
    * intro.
      destruct H.
      left.
      apply H0.
    * intro.
      destruct H.
      right.
      apply H0.
Qed.

Theorem not_true_is_false : forall (b : bool), b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
    - unfold not in H.
      destruct H.
      reflexivity.
    - reflexivity.
Qed.

Theorem not_true_is_false' : forall (b : bool), b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
    - unfold not in H.
      apply ex_falso_quodlibet.
      apply H.
      reflexivity.
    - reflexivity.
Qed.

Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Definition disc_fn (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ O = S n.
Proof.
  intros n H1.
  assert (H2 : disc_fn O).
  {
    simpl.
    apply I.
  }
  rewrite -> H1 in H2.
  simpl in H2.
  apply H2.
Qed.

Theorem iff_sym : forall (P Q : Prop), P <-> Q -> Q <-> P.
Proof.
  intros P Q [HAB HBA].
  split.
    - apply HBA.
    - apply HAB.
Qed.

Lemma not_true_iff_false : forall b, b <> true <-> b = false.
Proof.
  intros b.
  split.
    - apply not_true_is_false.
    - intros H.
      rewrite -> H.
      intros H'.
      discriminate H'.
Qed.

Lemma apply_iff_example1 : forall (P Q R : Prop), P <-> Q -> (Q -> R) -> P -> R.
  intros P Q R Hiff H HP.
  apply H.
  apply Hiff.
  apply HP.
Qed.

Lemma apply_iff_example2 : forall (P Q R : Prop), P <-> Q -> (P -> R) -> Q -> R.
Proof.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Theorem or_distributes_over_and :
  forall (P Q R : Prop), P \/ Q /\ R <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
    * intros.
      destruct H as [Hl | Hr].
        - split.
            + left.
              apply Hl.
            + left.
              apply Hl.
        - destruct Hr as [HQ HR].
          split.
            + right.
              apply HQ.
            + right.
              apply HR.
    * intro H.
      destruct H as [HL HR].
      destruct HL as [HP | HQ], HR as [HP' | HR].
        - left.
          apply HP.
        - left.
          apply HP.
        - left.
          apply HP'.
        - right.
          split.
            + apply HQ.
            + apply HR.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros n.
  destruct n.
  + intro m.
    split.
    - intro.
      left.
      reflexivity.
    - intro.
      simpl.
      reflexivity.
  + intros.
    split.
    - intro.
      destruct m eqn:M in H .
      * right.
        apply M.
      * discriminate H.
    - intro.
      destruct H as [HL | HR].
      * rewrite HL.
        reflexivity.
      * rewrite HR.
        apply Nat.mul_0_r.
Qed.

Lemma mul_eq_0' : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros.
  split.
  * intros.
    destruct H as [HP | [HQ | HR]].
    - left. left. apply HP.
    - left. right. apply HQ.
    - right. apply HR.
  * intro.
    destruct H as [[HP | HQ] | HR].
    - left. apply HP.
    - right. left. apply HQ.
    - right. right. apply HR.
Qed.

 Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros.
  split.
  - intro.
    apply mul_eq_0 in H.
    destruct H as [HL | HR].
    * apply mul_eq_0 in HL.
      destruct HL as [HL | HR].
      + left. apply HL.
      + right. left. apply HR.
    * right. right. apply HR.
  - intro H. 
    destruct H as [HL | HR].
    * rewrite HL.
    simpl.
    reflexivity.
    * destruct HR as [HL | HR].
      + rewrite HL.
        rewrite Nat.mul_0_r.
        reflexivity.
      + rewrite HR.
        apply Nat.mul_0_r. 
Qed.

Lemma mul_eq_0_ternary' :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.    


Definition Even x := exists n : nat, x = Nat.double n. 

Lemma four_is_Even : Even 4. Proof.
  unfold Even. 
  exists 2. 
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n H.
  destruct H as [m Hm]. (* note the implicit destruct here *)
  exists (2 + m).
  apply Hm. 
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros.
  unfold not.
  intros.
  destruct H0 as [x H'].
  destruct H'.
  apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  * intro H.
    destruct H as [x [HL | HR]].
    + left. exists x. apply HL.
    + right. exists x. apply HR.
  * intros [HL | HR].
    + destruct HL as [x0 H].
      exists x0.
      left. apply H.
    + destruct HR as [x0 H].
      exists x0.
      right.
      apply H.
Qed.


Lemma zero_is_min: forall m : nat, (0 <=? S m = true) -> (0 <=? m = true).
  intros.
  simpl.
  reflexivity.
Qed.

Theorem leb_plus_exists : 
  forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IHm'].
  * intros.
    destruct n.
    - exists 0.
      reflexivity.
    - discriminate H.
  * intros n'.
    intro H.
    destruct n'.
    - apply zero_is_min in H.
      apply IHm' in H.
      destruct H as [x0 H].
      simpl in H.
      exists (1 + x0).
      rewrite H.
      simpl.
      reflexivity.
    - simpl in H.
      apply IHm' in H.
      destruct H as [x0 H].
      rewrite H.
      exists (x0).
      reflexivity.
Qed.

Lemma leb_n_n : forall n,  (n <=? n) = true.
Proof.
  intros.
  induction n.
  * reflexivity.
  * simpl.
    apply IHn.
Qed.

Lemma leb_n_n_plus_x: forall n x, (n <=? (n + x)) = true.
Proof.
  intros n.
  induction n.
  * intros.
    simpl.
    reflexivity.
  * intro. simpl.
    apply IHn.
Qed.

Theorem plus_exists_leb : 
  forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  intros n m.
  generalize dependent n.
  destruct m.
  * intros.
    destruct n.
    + reflexivity.
    + destruct H.
      discriminate H.
  * intros.
    destruct H.
    rewrite H.
    apply leb_n_n_plus_x.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4]-> exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
     In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros.
  induction l.
  * simpl.
    split.
    + intro.
      destruct H.
    + intro H.
      destruct H as [x' [_ H]].
      apply H.
  * simpl.
    split.
    + intros [HL | HR].
      - exists a. 
        split.
        ** apply HL.
        ** left. reflexivity.
      - apply IHl in HR.
        destruct HR as [x' [HL HR]].
        exists x'.
        split.
        ** apply HL.
        ** right. apply HR.
    + intro.
      destruct H as [x' H].
      destruct H as [HL HR].
      destruct HR.
      - rewrite <- H in HL.
        left.
        apply HL.
      - right.
        apply IHl.
        exists x'.
        split.
        ** apply HL.
        ** apply H.
Qed.

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. 
  induction l as [|a' l' IH].
  * simpl.
    intros.
    split.
    - intro. right. apply H.
    - intro.
      destruct H as [[] | HR].
      apply HR.
  * simpl.
    intros l''.
    split.
    - intros [HL | HR].
      + left. left. apply HL.
      + apply IH in HR.
        destruct HR as [HL | HR].
        ** left. right. apply HL.
        ** right. apply HR.
    - intros [HL | HR].
      + destruct HL as [HL | HR].
        ** left. apply HL.
        ** right. apply IH. left. apply HR.
      + right. apply IH. right. apply HR.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | nil => True
  | h :: t => P h /\ All P t
  end.
  

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros.
  split.
  * induction l as [| h l' IHl'].
    - simpl. intros. apply I.
    - simpl. intros. split.
      + apply H. left. reflexivity. 
      + apply IHl'. intros. apply H. right. apply H0.
  * induction l as [| h l' IHl'].
    - simpl. intros. destruct H0.
    - simpl. intros [HL HR]. intros x [H'L | H'R].
      + rewrite <- H'L. apply HL.
      + specialize IHl' with x.
        apply IHl' in HR as E.
        ** apply E.
        ** apply H'R.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun (n : nat) => if Nat.odd n then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (Nat.odd n = true -> Podd n) ->
    (Nat.odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros.
  unfold combine_odd_even.
  destruct (Nat.odd n) eqn:E.
  * apply H. reflexivity.
  * apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    Nat.odd n = true ->
    Podd n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H.
  apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    Nat.odd n = false ->
    Peven n.
Proof.
  intros.
  unfold combine_odd_even in H.
  rewrite H0 in H.
  apply H.
Qed.

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite Nat.add_comm.
  rewrite (Nat.add_comm y z).
  reflexivity.
Qed.

Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl.
  rewrite Hl in H.
  simpl in H.
  apply H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Lemma in_not_nil_42_take_4:
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Lemma neg_neg_b: forall b: bool, negb (negb b) = b.
Proof.
  destruct b.
  * reflexivity.
  * reflexivity.
Qed.

Lemma bar : forall (b1 b2: bool), b1 = b2 <-> negb b1 = negb b2.
Proof.
  intros [] [].
  * split. 
    - intro. reflexivity.
    - intro. reflexivity.
  * split.
    - intro. discriminate.
    - intro. discriminate.
  * split. 
    - intro. discriminate.
    - intro. discriminate.
  * split.
    - intro. reflexivity.
    - intro. reflexivity.
Qed.

Lemma even_S_n : forall (n : nat), Nat.even (S n) = negb (Nat.even n).
Proof.
  induction n as [| n' IHn'].
  * reflexivity.
  * assert (R: Nat.even (S (S n')) = Nat.even n'). { 
      simpl. reflexivity. 
    }
    rewrite R.
    apply bar.
    rewrite IHn'.
    rewrite neg_neg_b.
    reflexivity.
Qed.

Lemma double_S_n: forall n, Nat.double (S n) = S (S (Nat.double n)).
Proof.
  intro n.
  induction n.
  * reflexivity.
  * unfold Nat.double.
    simpl.
    replace (n + (S (S n))) with (S (n + S n)).
    - reflexivity.
    - rewrite Nat.add_comm.
      rewrite (Nat.add_comm n (S (S n))).
      simpl.
      reflexivity.
Qed.

Lemma even_S_S_n: forall n, Nat.even (S (S n)) = Nat.even n.
Proof.
  intro n.
  rewrite even_S_n.
  rewrite even_S_n.
  rewrite neg_neg_b.
  reflexivity.
Qed.

Lemma even_S_double_n: forall n, Nat.even (S (Nat.double n)) = false.
Proof.
  intro n.
  induction n.
  * reflexivity.
  * rewrite double_S_n.
    rewrite even_S_S_n.
    rewrite IHn.
    reflexivity.
Qed.

Lemma even_double_n: forall n, Nat.even (Nat.double n) = true.
Proof.
  induction n.
  * reflexivity.
  * rewrite double_S_n.
    rewrite even_S_S_n.
    rewrite IHn.
    reflexivity.
Qed.

Lemma even_double_conv : 
  forall n, exists k,
    n = if Nat.even n then Nat.double k else S (Nat.double k).
Proof.
  intros.
  induction n.
  * simpl.
    exists 0.
    reflexivity.
  * destruct (Nat.even n) eqn:E.
    - destruct IHn as [k H].
      rewrite H.
      exists k.
      rewrite even_S_double_n.
      reflexivity.
    - destruct IHn as [k H].
      rewrite H.
      rewrite even_S_S_n.
      exists (S k).
      rewrite even_double_n.
      rewrite double_S_n.
      reflexivity.
Qed.