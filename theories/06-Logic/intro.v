Require Import PeanoNat.
Require Import List.
Import ListNotations.

From Coq Require Import Unicode.Utf8.

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

Theorem even_bool_prop : forall n,
  Nat.even n = true <-> Even n.
  intros.
  split.
  * intro H.
    assert (Q: exists k : nat,
      (n = (if Nat.even n then Nat.double k else S (Nat.double k)))). {
        apply even_double_conv with (n:=n).
    }
    destruct Q.
    rewrite H in H0.
    unfold Even.
    exists x.
    apply H0.
  * unfold Even.
    intros.
    destruct H.
    rewrite H.
    apply even_double_n.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply Nat.eqb_eq.
  - intros H. rewrite H. rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem andb_true_iff : forall b1 b2:bool,
  andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros.
  split.
  - intro.
    split.
    * destruct b1,b2.
      + reflexivity.
      + reflexivity.
      + simpl in H. discriminate H.
      + simpl in H. discriminate H.
    * destruct b1,b2.
      + reflexivity.
      + simpl in H. discriminate H.
      + reflexivity.
      + simpl in H. discriminate H.
  - intro H.
    destruct H as [HL HR].
    * rewrite HL, HR. reflexivity.
Qed.


 Theorem orb_true_iff : forall b1 b2,
  orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros.
  split.
  * intro H.
    destruct b1,b2.
    - left. reflexivity.
    - left. reflexivity.
    - right. reflexivity.
    - simpl in H. discriminate H.
  * intros [HL | HR].
    - rewrite HL.
      reflexivity.
    - destruct b1.
      + reflexivity.
      + rewrite HR.
        reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> x <> y.
Proof.
  intros.
  split.
  * intro.
    unfold not.
    intro.
    rewrite H0 in H.
    apply Nat.eqb_eq in H0 as E.
    rewrite H0 in E.
    rewrite E in H.
    discriminate H.
  * intros.
    unfold not in H.
    apply not_true_iff_false.
    unfold not.
    intro.
    destruct H.
    apply eqb_eq in H0.
    apply H0.
Qed.

Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match (l1,l2) with
  | ([],[]) => true
  | (_,[]) => false
  | ([],_) => false
  | (h :: t, h' :: t') => if eqb h h' then eqb_list eqb t t' else false
  end.

Lemma foo: forall (X : Type) (a : X) l1 l2, l1 = l2 -> a :: l1 = a :: l2.
Proof.
  intros.
  generalize dependent l2.
  destruct l1.
  * intros.
    rewrite H.
    reflexivity.
  * intros.
    rewrite H.
    reflexivity.
Qed.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1 as [|h' l1' IHl1'].
  * intros.
    split.
    - intro.
      simpl in H0.
      destruct l2.
      + reflexivity.
      + discriminate H0.
    - intro.
      rewrite <- H0.
      reflexivity.
  * intro.
    simpl.
    destruct l2 eqn:L2.
    - split.
      + intro. discriminate H0.
      + intro. discriminate H0.
    - split.
      + intro.
        destruct (eqb h' a) eqn:R in H0.
        **apply H in R as P.
          rewrite P.
            apply foo.
            apply IHl1'.
            apply H0.
        **discriminate H0.
      + intros.
        injection H0.
        intros.
        destruct (eqb h' a) eqn:R.
        **apply IHl1'.
          apply H1.
        **apply H in H2.
          rewrite H2 in R.
          discriminate R.
Qed.

Fixpoint forallb { X : Type } (f : X -> bool) (l : list X) : bool := 
  match l with 
  | h :: t => if f h then forallb f t else false
  | nil => true
  end.

Theorem forallb_true_iff : forall X test (l : list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros.
  induction l as [|h' l' IHl'].
  * simpl. 
    split.
    - intro. apply I.
    - intro. reflexivity.
  * simpl.
    split.
    - intro.
      split.
      + destruct (test0 h') eqn:P.
        **reflexivity.
        **discriminate H.
      + destruct (test0 h') eqn:P.
        **apply IHl' in H. apply H.
        **discriminate H.
    - intros [HL HR].
      rewrite HL.
      apply IHl' in HR.
      apply HR.
Qed.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

 Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. 
  intros x.
  apply Nat.add_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].
  
Lemma rev_append_app_cons: 
  forall (X : Type) l l1 l2 (a: X), 
    (rev_append l l1) ++ (a :: l2) = (rev_append (l) (l1 ++ [a])) ++ l2.
Proof.
  intros X l.
  induction l.
  * intros. 
    simpl.
    rewrite <- List.app_assoc.
    reflexivity.
  * intros.
    simpl.
    specialize IHl with (a::l1) (l2) (a0).
    rewrite IHl.
    simpl.
    reflexivity.
Qed.

Lemma rev_append_cons: forall (X : Type) l l1 l2 (a: X), 
  l = rev_append (a :: l1) l2 -> l = (rev_append l1 []) ++ [a] ++ l2.
Proof.
  intros X l l1.
  induction l1 as [| h' l1' IHl1'].
  * simpl.
    intros.
    apply H.
  * intros.
    simpl.
    simpl in IHl1'.
    simpl in H.
    apply IHl1' in H as E.
    rewrite (rev_append_app_cons _ l1' ) in E.
    simpl in E.
    apply E.
Qed.

Lemma asdfaf: forall (X : Type) l1 l2 (a: X), 
  rev_append l1 (l2 ++ [a]) = (rev_append l1 l2) ++ [a].
Proof.
  intros X l1.
  induction l1.
  * intros. reflexivity.
  * intros.
    simpl.
    assert (Q: a::(l2 ++ [a0]) = ((a :: l2) ++ [a0])). {
      simpl.
      reflexivity.
    }
    rewrite Q.
    apply IHl1.
Qed.

Lemma tr_rev_cons : 
  forall (X: Type) (x : X) (l : list X), 
    tr_rev (x :: l) = (tr_rev l) ++ [x].
Proof.
  intros.
  generalize dependent x.
  induction l.
  * intro. reflexivity.
  * intro.
    unfold tr_rev.
    unfold rev_append.

    unfold tr_rev in IHl.
    unfold rev_append in IHl.
    specialize IHl with a.
    rewrite IHl.

    fold (@rev_append X) in IHl.
    fold (@rev_append X).
    rewrite <- IHl.
    replace ([a;x]) with ([a] ++ [x]).
    - rewrite (asdfaf X l [a] x).
      reflexivity.
    - reflexivity.
Qed.

Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intro.
  apply functional_extensionality.
  induction x.
  * reflexivity.
  * simpl.
    rewrite tr_rev_cons.
    rewrite IHx.
    reflexivity.
Qed.

Theorem excluded_middle_irrefutable: forall (P : Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intro P.
  unfold not.
  intro.
  apply de_morgan_not_or in H.
  unfold not in H.
  destruct H as [HL HR].
  destruct HR.
  apply HL.
Qed.

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem not_exists_dist :
  excluded_middle ->
    forall (X:Type) (P : X -> Prop),
      ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle.
  intros ExcludedMiddle X P.
  intros NotExists x.
  unfold not in NotExists.
  specialize ExcludedMiddle with (P x).
  destruct ExcludedMiddle as [HL | HR].
  * apply HL.
  * unfold not in HR.
    destruct NotExists.
    exists x.
    apply HR.
Qed.

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.

Theorem LEM_impl_peirce: excluded_middle -> peirce.
Proof.
  unfold excluded_middle, peirce.
  intros LEM P Q H.
  specialize LEM with P as R.
  destruct R.
  * apply H0.
  * apply H.
    intro.
    unfold not in H0.
    destruct H0.
    apply H1.
Qed.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Theorem LEM_impl_double_neg: excluded_middle -> double_negation_elimination.
Proof.
  unfold excluded_middle, double_negation_elimination.
  unfold not.
  intros.
  specialize H with P as Q.
  destruct Q.
  * apply H1.
  * apply H0 in H1.
    destruct H1.
Qed.
  
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Theorem excluded_middle_implies_de_morgan_not_and_not: excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle, de_morgan_not_and_not.
  intros LEM P Q H.
  specialize LEM with P as E.
  specialize LEM with Q as R.
  destruct E as [HP | HNP].
  - left. apply HP.
  - destruct R as [HQ | HNQ].
    * right. apply HQ.
    * unfold not in H.
      destruct H.
      split.
      + apply HNP.
      + apply HNQ.
Qed.

Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~P \/ Q).

Theorem excluded_middle_implies_implies_to_or: excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle, implies_to_or.
  intro LEM.
  intros.
  specialize LEM with P as E.
  destruct E as [HP | HNP].
  * right. apply H. apply HP.
  * left. apply HNP.
Qed.

Definition consequentia_mirabilis := forall P:Prop,
  (~P -> P) -> P.

Theorem excluded_middle_implies_consequentia_mirabilis: excluded_middle -> consequentia_mirabilis.
Proof.
  unfold excluded_middle, consequentia_mirabilis.
  intro LEM.
  intros.
  specialize LEM with P as E.
  destruct E as [HP | HNP].
  * apply HP.
  * apply H. apply HNP.
Qed.


Theorem CM_implies_DNE: 
  consequentia_mirabilis -> double_negation_elimination.
Proof.
  unfold consequentia_mirabilis, double_negation_elimination.
  intro CM.
  intro P.
  intro.
  specialize CM with P.
  unfold not in H.
  apply CM.
  intro.
  unfold not in H0.
  destruct H.
  apply H0.
Qed.
