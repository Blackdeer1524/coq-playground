Require Import List.
Require Import PeanoNat.

Set Printing Parentheses.

Import ListNotations.

Theorem silly1 : forall (n m : nat), n = m -> n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

Theorem silly2 :
  forall (n m o p : nat), n = m -> (n = m -> [n; o] = [m; p]) -> [n; o] = [m; p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2a :
  forall (n m : nat),
    (n, n) = (m, m) ->
    (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) -> [n] = [m].
Proof.
  intros n m.
  intro eq1.
  intro eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex :
  forall p,
    (forall n, Nat.even n = true -> Nat.even (S n) = false) ->
    (forall n, Nat.even n = false -> Nat.odd n = true) ->
    Nat.even p = true -> Nat.odd (S p) = true.
Proof.
  intro p.
  intro even_then_succ_odd.
  intro odd_then_not_even.
  intro p_is_even.
  apply odd_then_not_even.
  apply even_then_succ_odd.
  apply p_is_even.
Qed.

Theorem rev_involutive :
  forall (X : Type), forall (l : list X), rev (rev l) = l.
Proof.
  intros.
  induction l.
    * reflexivity.
    * simpl.
      rewrite -> rev_app_distr.
      rewrite -> IHl.
      reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat), l = rev l' -> l' = rev l.
Proof.
  intros.
  symmetry.
  rewrite <- rev_involutive.
  symmetry.
  rewrite -> H.
  reflexivity.
Qed.

Theorem trans_eq : forall (X : Type) (n m o : X), n = m -> m = o -> n = o.
Proof.
  intros X n m o.
  intro eq1.
  intros eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example :
  forall (a b c d e f : nat),
    [a; b] = [c; d] -> [c; d] = [e; f] -> [a; b] = [e; f].
Proof.
  intros.
  transitivity [c; d].
    * apply H.
    * apply H0.
Qed.

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n) => n
  end.

Example trans_eq_exercise :
  forall (n m o p : nat), m = minustwo o -> n + p = m -> n + p = minustwo o.
Proof.
  intros n m o p.
  intro H0.
  intro H1.
  transitivity m.
    * apply H1.
    * apply H0.
Qed.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n => n
  end.

Theorem S_injective' : forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m H.
  assert (H' : forall n, n = pred (S n)).
  {
    simpl.
    reflexivity.
  }
  rewrite -> H'.
  rewrite <- H.
  rewrite <- H'.
  reflexivity.
Qed.

Theorem S_injective'' : forall (n m : nat), S n = S m -> n = m.
Proof.
  intros n m H.
  injection H as Hmn.
  apply Hmn.
Qed.

Theorem injection_ex1 : forall (n m o : nat), [n; m] = [o; o] -> n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  transitivity o.
    * apply H1.
    * symmetry.
      apply H2.
Qed.

Example injection_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros.
  injection H.
  rewrite -> H0.
  intros.
  injection H1.
  intro.
  transitivity z.
    * apply H2.
    * symmetry.
      apply H3.
Qed.

Example injection_ex3' :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j -> j = z :: l -> x = y.
Proof.
  intros.
  rewrite -> H0 in H.
  injection H.
  intros.
  transitivity z.
    * apply H2.
    * symmetry.
      apply H1.
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X), x :: y :: l = [] -> x = z.
Proof.
  intros.
  discriminate H.
Qed.

Lemma eqb_def :
  forall (n m : nat),
    (n =? m) =
    match n, m with
    | O, O => true
    | _, O => false
    | O, _ => false
    | S n', S m' => n' =? m'
    end.
Proof.
  intros.
  destruct n, m.
    * reflexivity.
    * reflexivity.
    * reflexivity.
    * simpl.
      reflexivity.
Qed.

Theorem eqb_0_l : forall n, (0 =? n) = true -> n = 0.
Proof.
  intros.
  destruct n.
    * reflexivity.
    * discriminate.
Qed.

Theorem silly4 : forall (n m p q : nat), (n = m -> p = q) -> m = n -> q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H.
  apply EQ in H.
  symmetry in H.
  apply H.
Qed.

Theorem specialize_example : forall n, (forall m, m * n = 0) -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  simpl in H.
  rewrite -> Nat.add_comm in H.
  simpl in H.
  apply H.
Qed.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n => S (S (double n))
  end.

Theorem eqb_true : forall n m, (n =? m) = true -> n = m.
Proof.
  intros n.
  induction n as [ | n' IHn'].
    * intros.
      destruct m.
        - reflexivity.
        - discriminate.
    * intros.
      destruct m.
        - discriminate.
        - simpl in H.
          apply IHn' in H.
          rewrite -> H.
          reflexivity.
Qed.

Lemma double_is_n_plus_n : forall (n : nat), n + n = double n.
Proof.
  intros.
  unfold double.
  induction n.
    * reflexivity.
    * simpl.
      rewrite -> Nat.add_comm.
      simpl.
      rewrite -> IHn.
      reflexivity.
Qed.

Theorem plus_n_n_injective : forall n m, n + n = m + m -> n = m.
Proof.
  intro n.
  induction n.
    * intro m.
      intro H.
      destruct m.
        - reflexivity.
        - discriminate.
    * intros.
      destruct m.
        - discriminate.
        - simpl in H.
          assert (Q : forall (x : nat), S (x + S x) = S (S x + x)).
          {
            intros.
            rewrite -> Nat.add_comm.
            reflexivity.
          }
          rewrite -> !Q in H.
          simpl in H.
          injection H.
          intros.
          apply IHn in H0.
          rewrite -> H0.
          reflexivity.
Qed.

Theorem double_injective_take2 : forall n m, double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [ | m' IHm'].
    * intros.
      destruct n.
        - reflexivity.
        - discriminate.
    * intros.
      destruct n.
        - discriminate.
        - f_equal.
          simpl in H.
          injection H.
          apply IHm'.
Qed.

Theorem nth_error_after_last :
  forall (n : nat) (X : Type) (l : list X), length l = n -> nth_error l n = None.
Proof.
  intros.
  generalize dependent n.
  induction l.
    * intros.
      rewrite <- H.
      reflexivity.
    * intros.
      rewrite <- H.
      simpl.
      apply IHl.
      reflexivity.
Qed.

Fixpoint split {X Y : Type} (l : list (X * Y)) : list X * list Y :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => ((x :: lx), y :: ly)
    end
  end.

Search hd.

Lemma uncurried_combine :
  forall (X Y : Type) (l1 : list X) (l2 : list Y),
    combine l1 l2 = (uncurry (combine (B := Y))) (l1, l2).
Proof.
  intros.
  reflexivity.
Qed.

Definition distr_pair {X Y : Type} (p : X * Y) (l : list X * list Y)
  : list X * list Y :=
  match p, l with
  | (x, y), (l1, l2) => ((x :: l1), y :: l2)
  end.

Lemma split_distr :
  forall (X Y : Type) (p : X * Y) (l : list (X * Y)),
    split (p :: l) = distr_pair p (split l).
Proof.
  intros.
  reflexivity.
Qed.

Lemma combine_pair :
  forall X Y (ll : list X * list Y) p,
    (uncurry (combine (B := Y))) (distr_pair p ll) =
    p :: (uncurry (combine (B := Y))) ll.
Proof.
  intros.
  destruct p.
  destruct ll as [l r].
  unfold distr_pair.
  reflexivity.
Qed.

Lemma combine_is_split_inv :
  forall (X Y : Type) (l : list (X * Y)),
    (uncurry (combine (B := Y))) (split l) = l.
Proof.
  induction l.
    * reflexivity.
    * destruct a.
      rewrite -> split_distr.
      rewrite -> combine_pair.
      rewrite -> IHl.
      reflexivity.
Qed.

Theorem combine_split :
  forall X Y (l : list (X * Y)) l1 l2, split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y.
  destruct l.
    * intros.
      simpl in H.
      injection H.
      intros.
      rewrite <- H0, <- H1.
      reflexivity.
    * intros l1 l2.
      destruct p.
      intro H.
      rewrite -> uncurried_combine.
      rewrite <- H.
      rewrite -> combine_is_split_inv.
      reflexivity.
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3
    then true
    else if n =? 5
           then true
           else false.

Theorem sillyfun1_odd :
  forall (n : nat), sillyfun1 n = true -> Nat.odd n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
    * apply eqb_true in Heqe3.
      rewrite -> Heqe3.
      reflexivity.
    * destruct (n =? 5) eqn:Heqe5.
        - apply eqb_true in Heqe5.
          rewrite -> Heqe5.
          reflexivity.
        - discriminate eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool), f (f (f b)) = f b.
Proof.
  intros.
  destruct b eqn:B.
    + destruct (f true) eqn:E.
        - rewrite -> !E.
          reflexivity.
        - destruct (f false) eqn:Q.
            * rewrite -> E.
              reflexivity.
            * rewrite -> Q.
              reflexivity.
    + destruct (f false) eqn:E.
        - destruct (f true) eqn:Q.
            * rewrite -> Q.
              reflexivity.
            * rewrite -> E.
              reflexivity.
        - rewrite -> E.
          rewrite -> E.
          reflexivity.
Qed.

Lemma eqb_self_true : forall (n : nat), (n =? n) = true.
Proof.
  intros.
  induction n.
    * reflexivity.
    * simpl.
      apply IHn.
Qed.

Lemma eqb_is_eq : forall (n m : nat), n = m -> (n =? m) = true.
Proof.
  intros n m.
  intros.
  rewrite -> H.
  apply eqb_self_true.
Qed.

Search Nat.eqb.

Theorem eqb_sym : forall (n m : nat), (n =? m) = (m =? n).
Proof.
  intros.
  destruct (n =? m) eqn:E.
    * symmetry.
      apply eqb_true in E.
      rewrite -> E.
      apply eqb_self_true.
    * symmetry.
      apply Nat.eqb_neq in E.
      apply Nat.eqb_neq.
      symmetry.
      apply E.
Qed.

Theorem eqb_trans :
  forall n m p, (n =? m) = true -> (m =? p) = true -> (n =? p) = true.
Proof.
  intros.
  apply eqb_true in H.
  apply eqb_true in H0.
  rewrite -> H.
  rewrite <- H0.
  apply eqb_is_eq.
  reflexivity.
Qed.

Definition split_combine_statement : Prop :=
  forall (X Y : Type) (l : list (X * Y)) l1 l2,
    l = combine l1 l2 -> length l1 = length l2 -> split l = (l1, l2).

Lemma len_of_combine_of_same_len_lists :
  forall (X Y : Type) (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> length (combine l1 l2) = length l1.
Proof.
  intros X Y l1.
  induction l1.
    * intros.
      reflexivity.
    * destruct l2 eqn:L2.
        - intro H.
          simpl.
          discriminate.
        - intro H.
          simpl in H.
          injection H.
          intro Q.
          apply IHl1 in Q.
          simpl.
          rewrite -> Q.
          reflexivity.
Qed.

Lemma bar :
  forall
    (X Y : Type)
    x
    y
    (l1 : list X)
    (l2 : list Y)
    (l3 : list X)
    (l4 : list Y),
    (l1,l2) = (l3,l4) -> (x :: l1, y :: l2) = (x :: l3, y :: l4).
Proof.
  intros.
  injection H.
  intros.
  rewrite H0.
  rewrite H1.
  reflexivity.
Qed.

Lemma zero_length_means_nil: forall (X : Type) (l : list X), length l = 0 -> l = [].
Proof.
  intros.
  destruct l.
  * reflexivity.
  * simpl in H.
    discriminate H.
Qed.


Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l.
  induction l as [ | h l' IHl'].
    * intros l1 l2 CombineRes H.
      apply len_of_combine_of_same_len_lists in H as CombineLen.
      simpl.
      rewrite <- CombineRes in CombineLen.
      simpl in CombineLen.
      rewrite <- CombineLen in H.
      symmetry in H.
      apply zero_length_means_nil in H.
      symmetry in CombineLen.
      apply zero_length_means_nil in CombineLen.
      rewrite H.
      rewrite CombineLen.
      reflexivity.
    * destruct h.
      intros l3 l4.
      rewrite -> split_distr.
      destruct (split l') as [l1 l2] eqn:SplitL.
      destruct l3 as [|hl3 l3'] eqn:L3, l4 as [|hl4 l4'] eqn:L4.
      - simpl.
        intros.
        discriminate H.
      - simpl.
        intros.
        discriminate H.
      - simpl.
        intros.
        discriminate H.
      - simpl.
        intros.
        injection H.
        intros.
        rewrite <- H2.
        rewrite <- H3.
        simpl.
        apply bar.
        apply IHl'.
        apply H1.
        injection H0.
        intro.
        apply H4.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.       
  intros X test x l.
  generalize dependent x.
  induction l as [|h l' IHl'].
  * intros.
    simpl in H.
    discriminate H.
  * intros.
    unfold filter in H.
    destruct (test h) eqn:TestH.
    - injection H.
      intros.
      rewrite <- H1.
      apply TestH.
    - fold filter in H.
      apply IHl' in H.
      apply H.
Qed.


Fixpoint forallb { X : Type } (f : X -> bool) (l : list X) : bool := 
  match l with 
  | h :: t => if f h then forallb f t else false
  | nil => true
  end.
  
Example forall_1: forallb Nat.odd [1;3;5;7;9] = true.
Proof.
  reflexivity.
Qed.
        
Example forall_2: forallb negb [false;false] = true. 
Proof. reflexivity. Qed.

Example forall_3: forallb Nat.even [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example forall_4: forallb (Nat.eqb 5) [] = true. 
Proof. reflexivity. Qed.

Fixpoint existsb { X : Type } (f : X -> bool) (l : list X) : bool := 
  match l with 
  | h :: t => if f h then true else existsb f t
  | nil => false
  end.

Example existsb_1: existsb (Nat.eqb 5) [0;2;3;6] = false. Proof. reflexivity. Qed.
Example existsb_2:existsb (andb true) [true;true;false] = true. Proof. reflexivity. Qed.
Example existsb_3:existsb Nat.odd [1;0;0;0;0;3] = true. Proof. reflexivity. Qed.
Example existsb_4:existsb Nat.even [] = false. Proof. reflexivity. Qed.

Definition existsb' { X : Type } (f : X -> bool) (l : list X) : bool := 
  negb (forallb (fun b => negb (f b)) l).

Example existsb'_1: existsb' (Nat.eqb 5) [0;2;3;6] = false. Proof. reflexivity. Qed.
Example existsb'_2: existsb' (andb true) [true;true;false] = true. Proof. reflexivity. Qed.
Example existsb'_3: existsb' Nat.odd [1;0;0;0;0;3] = true. Proof. reflexivity. Qed.
Example existsb'_4: existsb' Nat.even [] = false. Proof. reflexivity. Qed.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test.
  induction l as [|h l' IHl'].
  * reflexivity.
  * unfold existsb.
    unfold existsb'.
    unfold forallb.
    destruct (test h) eqn:TestH.
    + reflexivity.
    + simpl.
      apply IHl'.
Qed.
    
