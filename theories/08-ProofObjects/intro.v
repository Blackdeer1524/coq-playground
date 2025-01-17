Require Import List PeanoNat.

From Coq Require Import Unicode.Utf8.
From Coq Require Import Setoids.Setoid.

Set Printing Parentheses.

Import ListNotations.

Theorem filter_not_empty_In : ∀ n l,
  filter (fun x => n =? x) l ≠ [] → In n l.
Proof.
  intros n l. 
  induction l as [|m l' IHl'].
  - simpl. intros H. apply H. reflexivity.
  - simpl. 
    destruct (n =? m) eqn:H.
    + intros _. 
      rewrite Nat.eqb_eq in H. 
      rewrite H.
      left. 
      reflexivity.
    + intros H'. 
      right. 
      apply IHl'. 
      apply H'.
Qed.

Print filter_not_empty_In.

Inductive reflect (P : Prop) : bool → Prop :=
  | ReflectT (H : P) : reflect P true
  | ReflectF (H : ¬ P) : reflect P false.

Theorem iff_reflect : ∀ P b, (P ↔ b = true) → reflect P b.
Proof.
  intros P b H. 
  destruct b eqn:Eb.
  - apply ReflectT. 
    rewrite H. 
    reflexivity.
  - apply ReflectF. 
    rewrite H. 
    intros H'. 
    discriminate.
Qed.

Theorem reflect_iff : ∀ P b, reflect P b → (P ↔ b = true).
Proof.
  intros.
  inversion H.
  * split.
    - intro.
      reflexivity.
    - intro.
      apply H0.
  * split.
    - intro.
      unfold not in H0.
      apply H0 in H2.
      destruct H2.
    - intros.
      discriminate H2.
Qed.

Lemma eqbP : ∀ n m, reflect (n = m) (n =? m).
Proof.
  intros n m. 
  Show Proof.
  apply iff_reflect. 
  Show Proof.
  rewrite Nat.eqb_eq. 
  Show Proof.
  reflexivity.
Qed.

Print eqbP.

Theorem filter_not_empty_In' : ∀ n l,
  filter (fun x => n =? x) l ≠ [] →
  In n l.
Proof.
  intros n l. 
  induction l as [| m l' IHl'].
  - simpl. 
    intros H. 
    apply H. 
    reflexivity.
  - simpl. 
    destruct (eqbP n m) as [H | H].
    + intros _. 
      rewrite H. 
      left. 
      reflexivity.
    + intros H'.
      right. 
      apply IHl'. 
      apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : ∀ n l,
  count n l = 0 → ~(In n l).
Proof.
  intros n l Hcount. 
  induction l as [| m l' IHl'].
  * simpl.
    intro.
    destruct H.
  * unfold not.
    simpl in *.
    destruct (eqbP n m).
    - discriminate Hcount.
    - simpl in Hcount.
      intros.
      destruct H0.
      + destruct H.
        rewrite H0.
        reflexivity.
      + apply IHl' in Hcount.
        apply Hcount.
        apply H0.
Qed.

Print eqbP.

Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_4''.
Qed.

Print ev_8.

Definition ev_8' : ev 8 := ev_SS 6 (ev_SS 4(ev_4'')).

Definition add1 : nat → nat.
  intro n.
  Show Proof.
  apply S.
  Show Proof.
  apply n. 
Defined.

Print add1.

Module Props.
  Module And.
    Inductive and (P Q : Prop) : Prop :=
      | conj : P → Q → and P Q.

    Arguments conj [P] [Q].

    Notation "P /\ Q" := (and P Q) : type_scope.

    Theorem proj1' : 
      ∀ P Q, P ∧ Q → P.
    Proof.
      intros P Q HPQ. 
      destruct HPQ as [HP HQ]. 
      apply HP.
      Show Proof.
    Qed.

    Lemma and_comm : 
      ∀ P Q : Prop, P ∧ Q ↔ Q ∧ P.
    Proof.
      intros P Q. 
      split.
      - intros [HP HQ]. 
        split.
        + apply HQ.
        + apply HP.
      - intros [HQ HP]. 
        split.
        + apply HP.
        + apply HQ.
    Qed.
  End And.

  Definition and_comm'_aux P Q (H : P ∧ Q) : Q ∧ P :=
    match H with
    | conj HP HQ => conj HQ HP
    end.

  Definition and_comm' P Q : P ∧ Q ↔ Q ∧ P :=
    conj (and_comm'_aux P Q) (and_comm'_aux Q P).
  
  Definition conj_fact :  
    ∀ P Q R, P ∧ Q → Q ∧ R → P ∧ R.
    intros P Q R HPQ HQR.
    destruct HPQ as [HP HQ].
    inversion HQR as [HQ' HR].
    split.
    - apply HP.
    - apply HR.
  Defined.
  
  Print conj_fact.
 
  Module Or.
    Inductive or (P Q : Prop) : Prop :=
      | or_introl : P → or P Q
      | or_intror : Q → or P Q.

    Arguments or_introl [P] [Q].
    Arguments or_intror [P] [Q].

    Notation "P ∨ Q" := (or P Q) : type_scope.
    
    Definition inj_l : ∀ (P Q : Prop), P → P ∨ Q :=
      fun P Q HP => or_introl HP.

    Theorem inj_l' : ∀ (P Q : Prop), P → P ∨ Q.
    Proof.
      intros P Q HP. left. apply HP.
    Qed.
    
    Definition or_elim : ∀ (P Q R : Prop), (P ∨ Q) → (P → R) → (Q → R) → R :=
    fun P Q R HPQ HPR HQR =>
      match HPQ with
      | or_introl HP => HPR HP
      | or_intror HQ => HQR HQ
      end.

    Theorem or_elim' : 
      ∀ (P Q R : Prop), (P ∨ Q) → (P → R) → (Q → R) → R.
    Proof.
      intros P Q R HPQ HPR HQR.
      destruct HPQ as [HP | HQ].
      - apply HPR. apply HP.
      - apply HQR. apply HQ.
    Qed.
  End Or.

  Definition or_commut' : ∀ P Q, P ∨ Q → Q ∨ P :=
    fun P => fun Q => fun P_or_Q =>
    match P_or_Q with
    | or_introl P => or_intror P
    | or_intror Q => or_introl Q
    end.

  Print or_commut'.
  
  Module Ex.
    Inductive ex {A : Type} (P : A → Prop) : Prop :=
      | ex_intro : ∀ (x : A), P x → ex P.
    
    Print ex_intro.

    Notation "'exists' x , p" :=
      (ex (fun x => p))
        (at level 200, right associativity) : type_scope.
  End Ex.

  Definition some_nat_is_even : ∃ n, ev n :=
    ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).
  
  Definition ex_ev_Sn : ex (fun n => ev (S n)).
    exists 1.
    apply ev_SS.
    apply ev_0.
  Defined.
  
  Print ex_ev_Sn.
  
  Definition ex_ev_Sn' : ex (fun n => ev (S n)) :=
    ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).

End Props.

Module EqualityPlayground.

  Inductive eq {X:Type} : X → X → Prop :=
    | eq_refl : ∀ x, eq x x.

  Notation "x == y" := (eq x y)
                         (at level 70, no associativity)
                       : type_scope.

  Lemma four: 2 + 2 == 1 + 3.
  Proof.
    apply eq_refl.
  Qed.

  Definition eq_add : ∀ (n1 n2 : nat), n1 == n2 → (S n1) == (S n2) :=
    fun n1 n2 Heq =>
      match Heq with
      | eq_refl n => eq_refl (S n)
      end.

  Theorem eq_add' : ∀ (n1 n2 : nat), n1 == n2 → (S n1) == (S n2).
  Proof.
    intros n1 n2 Heq.
    Fail rewrite Heq.
    destruct Heq.
    Fail reflexivity.
    apply eq_refl.
  Qed.

  Definition eq_cons : ∀ (X : Type) (h1 h2 : X) (t1 t2 : list X),
    h1 == h2 → t1 == t2 → h1 :: t1 == h2 :: t2 :=
      fun X h1 h2 t1 t2 Hh1h2 Ht1t2 => 
        match Hh1h2, Ht1t2 with
        | (eq_refl h),(eq_refl t) => eq_refl (h :: t)
        end. 

  Lemma equality__leibniz_equality : ∀ (X : Type) (x y: X),
    x == y → ∀ (P : X → Prop), P x → P y.
  Proof.
    intros X x y Hxy P HPx.
    destruct Hxy.
    apply HPx.
  Qed.

  Definition equality__leibniz_equality_term : ∀ (X : Type) (x y: X),
    x == y → ∀ P : (X → Prop), P x → P y :=
    fun X x y Hxy =>
      match Hxy with
      | eq_refl x => fun P HP => HP
      end.
  
  Definition eq_spec (X : Type) (x : X) : X -> Prop :=
    fun x' => eq x x'.
  
  Lemma leibniz_equality__equality : ∀ (X : Type) (x y: X),
    (∀ P:X → Prop, P x → P y) → x == y.
  Proof.
    intros.
    specialize H with (eq_spec X x).
    unfold eq_spec in H.
    apply H.
    apply eq_refl.
  Qed.
  
  Print leibniz_equality__equality.
End EqualityPlayground.

Definition and_assoc : ∀ P Q R : Prop,
  P ∧ (Q ∧ R) → (P ∧ Q) ∧ R :=
    fun P Q R HP_QR =>
      match HP_QR with
      | conj P HQR => match HQR with
                       | conj Q R => conj (conj P Q) R
                       end
      end.

Definition or_distributes_over_and_forward :
  ∀ P Q R : Prop, P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) :=
  fun P Q R HP_OR_QR =>
    match HP_OR_QR with
    | or_introl HP => conj (or_introl HP) (or_introl HP)
    | or_intror HQR => 
      match HQR with
      | conj HQ HR => conj (or_intror HQ) (or_intror HR)
      end
    end.

Definition or_distributes_over_and_backward :
  ∀ P Q R : Prop, (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R) :=
  fun P Q R HPorQ_PorR =>
    match HPorQ_PorR with
    | conj HPorQ HPorR => 
      match HPorQ,HPorR with
      | (or_introl P),_ => or_introl P
      | (or_intror Q),(or_introl P) => or_introl P
      | (or_intror Q),(or_intror R) => or_intror (conj Q R)
      end
    end.

Definition or_distributes_over_and : ∀ P Q R : Prop,
  P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) :=
    fun P Q R => 
      conj 
        ( fun HP_OR_QR => or_distributes_over_and_forward P Q R HP_OR_QR)
        ( fun HPorQ_PorR => or_distributes_over_and_backward P Q R HPorQ_PorR ).
      
Definition double_neg : ∀ P : Prop,
  P → ~~P.
  intros.
  unfold not.
  intro.
  apply H0.
  apply H.
Qed.

Definition double_neg' : ∀ P : Prop,
  P → (P -> False) -> False := fun P HP HNP => HNP HP. 

Definition double_neg'' : ∀ P : Prop,
  P → ~~P := fun P => double_neg' P.

Definition contradiction_implies_anything : 
  ∀ P Q : Prop, (P ∧ ¬P) → Q :=
    fun P Q HPNP =>
      match HPNP with
      | conj HP HNP => match (HNP HP) with end
      end.

Definition de_morgan_not_or : 
  ∀ P Q : Prop, ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
    λ P Q HNPorQ,
      conj 
      (λ HP, HNPorQ (or_introl HP)) 
      (λ HQ, HNPorQ (or_intror HQ)).

Definition curry : ∀ P Q R : Prop,
  ((P ∧ Q) → R) → (P → (Q → R)) :=
    λ P Q R HPQ_R HP HQ, HPQ_R (conj HP HQ).
  
Definition uncurry : ∀ P Q R : Prop,
  (P → (Q → R)) → ((P ∧ Q) → R) :=
    λ P Q R HPQR HPQ,
      match HPQ with
      | conj HP HQ => HPQR HP HQ
      end.

Definition propositional_extensionality : Prop :=
  ∀ (P Q : Prop), (P ↔ Q) → P = Q.

Theorem pe_implies_or_eq :
  propositional_extensionality →
    ∀ (P Q : Prop), (P ∨ Q) = (Q ∨ P).
Proof.
  unfold propositional_extensionality.
  intros.
  apply H.
  split.
  * intros HPQ.
    destruct HPQ as [HP | HQ].
    - right. apply HP.
    - left. apply HQ.
  * intros HQP.
    destruct HQP as [HQ | HP].
    - right. apply HQ.
    - left. apply HP.
Qed.

Lemma pe_implies_true_eq :
  propositional_extensionality →
    ∀ (P : Prop), P → True = P.
Proof.
  unfold propositional_extensionality.
  intros PE P HP.
  apply PE.
  split.
  * intro T. apply HP.
  * intro. apply I.
Qed. 

Definition proof_irrelevance : Prop :=
  ∀ (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Theorem pe_implies_pi :
  propositional_extensionality → proof_irrelevance.
Proof.
  unfold propositional_extensionality, proof_irrelevance.
  intro PE.
  intros P pf1 pf2.
  apply pe_implies_true_eq in pf1 as E. 
  * destruct E.
    destruct pf1, pf2.
    reflexivity.
  * unfold propositional_extensionality.
    intros. 
    apply PE. 
    apply H.
Qed.