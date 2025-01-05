Inductive bool : Type :=
  | true
  | false.

Definition negb (b_1 : bool) : bool :=
  match b_1 with
  | true => false
  | false => true
  end.

Compute (negb true).

Definition andb (left : bool) (right : bool) : bool :=
  match left with
  | true => right
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1 : orb true false = true.
Proof.
  simpl.
  reflexivity.
Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5 : false || false || true = true.
Proof.
  simpl.
  reflexivity.
Qed.

Definition negb' (b : bool) : bool :=
  if b
    then false
    else true.

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  match (b1, b2, b3) with
  | (true, true, true) => true
  | (_, _, _) => false
  end.

Example test_andb31 : andb3 true true true = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_andb32 : andb3 false true true = false.
  simpl.
  reflexivity.
Qed.

Example test_andb33 : andb3 true false true = false.
  simpl.
  reflexivity.
Qed.

Example test_andb34 : andb3 true true false = false.
  simpl.
  reflexivity.
Qed.
