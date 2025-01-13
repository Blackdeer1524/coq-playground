Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Inductive test : Type :=
  | some
  | other.

Inductive Nat' : Type :=
  | Zero
  | Succ (x : Nat').

Definition next_weekend (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekend friday).

Example test_example : next_weekend friday = monday.
Proof.
  simpl.
  reflexivity.
Qed.
