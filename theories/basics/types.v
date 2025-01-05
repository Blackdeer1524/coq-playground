Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition something (c : color) : bool :=
  match c with
  | black => true
  | white => false
  | primary _ => false
  end.
