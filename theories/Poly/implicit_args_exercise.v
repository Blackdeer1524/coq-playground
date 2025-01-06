Require Import PeanoNat.

Set Printing Parentheses.

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check (cons nat 3 (nil nat)) : list nat.

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Module MumbleGrumble.
  Inductive mumble : Type :=
    | a
    | b (x : mumble) (y : nat)
    | c.

  Inductive grumble (X : Type) : Type :=
    | d (m : mumble)
    | e (x : X).
End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat' _ x count')
  end.

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

Compute (repeat''' 4 4).

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil : forall (X : Type), list X.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y [ ]) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Theorem app_nil_r : forall (X : Type), forall (l : list X), l ++ [ ] = l.
Proof.
  intros.
  induction l.
    * reflexivity.
    * simpl.
      rewrite -> IHl.
      reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros.
  induction l.
    * reflexivity.
    * simpl.
      rewrite -> IHl.
      simpl.
      reflexivity.
Qed.

Lemma app_length :
  forall (X : Type),
    forall (l1 l2 : list X), length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
    * reflexivity.
    * simpl.
      rewrite -> IHl1.
      reflexivity.
Qed.

Theorem rev_app_distr :
  forall (X : Type) (l1 l2 : list X), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
    * simpl.
      rewrite -> app_nil_r.
      reflexivity.
    * simpl.
      rewrite -> IHl1.
      rewrite -> app_assoc.
      reflexivity.
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

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments prod {X} {Y}.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [ ], _ => [ ]
  | _, [ ] => [ ]
  | x :: tx, y :: ty => (x, y) :: combine tx ty
  end.

Check @combine.

Compute (combine [1; 2] [false; false; true; true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : list X * list Y :=
  match l with
  | nil => (nil, nil)
  | (x, y) :: t =>
    match split t with
    | (list1, list2) => ((x :: list1), y :: list2)
    end
  end.

Example test_split : split [(1, false); (2, false)] = ([1; 2], [false; false]).
Proof.
  simpl.
  reflexivity.
Qed.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | a :: l' =>
    match n with
    | O => Some a
    | S n' => nth_error l' n'
    end
  end.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Check @hd_error : forall (X : Type), list X -> option X.

Example test_hd_error1 : hd_error [1; 2] = Some 1.
Proof.
  reflexivity.
Qed.

Example test_hd_error2 : hd_error [[1]; [2]] = Some [1].
Proof.
  reflexivity.
Qed.

Fixpoint filter ( X : Type ) (test : X -> bool) (l : list X) : list X :=
  match l with
  | [ ] => [ ]
  | h :: t =>
    if test h
      then h :: filter X test t
      else filter X test t
  end.

Compute (filter nat (fun n => Nat.even n) [1; 2; 3; 4]).

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter nat 
    (fun n =>
       if Nat.even n
         then 7 <? n
         else false)
    l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1; 2; 6; 9; 10; 3; 12; 8] = [10; 12; 8].
Proof.
  reflexivity.
Qed.

Example test_filter_even_gt7_2 : filter_even_gt7 [5; 2; 6; 19; 129] = [ ].
Proof.
  reflexivity.
Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X)
  : list X * list X :=
  (filter X test l,
  filter X
    (fun x =>
       if test x
         then false
         else true)
    l).

Example test_partition1 :
  partition Nat.odd [1; 2; 3; 4; 5] = ([1; 3; 5], [2; 4]).
Proof.
  reflexivity.
Qed.

Example test_partition2 :
  partition (fun x => false) [5; 9; 0] = ([ ], [5; 9; 0]).
Proof.
  reflexivity.
Qed.

Fixpoint map ( X Y : Type ) (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [ ] => [ ]
  | h :: t => f h :: map X Y f t
  end.

Lemma map_app_distr :
  forall (X Y : Type) (f : X -> Y) (l1 : list X) (l2 : list X),
    map X Y f (l1 ++ l2) = map X Y f l1 ++ map X Y f l2.
Proof.
  intros.
  induction l1.
    * reflexivity.
    * simpl.
      rewrite -> IHl1.
      reflexivity.
Qed.

Theorem map_rev :
  forall (X Y : Type) (f : X -> Y) (l : list X), map X Y f (rev l) = rev (map X Y f l).
Proof.
  intros.
  induction l.
    * reflexivity.
    * simpl.
      rewrite <- IHl.
      simpl.
      rewrite -> map_app_distr.
      reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | nil => nil
  | h :: t => f h ++ flat_map f t
  end.                   

Example test_flat_map1 :
  flat_map (fun n => [n; n; n]) [1; 5; 4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
  reflexivity.
Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.
