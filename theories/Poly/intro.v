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

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | [ ] => [ ]
  | h :: t =>
    if test h
      then h :: filter test t
      else filter test t
  end.

Compute (filter (fun n => Nat.even n) [1; 2; 3; 4]).

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter
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
  (filter test l,
  filter
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

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [ ] => [ ]
  | h :: t => f h :: map f t
  end.

Lemma map_app_distr :
  forall (X Y : Type) (f : X -> Y) (l1 : list X) (l2 : list X),
    map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros.
  induction l1.
    * reflexivity.
    * simpl.
      rewrite -> IHl1.
      reflexivity.
Qed.

Theorem map_rev :
  forall (X Y : Type) (f : X -> Y) (l : list X), map f (rev l) = rev (map f l).
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

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Theorem fold_def :
  forall (X Y : Type) (f : X -> Y -> Y) (l : list X) (b : Y),
    fold f l b =
    match l with
    | nil => b
    | h :: t => f h (fold f t b)
    end.
Proof.
  intros.
  destruct l.
    * reflexivity.
    * reflexivity.
Qed.

Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 : fold andb [true; true; false; true] true = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example fold_example2 : fold mult [1; 2; 3; 4] 1 = 24.
Proof.
  reflexivity.
Qed.

Example fold_example3 : fold app [[1]; [ ]; [2; 3]; [4]] [ ] = [1; 2; 3; 4].
Proof.
  reflexivity.
Qed.

Module Exercises.
  Definition fold_length {X : Type} (l : list X) : nat :=
    fold (fun _ n => S n) l 0.

  Theorem fold_length_def :
    forall (X : Type) (l : list X), fold_length l = fold (fun _ n => S n) l 0.
  Proof.
    intros.
    destruct l.
      * reflexivity.
      * reflexivity.
  Qed.

  Lemma fold_length_cons :
    forall (X : Type) (l : list X) (x : X),
      fold_length (x :: l) = 1 + fold_length l.
  Proof.
    intros.
    rewrite -> fold_length_def.
    rewrite -> fold_length_def.
    simpl.
    reflexivity.
  Qed.

  Theorem fold_length_correct : forall X (l : list X), fold_length l = length l.
  Proof.
    intros.
    induction l.
      * reflexivity.
      * simpl.
        rewrite -> fold_length_def.
        simpl.
        rewrite <- fold_length_def.
        rewrite -> IHl.
        reflexivity.
  Qed.

  Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
    fold (fun cur base => f cur :: base) l nil.

  Lemma fold_map_def :
    forall (X Y : Type) (f : X -> Y) (l : list X),
      fold_map f l = fold (fun cur base => f cur :: base) l nil.
  Proof.
    intros.
    reflexivity.
  Qed.

  Compute (fold_map (fun n => n + 1) [1; 2; 3]).

  Theorem fold_map_correct :
    forall (X Y : Type) (f : X -> Y) (l : list X), fold_map f l = map f l.
  Proof.
    intros.
    induction l.
      * reflexivity.
      * simpl.
        rewrite <- IHl.
        reflexivity.
  Qed.

  Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z :=
    f (x, y).

  Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z :=
    f (fst p) (snd p).

  Check @prod_curry.
  Check @prod_uncurry.

  Example test_map1' : map (plus 3) [2; 0; 2] = [5; 3; 5].
  Proof.
    reflexivity.
  Qed.

  Theorem uncurry_curry :
    forall (X Y Z : Type) (f : X -> Y -> Z) x y,
      prod_curry (prod_uncurry f) x y = f x y.
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem curry_uncurry :
    forall (X Y Z : Type) (f : X * Y -> Z) (p : X * Y),
      prod_uncurry (prod_curry f) p = f p.
  Proof.
    intros.
    destruct p.
    reflexivity.
  Qed.

  Module Church.
    Definition cnat := forall (X : Type), (X -> X) -> X -> X.

    Definition one : cnat := fun (X : Type) (f : X -> X) (x : X) => f x.

    Definition two : cnat := fun (X : Type) (f : X -> X) (x : X) => f (f x).

    Definition zero : cnat := fun (X : Type) (f : X -> X) (x : X) => x.

    Definition zero' : cnat := fun (X : Type) (succ : X -> X) (zero : X) => zero.

    Definition one' : cnat :=
      fun (X : Type) (succ : X -> X) (zero : X) => succ zero.

    Definition two' : cnat :=
      fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

    Definition scc (n : cnat) : cnat := fun (X : Type) f x => f (n X f x).

    Compute (scc zero).

    Example scc_1 : scc zero = one.
    Proof.
      reflexivity.
    Qed.

    Example scc_2 : scc one = two.
    Proof.
      reflexivity.
    Qed.

    Definition plus (n m : cnat) : cnat := fun (X : Type) f x => n X f (m X f x).

    Example churc_1_plus_1 : plus one one = two.
    Proof.
      reflexivity.
    Qed.

    Example churc_1_plus_0 : plus one zero = one.
    Proof.
      reflexivity.
    Qed.

    Definition mult (n m : cnat) : cnat := fun (X : Type) f x => n X (m X f) x.

    Example mult_1 : mult one one = one.
    Proof.
      reflexivity.
    Qed.

    Example mult_2 : mult zero (plus two two) = zero.
    Proof.
      reflexivity.
    Qed.

    Example mult_3 : mult two two = plus two two.
    Proof.
      reflexivity.
    Qed.

    Definition what (X : Type) (m : cnat) (x : X) : list X :=
      match m
        (list X)
        (fun xs =>
           match xs with
           | nil => nil
           | h :: t => h :: h :: t
           end)
        [x] with
      | nil => nil
      | h :: t => t
      end.

    Definition exp (n m : cnat) : cnat :=
      fun (X : Type) f x => m (X -> X) (fun f' => n X f') f x.
    
    Example exp_1: exp one one = one.
    Proof.
      reflexivity.
    Qed.
    
    Example exp_2: exp zero one = zero.
    Proof.
      reflexivity.
    Qed.
    
    Example exp_3: exp one two = one.
    Proof.
      reflexivity.
    Qed.

    Example exp_4: exp two one = two.
    Proof.
      reflexivity.
    Qed.
      
  End Church.
End Exercises.
