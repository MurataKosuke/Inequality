Require Import Omega.
Require Import ineqchain.
Require Import Coq.Classes.Morphisms.

Fixpoint ack (x y : nat) : nat :=
  match x with
  | 0 => S y
  | S x' => let fix ackn (y : nat) :=
               match y with
               | 0 => ack x' 1
               | S y' => ack x' (ackn y')
               end
           in ackn y
  end.

Proposition ack_1_y_eq_SSy :
  forall (y : nat), ack 1 y = S (S y).
Proof.
  induction y.
  - @ goal : (ack 1 0 = 2).
    Left
    = 2.
    = Right.
  - @ goal : (ack 1 (S y) = S (S (S y))).
    @ IHy  : (ack 1 y = S (S y)).
    Left
    = (ack 1 (S y)).
    = (ack 0 (ack 1 y)).
    = (ack 0 (S (S y)))      { by IHy }.
    = (S (S (S y))).
    = Right.
Qed.

Proposition ack_SSy_le_ack_Sx_y :
  forall (x y : nat), S (S y) <= ack (S x) y.
Proof.
  induction x.
  - intros y.
    @ goal : (S (S y) <= ack 1 y).
    Left
    = (S (S y)).
    = (ack 1 y)   { by ack_1_y_eq_SSy }.
    = Right.
  - induction y.
    + @ goal : (2 <= ack (S (S x)) 0).
      @ IHx :
        (forall y : nat, S (S y) <= ack (S x) y).
      Right
      =  (ack (S (S x)) 0).
      =  (ack (S x) 1).
      >= (S (S 1))         { by IHx }.
      >= 2                 { omega }.
      = Left.
    + @ goal :
        (S (S (S y)) <= ack (S (S x)) (S y)).
      @ IHx  :
        (forall y : nat, S (S y) <= ack (S x) y).
      @ IHy  :
        (S (S y) <= ack (S (S x)) y).
      Right
      =  (ack (S (S x)) (S y)).
      =  (ack (S x) (ack (S (S x)) y)).
      >= (S (S (ack (S (S x)) y))) { by IHx }.
      >= (S (S (S (S y))))         { by IHy }.
      >= (S (S (S y)))             { omega }.
      = Left.
Qed.

Proposition Sy_le_ack_x_y :
  forall (x y : nat), y < ack x y.
Proof.
  induction x.
  - intros y.
    @ goal : (y < ack 0 y).
    Left
    = y.
    < (S y)            { omega }.
    = Right.
  - intros y.
    @ goal : (y < ack (S x) y).
    Right
    =  (ack (S x) y).
    >= (S (S y))       { by ack_SSy_le_ack_Sx_y }.
    >  y               { omega }.
    = Left.
Qed.

Proposition ack_x_y_lt_ack_x_Sy :
  forall (x y : nat), ack x y < ack x (S y).
Proof.
  induction x.
  - intros y.
    @ goal : (ack 0 y < ack 0 (S y)).
    Right
    = (ack 0 (S y)).
    = (S (S y)).
    > (S y)  { omega }.
    = (ack 0 y).
    = Left.
  - intros y.
    @ goal : (ack (S x) y < ack (S x) (S y)).
    Right
    =  (ack (S x) (S y)).
    =  (ack x (ack (S x) y)).
    >  (ack (S x) y)     { by Sy_le_ack_x_y }.
    =  Left.
Qed.

Program Instance ack_monotone_y : Proper (eq ++> le ++> le) (ack).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  rewrite H.
  induction H0.
  - reflexivity.
  - Left
    =  (ack y x0).
    <= (ack y m)     { by IHle }.
    <= (ack y (S m)) { by ack_x_y_lt_ack_x_Sy }.
    =  Right.
Qed.

Proposition ack_x_Sy_le_ack_Sx_y :
  forall (x y : nat), ack x (S y) <= ack (S x) y.
Proof.
  intros x y; revert x.
  induction y.
  - intros x.
    @ goal : (ack x 1 <= ack (S x) 0).
    Left
    = (ack (S x) 0).
    = (ack x 1).
    = Right.
  - intros x.
    @ goal : (ack x (S (S y)) <= ack (S x) (S y)).
    @ IHy  : (forall x : nat, ack x (S y) <= ack (S x) y).
    Left
    =  (ack x (S (S y))).
    <= (ack x (ack (S x) y))  { by ack_SSy_le_ack_Sx_y }.
    =  (ack (S x) (S y)).
    =  Right.
Qed.

Proposition ack_x_y_le_ack_Sx_y :
  forall (x y : nat), ack x y < ack (S x) y.
Proof.
  intros x y.
  Left
  =  (ack x y).
  <  (ack x (S y)) { by ack_x_y_lt_ack_x_Sy }.
  <= (ack (S x) y) { by ack_x_Sy_le_ack_Sx_y }.
  =  Right.
Qed.

Program Instance ack_monotone_x : Proper (le ++> eq ++> le) (ack).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  rewrite H0.
  induction H.
  - reflexivity.
  - Left
    =  (ack x y0).
    <= (ack m y0)     { by IHle }.
    <= (ack (S m) y0) { by ack_x_y_le_ack_Sx_y }.
    =  Right.
Qed.

Proposition ack_c1_ack_c2_x_le_ack_c3_x :
  forall (x c1 c2 : nat), exists (c3 : nat),
      ack c1 (ack c2 x) <= ack c3 x.
Proof.
  intros x c1 c2.
  exists (S (S (max c1 c2))).
  Left
  =  (ack c1 (ack c2 x)).
  <= (ack (max c1 c2) (ack c2 x))
       { because (c1 <= max c1 c2) by (apply Nat.le_max_l) }.
  <= (ack (max c1 c2) (ack (S (max c1 c2)) x))
       { because (c2 <= S (max c1 c2)) by (rewrite <- Nat.le_max_r; omega) }.
  =  (ack (S (max c1 c2)) (S x)).
  <= (ack (S (S (max c1 c2))) x)  { by ack_x_Sy_le_ack_Sx_y }.
  =  Right.
Qed.