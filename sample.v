Require Import Omega.
Require Import ineqchain.

Notation "n !" := (fact n) (at level 10).

Lemma sampl_ineq_prop :
  forall (n : nat), 5 <= n -> 2^(n+1) <= n!.
Proof.
  intros n H.
  @ H : (5 <= n).
  induction H.
  (* base case : n = 5 *)
  - @ goal : (2 ^ (5 + 1) <= 5!).
    Left
    = 64.
    <= 120   { omega }.
    = Right.
  (* induction step *)
  - @ goal : (2 ^ (S m + 1) <= (S m)!).
    @ IHle : (2 ^ (m + 1) <= m !).
    Left
    = (2 ^ (S m + 1)).
    = (2 * 2 ^ (m + 1)). 
    <= (2 * m !)     { by IHle }.
    <= ((S m) * m !) { because (2 <= (S m)) by omega }.
    = ((S m)!).
    = Right.
Qed.
