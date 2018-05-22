Require Import Arith.
Require Import String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.

Inductive calstate : Type :=
  CFL   : calstate
| CFR   : calstate
| CFTMP : string -> calstate.

Inductive memo (cs : calstate) : Prop :=
  state : memo cs.

Tactic Notation "add_state" constr(cs) :=
  pose ( state _ : memo cs ).

Tactic Notation "set_state" constr(cs) :=
  first [ match goal with
          | [m := _ : _ |- _] => clear m ; add_state cs
          end
        | add_state cs
        ].

Tactic Notation "calrewrite_inner" constr(l) constr(term) tactic(tactic) :=
  let Hre := fresh "Hrewrite" in (
         assert (l = term) as Hre by (tactic ; (try reflexivity)) ;
         match goal with
         | [Hre : ?l1 = ?l1 |- _] => clear Hre
         | [Hre : _ |- _]         => (rewrite Hre at 1 || rewrite <- Hre at 1); clear Hre
         end).

Tactic Notation "calrewrite_inner_tmp" ident(i) constr(l) constr(term) tactic(tactic) :=
  let Hre := fresh "Hrewrite" in (
    assert (l = term) as Hre by (tactic ; (try reflexivity))
  ).

Tactic Notation "calrewrite_l" constr(term) "by" tactic(tactic) :=
  match goal with
  | [|- _ ?l _]  => calrewrite_inner l term tactic
  end.

Tactic Notation "calrewrite_r" constr(term) "by" tactic(tactic) :=
  match goal with
  | [|- _ _ ?l] => calrewrite_inner l term tactic
  | [|- ?l = _] => calrewrite_inner l term tactic
  | [|- ?l < _] => calrewrite_inner l term tactic
  | [|- ?l > _] => calrewrite_inner l term tactic
  | [|- ?l <= _] => calrewrite_inner l term tactic
  | [|- ?l >= _] => calrewrite_inner l term tactic
  end.

Tactic Notation "calrewrite_tmp" ident(i) constr(term) "by" tactic(tactic) :=
  match goal with
  | [_ : i = ?l |- _] => calrewrite_inner_tmp i l term tactic
  end.

Ltac equal_l term tactic :=
  match goal with
  | [|- _ ?l _]  => calrewrite_inner l term tactic
  end.
     
Ltac equal_r term tactic := calrewrite_r term by (tactic).
Ltac equal_tmp ident term tactic := calrewrite_tmp i term by (tactic).
Ltac equal term tactic :=
  match goal with
  | [Hst : (memo ?ns) |- _] =>
    match ns with
    | CFL        => calrewrite_l term by (tactic)
    | CFR        => calrewrite_r term by (tactic)
    | (CFTMP ?s) => calrewrite_tmp s term by tactic
    end
  end.

Ltac bydef := simpl ; reflexivity.

Ltac bydefof q := unfold q.
  
Ltac strivial := (repeat bydef) ; (try trivial).
  

Tactic Notation (at level 2)
       "Left"  "=" constr(e) "{" tactic(t) "}" :=
  (equal_l e t) ; set_state CFL.

Tactic Notation (at level 2) "Left"  "=" constr(e):=
  (equal_l e (strivial)) ; set_state CFL.

Tactic Notation (at level 2) "Right" "=" constr(e) "{" tactic(t) "}" :=
  (equal_r e t) ; set_state CFR.

Tactic Notation (at level 2) "Right" "=" constr(e) :=
  (equal_r e (strivial)) ; set_state CFR.

Tactic Notation (at level 2) "=" constr(x) "{" tactic(t) "}" := (equal x t).

Tactic Notation (at level 2) "=" constr(x) := (equal x (strivial)).

Tactic Notation (at level 2) "=" "Right" :=
  match goal with
  | [Hst : (memo CFL) |- _] =>
    trivial || tauto || (try apply transitivity ; reflexivity)
  end.

Tactic Notation (at level 2) "=" "Left"  :=
  match goal with
  | [Hst : (memo CFR) |- _] => trivial
  end.

Tactic Notation (at level 2) "=" constr(x) "{" "by" uconstr(u) "}" :=
  match goal with
  | [Hst : (memo ?ns) |- _] =>
    match ns with
    | CFL        => calrewrite_l x by (try rewrite u || (try rewrite <- u))
    | CFR        => calrewrite_r x by (try rewrite u || (try rewrite <- u))
    | (CFTMP ?s) => calrewrite_tmp s x by ((try rewrite u) || (try rewrite <- u))
    end
  end.

Tactic Notation (at level 2) "=" constr(x) "{" "by" uconstr(u0) "," uconstr(u1) "}" :=
  match goal with
  | [Hst : (memo ?ns) |- _] =>
    match ns with
    | CFL        => calrewrite_l x by
          ((try rewrite -> u0 , -> u1)
           || (try rewrite <- u0 , -> u1)
           || (try rewrite -> u0 , <- u1)
           || (try rewrite <- u0 , <- u1))
    | CFR        => calrewrite_r x by
          ((try rewrite -> u0 , -> u1)
           || (try rewrite <- u0 , -> u1)
           || (try rewrite -> u0 , <- u1)
           || (try rewrite <- u0 , <- u1))
    | (CFTMP ?s) => calrewrite_tmp s x by
          ((try rewrite -> u0 , -> u1)
           || (try rewrite <- u0 , -> u1)
           || (try rewrite -> u0 , <- u1)
           || (try rewrite <- u0 , <- u1))
    end
  end.

Require Import Ring.
Require Import Omega.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Morphisms.

Program Instance c : Proper (le ++> le) S.
Next Obligation.
  unfold respectful.
  intros x y.
  omega.
Qed.

Program Instance S_monotone_le : Proper (le ++> le) S.
Next Obligation.
Proof.
  unfold respectful.
  exact le_n_S.
Qed.

Program Instance S_monotone_lt : Proper (lt ++> lt) S.
Next Obligation.
Proof.
  unfold respectful.
  intros x y H.
  omega.
Qed.

Program Instance plus_left_monotone_le : Proper (le ++> eq ++> le) (plus).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  omega.
Qed.

Program Instance plus_left_monotone_lt : Proper (lt ++> eq ++> lt) (plus).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  omega.
Qed.

Program Instance plus_left_monotone_lt_le : Proper (lt ++> eq ++> le) (plus).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  omega.
Qed.

Program Instance plus_right_monotone_le : Proper (eq ++> le ++> le) (plus).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  omega.
Qed.

Program Instance plus_right_monotone_lt : Proper (eq ++> lt ++> lt) (plus).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  omega.
Qed.

Program Instance plus_right_monotone_lt_le : Proper (eq ++> lt ++> le) (plus).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  omega.
Qed.

Program Instance mult_monotone_lt : Proper (lt ++> lt ++> lt) (plus).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  omega.
Qed.

Program Instance mult_left_monotone_le : Proper (le ++> eq ++> le) (mult).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  rewrite H0.
  apply Nat.mul_le_mono_r.
  exact H.
Qed.

Program Instance mult_left_monotone_lt_le : Proper (lt ++> eq ++> le) (mult).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  rewrite H0.
  apply Nat.mul_le_mono_r.
  apply Nat.lt_le_incl.
  exact H.
Qed.

Program Instance mult_right_monotone_lt : Proper (eq ++> le ++> le) (mult).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  rewrite H.
  apply Nat.mul_le_mono_l.
  exact H0.
Qed.

Definition eq0 := fun x y => x = y /\ x <> 0.
Program Instance s : Proper (lt ++> eq0 ++> lt) (mult).
Next Obligation.
Proof.
  intros x y H.
  unfold respectful.
  intros x0 y0 H0.
  unfold eq0 in H0.
  induction H0.
  rewrite H0.
  unfold lt.
  unfold lt in H.
  induction x0.
  - rewrite <- H0.
    contradiction H1.
    reflexivity.
  - transitivity ((S x) * y0).
    + induction x.
      * simpl.
        rewrite <- H0.
        omega.
      * simpl.
        omega.
    + rewrite H.
      easy.
Qed.

Program Instance mult : Proper (le ++> le ++> le) (mult).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  induction H.
  - rewrite H0.
    reflexivity.
  - simpl.
    rewrite IHle.
    omega.
Qed.
(*
Program Instance pow_monotone_l : Proper (le ++> eq ++> le) (Nat.pow).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  rewrite H0.
  apply Nat.pow_le_mono_l.
  exact H.
Qed.

Program Instance pow_monotone_r : Proper (eq ++> le ++> le) (fun x y => (S x)^y).
Next Obligation.
Proof.
  unfold respectful.
  intros x y H x0 y0 H0.
  rewrite H.
  apply Nat.pow_le_mono_r.
  - omega.
  - exact H0.
Qed.

 *)

Proposition trans_le_lt_lt :
  forall x y z : nat, x <= y -> y < z -> x < z.
Proof.
  intros x y z ; omega.
Qed.

Tactic Notation (at level 2)
       "<=" constr(e) "{" tactic(t) "}" :=
  match goal with
  | [|- (le ?l ?r)] =>
    let Hre := fresh "Hrewrite" in (
      assert (le l e) as Hre by (t ; (try reflexivity))
      ; apply (transitivity Hre) || reflexivity
      ; clear Hre
      ; set_state CFL
    )
  | [|- (lt ?l ?r)] =>
    let Hre := fresh "Hrewrite" in (
      assert (le l e) as Hre by (t ; (try reflexivity))
      ; apply (trans_le_lt_lt l e r)
      ; [apply Hre | idtac]
      ; clear Hre
      ; set_state CFL
    )
  end.

Proposition trans_lt_le_lt :
  forall x y z : nat, x < y -> y <= z -> x < z.
Proof.
  intros x y z ; omega.
Qed.

Proposition trans_lt_le_le :
  forall x y z : nat, x < y -> y <= z -> x <= z.
Proof.
  intros x y z ; omega.
Qed.

Proposition trans_le_lt_le :
  forall x y z : nat, x <= y -> y < z -> x <= z.
Proof.
  intros x y z ; omega.
Qed.

Tactic Notation (at level 2)
       "<" constr(e) "{" tactic(t) "}" :=
  match goal with
  | [|- (lt ?l ?r)] =>
    let Hre := fresh "Hrewrite" in
    let Hre1 := fresh "Hn" in (
      assert (lt l e) as Hre by t   
      ; specialize trans_lt_le_lt as Hre1
      ; specialize (Hre1 l e r Hre)
      ; apply Hre1
      ; clear Hre
      ; clear Hre1
      ; set_state CFL
    )
  | [|- (le ?l ?r)] =>
    let Hre := fresh "Hrewrite" in (
      assert (lt l e) as Hre by (t ; (try reflexivity))
      ; apply (trans_lt_le_le l e r Hre)
      ; clear Hre
      ; set_state CFL
    )
  end.

Tactic Notation (at level 2)
       "<=" constr(e) "{" "by" uconstr(u) "}" :=
  match goal with
  | [|- (le ?l ?r)] =>
    let Hre := fresh "Hrewrite" in (
      (assert (le l e) as Hre by ((rewrite u + rewrite <- u + apply u) ; (try reflexivity))
       ; apply (transitivity Hre) || reflexivity
       ; clear Hre
       ; set_state CFL
      ) ||
      (assert (lt l e) as Hre by (rewrite u + rewrite <- u + apply u)
       ; apply (trans_lt_le_le l e r Hre)
       ; clear Hre
       ; set_state CFL
      )
    )
  end.

Tactic Notation (at level 2)
       "<" constr(e) "{" "by" uconstr(u) "}" :=
  match goal with
  | [|- (lt ?l ?r)] =>
    let Hre := fresh "Hrewrite" in (
      assert (lt l e) as Hre
        by ((rewrite u + rewrite <- u + apply u ) ; (try reflexivity))
      ; apply (trans_lt_le_lt l e r Hre) || reflexivity
      ; clear Hre
      ; set_state CFL
    )
  end.

Tactic Notation (at level 2)
       "<" constr(e) "{" "because" constr(w) "by" tactic(t)  "}" :=
  match goal with
  | [|- (lt ?l ?r)] =>
    let Hre := fresh "Hrewrite" in
    let Hre1 := fresh "Hrewrite1" in (
      assert (lt l e) as Hre by
          ( assert w as Hre1 by t
            ; (rewrite Hre1 || rewrite <- Hre1)
            ; (try reflexivity))
      ; apply (transitivity Hre)
      ; clear Hre
      ; set_state CFL
    )
  | [|- (le ?l ?r)] =>
    let Hre := fresh "Hrewrite" in
    let Hre1 := fresh "Hrewrite1" in (
      assert (lt l e) as Hre by
          ( assert w as Hre1 by t
            ; (rewrite Hre1 || rewrite <- Hre1)
            ; (try reflexivity))
      ; apply (trans_lt_le_le l e r Hre)
      ; [apply Hre1 |]
      ; clear Hre
      ; set_state CFL
    )
  end.

Tactic Notation (at level 2)
       "<=" constr(e) "{" "because" constr(w) "by" tactic(t)  "}" :=
  match goal with
  | [|- (le ?l ?r)] =>
    let Hre := fresh "Hrewrite" in
    let Hre1 := fresh "Hrewrite1" in (
      assert (le l e) as Hre by
          ( assert w as Hre1 by t
            ; (rewrite Hre1 + rewrite <- Hre1 + apply Hre1)
            ; (try reflexivity))
      ; apply (transitivity Hre) || reflexivity
      ; clear Hre
      ; set_state CFL
    )
  end.

Tactic Notation (at level 2)
       "@" ident(H1) ":" constr(t) :=
  match goal with
  | [ H : t |- _ ] =>
    match H with
    | H1 => idtac "Type Annotation:" ; idtac "OK, "H":"t"is in current environment."
    | _  => fail 2 "Type Annotation Error: No such identifier"H1"that is typed"t
    end
  | _ => fail 2 "Type Annotation Error: No such identifiers that is typed"t
  end.

Tactic Notation (at level 2)
       "@" "goal" ":" constr(t) :=
  match goal with
  | [ |- t ] => idtac "OK, current goal is"t
  | [ |- ?t1 ] => fail 2 "Current goal is not"t", but is"t1
  end.


Tactic Notation (at level 2)
       ">=" constr(e) "{" tactic(t) "}" :=
  match goal with
  | [_ : memo CFR |- (le ?l ?r)] =>
    let Hre := fresh "Hrewrite" in
    let Hre1 := fresh "Hn" in (
      assert (le e r) as Hre by ((t ; reflexivity) || t)
      ; specialize Nat.le_trans as Hre1
      ; specialize (Hre1 l e r)
      ; apply Hre1
      ; [idtac | apply Hre]
      ; clear Hre
      ; clear Hre1
      ; set_state CFR
    )
  end.

Tactic Notation (at level 2)
       ">=" constr(e) "{" "by" uconstr(ue) "}" :=
  match goal with
  | [_ : memo CFR |- (le ?l ?r)] =>
    let Hre := fresh "Hrewrite" in
    let Hre1 := fresh "Hn" in (
      assert (le e r) as Hre by ((rewrite ue || rewrite <- ue) ; reflexivity)
      ; specialize Nat.le_trans as Hre1
      ; specialize (Hre1 l e r)
      ; apply Hre1
      ; [idtac | apply Hre]
      ; clear Hre
      ; clear Hre1
      ; set_state CFR
    )
  | [_ : memo CFR |- (lt ?l ?r)] =>
    let Hre := fresh "Hrewrite" in
    let Hre1 := fresh "Hn" in (
      assert (le e r) as Hre by ((rewrite ue || rewrite <- ue) ; reflexivity)
      ; specialize trans_lt_le_lt as Hre1
      ; specialize (Hre1 l e r)
      ; apply Hre1
      ; [idtac | apply Hre]
      ; clear Hre
      ; clear Hre1
      ; set_state CFR
    )
  end.

Tactic Notation (at level 2)
       ">" constr(e) "{" tactic(t) "}" :=
  match goal with
  | [_ : memo CFR |- (lt ?l ?r)] =>
    let Hre := fresh "Hrewrite" in
    let Hre1 := fresh "Hn" in (
      assert (lt e r) as Hre by t
      ; specialize trans_le_lt_lt as Hre1
      ; specialize (Hre1 l e r)
      ; apply Hre1
      ; [idtac | apply Hre]
      ; clear Hre
      ; clear Hre1
      ; set_state CFR
    )
  end.

Tactic Notation (at level 2)
       ">" constr(e) "{" "by" uconstr(ue) "}" :=
  match goal with
  | [_ : memo CFR |- (lt ?l ?r)] =>
    let Hre := fresh "Hrewrite" in
    let Hre1 := fresh "Hn" in (
      assert (lt e r) as Hre by ( apply ue )
      ; specialize trans_le_lt_lt as Hre1
      ; specialize (Hre1 l e r)
      ; apply Hre1
      ; [idtac | apply Hre]
      ; clear Hre
      ; clear Hre1
      ; set_state CFR
    )
  end.