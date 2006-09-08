(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-20
- Frederic Blanqui, 2005-02-25

useful definitions and lemmas about integers
************************************************************************)

(* $Id: ZUtil.v,v 1.1.1.1 2006-09-08 09:07:00 blanqui Exp $ *)

Require Export LogicUtil.

Set Implicit Arguments.

Require Export ZArith.

Open Local Scope Z_scope.

(***********************************************************************)
(* simplification *)

Lemma zeql : forall x, match x with Z0 => 0 | Zpos y' => Zpos y'
  | Zneg y' => Zneg y' end = x.

Proof.
intro. destruct x; refl.
Qed.

Lemma zeqr : forall x, x = match x with Z0 => 0 | Zpos y' => Zpos y'
  | Zneg y' => Zneg y' end.

Proof.
intro. destruct x; refl.
Qed.

(***********************************************************************)
(* inequalities *)

Lemma pos_lt : forall x y : Z, 0 <= y-x-1 -> x < y.

Proof.
intros. omega.
Qed.

(***********************************************************************)
(* power *)

Fixpoint power (x : Z) (n : nat) {struct n} : Z :=
  match n with
    | O => 1
    | S n' => x * power x n'
  end.

Infix "^" := power.

Lemma power_plus : forall x n1 n2, power x (n1+n2) = power x n1 * power x n2.

Proof.
induction n1; intros; simpl. apply zeqr. rewrite IHn1. ring.
Qed.

Lemma power_one : forall n, power 1 n = 1.

Proof.
induction n; simpl. refl. rewrite IHn. refl.
Qed.

Lemma power_mult : forall x n1 n2, power x (n1*n2) = power (power x n1) n2.

Proof.
induction n1; induction n2; intros. refl. rewrite power_one. refl.
rewrite mult_0_r. refl. rewrite <- mult_n_Sm. rewrite power_plus. rewrite IHn2. ring.
Qed.

Lemma pos_power : forall x n, 0 <= x -> 0 <= power x n.

Proof.
induction n; intros; simpl. omega. apply Zmult_le_0_compat. assumption.
apply IHn. assumption.
Qed.

Lemma spos_power : forall x n, 0 < x -> 0 < power x n.

Proof.
induction n; intros; simpl. omega. apply Zmult_lt_O_compat. assumption.
apply IHn. assumption.
Qed.

Lemma power_le_compat : forall x y n, 0<=x -> x<=y -> power x n <= power y n.

Proof.
induction n; intros; simpl. omega. apply Zmult_le_compat. assumption.
apply IHn; assumption. assumption. apply pos_power. assumption.
Qed.

(***********************************************************************)
(* positive integers *)

Notation pos := (fun z => 0 <= z).
Notation D := (sig pos).
Notation val := (@proj1_sig Z pos).
Notation inj := (@exist Z pos _).

Lemma pos_power_val : forall x n, pos (power (val x) n).

Proof.
intros. destruct x. apply pos_power. assumption.
Qed.

Definition Dlt (x y : D) := Zlt (val x) (val y).
Definition Dle (x y : D) := Zle (val x) (val y).

Require Export Zwf.
Require Export Wellfounded.
Require Export Relations.

Lemma Dlt_wf : well_founded Dlt.

Proof.
unfold Dlt. apply wf_incl with (R2 := (fun x y : D => Zwf 0 (val x) (val y))).
unfold inclusion, Zwf. intros (x,Hx) (y,Hy). simpl. intuition omega.
apply (wf_inverse_image D Z (Zwf 0) val). apply Zwf_well_founded.
Qed.

Lemma power_Dlt_compat : forall x y n,
  Dlt x y -> Dlt (inj (pos_power_val x (S n))) (inj (pos_power_val y (S n))).

Proof.
intros x y. destruct x. destruct y. unfold Dlt. simpl.
induction n; simpl; intros. omega. deduce (IHn H).
apply Zle_lt_trans with (m := x * (x0 * power x0 n)). apply Zmult_le_compat_l.
omega. assumption. apply Zmult_gt_0_lt_compat_r. apply Zlt_gt.
apply Zmult_lt_O_compat. omega. apply spos_power. omega. assumption.
Qed.
