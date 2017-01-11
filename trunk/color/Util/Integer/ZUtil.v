(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-20
- Frederic Blanqui, 2005-02-25
- Adam Koprowski, 2008-01-30

useful definitions and lemmas about integers
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil.
From Coq Require Export ZArith.

(***********************************************************************)
(** decidability of equality *)

Local Open Scope positive_scope.

Fixpoint beq_pos x y :=
  match x, y with
    | xI x', xI y' => beq_pos x' y'
    | xO x', xO y' => beq_pos x' y'
    | xH, xH => true
    | _, _ => false
  end.

Lemma beq_pos_ok : forall x y, beq_pos x y = true <-> x = y.

Proof.
induction x; destruct y; simpl; intros; try (intuition; discr).
rewrite IHx. intuition. subst. refl. inversion H. refl.
rewrite IHx. intuition. subst. refl. inversion H. refl.
Qed.

Local Open Scope Z_scope.

Fixpoint beq_Z x y :=
  match x, y with
    | Z0, Z0 => true
    | Zpos x', Zpos y' => beq_pos x' y'
    | Zneg x', Zneg y' => beq_pos x' y'
    | _, _ => false
  end.

Lemma beq_Z_ok : forall x y, beq_Z x y = true <-> x = y.

Proof.
induction x; destruct y; simpl; intros; try (intuition; discr).
rewrite beq_pos_ok. intuition. subst. refl. inversion H. refl.
rewrite beq_pos_ok. intuition. subst. refl. inversion H. refl.
Qed.

(***********************************************************************)
(** simplification *)

Lemma zeql : forall x, 
  match x with
    | Z0 => 0
    | Zpos y' => Zpos y'
    | Zneg y' => Zneg y'
  end = x.

Proof. intro. destruct x; refl. Qed.

Lemma zeqr : forall x,
  x = match x with
        | Z0 => 0
        | Zpos y' => Zpos y'
        | Zneg y' => Zneg y'
      end.

Proof. intro. destruct x; refl. Qed.

(***********************************************************************)
(** inequalities *)

Lemma pos_lt : forall x y : Z, 0 <= y-x-1 -> x < y.

Proof. intros. omega. Qed.

Lemma pos_le : forall x y : Z, 0 <= y-x -> x <= y.

Proof. intros. omega. Qed.

(***********************************************************************)
(** power *)

Fixpoint power (x : Z) (n : nat) : Z :=
  match n with
    | O => 1
    | S n' => x * power x n'
  end.

Infix "^" := power.

Lemma power_plus : forall x n1 n2, power x (n1+n2) = power x n1 * power x n2.

Proof. induction n1; intros; simpl. apply zeqr. rewrite IHn1. ring. Qed.

Lemma power_one : forall n, power 1 n = 1.

Proof. induction n; simpl. refl. rewrite IHn. refl. Qed.

Lemma power_succ : forall x n, power x (S n) = x * power x n.

Proof. refl. Qed.

Lemma power_mult : forall x n1 n2, power x (n1*n2) = power (power x n1) n2.

Proof.
induction n1; induction n2; intros. refl. rewrite power_one. refl.
rewrite mult_0_r. refl. rewrite power_succ, <- IHn2, <- mult_n_Sm. simpl.
rewrite !power_plus. simpl. ring.
Qed.

Lemma pos_power : forall x n, 0 <= x -> 0 <= power x n.

Proof.
induction n; intros; simpl. omega. apply Zmult_le_0_compat. hyp.
apply IHn. hyp.
Qed.

Lemma spos_power : forall x n, 0 < x -> 0 < power x n.

Proof.
induction n; intros; simpl. omega. apply Zmult_lt_O_compat. hyp.
apply IHn. hyp.
Qed.

Lemma power_le_compat : forall x y n, 0<=x -> x<=y -> power x n <= power y n.

Proof.
induction n; intros; simpl. omega. apply Zmult_le_compat. hyp.
apply IHn; hyp. hyp. apply pos_power. hyp.
Qed.

(***********************************************************************)
(** positive integers *)

Definition is_pos z :=
  match z with
    | Zpos _ => true
    | _ => false
  end.

Lemma is_pos_ok : forall z, is_pos z = true <-> z > 0.

Proof. destruct z; simpl; intuition; discr. Qed.

(***********************************************************************)
(** non-negative integers *)

Definition is_not_neg z :=
  match z with
    | Zneg _ => false
    | _ => true
  end.

Lemma is_not_neg_ok : forall z, is_not_neg z = true <-> 0 <= z.

Proof. destruct z; simpl; intuition; discr. Qed.

Notation pos := (fun z => 0 <= z).
Notation D := (sig pos).
Notation val := (@proj1_sig Z pos).
Notation inj := (@exist Z pos _).

Lemma Zero_in_D : pos 0.

Proof. simpl. omega. Qed.

Notation D0 := (inj Zero_in_D).

Lemma pos_power_val : forall x n, pos (power (val x) n).

Proof. intros. destruct x. apply pos_power. hyp. Qed.

Definition Dlt x y := Zlt (val x) (val y).
Definition Dle x y := Zle (val x) (val y).

From CoLoR Require Import RelUtil.

Definition Dgt := transp Dlt.
Definition Dge := transp Dle.

From Coq Require Import Zwf Wellfounded.

Lemma well_founded_Dlt : well_founded Dlt.

Proof.
unfold Dlt. apply wf_incl with (R2 := (fun x y : D => Zwf 0 (val x) (val y))).
unfold inclusion, Zwf. intros (x,Hx) (y,Hy). simpl. intuition omega.
apply (wf_inverse_image D Z (Zwf 0) val). apply Zwf_well_founded.
Qed.

From CoLoR Require Import SN.

Lemma WF_Dgt : WF Dgt.

Proof. apply wf_transp_WF. apply well_founded_Dlt. Qed.

Lemma power_Dlt_compat : forall x y n,
  Dlt x y -> Dlt (inj (pos_power_val x (S n))) (inj (pos_power_val y (S n))).

Proof.
intros x y. destruct x. destruct y. unfold Dlt. simpl.
induction n; simpl; intros. omega. ded (IHn H).
apply Zle_lt_trans with (m := x * (x0 * power x0 n)). apply Zmult_le_compat_l.
omega. hyp. apply Zmult_gt_0_lt_compat_r. apply Zlt_gt.
apply Zmult_lt_O_compat. omega. apply spos_power. omega. hyp.
Qed.

Lemma trans_Dgt : transitive Dgt.

Proof. intros [x hx] [y hy] [z hz]. unfold Dgt, Dlt, transp. simpl. omega. Qed.

Lemma trans_Dge : transitive Dge.

Proof. intros [x hx] [y hy] [z hz]. unfold Dge, Dle, transp. simpl. omega. Qed.

Lemma refl_Dge : reflexive Dge.

Proof. intros [x hs]. unfold Dge, Dle, transp. simpl. refl. Qed.

(***********************************************************************)
(** max *)

Lemma Zmax_gub : forall m n k, m >= k -> n >= k -> Zmax m n >= k.

Proof. intros. apply Zmax_case; hyp. Qed.

Lemma elim_Zmax_l : forall x y z, x <= y -> x <= Zmax y z.

Proof. intros. eapply Zle_trans. apply H. apply Zle_max_l. Qed.

Lemma elim_lt_Zmax_l : forall x y z, x < y -> x < Zmax y z.

Proof. intros. eapply Zlt_le_trans. eexact H. apply Zle_max_l. Qed.

Lemma elim_Zmax_r : forall x y z, x <= z -> x <= Zmax y z.

Proof. intros. eapply Zle_trans. apply H. apply Zle_max_r. Qed.

Lemma elim_lt_Zmax_r : forall x y z, x < z -> x < Zmax y z.

Proof. intros. rewrite Zmax_comm. apply elim_lt_Zmax_l. hyp. Qed.

Lemma Zmax_l : forall x y, x >= y -> Zmax x y = x.

Proof.
intros. unfold Zmax. 
destruct (Dcompare_inf (x ?= y)) as [[xy | xy] | xy]; rewrite xy; try refl.
assert (x < y). hyp. omega.
Qed.

Lemma Zmax_r : forall x y, y >= x -> Zmax x y = y.

Proof. intros. rewrite Zmax_comm. apply Zmax_l. hyp. Qed.

Lemma Zmax_ge_compat : forall x y x' y',
  x >= x' -> y >= y' -> Zmax x y >= Zmax x' y'.

Proof.
intros. destruct (Zmax_irreducible_inf x' y'); rewrite e; unfold ge.
rewrite Zmax_comm. apply Zle_ge. apply elim_Zmax_r. omega.
apply Zle_ge. apply elim_Zmax_r. omega.
Qed.

Lemma Zmax_gt_compat : forall x y x' y',
  x > x' -> y > y' -> Zmax x y > Zmax x' y'.

Proof.
intros. destruct (Z_ge_dec x y); destruct (Z_ge_dec x' y');
  do 2 first 
    [ rewrite Zmax_r; [idtac | omega]
    | rewrite Zmax_l; [idtac | omega]
    | idtac ]; omega.
Qed.

(***********************************************************************)
(** orders *)

Lemma Zge_refl : forall k, k >= k.

Proof. intros. omega. Qed.
