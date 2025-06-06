(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

Definition of log2 (floor) and exp2, and some equalities
*)

From Stdlib Require Import Lia PeanoNat.
From CoLoR Require Import LogicUtil NatCompat.

Lemma div2_le_n : forall n, Nat.div2 n <= n.

Proof.
cut (forall n, Nat.div2 n <= n /\ Nat.div2 (S n) <= S n).
intros H n; gen (H n); tauto.
induction n; auto.
inversion IHn; split; auto.
simpl. apply le_n_S. auto with arith.
Qed.

Inductive log2_prop : nat -> nat -> Prop :=
| log2_prop_O : log2_prop 0 0
| log2_prop_1 : log2_prop 1 0
| log2_prop_p : forall p q,
  p <> 0 -> p <> 1 -> log2_prop (Nat.div2 p) q -> log2_prop p (S q).

#[global] Hint Constructors log2_prop : core.

Fixpoint log2_aux n count : nat :=
  match count with
    | 0 => 0
    | S count' =>
      match n with
        | 0 => 0
        | 1 => 0
        | _ => S (log2_aux (Nat.div2 n) count')
      end
  end.

(* log2_aux is correct as soon as count >= n *)

Lemma log2_aux_matches : forall count n, n <= count ->
  log2_prop n (log2_aux n count).

Proof.
induction count.
 intros. assert (n = 0). auto with arith.
 subst. simpl. auto. intros n Hn.
destruct n.
 simpl; auto.
destruct n.
 simpl; auto.
simpl.
apply log2_prop_p.
 intro; discr.
 intro H; discr.
apply IHcount; eapply Nat.le_trans.
eapply le_n_S; apply div2_le_n.
apply le_S_n; hyp.
Qed.

Definition log2 n := log2_aux n n.

Lemma log2_matches : forall n, log2_prop n (log2 n).

Proof. unfold log2. intros. apply log2_aux_matches. auto with arith. Qed.

Lemma log2_prop_func : forall p q,
  log2_prop p q -> forall q', log2_prop p q' -> q = q'.

Proof.
induction 1.
 inversion 1.
 auto.
 congruence.
inversion 1.
 auto.
 congruence.
inversion 1.
 congruence.
 congruence.
 subst.
f_equal.
eapply IHlog2_prop; eauto.
Qed.

Lemma log2_matches_log2_prop : forall n p, log2_prop n p -> p = log2 n.

Proof. intros. eapply log2_prop_func. ehyp. apply log2_matches. Qed.

Fixpoint exp2 n :=
  match n with
    | O => 1
    | S i => 2 * exp2 i
  end.

Lemma double_div2 : forall n, S (2 * Nat.div2 n) >= n.

Proof.
intro n. destruct (Nat.Even_or_Odd n).
rewrite NatCompat.Even_double; [| exact H]; unfold Nat.double; lia.
rewrite NatCompat.Odd_double; auto; unfold Nat.double; lia.
Qed.

Lemma exp2_pos : forall n, exp2 n >0.

Proof. intro; induction n; simpl; auto with *. Qed.

Lemma exp2_log2_prop : forall n p, log2_prop n p -> exp2 (S p) > n.

Proof.
cut(forall n n' p, n'<=n -> log2_prop n' p -> exp2 (S p) > n').
intros. eapply H. assert (n<=n). lia. ehyp. hyp.
intro; induction n; intros. assert (n'=0). lia. subst. apply exp2_pos.
inversion H; auto.
subst; inversion H0. simpl; auto.
subst.
assert (exp2 (S q) > Nat.div2 (S n)).
apply IHn.
simpl; destruct n; auto with *.
assert (Nat.div2 n <= n); auto with *. apply div2_le_n.
hyp.
change (2*exp2 (S q) > S n).
gen(double_div2 (S n)); intro; lia.
Qed.

Lemma exp2_log2 : forall n, exp2(S (log2 n)) > n.

Proof. intro; apply exp2_log2_prop. apply log2_matches. Qed.
