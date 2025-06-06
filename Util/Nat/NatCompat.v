From Stdlib Require Import Arith.PeanoNat.
(***********************************************************************)
(** Adapt to the removal of some Arith files in 8.19:
    unidirectional version better suited to implicit arguments.
    WARNING: we want these to shadow some eventual remnants in Arith, so until
    Coq 8.19, one needs to be careful to Require NatUtil **after** Coq.Arith
    or to qualify these with NatUtil.
*)

Lemma lt_S_n : forall n m : nat, S n < S m -> n < m.
Proof. intros n m; now apply Nat.succ_lt_mono. Qed.

Lemma lt_n_S : forall n m : nat, n < m -> S n < S m.
Proof. intros n m; now apply Nat.succ_lt_mono. Qed.

Lemma gt_le_S : forall n m : nat, m > n -> S n <= m.
Proof. intros n m; now apply Nat.le_succ_l. Qed.

Lemma le_lt_n_Sm : forall n m : nat, n <= m -> n < S m.
Proof. intros n m; now apply Nat.lt_succ_r. Qed.

Lemma le_plus_minus : forall n m : nat, n <= m -> m = n + (m - n).
Proof. intros n m H; now rewrite Nat.add_comm, Nat.sub_add. Qed.

Lemma le_plus_minus_r : forall n m : nat, n <= m -> n + (m - n) = m.
Proof. intros n m H; now rewrite Nat.add_comm, Nat.sub_add. Qed.

Lemma le_lt_or_eq : forall n m : nat, n <= m -> n < m \/ n = m.
Proof. intros n m H; now apply Nat.lt_eq_cases. Qed.

Lemma lt_n_Sm_le : forall n m : nat, n < S m -> n <= m.
Proof. intros n m H; now apply Nat.lt_succ_r. Qed.

Lemma lt_le_S : forall n m : nat, n < m -> S n <= m.
Proof. intros n m H; now apply Nat.le_succ_l. Qed.

Lemma lt_not_le : forall n m : nat, n < m -> ~ m <= n.
Proof. intros n m H; now apply Nat.lt_nge. Qed.

Lemma le_not_lt : forall n m : nat, n <= m -> ~ m < n.
Proof. intros n m H; now apply Nat.le_ngt. Qed.

(* Other compatibility lemmas (not needed after 8.17 *)

(* NOTE: needed because Nat.le_add_l was only introduced in Coq 8.17 (see
 * Coq.Numbers.Natural.Abstract.NAddOrder). This can go away and be replaced
 * by Nat.le_add_r once the minimal Coq supported version is >= 8.17. *)
Lemma le_add_l : forall n m : nat, n <= m + n.
Proof.
  intros n m. rewrite <-(Nat.add_0_l n) at 1. apply Nat.add_le_mono.
  - exact (Nat.le_0_l m).
  - exact (Nat.le_refl n).
Qed.

(* NOTE: When the minimal supported Coq version is >= 8.16,
   remove it and rename NatUtil.Even_double into Nat.Even_double *)
Lemma Even_double : forall n : nat, Nat.Even n -> n = Nat.double (Nat.div2 n).
Proof. now intros n [k ->]; rewrite Nat.double_twice, Nat.div2_double. Qed.

(* NOTE: When the minimal supported Coq version is >= 8.16,
   remove it and rename NatUtil.Odd_double into Nat.Odd_double *)
Lemma Odd_double : forall n : nat, Nat.Odd n -> n = S (Nat.double (Nat.div2 n)).
Proof.
  intros n [k ->].
  now rewrite Nat.add_1_r, Nat.div2_succ_double, Nat.double_twice.
Qed.

(* NOTE: When the minimal supported Coq version is >= 8.16,
   remove it and rename NatUtil.Odd_double into Nat.Odd_double *)
Lemma Even_div2 : forall n : nat, Nat.Even n -> Nat.div2 n = Nat.div2 (S n).
Proof. now intros n [k ->]; rewrite Nat.div2_double, Nat.div2_succ_double. Qed.

(* NOTE: When the minimal supported Coq version is >= 8.16,
   remove it and rename NatUtil.Odd_div2 into Nat.Odd_div2 *)
Lemma Odd_div2 : forall n : nat, Nat.Odd n -> S (Nat.div2 n) = Nat.div2 (S n).
Proof.
  intros n [k ->]; rewrite Nat.add_1_r, Nat.div2_succ_double.
  rewrite <-(Nat.add_1_r (S (2 * k))), (Nat.add_succ_comm (2 * k)).
  rewrite <-(Nat.mul_1_r 2) at 2.
  rewrite <-(Nat.mul_add_distr_l 2), Nat.add_succ_r.
  now rewrite Nat.add_0_r, Nat.div2_double.
Qed.
