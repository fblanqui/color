(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02
- Adam Koprowski, 2007-03-29, Added [mult_gt_0] and [mult_lt_compat_lr]


useful definitions and lemmas on natural numbers
*)

(* $Id: NatUtil.v,v 1.7 2007-03-29 11:05:40 koper Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export Arith.

Implicit Arguments lt_S_n [n m].
Implicit Arguments lt_n_S [n m].

(***********************************************************************)
(** unicity of eq/le/lt proofs *)

Scheme eq_ind_dep := Induction for eq Sort Prop.

Require Export Eqdep.

Implicit Arguments UIP_refl [U x].

Scheme le_ind_dep := Induction for le Sort Prop.

Lemma le_unique : forall n m (h1 h2 : le n m), h1 = h2.

Proof.
intro n.
assert (forall m : nat, forall h1 : le n m, forall p : nat, forall h2 : le n p,
  m=p -> eq_dep nat (le n) m h1 p h2).
 intros m h1; elim h1 using le_ind_dep.
  intros p h2; case h2; intros.
   auto.
   subst n. absurd (S m0 <= m0); auto with arith.
 intros m0 l Hrec p h2. 
  case h2; intros.
   subst n; absurd (S m0 <= m0); auto with arith.
   assert (m0=m1); auto ; subst m0.
   replace l0 with l; auto.
   apply (eq_dep_eq nat (le n)); auto.
 intros; apply (eq_dep_eq nat (le n)); auto.
Qed.

Lemma lt_unique : forall n m (h1 h2 : lt n m), h1 = h2.

Proof.
intros n m. unfold lt. intros. apply le_unique.
Qed.

Lemma eq_nat_dec_refl : forall n, eq_nat_dec n n = left (n<>n) (refl_equal n).

Proof.
induction n; simpl. reflexivity. rewrite IHn. reflexivity.
Qed.

(***********************************************************************)
(** max *)

Require Export Max.

Implicit Arguments max_r [n m].
Implicit Arguments max_l [n m].
Implicit Arguments le_trans [n m p].

Require Export Compare.

Lemma max_assoc : forall a b c, max a (max b c) = max (max a b) c.

Proof.
intros.
case (le_dec b c); intro H.
 rewrite (max_r H).
 case (le_dec a b); intro H'.
  rewrite (max_r (le_trans H' H)).
  rewrite (max_r H'). rewrite (max_r H). reflexivity.
  case (le_dec a c); intro H''; rewrite (max_l H'); reflexivity.
  rewrite (max_l H).
  case (le_dec a b); intro H'.
   rewrite (max_r H').
   apply (sym_equal (max_l H)).
   assert (H'' : c <= max a b). eapply le_trans. apply H. apply le_max_r.
   apply (sym_equal (max_l H'')).
Qed.

Lemma elim_max_l : forall x y z, x <= y -> x <= max y z.

Proof.
intros. eapply le_trans. apply H. apply le_max_l.
Qed.

Lemma elim_max_r : forall x y z, x <= z -> x <= max y z.

Proof.
intros. eapply le_trans. apply H. apply le_max_r.
Qed.

Lemma intro_max_l : forall x y z, max x y <= z -> x <= z.

Proof.
intros. eapply le_trans. 2: apply H. apply le_max_l.
Qed.

Lemma intro_max_r : forall x y z, max x y <= z -> y <= z.

Proof.
intros. eapply le_trans. 2: apply H. apply le_max_r.
Qed.

(***********************************************************************)
(** min *)

Require Export Min.

Lemma elim_min_l : forall x y z, x <= z -> min x y <= z.

Proof.
intros. eapply le_trans. apply le_min_l. exact H.
Qed.

Lemma elim_min_r : forall x y z, y <= z -> min x y <= z.

Proof.
intros. eapply le_trans. apply le_min_r. exact H.
Qed.

(***********************************************************************)
(** various arithmetical lemmas *)

Require Export Omega.

Lemma plus_minus : forall v p, v+p-p=v.

Proof.
intros. omega.
Qed.

Lemma minus_plus : forall v p, p<=v -> v-p+p=v.

Proof.
intros. omega.
Qed.

Implicit Arguments minus_plus [v p].

Lemma plus_1_S : forall n, n+1 = S n.

Proof.
intro. omega.
Qed.

Lemma lt_from_le : forall x y, 0 < y -> x <= y-1 -> x < y.

Proof.
intros. omega.
Qed.

Lemma le_from_lt : forall x y, x < y+1 -> x <= y.

Proof.
intros. omega.
Qed.

Lemma lt_pm : forall n k x, n < x -> x <= n+k -> x-n-1 < k.

Proof.
intros. omega.
Qed.

Implicit Arguments lt_pm [n k x].

Lemma le_plus : forall k l, k <= k+l.

Proof.
intros. omega.
Qed.

Lemma misc1 : forall x k, S k = x+2+k-x-1.

Proof.
intros. omega.
Qed.

Lemma misc2 : forall x k, k = x+2+k-(x+1)-1.

Proof.
intros. omega.
Qed.

Lemma mult_gt_0 : forall i j, i > 0 -> j > 0 -> i * j > 0.

Proof.
  destruct i; destruct j; intros; try solve [elimtype False; omega | simpl; auto with arith].
Qed.

Lemma mult_lt_compat_lr : forall i j k l, i <= j -> j > 0 -> k < l -> i * k < j * l.

Proof.
  destruct i; intros.
  rewrite mult_0_l. apply mult_gt_0. assumption.
  destruct l. elimtype False. omega. auto with arith.
  simpl. destruct j. elimtype False. omega.
  simpl. apply plus_lt_le_compat. assumption.
  apply mult_le_compat; omega. 
Qed.
