(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-07

iteration of a relation
*)

Set Implicit Arguments.

Require Export Path.
Require Export NatUtil.
Require Export RelUtil.

Section S.

Variables (A : Set) (R : relation A).

Fixpoint iter (n : nat) : relation A :=
  match n with
    | O => R
    | S p => R @ iter p
  end.

(***********************************************************************)
(** properties *)

Lemma iter_tc : forall n, iter n << R!.

Proof.
induction n; intros; simpl. apply tc_incl. unfold inclusion. intros.
do 2 destruct H. apply t_trans with x0. apply t_step. exact H.
apply IHn. exact H0.
Qed.

Lemma iter_iter : forall p q, iter p @ iter q << iter (p+q+1).

Proof.
induction p; simpl; intros. rewrite plus_1_S. simpl. apply incl_refl.
assoc. comp. apply IHp.
Qed.

Lemma iter_plus_1 : forall p q, iter (p+q+1) << iter p @ iter q.

Proof.
induction p; simpl; intros. rewrite plus_1_S. simpl. apply incl_refl.
trans (R @ (iter p @ iter q)). comp. apply IHp. apply comp_assoc'.
Qed.

Lemma iter_commut : forall p q, iter p @ iter q << iter q @ iter p.

Proof.
intros. trans (iter (p+q+1)). apply iter_iter. assert (p+q+1 = q+p+1). omega.
rewrite H. apply iter_plus_1.
Qed.

(***********************************************************************)
(** unions of iterated relations *)

Definition Iter_ge k x y := exists n, n >= k /\ iter n x y.

Definition Iter := Iter_ge 0.

Fixpoint iter_le (n : nat) : relation A :=
  match n with
    | O => R
    | S p => iter n U iter_le p
  end.

(***********************************************************************)
(** properties *)

Lemma tc_iter : R! << Iter.

Proof.
unfold inclusion. induction 1; simpl; intros. exists 0. auto.
destruct IHclos_trans1. destruct IHclos_trans2. intuition.
exists (x0+x1+1). intuition. eapply incl_elim. apply iter_iter. exists y. auto.
Qed.

Lemma Iter_split : forall n, Iter << iter_le n U Iter_ge (S n).

Proof.
induction n; simpl; intros; unfold inclusion; intros.
do 2 destruct H. destruct x0. left. auto.
right. exists (S x0). intuition.
deduce (IHn _ _ H). destruct H0. left. right. exact H0.
do 2 destruct H0. case (le_lt_dec x0 (S n)); intro.
assert (x0 = S n). omega. subst x0. left. left. exact H1.
right. exists x0. intuition.
Qed.

Lemma Iter_ge_split : forall n, Iter_ge n << iter n U Iter_ge (S n).

Proof.
induction n; simpl; intros; unfold inclusion; intros; do 2 destruct H.
case (le_lt_dec x0 0); intro. assert (x0 = 0). omega. subst x0.
left. exact H0.
right. exists x0. intuition.
case (le_lt_dec x0 (S n)); intro. assert (x0 = S n). omega. subst x0.
left. exact H0.
right. exists x0. intuition.
Qed.

Lemma iter_Iter_ge_commut : forall n p, iter n @ Iter_ge p << Iter_ge p @ iter n.

Proof.
unfold inclusion. intros. do 2 destruct H. do 2 destruct H0.
assert ((iter x1 @ iter n) x y). eapply incl_elim. apply iter_commut.
exists x0. intuition. do 2 destruct H2. exists x2. intuition.
exists x1. intuition.
Qed.

Lemma iter_Iter_ge : forall n p, iter n @ Iter_ge p << Iter_ge (n+p+1).

Proof.
unfold inclusion. intros. do 2 destruct H. do 2 destruct H0.
exists (n+x1+1). intuition. apply iter_iter. exists x0. intuition.
Qed.

Lemma incl_Iter_ge : forall n p, p <= n -> Iter_ge n << Iter_ge p.

Proof.
unfold inclusion. intros. do 2 destruct H0. exists x0. intuition.
Qed.

(***********************************************************************)
(** relation with paths *)

Lemma iter_path : forall n x y,
  iter n x y -> exists l, length l = n /\ path R x y l.

Proof.
induction n; simpl; intros. exists (@nil A). intuition.
do 2 destruct H. deduce (IHn _ _ H0). do 2 destruct H1. subst n.
exists (x0 :: x1). simpl. intuition.
Qed.

End S.

(***********************************************************************)
(** implicit arguments *)

Implicit Arguments iter_path [A R n x y].
