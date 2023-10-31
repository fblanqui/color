(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-07
- Ducas Leo 2007-08-06

iteration of a relation
*)

Set Implicit Arguments.

From Coq Require Import List.
From CoLoR Require Import Path NatUtil RelUtil LogicUtil Log2.

Section S.

Variables (A : Type) (R : relation A).

Fixpoint iter (n : nat) : relation A :=
  match n with
    | O => R
    | S p => R @ iter p
  end.

(***********************************************************************)
(** properties *)

Lemma iter_tc : forall n, iter n << R!.

Proof.
induction n; intros; simpl. apply incl_tc. refl. unfold inclusion. intros.
do 2 destruct H. apply t_trans with x0. apply t_step. exact H.
apply IHn. exact H0.
Qed.

Lemma iter_iter : forall p q, iter p @ iter q << iter (p+q+1).

Proof.
induction p; simpl; intros. rewrite plus_1_S. simpl. refl.
assoc. comp. apply IHp.
Qed.

Lemma iter_plus_1 : forall p q, iter (p+q+1) << iter p @ iter q.

Proof.
induction p; simpl; intros. rewrite plus_1_S. simpl. refl.
incl_trans (R @ (iter p @ iter q)). comp. apply IHp. apply comp_assoc'.
Qed.

Lemma iter_commut : forall p q, iter p @ iter q << iter q @ iter p.

Proof.
intros. incl_trans (iter (p+q+1)). apply iter_iter.
assert (p+q+1 = q+p+1). lia.
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
exists (x0+x1+1). intuition. eapply incl_elim. apply iter_iter.
exists y. auto.
Qed.

Lemma Iter_split : forall n, Iter << iter_le n U Iter_ge (S n).

Proof.
induction n; simpl; intros; unfold inclusion; intros.
do 2 destruct H. destruct x0. left. auto.
right. exists (S x0). intuition.
ded (IHn _ _ H). destruct H0. left. right. exact H0.
do 2 destruct H0. case (le_lt_dec x0 (S n)); intro.
assert (x0 = S n). lia. subst x0. left. left. exact H1.
right. exists x0. intuition.
Qed.

Lemma Iter_ge_split : forall n, Iter_ge n << iter n U Iter_ge (S n).

Proof.
induction n; simpl; intros; unfold inclusion; intros; do 2 destruct H.
case (le_lt_dec x0 0); intro. assert (x0 = 0). lia. subst x0.
left. exact H0.
right. exists x0. intuition.
case (le_lt_dec x0 (S n)); intro. assert (x0 = S n). lia. subst x0.
left. exact H0.
right. exists x0. intuition.
Qed.

Lemma iter_Iter_ge_commut : forall n p,
  iter n @ Iter_ge p << Iter_ge p @ iter n.

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
(** Alternative definitions of iter_le *)

Fixpoint iter_le2 n :=
  match n with 
    | O => R
    | S i => (R @ iter_le2 i) U iter_le2 i 
  end.

Fixpoint iter_le_fast n :=
  match n with 
    | O => R
    | S i => let R' := iter_le_fast i in R' @ R' U R'
  end.

(***********************************************************************)
(** Equivalence between the different definitions *)

Lemma iter_le_spec : forall n x y,
  iter_le n x y <-> exists p, p <= n /\ iter p x y.

Proof.
intro; induction n.
intros; simpl in *.
split; intros. exists 0; split; auto with *.
destruct H as [p]; destruct H; assert(p=0); auto with *.
subst; auto with *. 
split; intros; simpl in *.
unfold compose in H; destruct H.
destruct H as [z]; exists (S n); split; auto with *.
simpl; unfold compose; exists z; hyp.

rewrite IHn in H; destruct H as [p]; exists p; intuition; auto with *.

destruct H as [p]; destruct H. destruct (le_lt_eq_dec H).
right; apply NatCompat.lt_n_Sm_le in l; rewrite IHn; exists p; auto with *.
subst; left; unfold compose in H0; auto with *.
Qed.

Lemma iter_le2_spec : forall n x y,
  iter_le2 n x y <-> exists p, p <= n /\ iter p x y.

Proof.
intro. induction n.
intros; simpl in *; split; intros. exists 0; split; auto with *.
destruct H as [p]; destruct H; assert(p=0); auto with *.
subst; auto with *. 
split; intros; simpl in *.

unfold compose in H; destruct H.
destruct H as [z]; destruct H; rewrite IHn in H0; destruct H0 as [p];
  exists (S p).
split; auto with *. simpl; unfold compose; exists z; intuition; auto with *.

rewrite IHn in H; destruct H as [p]; exists p; intuition; auto with *.

destruct H as [p]; destruct H.
destruct (le_lt_eq_dec H).
right; apply NatCompat.lt_n_Sm_le in l; rewrite IHn; exists p; auto with *.
subst; left; unfold compose in H0; auto with *.
simpl in H0; unfold compose in *; destruct H0 as [z]; exists z.
split; destruct H0; auto with *.
rewrite IHn; exists n; auto.
Qed.

Lemma iter_compose : forall p q, iter p @ iter q << iter (p+q+1).

Proof.
intros; induction p.
assert (S(q) = q+1); auto with *.
simpl; rewrite <- H; simpl; intuition.
unfold inclusion; intros.
simpl in H; repeat destruct H.
simpl; unfold compose.
exists x1; split; auto with *.
unfold inclusion in IHp; eapply IHp.
simpl; unfold compose.
exists x0; split; auto with *.
Qed.

Lemma iter_le_fast_spec : forall n x y,
  iter_le_fast n x y <-> exists p,(S p) <= exp2 n /\ iter p x y.

Proof.
intro. induction n.
intros; simpl in *; split; intros. exists 0; split; auto with *.
destruct H as [p]; destruct H; assert(p=0); auto with *.
subst; auto with *. split; intros; simpl in *.
destruct H. 
destruct H as [z]; destruct H. rewrite IHn in H0; rewrite IHn in H.
destruct H0 as [p]; destruct H as [p']; destruct H0; destruct H.
exists (p+p'+1). split. lia.
assert ((iter p' @ iter p) x y). unfold compose; exists z; auto with *.
assert (p+p'+1=p'+p+1); intuition.
rewrite H4; apply iter_compose; auto with *.
rewrite IHn in H; destruct H as [p]; exists p; intuition.
destruct H as [p]; destruct H; simpl in H.

destruct (le_gt_dec (S p) (exp2 n)).
right; rewrite IHn; exists p; split; auto with *.
assert(p = (exp2 n - 1) + (p - exp2 n) +1 ).
lia.
rewrite H1 in H0. ded (iter_plus_1 _ _ _ _ H0).
left; unfold compose in *; destruct H2 as [z]; destruct H2.
exists z; split; rewrite IHn.
exists (exp2 n -1); intuition; lia.
exists (p -exp2 n); intuition; lia. 
Qed.

Lemma iter_le_same n x y : iter_le2 n x y <-> iter_le n x y.

Proof. rewrite iter_le_spec, iter_le2_spec. tauto. Qed.

Lemma iter_le_fast_exp2_same n x y :
  iter_le_fast n x y <-> iter_le ((exp2 n)-1) x y.

Proof.
rewrite iter_le_spec, iter_le_fast_spec.
split; intro; destruct H as [p]; exists p; split_all; ded (exp2_pos n); lia.
Qed.

(***********************************************************************)
(** relation with paths *)

Lemma iter_path : forall n x y,
  iter n x y -> exists l, length l = n /\ path R x y l.

Proof.
induction n; simpl; intros. exists nil. intuition.
do 2 destruct H. ded (IHn _ _ H0). do 2 destruct H1. subst n.
exists (x0 :: x1). simpl. intuition.
Qed.

Lemma path_iter : forall l x y, path R x y l -> iter (length l) x y.

Proof.
induction l; simpl; intros. exact H. exists a. intuition.
Qed.

Lemma bpath_iter_le : forall n x y, bpath R n x y -> iter_le n x y.

Proof.
intro; induction n; intros; simpl in *.
inversion H; subst; destruct l; simpl in *; auto with *; inversion H0.
gen (bpath_Sn_n_or_Rn H); intros; destruct H0.
simpl in *; right; apply IHn; auto with *.
destruct H0 as [z]; destruct H0; ded (IHn _ _ H1).
simpl; rewrite iter_le_spec in *; destruct H2 as [p]; destruct H2.
destruct (le_lt_eq_dec H2).
right; rewrite iter_le_spec; exists (S p); intuition.
simpl; unfold compose; exists z; intuition.
left; subst; unfold compose; exists z; intuition.
Qed.

Lemma iter_le_bpath : forall n x y, iter_le n x y -> bpath R n x y .

Proof.
intros.
rewrite iter_le_spec in H; destruct H as [j]; destruct H.
ded (iter_path _ _ _ H0); destruct H1 as [l]; destruct H1.
eapply bp_intro; try ehyp; auto; subst; hyp.
Qed.

End S.

(***********************************************************************)
(** implicit arguments *)

Arguments iter_path [A R n x y] _.
Arguments path_iter [A R l x y] _.
