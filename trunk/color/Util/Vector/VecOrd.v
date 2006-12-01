(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-01-24

symmetric product on vectors
************************************************************************)

(* $Id: VecOrd.v,v 1.2 2006-12-01 09:37:48 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export VecUtil.

Section S.

Variables (A : Set) (ltA : A->A->Prop).

Notation vec := (vector A).

Infix "<A" := ltA (at level 70).

(* product ordering *)

Require Export Relations.

Implicit Arguments symprod [A B].

Fixpoint Vlt_prod n : vec n -> vec n -> Prop :=
  match n as n return vec n -> vec n -> Prop with
    | O => fun _ _ => False
    | S n => fun v1 v2 => symprod ltA (@Vlt_prod n) (Vsplit v1) (Vsplit v2)
  end.

Infix "<prod" := Vlt_prod (at level 70).

Lemma Vlt_prod_lt : forall n (v1 v2 : vec n), v1 <prod v2 -> exists i,
  exists vi : vec i, exists x, exists j, exists vj : vec j, exists h, exists y,
  v1 = Vcast (Vapp vi (Vcons x vj)) h /\ v2 = Vcast (Vapp vi (Vcons y vj)) h
  /\ x <A y.

Proof.
induction v1; simpl. intros. contradiction. intro. VSntac v2.
unfold Vsplit. simpl. intro. inversion H0.
exists 0. exists (@Vnil A). exists a. exists n. exists (Vtail v2).
exists (refl_equal (S n)). exists (Vhead v2). split. rewrite Vcast_refl. refl.
split. rewrite Vcast_refl. refl. assumption.
deduce (IHv1 (Vtail v2) H2). do 8 destruct H6. destruct H7. rewrite H6.
rewrite H7.
exists (S x0). exists (Vcons (Vhead v2) x1). exists x2.
exists x3. exists x4. assert (S x0 + S x3 = S n). omega. exists H9. exists x6.
simpl. intuition. apply Vcons_eq_tail. apply Vcast_eq.
apply Vcons_eq_tail. apply Vcast_eq.
Qed.

Lemma Vlt_prod_cons : forall x1 x2 n (v1 v2 : vec n),
  (x1 <A x2 /\ v1 = v2) \/ (x1 = x2 /\ v1 <prod v2)
  -> Vcons x1 v1 <prod Vcons x2 v2.

Proof.
intros. simpl. unfold Vsplit. simpl. destruct H; destruct H.
subst v2. apply left_sym. assumption.
subst x2. apply right_sym. assumption.
Qed.

Lemma Vlt_prod_inv : forall x1 x2 n (v1 v2 : vec n),
  Vcons x1 v1 <prod Vcons x2 v2 ->
  (x1 <A x2 /\ v1 = v2) \/ (x1 = x2 /\ v1 <prod v2).

Proof.
intros. simpl in H. unfold Vsplit in H. simpl in H. inversion H.
left. auto. right. auto.
Qed.

Lemma Vlt_prod_app : forall n (v : vec n) m (v1 v2 : vec m),
  v1 <prod v2 -> Vapp v v1 <prod Vapp v v2.

Proof.
induction v; intros. assumption.
simpl. unfold Vsplit. simpl. apply right_sym. apply IHv. assumption.
Qed.

Lemma Vlt_prod_cast : forall m n (h : m=n) (v1 v2 : vec m),
  v1 <prod v2 -> Vcast v1 h <prod Vcast v2 h.

Proof.
induction v1; intros; destruct n; intros.
contradiction. discriminate. discriminate.
assert (n0 = n). apply eq_add_S. assumption. subst n0.
assert (h = refl_equal (S n)). apply UIP. subst h.
rewrite (Vcast_refl_eq (Vcons a v1)). rewrite (Vcast_refl_eq v2). assumption.
Qed.

Lemma Vlt_prod_cast_inv : forall m n (h : m=n) (v1 v2 : vec m),
  Vcast v1 h <prod Vcast v2 h -> v1 <prod v2.

Proof.
induction m; destruct n; intros.
assert (h = refl_equal 0). apply UIP. subst h. contradiction.
discriminate. discriminate.
assert (v1 = Vcons (Vhead v1) (Vtail v1)). apply VSn_eq. rewrite H0.
assert (v2 = Vcons (Vhead v2) (Vtail v2)). apply VSn_eq. rewrite H1.
rewrite H0 in H. rewrite H1 in H. simpl in H. unfold Vsplit in H. simpl in H.
apply Vlt_prod_cons. inversion H. left. split. assumption.
eapply Vcast_eq_intro with (m := n). apply H6.
right. split. reflexivity. eapply IHm with (n := n). apply H3.
Qed.

Require Export Wellfounded.

Lemma Vforall_Acc_lt_prod : forall n (v : vec n),
  Vforall (Acc ltA) v -> Acc (@Vlt_prod n) v.

Proof.
induction v; intros; apply Acc_intro; intros. contradiction.
simpl. eapply Acc_inverse_image with (R := symprod ltA (@Vlt_prod n)).
VSntac y. unfold Vsplit. simpl. simpl in H. destruct H.
rewrite H1 in H0. inversion H0.
apply Acc_symprod. eapply Acc_inv. apply H. assumption.
rewrite H7. apply IHv. assumption.
apply Acc_symprod. rewrite H6. assumption.
eapply Acc_inv. apply IHv. apply H2. assumption.
Qed.

Lemma Acc_lt_prod_Sn_head : forall n (v : vec (S n)),
  Acc (@Vlt_prod (S n)) v -> Acc ltA (Vhead v).

Proof.
induction 1. VSntac x. apply Acc_intro. intros.
deduce (H0 (Vcons y (Vtail x))). apply H3. rewrite H1. simpl.
unfold Vsplit. simpl. apply left_sym. assumption.
Qed.

Lemma Acc_lt_prod_head : forall a n (v : vec n),
  Acc (@Vlt_prod (S n)) (Vcons a v) -> Acc ltA a.

Proof.
intros. deduce (Acc_lt_prod_Sn_head H). assumption.
Qed.

Lemma Acc_lt_prod_Sn_tail : forall n (v : vec (S n)),
  Acc (@Vlt_prod (S n)) v -> Acc (@Vlt_prod n) (Vtail v).

Proof.
induction 1. VSntac x. apply Acc_intro. intros.
deduce (H0 (Vcons (Vhead x) y)). rewrite H1 in H3. apply H3.
simpl. unfold Vsplit. simpl. apply right_sym. assumption.
Qed.

Lemma Acc_lt_prod_tail : forall a n (v : vec n),
  Acc (@Vlt_prod (S n)) (Vcons a v) -> Acc (@Vlt_prod n) v.

Proof.
intros. deduce (Acc_lt_prod_Sn_tail H). assumption.
Qed.

Lemma Acc_lt_prod_forall : forall n (v : vec n),
  Acc (@Vlt_prod n) v -> Vforall (Acc ltA) v.

Proof.
induction v; intros; simpl. exact I. split.
apply (Acc_lt_prod_head H). apply IHv. apply (Acc_lt_prod_tail H).
Qed.

End S.

Implicit Arguments Vlt_prod_lt [A ltA n v1 v2].
