(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-01-24

orderings on vectors
*)

Set Implicit Arguments.

Require Import LogicUtil VecUtil RelUtil NatUtil RelMidex Syntax.

Implicit Arguments symprod [A B].

(***********************************************************************)
(** Component-wise extension to vectors on [A] of a relation on [A]. *)

Fixpoint Vgt_prod n A (R : relation A) : relation (vector A n) :=
  match n with
    | O => fun _ _ => False
    | S n => fun v1 v2 => symprod R (Vgt_prod R) (Vsplit v1) (Vsplit v2)
  end.

Definition Vgt_prod_alt n A (R : relation A) (v1 v2 : vector A n) :=
  exists i (vi : vector A i) x j (vj : vector A j) h y,
    v1 = Vcast (Vapp vi (Vcons x vj)) h
    /\ v2 = Vcast (Vapp vi (Vcons y vj)) h /\ R x y.

Section S.

  Variable A : Type. Notation vec := (vector A).

  Variable R : relation A. Infix ">" := R (at level 70).

  Notation prod := (Vgt_prod R). Infix ">prod" := (Vgt_prod R) (at level 70).

  Lemma Vgt_prod_gt : forall n (v1 v2 : vec n), v1 >prod v2 ->
    exists i (vi : vec i) x j (vj : vec j) h y,
      v1 = Vcast (Vapp vi (Vcons x vj)) h
      /\ v2 = Vcast (Vapp vi (Vcons y vj)) h /\ x > y.

  Proof.
    induction v1; simpl. intros. contr. intro. VSntac v2.
    unfold Vsplit. simpl. intro. inversion H0.
    exists 0 (@Vnil A) h. exists n (Vtail v2) (refl_equal (S n)) (Vhead v2).
    split. rewrite Vcast_refl. refl.
    split. rewrite Vcast_refl. refl. hyp.
    ded (IHv1 (Vtail v2) H2). do 8 destruct H6. destruct H7. rewrite H6, H7.
    exists (S x0) (Vcons (Vhead v2) x1) x2. exists x3 x4.
    assert (S x0 + S x3 = S n). omega. exists H9 x6.
    simpl. intuition. apply Vtail_eq. apply Vcast_pi.
    apply Vtail_eq. apply Vcast_pi.
  Qed.

  Lemma Vgt_prod_cons : forall x1 x2 n (v1 v2 : vec n),
    (x1 > x2 /\ v1 = v2) \/ (x1 = x2 /\ v1 >prod v2)
    -> Vcons x1 v1 >prod Vcons x2 v2.

  Proof.
    intros. simpl. unfold Vsplit. simpl. destruct H; destruct H.
    subst v2. apply left_sym. hyp.
    subst x2. apply right_sym. hyp.
  Qed.

  Lemma Vgt_prod_inv : forall x1 x2 n (v1 v2 : vec n),
    Vcons x1 v1 >prod Vcons x2 v2 ->
    (x1 > x2 /\ v1 = v2) \/ (x1 = x2 /\ v1 >prod v2).

  Proof.
    intros. simpl in H. unfold Vsplit in H. simpl in H. inversion H.
    left. auto. right. auto.
  Qed.

  Lemma Vgt_prod_add : forall x1 x2 n (v1 v2 : vec n),
    (x1 > x2 /\ v1 = v2) \/ (x1 = x2 /\ v1 >prod v2)
    -> Vadd v1 x1 >prod Vadd v2 x2.

  Proof.
    intros x1 x2. induction n; intros v1 v2.
    VOtac. intuition. apply left_sym. hyp.
    VSntac v1; VSntac v2. simpl Vadd. intros [[h1 h2]|[h1 h2]].
    Veqtac. apply Vgt_prod_cons. right. fo.
    subst x2. destruct (Vgt_prod_inv h2) as [[i1 i2]|[i1 i2]].
    rewrite i2. apply Vgt_prod_cons. left. fo.
    apply Vgt_prod_cons. right. fo.
  Qed.

  Lemma Vgt_prod_app : forall n (v : vec n) m (v1 v2 : vec m),
    v1 >prod v2 -> Vapp v v1 >prod Vapp v v2.

  Proof.
    induction v; intros. hyp.
    simpl. unfold Vsplit. simpl. apply right_sym. apply IHv. hyp.
  Qed.

  Lemma Vgt_prod_iff : forall n (v1 v2 : vec n), v1 >prod v2 <->
    exists i (vi : vec i) x j (vj : vec j) h y,
      v1 = Vcast (Vapp vi (Vcons x vj)) h
      /\ v2 = Vcast (Vapp vi (Vcons y vj)) h /\ x > y.

  Proof.
    intros n v1 v2. split. apply Vgt_prod_gt.
    intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]]; subst.
    rewrite 2!Vcast_refl. apply Vgt_prod_app. apply Vgt_prod_cons. fo.
  Qed.

  Lemma Vgt_prod_eq n : @Vgt_prod n _ R == @Vgt_prod_alt n _ R.

  Proof. rewrite rel_eq. apply Vgt_prod_iff. Qed.

  Lemma Vgt_prod_cast : forall m n (h : m=n) (v1 v2 : vec m),
    v1 >prod v2 -> Vcast v1 h >prod Vcast v2 h.

  Proof.
    induction v1; intros; destruct n; intros.
    contr. discr. discr.
    assert (n0 = n). apply eq_add_S. hyp. subst n0.
    assert (h = refl_equal (S n)). apply eq_unique. subst h.
    rewrite (Vcast_refl (Vcons h0 v1)). rewrite (Vcast_refl v2). hyp.
  Qed.

  Lemma Vgt_prod_cast_inv : forall m n (h : m=n) (v1 v2 : vec m),
    Vcast v1 h >prod Vcast v2 h -> v1 >prod v2.

  Proof.
    induction m; destruct n; intros.
    assert (h = refl_equal 0). apply eq_unique. subst h. contr.
    discr. discr.
    assert (v1 = Vcons (Vhead v1) (Vtail v1)). apply VSn_eq. rewrite H0.
    assert (v2 = Vcons (Vhead v2) (Vtail v2)). apply VSn_eq. rewrite H1.
    rewrite H0, H1 in H. simpl in H. unfold Vsplit in H. simpl in H.
    apply Vgt_prod_cons. inversion H. left. split. hyp.
    eapply Vcast_eq_elim with (m := n). apply H6.
    right. split. refl. eapply IHm with (n := n). apply H3.
  Qed.

  Require Import SN.

  Lemma Vforall_SN_gt_prod : forall n (v : vec n),
    Vforall (SN R) v -> SN (Vgt_prod R) v.

  Proof.
    induction v; intros; apply SN_intro; intros. contr. simpl.
    eapply SN_inverse with (f := @Vsplit A n) (R := symprod R (Vgt_prod R)).
    VSntac y. unfold Vsplit. simpl. simpl in H. destruct H.
    rewrite H1 in H0. inversion H0.
    apply SN_symprod. eapply SN_inv. apply H. hyp.
    rewrite <- H7. apply IHv. hyp.
    apply SN_symprod. rewrite <- H6. hyp.
    eapply SN_inv. apply IHv. apply H2. hyp.
  Qed.

  Lemma SN_gt_prod_Sn_head : forall n (v : vec (S n)),
    SN (Vgt_prod R) v -> SN R (Vhead v).

  Proof.
    induction 1. VSntac x. apply SN_intro. intros.
    ded (H0 (Vcons y (Vtail x))). apply H3. rewrite H1. simpl.
    unfold Vsplit. simpl. apply left_sym. hyp.
  Qed.

  Lemma SN_gt_prod_head : forall a n (v : vec n),
    SN (Vgt_prod R) (Vcons a v) -> SN R a.

  Proof. intros. ded (SN_gt_prod_Sn_head H). hyp. Qed.

  Lemma SN_gt_prod_Sn_tail : forall n (v : vec (S n)),
    SN (Vgt_prod R) v -> SN (Vgt_prod R) (Vtail v).

  Proof.
    induction 1. VSntac x. apply SN_intro. intros.
    ded (H0 (Vcons (Vhead x) y)). rewrite H1 in H3. apply H3.
    simpl. unfold Vsplit. simpl. apply right_sym. hyp.
  Qed.

  Lemma SN_gt_prod_tail : forall a n (v : vec n),
    SN (Vgt_prod R) (Vcons a v) -> SN (Vgt_prod R) v.

  Proof. intros. ded (SN_gt_prod_Sn_tail H). hyp. Qed.

  Lemma SN_gt_prod_forall : forall n (v : vec n),
    SN (Vgt_prod R) v -> Vforall (SN R) v.

  Proof.
    induction v; intros; simpl. exact I. split.
    apply (SN_gt_prod_head H). apply IHv. apply (SN_gt_prod_tail H).
  Qed.

(***********************************************************************)
(** Product ordering on vectors. *)

  Notation ge := @R.

  Definition vec_ge := Vforall2n ge.

  Infix ">=v" := vec_ge (at level 70).

  Lemma vec_tail_ge : forall n (v v' : vec (S n)),
    v >=v v' -> Vtail v >=v Vtail v'.

  Proof. intros. unfold vec_ge. apply Vforall2n_tail. hyp. Qed.

  Lemma vec_ge_refl : reflexive ge -> forall n, reflexive (@vec_ge n).

  Proof. intros ge_refl n x. unfold vec_ge. apply Vforall2n_intro. auto. Qed.

  Lemma vec_ge_trans : transitive ge -> forall n, transitive (@vec_ge n).

  Proof.
    intros ge_trans n x y z xy yz. unfold vec_ge. apply Vforall2n_intro. intros.
    apply ge_trans with (Vnth y ip); apply Vforall2n_nth; hyp.
  Qed.

  Variable ge_dec : forall x y, {ge x y}+{~ge x y}.

  Lemma vec_ge_dec : forall n, rel_dec (@vec_ge n).

  Proof. intros n P Q. destruct (Vforall2n_dec ge_dec P Q); intuition. Defined.

End S.

Implicit Arguments Vgt_prod_gt [A R n v1 v2].
Implicit Arguments vec_ge_dec [A R n].

(***********************************************************************)
(** Compatibility of [Vgt_prod] with [same_relation]. *)

Require Import Morphisms.

Instance Vgt_prod_alt_same_rel n A :
  Proper (same_relation ==> same_relation) (@Vgt_prod_alt n A).

Proof.
  intros R R' RR'. rewrite rel_eq. intros v1 v2. unfold Vgt_prod_alt.
  split; intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
    exists i vi x; exists j vj h; exists y; fo.
Qed.

Instance Vgt_prod_same_rel n A :
  Proper (same_relation ==> same_relation) (@Vgt_prod n A).

Proof.
  intros R R' RR'. rewrite 2!Vgt_prod_eq. apply Vgt_prod_alt_same_rel. hyp.
Qed.
