(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-01-24


* Component-wise extension of a relation to vectors and product ordering
*)

Set Implicit Arguments.

Require Import LogicUtil VecUtil RelUtil NatUtil RelMidex Syntax.

Arguments symprod [A B] _ _ _ _.

(***********************************************************************)
(** * Component-wise extension to vectors on [A] of a relation on [A]. *)

Fixpoint Vgt_prod n A (R : relation A) : relation (vector A n) :=
  match n with
    | O => fun _ _ => False
    | S n => fun v1 v2 => symprod R (Vgt_prod R) (Vsplit v1) (Vsplit v2)
  end.

Definition Vgt_prod1 n A (R : relation A) : relation (vector A n) :=
  fun v1 v2 : vector A n =>
    exists i (vi : vector A i) x j (vj : vector A j) h y,
      v1 = Vcast (Vapp vi (Vcons x vj)) h
      /\ v2 = Vcast (Vapp vi (Vcons y vj)) h /\ R x y.

Definition Vgt_prod2 n A (R : relation A) : relation (vector A n) :=
  fun v1 v2 : vector A n =>
    exists i (hi : i<n), R (Vnth v1 hi) (Vnth v2 hi)
      /\ forall j (hj : j<n), j <> i -> Vnth v1 hj = Vnth v2 hj.

(***********************************************************************)
(** Properties of [Vgt_prod]. *)

Section S.

  Variable A : Type. Notation vec := (vector A).

  Variable R : relation A. Infix ">" := R (at level 70).

  Infix ">prod" := (Vgt_prod R) (at level 70).

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

(***********************************************************************)
(** Equivalence between [Vgt_prod] and [Vgt_prod1]. *)

  Lemma Vgt_prod_impl1 : forall n (v1 v2 : vec n),
    v1 >prod v2 -> Vgt_prod1 R v1 v2.

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

  Lemma Vgt_prod_iff1 : forall n (v1 v2 : vec n),
    v1 >prod v2 <-> Vgt_prod1 R v1 v2.

  Proof.
    intros n v1 v2. split. apply Vgt_prod_impl1.
    intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]]; subst.
    rewrite 2!Vcast_refl. apply Vgt_prod_app. apply Vgt_prod_cons. fo.
  Qed.

  Lemma Vgt_prod_eq1 n : @Vgt_prod n _ R == @Vgt_prod1 n _ R.

  Proof. rewrite rel_eq. apply Vgt_prod_iff1. Qed.

(***********************************************************************)
(** Equivalence between [Vgt_prod] and [Vgt_prod2]. *)

  Lemma Vgt_prod_iff2 : forall n (v1 v2 : vec n),
    v1 >prod v2 <-> Vgt_prod2 R v1 v2.

  Proof.
    intros n v1 v2. rewrite Vgt_prod_iff1. split.

    intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
      subst; rewrite !Vcast_refl.
    exists i. assert (hi : i<i+S j). omega. exists hi.
    rewrite !Vnth_app_cons. intuition.
    rewrite !Vnth_app. destruct (le_gt_dec i j0). 2: refl.
    rewrite !Vnth_cons. destruct (lt_ge_dec 0 (j0-i)). 2: omega.
    apply Vnth_eq. refl.

    intros [i [hi [i1 i2]]].
    assert (ki : 0+i<=n). omega. exists i (Vsub v1 ki) (Vnth v1 hi).
    assert (kj : S i+(n-i-1)<=n). omega. exists (n-i-1) (Vsub v1 kj).
    assert (k : i+S(n-i-1)=n). omega. exists k (Vnth v2 hi).
    split; [idtac|split;[idtac|hyp]].

    apply Veq_nth. intros j hj. rewrite Vnth_cast, Vnth_app.
    destruct (le_gt_dec i j). rewrite Vnth_cons. destruct (lt_ge_dec 0 (j-i)).
    rewrite Vnth_sub. apply Vnth_eq. omega.
    apply Vnth_eq. omega.
    rewrite Vnth_sub. apply Vnth_eq. refl.

    apply Veq_nth. intros j hj. rewrite Vnth_cast, Vnth_app.
    destruct (le_gt_dec i j). rewrite Vnth_cons. destruct (lt_ge_dec 0 (j-i)).
    rewrite Vnth_sub.
    trans (Vnth v1 hj). sym. apply i2. omega. apply Vnth_eq. omega.
    apply Vnth_eq. omega.
    rewrite Vnth_sub.
    trans (Vnth v1 hj). sym. apply i2. omega. apply Vnth_eq. refl.
  Qed.

  Lemma Vgt_prod_sub : forall n (v1 v2 : vec n) p q (h : p+q<=n),
    v1 >prod v2 -> (Vgt_prod R)% (Vsub v1 h) (Vsub v2 h).

  Proof.
    intros n v1 v2 p q k. rewrite Vgt_prod_iff2.
    intros [i [hi [i1 i2]]]. destruct (lt_dec i p).
    left. apply Veq_nth. intros j hj. rewrite !Vnth_sub. apply i2. omega.
    destruct (ge_dec i (p+q)).
    left. apply Veq_nth. intros j hj. rewrite !Vnth_sub. apply i2. omega.
    right. rewrite Vgt_prod_iff2.
    exists (i-p). assert (l : i-p<q). omega. exists l. split.
    rewrite !Vnth_sub. erewrite Vnth_eq, Vnth_eq with (v:=v2). apply i1.
    omega. omega.
    intros j hj m. rewrite !Vnth_sub. apply i2. omega.
  Qed.

(***********************************************************************)
(** Properties of [Vgt_prod] wrt termination. *)

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

End S.

Arguments Vgt_prod_impl1 [A R n v1 v2] _.
Arguments Vgt_prod_sub [A R n v1 v2 p q] h _.

(***********************************************************************)
(** Compatibility of [Vgt_prod] with [same_relation]. *)

Require Import Morphisms.

Instance Vgt_prod1_same_rel n A :
  Proper (same_relation ==> same_relation) (@Vgt_prod1 n A).

Proof.
  intros R R' RR'. rewrite rel_eq. intros v1 v2. unfold Vgt_prod.
  split; intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
    exists i vi x; exists j vj h; exists y; fo.
Qed.

Instance Vgt_prod_same_rel n A :
  Proper (same_relation ==> same_relation) (@Vgt_prod n A).

Proof.
  intros R R' RR'. rewrite 2!Vgt_prod_eq1. apply Vgt_prod1_same_rel. hyp.
Qed.

(***********************************************************************)
(** Distributivity of [Vgt_prod] wrt [union]. *)

Lemma Vgt_prod1_union n A (R S : relation A) :
  @Vgt_prod1 n _ (R U S) == @Vgt_prod1 n _ R U @Vgt_prod1 n _ S.

Proof.
  rewrite rel_eq; intros v1 v2. split.
  intros [i [vi [x [j [vj [h [y [h1 [h2 [h3|h3]]]]]]]]]].
  left. exists i vi x. exists j vj h. exists y. intuition.
  right. exists i vi x. exists j vj h. exists y. intuition.
  intros [h|h]; destruct h as [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
    exists i vi x; exists j vj h; exists y; intuition.
Qed.

Lemma Vgt_prod_union n A (R S : relation A) :
  @Vgt_prod n _ (R U S) == @Vgt_prod n _ R U @Vgt_prod n _ S.

Proof. rewrite !Vgt_prod_eq1. apply Vgt_prod1_union. Qed.

(***********************************************************************)
(** * Product ordering on vectors. *)

Section vec_prod.

  Variable A : Type. Notation vec := (vector A).

  Variable R : relation A.

  Definition vec_prod {n} := Vforall2n R (n:=n).

  Lemma vec_prod_tail : forall n (v v' : vec (S n)),
    vec_prod v v' -> vec_prod (Vtail v) (Vtail v').

  Proof. intros. unfold vec_prod. apply Vforall2n_tail. hyp. Qed.

  Global Instance vec_prod_refl n : Reflexive R -> Reflexive (@vec_prod n).

  Proof. intros h x. apply Vforall2n_intro. refl. Qed.

  Global Instance vec_prod_trans n : Transitive R -> Transitive (@vec_prod n).

  Proof.
    intros h x y z xy yz. apply Vforall2n_intro. intros i ip.
    trans (Vnth y ip); apply Vforall2n_nth; hyp.
  Qed.

  Global Instance vec_prod_sym n : Symmetric R -> Symmetric (@vec_prod n).

  Proof.
    intros h x y xy. apply Vforall2n_intro. intros i ip. sym.
    apply Vforall2n_nth. hyp.
  Qed.

  Lemma vec_prod_dec n : rel_dec R -> rel_dec (@vec_prod n).

  Proof.
    intros R_dec P Q. destruct (Vforall2n_dec R_dec P Q); intuition.
  Defined.

End vec_prod.

Arguments vec_prod_refl [A R] _ _ _.
Arguments vec_prod_trans [A R] _ _ _ _ _ _ _.
Arguments vec_prod_sym [A R] _ _ _ _ _.
Arguments vec_prod_dec [A R] {n} _ _ _.
