(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-01-24


* Component-wise extension of a relation to vectors and product ordering
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil VecUtil RelUtil NatUtil SN.

(***********************************************************************)
(** * Component-wise extension to vectors on [A] of a relation on [A]. *)

Fixpoint Vrel1 n A (R : relation A) : relation (vector A n) :=
  match n with
    | O => fun _ _ => False
    | S n => fun v1 v2 => symprod R (Vrel1 R) (Vhead_tail v1) (Vhead_tail v2)
  end.

Definition Vrel1_app n A (R : relation A) : relation (vector A n) :=
  fun v1 v2 : vector A n =>
    exists i (vi : vector A i) x j (vj : vector A j) h y,
      v1 = Vcast (Vapp vi (Vcons x vj)) h
      /\ v2 = Vcast (Vapp vi (Vcons y vj)) h /\ R x y.

Definition Vrel1_nth n A (R : relation A) : relation (vector A n) :=
  fun v1 v2 : vector A n =>
    exists i (hi : i<n), R (Vnth v1 hi) (Vnth v2 hi)
      /\ forall j (hj : j<n), j <> i -> Vnth v1 hj = Vnth v2 hj.

(***********************************************************************)
(** Properties of [Vrel1]. *)

Section S.

  Variables (A : Type) (R : relation A).

  Lemma Vrel1_cons_intro : forall x1 x2 n (v1 v2 : vector A n),
    (R x1 x2 /\ v1 = v2) \/ (x1 = x2 /\ Vrel1 R v1 v2)
    -> Vrel1 R (Vcons x1 v1) (Vcons x2 v2).

  Proof.
    intros. simpl. unfold Vhead_tail. simpl. destruct H; destruct H.
    subst v2. apply left_sym. hyp.
    subst x2. apply right_sym. hyp.
  Qed.

  Lemma Vrel1_cons_elim : forall x1 x2 n (v1 v2 : vector A n),
    Vrel1 R (Vcons x1 v1) (Vcons x2 v2) ->
    (R x1 x2 /\ v1 = v2) \/ (x1 = x2 /\ Vrel1 R v1 v2).

  Proof.
    intros. simpl in H. unfold Vhead_tail in H. simpl in H. inversion H; auto.
  Qed.

  Lemma Vrel1_add_intro : forall x1 x2 n (v1 v2 : vector A n),
    (R x1 x2 /\ v1 = v2) \/ (x1 = x2 /\ Vrel1 R v1 v2)
    -> Vrel1 R (Vadd v1 x1) (Vadd v2 x2).

  Proof.
    intros x1 x2. induction n; intros v1 v2.
    VOtac. intuition auto with *. apply left_sym. hyp.
    VSntac v1; VSntac v2. simpl Vadd. intros [[h1 h2]|[h1 h2]].
    Veqtac. apply Vrel1_cons_intro. right. fo.
    subst x2. destruct (Vrel1_cons_elim h2) as [[i1 i2]|[i1 i2]].
    rewrite i2. apply Vrel1_cons_intro. left. fo.
    apply Vrel1_cons_intro. right. fo.
  Qed.

  Lemma Vrel1_app_intro_l : forall n (v : vector A n) m (v1 v2 : vector A m),
    Vrel1 R v1 v2 -> Vrel1 R (Vapp v v1) (Vapp v v2).

  Proof.
    induction v; intros. hyp.
    simpl. unfold Vhead_tail. simpl. apply right_sym. apply IHv. hyp.
  Qed.

  Lemma Vrel1_cast_intro : forall m n (h : m=n) (v1 v2 : vector A m),
    Vrel1 R v1 v2 -> Vrel1 R (Vcast v1 h) (Vcast v2 h).

  Proof.
    induction v1; intros; destruct n; intros.
    contr. discr. discr.
    assert (n0 = n). apply eq_add_S. hyp. subst n0.
    assert (h = eq_refl (S n)). apply eq_unique. subst h.
    rewrite (Vcast_refl (Vcons h0 v1)), (Vcast_refl v2). hyp.
  Qed.

  Lemma Vrel1_cast_elim : forall m n (h : m=n) (v1 v2 : vector A m),
    Vrel1 R (Vcast v1 h) (Vcast v2 h) -> Vrel1 R v1 v2.

  Proof.
    induction m; destruct n; intros.
    assert (h = eq_refl 0). apply eq_unique. subst h. contr.
    discr. discr.
    assert (v1 = Vcons (Vhead v1) (Vtail v1)). apply VSn_eq. rewrite H0.
    assert (v2 = Vcons (Vhead v2) (Vtail v2)). apply VSn_eq. rewrite H1.
    rewrite H0, H1, !Vcast_cons in H. simpl in H.
    unfold Vhead_tail in H. simpl in H.
    apply Vrel1_cons_intro. inversion H. left. split. hyp.
    eapply Vcast_eq_elim with (m := n). apply H6.
    right. split. refl. eapply IHm with (n := n). apply H3.
  Qed.

(***********************************************************************)
(** Equivalence between [Vrel1] and [Vrel1_app]. *)

  Lemma Vrel1_app_impl : forall n (v1 v2 : vector A n),
    Vrel1 R v1 v2 -> Vrel1_app R v1 v2.

  Proof.
    induction v1; simpl. intros. contr. intro. VSntac v2.
    unfold Vhead_tail. simpl. intro. inversion H0.
    ex 0 (@Vnil A) h n (Vtail v2) (eq_refl (S n)) (Vhead v2).
    split. refl. split. refl. hyp.
    ded (IHv1 (Vtail v2) H2). do 8 destruct H6. destruct H7. rewrite H6, H7.
    ex (S x0) (Vcons (Vhead v2) x1) x2 x3 x4.
    assert (S x0 + S x3 = S n). lia. ex H9 x6.
    simpl. rewrite !Vcast_cons, (eq_unique (@eq_add_S (x0 + (S x3)) n H9) x5). intuition.
  Qed.

  Lemma Vrel1_app_iff : forall n (v1 v2 : vector A n),
    Vrel1 R v1 v2 <-> Vrel1_app R v1 v2.

  Proof.
    intros n v1 v2. split. apply Vrel1_app_impl.
    intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]]; subst.
    rewrite 2!Vcast_refl. apply Vrel1_app_intro_l. apply Vrel1_cons_intro. fo.
  Qed.

  Lemma Vrel1_app_eq n : @Vrel1 n _ R == @Vrel1_app n _ R.

  Proof. rewrite rel_eq. apply Vrel1_app_iff. Qed.

(***********************************************************************)
(** Equivalence between [Vrel1] and [Vrel1_nth]. *)

  Lemma Vrel1_nth_iff : forall n (v1 v2 : vector A n),
    Vrel1 R v1 v2 <-> Vrel1_nth R v1 v2.

  Proof.
    intros n v1 v2. rewrite Vrel1_app_iff. split.

    intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
      subst; rewrite !Vcast_refl.
    exists i. assert (hi : i<i+S j). lia. exists hi.
    rewrite !Vnth_app_cons. intuition.
    rewrite !Vnth_app. destruct (le_gt_dec i j0). 2: refl.
    rewrite !Vnth_cons. destruct (lt_ge_dec 0 (j0-i)). 2: lia.
    apply Vnth_eq. refl.

    intros [i [hi [i1 i2]]].
    assert (ki : 0+i<=n). lia. ex i (Vsub v1 ki) (Vnth v1 hi).
    assert (kj : S i+(n-i-1)<=n). lia. ex (n-i-1) (Vsub v1 kj).
    assert (k : i+S(n-i-1)=n). lia. ex k (Vnth v2 hi).
    split; [idtac|split;[idtac|hyp]].

    apply Veq_nth. intros j hj. rewrite Vnth_cast, Vnth_app.
    destruct (le_gt_dec i j). rewrite Vnth_cons. destruct (lt_ge_dec 0 (j-i)).
    rewrite Vnth_sub. apply Vnth_eq. clear -l0; lia.
    apply Vnth_eq. clear -l g; lia.
    rewrite Vnth_sub. apply Vnth_eq. refl.

    apply Veq_nth. intros j hj. rewrite Vnth_cast, Vnth_app.
    destruct (le_gt_dec i j). rewrite Vnth_cons. destruct (lt_ge_dec 0 (j-i)).
    rewrite Vnth_sub.
    trans (Vnth v1 hj). sym. apply i2. clear -l0; lia. apply Vnth_eq.
    clear -l0; lia. apply Vnth_eq. clear -l g; lia. rewrite Vnth_sub.
    trans (Vnth v1 hj). sym. apply i2. clear -g; lia. apply Vnth_eq. refl.
  Qed.

  Lemma Vrel1_sub : forall n (v1 v2 : vector A n) p q (h : p+q<=n),
    Vrel1 R v1 v2 -> (Vrel1 R)% (Vsub v1 h) (Vsub v2 h).

  Proof.
    intros n v1 v2 p q k. rewrite Vrel1_nth_iff.
    intros [i [hi [i1 i2]]]. destruct (lt_dec i p).
    left. apply Veq_nth. intros j hj. rewrite !Vnth_sub. apply i2. lia.
    destruct (ge_dec i (p+q)).
    left. apply Veq_nth. intros j hj. rewrite !Vnth_sub. apply i2. lia.
    right. rewrite Vrel1_nth_iff.
    exists (i-p). assert (l : i-p<q). lia. exists l. split.
    rewrite !Vnth_sub. erewrite Vnth_eq, Vnth_eq with (v:=v2). apply i1.
    lia. lia.
    intros j hj m. rewrite !Vnth_sub. apply i2. lia.
  Qed.

(***********************************************************************)
(** Properties of [Vrel1] wrt termination. *)

  Lemma Vforall_SN_rel1 : forall n (v : vector A n),
    Vforall (SN R) v -> SN (Vrel1 R) v.

  Proof.
    induction v; intros; apply SN_intro; intros. contr. simpl.
    eapply SN_inverse with (f := @Vhead_tail A n) (R := symprod R (Vrel1 R)).
    VSntac y. unfold Vhead_tail. simpl. simpl in H. destruct H.
    rewrite H1 in H0. inversion H0.
    apply SN_symprod. eapply SN_inv. apply H4. hyp.
    rewrite <- H7. apply IHv. hyp.
    apply SN_symprod. rewrite <- H6. hyp.
    eapply SN_inv. apply H4. apply IHv. hyp.
  Qed.

  Lemma SN_rel1_head : forall n (v : vector A (S n)),
    SN (Vrel1 R) v -> SN R (Vhead v).

  Proof.
    induction 1. VSntac x. apply SN_intro. intros.
    ded (H0 (Vcons y (Vtail x))). apply H3. rewrite H1. simpl.
    unfold Vhead_tail. simpl. apply left_sym. hyp.
  Qed.

  Lemma SN_rel1_cons_head : forall a n (v : vector A n),
    SN (Vrel1 R) (Vcons a v) -> SN R a.

  Proof. intros. ded (SN_rel1_head H). hyp. Qed.

  Lemma SN_rel1_tail : forall n (v : vector A (S n)),
    SN (Vrel1 R) v -> SN (Vrel1 R) (Vtail v).

  Proof.
    induction 1. VSntac x. apply SN_intro. intros.
    ded (H0 (Vcons (Vhead x) y)). rewrite H1 in H3. apply H3.
    simpl. unfold Vhead_tail. simpl. apply right_sym. hyp.
  Qed.

  Lemma SN_rel1_cons_tail : forall a n (v : vector A n),
    SN (Vrel1 R) (Vcons a v) -> SN (Vrel1 R) v.

  Proof. intros. ded (SN_rel1_tail H). hyp. Qed.

  Lemma SN_rel1_forall : forall n (v : vector A n),
    SN (Vrel1 R) v -> Vforall (SN R) v.

  Proof.
    induction v; intros; simpl. exact I. split.
    apply (SN_rel1_head H). apply IHv. apply (SN_rel1_tail H).
  Qed.

End S.

Arguments Vrel1_app_impl [A R n v1 v2] _.
Arguments Vrel1_sub [A R n v1 v2 p q] h _.

(***********************************************************************)
(** Compatibility of [Vrel1] with [inclusion] and [same]. *)

From Stdlib Require Import Morphisms.

Global Instance Vrel1_app_incl n A :
  Proper (inclusion ==> inclusion) (@Vrel1_app n A).

Proof.
  intros R R' RR' v1 v2.
  intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
    ex i vi x j vj h y; fo.
Qed.

Global Instance Vrel1_incl n A : Proper (inclusion ==> inclusion) (@Vrel1 n A).

Proof. intros R R' RR'. rewrite 2!Vrel1_app_eq. apply Vrel1_app_incl. hyp. Qed.

Global Instance Vrel1_app_same n A :
  Proper (same ==> same) (@Vrel1_app n A).

Proof.
  intros R R' RR'. rewrite rel_eq. intros v1 v2. unfold Vrel1.
  split; intros [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
    ex i vi x j vj h y; fo.
Qed.

Global Instance Vrel1_same n A : Proper (same ==> same) (@Vrel1 n A).

Proof.
  intros R R' RR'. rewrite 2!Vrel1_app_eq. apply Vrel1_app_same. hyp.
Qed.

(***********************************************************************)
(** Distributivity of [Vrel1] wrt [union]. *)

Lemma Vrel1_app_union n A (R S : relation A) :
  @Vrel1_app n _ (R U S) == @Vrel1_app n _ R U @Vrel1_app n _ S.

Proof.
  rewrite rel_eq; intros v1 v2. split.
  intros [i [vi [x [j [vj [h [y [h1 [h2 [h3|h3]]]]]]]]]].
  left. ex i vi x j vj h y. intuition.
  right. ex i vi x j vj h y. intuition.
  intros [h|h]; destruct h as [i [vi [x [j [vj [h [y [h1 [h2 h3]]]]]]]]];
    ex i vi x j vj h y; intuition auto with *.
Qed.

Lemma Vrel1_union n A (R S : relation A) :
  @Vrel1 n _ (R U S) == @Vrel1 n _ R U @Vrel1 n _ S.

Proof. rewrite !Vrel1_app_eq. apply Vrel1_app_union. Qed.
