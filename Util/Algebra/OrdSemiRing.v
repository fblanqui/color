(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-04-14

Semi-ring equipped with two (strict and non-strict) orders.
*)

Require Import RelDec.
Require Export SemiRing.
Require Export SN.

(** Semi-rings equipped with orders *)

Module Type OrdSemiRingType.

  Declare Module SR : SemiRingType.
  Export SR.

  Parameter gt : relation A.
  Parameter ge : relation A.

  Notation "x >> y" := (gt x y) (at level 70).
  Notation "x >>= y" := (ge x y) (at level 70).

  Parameter ge_refl : reflexive ge.
  Parameter ge_trans : transitive ge.
  Parameter ge_antisym : antisymmetric ge.

  Parameter gt_irrefl : irreflexive gt.
  Parameter gt_trans : transitive gt.

  Parameter ge_dec : rel_dec ge.
  Parameter gt_dec : rel_dec gt.

  Parameter plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.
  Parameter mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Hint Resolve ge_refl ge_antisym : arith.

End OrdSemiRingType.

Module OrdSemiRing (OSR : OrdSemiRingType).

  Module SR := SemiRing OSR.SR.
  Export SR.
  Export OSR.

End OrdSemiRing.

(** Natural numbers semi-rings with natural order *)

Module NOrdSemiRingT <: OrdSemiRingType.

  Module SR := NSemiRingT.
  Export SR.

  Definition gt := Peano.gt.
  Definition ge := Peano.ge.

  Lemma ge_refl : reflexive ge.

  Proof.
    intro m. unfold ge. auto with arith.
  Qed.

  Lemma ge_trans : transitive ge.

  Proof.
    intros m n p. unfold ge, Peano.ge. eauto with arith.
  Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros m n. unfold ge, Peano.ge. auto with arith.
  Qed.

  Definition gt_irrefl := Gt.gt_irrefl.

  Definition gt_trans := Gt.gt_trans.

  Definition ge_dec := nat_ge_dec.

  Definition gt_dec := nat_gt_dec.

  Lemma gt_WF : WF gt.

  Proof.
    apply wf_transp_WF. 
    apply well_founded_lt_compat with (fun x:nat => x). auto.
  Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m + n >= m' + n'.

  Proof.
    intros. unfold Peano.ge.
    apply plus_le_compat; assumption.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m * n >= m' * n'.

  Proof.
    intros. unfold Peano.ge.
    apply mult_le_compat; assumption.
  Qed.

End NOrdSemiRingT.

Module NOrdSemiRing := OrdSemiRing NOrdSemiRingT.

(** Arctic ordered semi-ring *)

Module ArcticOrdSemiRingT <: OrdSemiRingType.

  Module SR := ArcticSemiRingT.
  Export SR.

  Definition gt m n :=
    match m, n with
    | MinusInf, _ => False
    | Pos _, MinusInf => True
    | Pos m, Pos n => m > n
    end.

  Definition ge m n := gt m n \/ m = n.

  Lemma gt_irrefl : irreflexive gt.

  Proof.
    intros x xx. destruct x.
    unfold gt in xx. omega.
    auto.
  Qed.

  Lemma gt_trans : transitive gt.

  Proof.
    intros x y z xy yz. 
    destruct x. destruct y. destruct z. 
    unfold gt. apply gt_trans with n0; assumption.
    auto.
    elimtype False. auto.
    elimtype False. auto.    
  Qed.

  Lemma gt_asym : forall x y, gt x y -> ~gt y x.

  Proof.
    intros x y xy. 
    destruct x; auto. 
    destruct y; auto.
    simpl in *. omega.
  Qed.

  Lemma gt_dec : rel_dec gt.

  Proof.
    unfold rel_dec. intros.
    destruct x; destruct y.
    destruct (nat_gt_dec n n0); auto.
    left. unfold gt. trivial.
    right. unfold gt. tauto.
    right. unfold gt. tauto.
  Defined.

  Lemma gt_WF : WF gt.

  Proof.
    apply wf_transp_WF. 
    apply well_founded_lt_compat with 
      (fun x => 
        match x with
        | Pos x => x + 1
        | MinusInf => 0
        end).
    intros. destruct x; destruct y; 
      solve [auto with arith | elimtype False; auto].
  Qed.

  Lemma ge_refl : reflexive ge.

  Proof.
    intro m. right. trivial.
  Qed.

  Lemma ge_trans : transitive ge.

  Proof.
    intros x y z xy yz. destruct xy. destruct yz.
    left. apply (gt_trans x y z); assumption.
    subst y. left. assumption.
    subst x. assumption.
  Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros x y xy yx. destruct xy. destruct yx.
    absurd (gt y x). apply gt_asym. assumption. assumption.
    auto. assumption.
  Qed.

  Lemma eq_dec : rel_dec Aeq.

  Proof.
    intros x y. unfold Aeq.
    destruct x; destruct y; try solve [right; discriminate].
    destruct (eq_nat_dec n n0).
    left. subst n. refl.
    right. injection. auto.
    left. refl.
  Defined.

  Lemma ge_dec : rel_dec ge.

  Proof.
    intros x y. destruct (gt_dec x y).
    left. left. assumption.
    destruct (eq_dec x y).
    left. right. assumption.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Notation "x >= y" := (ge x y).
  Notation "x > y" := (gt x y).

  Lemma pos_ord : forall m n,
    Pos m >= Pos n -> Peano.ge m n.

  Proof.
    intros. inversion H; simpl in H0. omega.
    injection H0. omega.
  Qed.

  Lemma plus_inf_dec : forall m n,
    { exists p, (m = Pos p \/ n = Pos p) /\ m + n = Pos p} +
    { m + n = MinusInf /\ m = MinusInf /\ n = MinusInf }.

  Proof.
    intros. destruct m. 
    left. destruct n.
    exists (max n0 n). split.
    apply max_case; auto. trivial.
    exists n0. auto.
    destruct n.
    left. exists n. auto.
    right. auto.
  Qed.

  Lemma mult_inf_dec : forall m n,
    { exists mi, exists ni, m = Pos mi /\ n = Pos ni /\ m * n = Pos (mi + ni) } +
    { m * n = MinusInf /\ (m = MinusInf \/ n = MinusInf) }.

  Proof.
    intros. destruct m. destruct n.
    left. exists n0. exists n. repeat split. 
    right. auto.
    right. auto.
  Qed.

  Lemma plus_gt_compat_l : forall m n m' n',
    m > m' -> n > n' -> m + n > m' + n'.

  Proof.
    intros. 
    destruct m; destruct m'; destruct n; destruct n'; simpl in *;
      try solve [contradiction | auto with arith | discriminate].
    apply max_gt_compat; assumption.
    destruct (max_dec n0 n); rewrite e. assumption.
    assert (n0 <= n).
    apply intro_max_l with n. rewrite e. auto.
    omega.
    destruct (max_dec n0 n); rewrite e. 
    assert (n <= n0).
    apply intro_max_l with n0. rewrite max_comm. rewrite e. auto.
    omega.
    assumption.
  Qed.

  Lemma ge_impl_pos_ge : forall m n, (m >= n)%nat -> Pos m >= Pos n.

  Proof.
    intros. destruct (lt_eq_lt_dec m n) as [[m_n | m_n] | m_n].
    elimtype False. omega.
    subst m. right. refl.
    left. trivial.
  Qed.

  Lemma pos_ge_impl_ge : forall m n, Pos m >= Pos n -> (m >= n)%nat.

  Proof.
    intros. destruct H. auto with arith. 
    injection H. intro. subst m. auto with arith.
  Qed.

  Ltac arctic_ord :=
    match goal with
    | H: MinusInf > Pos _ |- _ =>
        contradiction
    | H: MinusInf >= Pos _ |- _ =>
        destruct H; [ contradiction | discriminate ]
    | H: Pos ?m >= Pos ?n |- _ =>
        assert ((m >= n)%nat); 
          [ apply pos_ge_impl_ge; assumption 
          | clear H; arctic_ord
          ]
    | |- Pos _ >= MinusInf => left; simpl; trivial
    | |- Pos ?m >= Pos ?n => apply ge_impl_pos_ge
    | _ => try solve [contradiction | discriminate]
    end.

  Lemma plus_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m + n >= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply max_ge_compat; assumption.
    unfold Peano.ge. apply elim_max_l. assumption.
    unfold Peano.ge. apply elim_max_r. assumption.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m * n >= m' * n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    omega.
  Qed.

End ArcticOrdSemiRingT.

Module ArcticOrdSemiRing := OrdSemiRing ArcticOrdSemiRingT.

(** Arctic below-zero ordered semi-ring *)

Module ArcticBZOrdSemiRingT <: OrdSemiRingType.

  Module SR := ArcticBZSemiRingT.
  Export SR.

  Definition gt m n :=
    match m, n with
    | MinusInf, _ => False
    | Fin _, MinusInf => True
    | Fin m, Fin n => m > n
    end.

  Definition ge m n := gt m n \/ m = n.

  Lemma ge_refl : reflexive ge.

  Proof.
    intro m. right. trivial.
  Qed.

  Lemma gt_trans : transitive gt.

  Proof.
    intros m n p mn np.
    destruct m; auto. 
    destruct n. 
    destruct p; auto.
    simpl in *. omega.
    simpl in *. tauto.
  Qed.

  Lemma gt_irrefl : irreflexive gt.

  Proof.
    intros x xx. destruct x.
    unfold gt in xx. omega.
    auto.
  Qed.

  Lemma gt_asym : forall m n, gt m n -> ~gt n m.

  Proof.
    intros. destruct m; destruct n; try tauto.
    simpl in *. omega.
  Qed.

  Lemma ge_trans : transitive ge.

  Proof.
    intros m n p mn np. 
    destruct mn. 
    destruct np.
    left. apply (gt_trans m n p); assumption.
    rewrite <- H0. left. trivial.
    rewrite H. trivial.
  Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros m n mn nm. destruct mn; auto. destruct nm; auto.
    absurd (gt n m). apply gt_asym. assumption. assumption.
  Qed.

  Lemma eq_dec : rel_dec Aeq.

  Proof.
    intros x y.
    destruct x; destruct y; unfold Aeq; try solve [right; discriminate].
    destruct (Z_eq_dec z z0). left. subst z. refl.
    right. injection. auto.
    left. refl.
  Defined.

  Lemma gt_dec : rel_dec gt.

  Proof.
    intros x y.
    destruct x; destruct y; simpl; auto.
    destruct (Z_lt_dec z0 z); [left | right]; omega.
  Defined.

  Lemma ge_dec : rel_dec ge.

  Proof.
    intros x y.
    destruct (gt_dec x y).
    left. left. trivial.
    destruct (eq_dec x y).
    left. right. trivial.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Notation "x >= y" := (ge x y).

  Lemma fin_ge_Zge : forall m n,
    Fin m >= Fin n -> (m >= n)%Z.
 
  Proof.
    intros. inversion H; simpl in H0. omega.
    injection H0. omega.
  Qed.

  Lemma plus_inf_dec : forall m n,
    { exists p, (m = Fin p \/ n = Fin p) /\ m + n = Fin p} +
    { m + n = MinusInf /\ m = MinusInf /\ n = MinusInf }.

  Proof.
    intros. destruct m. 
    left. destruct n.
    exists (Zmax z z0). split.
    apply Zmax_case; auto. trivial.
    exists z. auto.
    destruct n.
    left. exists z. auto.
    right. auto.
  Qed.

  Lemma mult_inf_dec : forall m n,
    { exists mi, exists ni, m = Fin mi /\ n = Fin ni /\ m * n = Fin (mi + ni) } +
    { m * n = MinusInf /\ (m = MinusInf \/ n = MinusInf) }.

  Proof.
    intros. destruct m. destruct n.
    left. exists z. exists z0. repeat split.
    right. auto.
    right. auto.
  Qed.

  Lemma ge_impl_fin_ge : forall m n, (m >= n)%Z -> Fin m >= Fin n.

  Proof.
    intros. destruct (Z_le_lt_eq_dec n m). omega.
    left. simpl. omega.
    subst n. right. refl.
  Qed.

  Lemma fin_ge_impl_ge : forall m n, Fin m >= Fin n -> (m >= n)%Z.

  Proof.
    intros. destruct H. 
    simpl in H. omega.
    injection H. intro. subst m. omega.
  Qed.

  Ltac arctic_ord :=
    match goal with
    | H: MinusInf > Fin _ |- _ =>
        contradiction
    | H: MinusInf >= Fin _ |- _ =>
        destruct H; [ contradiction | discriminate ]
    | H: Fin ?m >= Fin ?n |- _ =>
        assert ((m >= n)%Z); 
          [ apply fin_ge_impl_ge; assumption 
          | clear H; arctic_ord
          ]
    | |- Fin _ >= MinusInf => left; simpl; trivial
    | |- Fin ?m >= Fin ?n => apply ge_impl_fin_ge
    | _ => try solve [contradiction | discriminate]
    end.

  Lemma plus_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m + n >= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply Zmax_ge_compat; assumption.
    apply Zle_ge. apply elim_Zmax_l. omega.
    apply Zle_ge. apply elim_Zmax_r. omega.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m * n >= m' * n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    omega.
  Qed.

End ArcticBZOrdSemiRingT.

(** Semi-ring of booleans with order True > False *)

Module BOrdSemiRingT <: OrdSemiRingType.

  Module SR := BSemiRingT.
  Export SR.

  Definition gt x y := 
    match x, y with
    | true, false => True
    | _, _ => False
    end.

  Definition ge x y :=
    match x, y with
    | false, true => False
    | _, _ => True
    end.

  Notation "x >> y" := (gt x y) (at level 70).
  Notation "x >>= y" := (ge x y) (at level 70).

  Lemma ge_refl : reflexive ge.

  Proof.
    intro m. unfold ge. destruct m; auto.
  Qed.

  Lemma ge_trans : transitive ge.

  Proof.
    intros m n p. unfold ge. 
    destruct m; destruct n; destruct p; auto.
  Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros m n. unfold ge. 
    destruct m; destruct n; tauto.
  Qed.

  Lemma gt_irrefl : irreflexive gt.

  Proof.
    intros x. unfold gt. destruct x; tauto.
  Qed.

  Lemma gt_trans : transitive gt.

  Proof.
    intros x y z. 
    destruct x; destruct y; destruct z; tauto.
  Qed.

  Lemma ge_dec : rel_dec ge.

  Proof.
    intros x y. destruct x; destruct y; simpl; tauto.
  Qed.

  Lemma gt_dec : rel_dec gt.

  Proof.
    intros x y. destruct x; destruct y; simpl; tauto.
  Qed.

  Lemma gt_WF : WF gt.

  Proof.
    apply wf_transp_WF. 
    apply well_founded_lt_compat with 
      (fun x => 
        match x with
        | false => 0
        | true => 1
        end).
    destruct x; destruct y; unfold transp, gt; solve [tauto | auto with arith].
  Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> Aplus m n >>= Aplus m' n'.

  Proof.
    destruct m; destruct m'; destruct n; destruct n'; simpl; tauto.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> Amult m n >>= Amult m' n'.

  Proof.
    destruct m; destruct m'; destruct n; destruct n'; simpl; tauto.
  Qed.

End BOrdSemiRingT.

Module BOrdSemiRing := OrdSemiRing BOrdSemiRingT.
