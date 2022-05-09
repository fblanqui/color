(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski, 2007-04-14

Semi-ring equipped with two (strict and non-strict) orders.
*)

From Coq Require Import Morphisms Max Min.
From CoLoR Require Export SemiRing.
From CoLoR Require Import RelDec RelUtil SN RelExtras NatUtil LogicUtil ZUtil.
From CoLoR Require BigNUtil.

(***********************************************************************)
(** Semi-rings equipped with orders *)

Module Type OrdSemiRingType.

  Declare Module Export SR : SemiRingType.

  Parameter gt : relation A.
  Parameter ge : relation A.

  Notation "x >> y" := (gt x y) (at level 70).
  Notation "x >>= y" := (ge x y) (at level 70).

  Parameter eq_ge_compat : forall x y, x =A= y -> x >>= y.

  #[global] Declare Instance ge_refl : Reflexive ge.
  #[global] Declare Instance ge_trans : Transitive ge.
  #[global] Declare Instance gt_trans : Transitive gt.

  Parameter ge_dec : rel_dec ge.
  Parameter gt_dec : rel_dec gt.

  Parameter ge_gt_compat : forall x y z, x >>= y -> y >> z -> x >> z.
  Parameter ge_gt_compat2 : forall x y z, x >> y -> y >>= z -> x >> z.

  Parameter plus_gt_compat : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.
  Parameter plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Parameter mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  #[global] Hint Resolve ge_refl : arith.

End OrdSemiRingType.

Module OrdSemiRing (OSR : OrdSemiRingType).

  Module Export SR := SemiRing OSR.SR.
  Export OSR.

  #[global] Instance ge_mor : Proper (eqA ==> eqA ==> iff) ge.

  Proof.
    intros x y H x0 y0 H0. intuition.
    trans x. apply eq_ge_compat. hyp.
    trans x0. hyp. apply eq_ge_compat. hyp.
    trans y. apply eq_ge_compat. hyp.
    trans y0. hyp. apply eq_ge_compat. hyp.
  Qed.

  #[global] Instance gt_mor : Proper (eqA ==> eqA ==> iff) gt.

  Proof.
    intros x y H x0 y0 H0.
    intuition. apply ge_gt_compat2 with x0. 2: apply eq_ge_compat; hyp.
    apply ge_gt_compat with x. apply eq_ge_compat. hyp. hyp.
    apply ge_gt_compat2 with y0. 2: apply eq_ge_compat; hyp.
    apply ge_gt_compat with y. apply eq_ge_compat. hyp. hyp.
  Qed.

End OrdSemiRing.

(***********************************************************************)
(** Natural numbers semi-rings with natural order *)

Module NOrdSemiRingT <: OrdSemiRingType.

  Module Export SR := NSemiRingT.

  Definition gt := Peano.gt.
  Definition ge := Peano.ge.

  Lemma eq_ge_compat : forall x y, x = y -> x >= y.

  Proof. intros. subst. apply le_refl. Qed.

  #[global] Instance ge_refl : Reflexive ge.

  Proof. intro m. unfold ge. auto with arith. Qed.

  #[global] Instance ge_trans : Transitive ge.

  Proof. intros m n p. unfold ge, Peano.ge. eauto with arith. Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof. intros m n. unfold ge, Peano.ge. auto with arith. Qed.

  Definition gt_irrefl := Gt.gt_irrefl.

  Definition gt_trans := Gt.gt_trans.

  Definition ge_dec := ge_dec.

  Definition gt_dec := gt_dec.

  Lemma gt_WF : WF gt.

  Proof.
    apply wf_transp_WF. apply well_founded_lt_compat with (fun x => x). auto.
  Qed.

  Lemma ge_gt_compat : forall x y z, x >= y -> y > z -> x > z.

  Proof. intros. apply le_gt_trans with y; hyp. Qed.

  Lemma ge_gt_compat2 : forall x y z, x > y -> y >= z -> x > z.

  Proof. intros. apply gt_le_trans with y; hyp. Qed.

  Lemma plus_gt_compat : forall m n m' n',
    m > m' -> n > n' -> m + n > m' + n'.

  Proof. lia. Qed.

  Lemma plus_gt_compat_l : forall m n m' n',
    m > m' -> n >= n' -> m + n > m' + n'.

  Proof. lia. Qed.

  Lemma plus_gt_compat_r : forall m n m' n',
    m >= m' -> n > n' -> m + n > m' + n'.

  Proof. lia. Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m + n >= m' + n'.

  Proof. intros. unfold Peano.ge. apply plus_le_compat; hyp. Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m * n >= m' * n'.

  Proof. intros. unfold Peano.ge. apply mult_le_compat; hyp. Qed.

End NOrdSemiRingT.

Module NOrdSemiRing := OrdSemiRing NOrdSemiRingT.

(***********************************************************************)
(** BigN natural numbers semi-rings with natural order *)

Module BigNOrdSemiRingT <: OrdSemiRingType.

  Module Export SR := BigNSemiRingT.

  Import BigNUtil.

  Definition gt x y := BigN.lt y x.
  Definition ge x y := BigN.le y x.

  Lemma eq_ge_compat : forall x y, eqA x y -> x >= y.

  Proof. intros x y. unfold eqA, ge, BigN.eq, BigN.le. lia. Qed.

  Definition ge_refl := BigN.le_refl.

  #[global] Instance ge_trans : Transitive ge.

  Proof. intros m n p. unfold ge, BigN.le. lia. Qed.

  #[global] Instance gt_trans : Transitive gt.

  Proof. intros m n p. unfold gt, BigN.lt. lia. Qed.

  Lemma ge_dec : forall x y, {ge x y}+{~ge x y}.

  Proof.
    intros x y. unfold ge, BigN.le. destruct (Z_le_dec [y] [x]).
    left. lia. right. lia.
  Qed.

  Lemma gt_dec : forall x y, {gt x y}+{~gt x y}.

  Proof.
    intros. unfold gt, BigN.lt. destruct (Z_lt_dec [y] [x]).
    left. lia. right. lia.
  Qed.

  Definition gt_WF := wf_transp_WF BigN.lt_wf_0.

  Lemma ge_gt_compat : forall x y z, ge x y -> gt y z -> gt x z.

  Proof. intros x y z. unfold ge, gt, BigN.le, BigN.lt. lia. Qed.

  Lemma ge_gt_compat2 : forall x y z, gt x y -> ge y z -> gt x z.

  Proof. intros x y z. unfold gt, BigN.lt, ge, BigN.le. lia. Qed.

  Lemma plus_gt_compat :
    forall m n m' n', gt m m' -> gt n n' -> gt (m + n) (m' + n').

  Proof. intros m n m' n'. apply BigN.add_lt_mono; hyp. Qed.

  Lemma plus_gt_compat_l :
    forall m n m' n', gt m m' -> ge n n' -> gt (m + n) (m' + n').

  Proof. intros. apply BigN.add_lt_le_mono; hyp. Qed.

  Lemma plus_gt_compat_r :
    forall m n m' n', ge m m' -> gt n n' -> gt (m + n) (m' + n').

  Proof. intros. apply BigN.add_le_lt_mono; hyp. Qed.

  Lemma plus_ge_compat :
    forall m n m' n', ge m m' -> ge n n' -> ge (m + n) (m' + n').

  Proof. intros. apply BigN.add_le_mono; hyp. Qed.

  Lemma mult_ge_compat :
    forall m n m' n', ge m m' -> ge n n' -> ge (m * n) (m' * n').

  Proof. intros. apply BigN.mul_le_mono; hyp. Qed.

  Lemma mult_lt_compat_lr : forall i j k l,
    i <= j -> j > 0 -> k < l -> i * k < j * l.

  Proof.
    intros. case (bigN_le_gt_dec j i); intro.
    assert (i==j). apply BigN.le_antisymm; hyp. rewrite H2.
    rewrite <- (BigN.mul_lt_mono_pos_l _ _ _ H0). hyp.
    apply BigN.mul_lt_mono; hyp.
  Qed.

End BigNOrdSemiRingT.

Module BigNOrdSemiRing := OrdSemiRing BigNOrdSemiRingT.

(***********************************************************************)
(** Arctic ordered semi-ring *)

Module ArcticOrdSemiRingT <: OrdSemiRingType.

  Module Export SR := ArcticSemiRingT.

  Definition gt m n :=
    match m, n with
    | MinusInf, _ => False
    | Pos _, MinusInf => True
    | Pos m, Pos n => m > n
    end.

  Definition ge m n := gt m n \/ m = n.

  Lemma eq_ge_compat : forall x y, x = y -> ge x y.

  Proof. unfold ge. intuition. Qed.

  Lemma gt_irrefl : irreflexive gt.

  Proof. intros x xx. destruct x. unfold gt in xx. lia. auto. Qed.

  #[global] Instance gt_trans : Transitive gt.

  Proof.
    intros x y z xy yz. 
    destruct x; destruct y; destruct z; (contr||auto).
    apply gt_trans with n0; auto.
  Qed.

  Lemma gt_asym x y : gt x y -> ~gt y x.

  Proof. destruct x; destruct y; simpl; lia. Qed.

  Lemma gt_dec : rel_dec gt.

  Proof.
    unfold rel_dec. intros.
    destruct x; destruct y; simpl; auto.
    destruct (gt_dec n n0); auto.
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
      solve [auto with arith | exfalso; auto].
  Qed.

  #[global] Instance ge_refl : Reflexive ge.

  Proof. intro m. right. trivial. Qed.

  #[global] Instance ge_trans : Transitive ge.

  Proof.
    intros x y z xy yz. destruct xy. destruct yz.
    left. apply (gt_trans x y z); hyp.
    subst y. left. hyp.
    subst x. hyp.
  Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros x y xy yx. destruct xy. destruct yx.
    absurd (gt y x). apply gt_asym. hyp. hyp.
    auto. hyp.
  Qed.

  Lemma ge_dec : rel_dec ge.

  Proof.
    intros x y. destruct (gt_dec x y).
    left. left. hyp.
    destruct (eqA_dec x y).
    left. right. hyp.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Notation "x >>= y" := (ge x y) (at level 70).
  Notation "x >> y" := (gt x y) (at level 70).

  Lemma ge_gt_eq : forall x y, x >>= y -> x >> y \/ x = y.

  Proof. destruct 1; auto. Qed.

  Lemma ge_gt_compat : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof.
    intros. destruct y. destruct x. destruct z.
    unfold gt, ge in *. destruct H. 
    simpl in H. lia.
    injection H. intro. subst n0. hyp.
    auto.
    exfalso. destruct H. auto. discr.
    exfalso. destruct H. auto. subst x.  auto.
  Qed.

  Lemma ge_gt_compat2 : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    unfold ge, gt. destruct x; destruct y; destruct z; simpl; intuition.
    inversion H1. subst. hyp. discr.
  Qed.

  Lemma pos_ord : forall m n,
    Pos m >>= Pos n -> Peano.ge m n.

  Proof.
    intros. inversion H; simpl in H0. lia. injection H0. lia.
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
    { exists mi, exists ni,
      m = Pos mi /\ n = Pos ni /\ m * n = Pos (mi + ni) } +
    { m * n = MinusInf /\ (m = MinusInf \/ n = MinusInf) }.

  Proof.
    intros. destruct m. destruct n.
    left. exists n0. exists n. repeat split. 
    right. auto.
    right. auto.
  Qed.

  Lemma ge_impl_pos_ge : forall m n, (m >= n)%nat -> Pos m >>= Pos n.

  Proof.
    intros. destruct (lt_eq_lt_dec m n) as [[m_n | m_n] | m_n].
    lia.
    subst m. right. refl.
    left. trivial.
  Qed.

  Lemma pos_ge_impl_ge : forall m n, Pos m >>= Pos n -> (m >= n)%nat.

  Proof.
    intros. destruct H. auto with arith. 
    injection H. intro. subst m. auto with arith.
  Qed.

  Ltac arctic_ord :=
    match goal with
    | H: MinusInf >> Pos _ |- _ =>
        contr
    | H: MinusInf >>= Pos _ |- _ =>
        destruct H; [ contr | discr ]
    | H: Pos ?m >>= Pos ?n |- _ =>
        assert ((m >= n)%nat); 
          [ apply pos_ge_impl_ge; hyp 
          | clear H; arctic_ord
          ]
    | |- Pos _ >>= MinusInf => left; simpl; trivial
    | |- Pos ?m >>= Pos ?n => apply ge_impl_pos_ge
    | _ => try solve [contr | discr]
    end.

  Lemma plus_gt_compat : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply max_gt_compat; hyp.
    unfold Peano.gt. apply lt_max_intro_l. hyp.
    unfold Peano.gt. apply lt_max_intro_r. hyp.
  Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply max_ge_compat; hyp.
    unfold Peano.ge. apply le_max_intro_l. hyp.
    unfold Peano.ge. apply le_max_intro_r. hyp.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    lia.
  Qed.

  Lemma not_minusInf_ge_A1 : forall a, a <> MinusInf -> a >>= A1.

  Proof.
    intros. destruct a. destruct n.
    right. refl.
    left. simpl. lia.
    tauto.
  Qed.

  Lemma ge_A1_not_minusInf : forall a, a >>= A1 -> a <> MinusInf.

  Proof.
    intros. destruct a. 
    discr.
    destruct H. contr. discr.
  Qed.

End ArcticOrdSemiRingT.

Module ArcticOrdSemiRing := OrdSemiRing ArcticOrdSemiRingT.

(***********************************************************************)
(** Arctic below-zero ordered semi-ring *)

Module ArcticBZOrdSemiRingT <: OrdSemiRingType.

  Local Open Scope Z_scope.

  Module Export SR := ArcticBZSemiRingT.

  Definition gt m n :=
    match m, n with
    | MinusInfBZ, _ => False
    | Fin _, MinusInfBZ => True
    | Fin m, Fin n => m > n
    end.

  Definition ge m n := gt m n \/ m = n.

  Definition is_above_zero v :=
    match v with
      | MinusInfBZ => false
      | Fin z => is_not_neg z
    end.

  Lemma is_above_zero_ok :
    forall v, is_above_zero v = true <-> ge v (Fin 0).

  Proof.
    intro. destruct v; simpl; intuition.
    destruct z. right. refl. left. simpl. auto with zarith. discr.
    rewrite is_not_neg_ok. destruct H. simpl in H. auto with zarith.
    inversion H. auto with zarith.
    destruct H. simpl in H. contr. discr.
  Qed.

  Lemma eq_ge_compat : forall x y, x = y -> ge x y.

  Proof. unfold ge. intuition. Qed.

  #[global] Instance ge_refl : Reflexive ge.

  Proof. intro m. right. trivial. Qed.

  #[global] Instance gt_trans : Transitive gt.

  Proof.
    intros m n p mn np.
    destruct m; auto. 
    destruct n. 
    destruct p; auto.
    simpl in *. lia.
    simpl in *. tauto.
  Qed.

  Lemma gt_irrefl : irreflexive gt.

  Proof. intros x xx. destruct x. unfold gt in xx. lia. auto. Qed.

  Lemma gt_asym : forall m n, gt m n -> ~gt n m.

  Proof. intros. destruct m; destruct n; try tauto. simpl in *. lia. Qed.

  #[global] Instance ge_trans : Transitive ge.

  Proof.
    intros m n p mn np. 
    destruct mn. 
    destruct np.
    left. apply (gt_trans m n p); hyp.
    rewrite <- H0. left. trivial.
    rewrite H. trivial.
  Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros m n mn nm. destruct mn; auto. destruct nm; auto.
    absurd (gt n m). apply gt_asym. hyp. hyp.
  Qed.

  Lemma gt_dec : rel_dec gt.

  Proof.
    intros x y. destruct x; destruct y; simpl; auto.
    destruct (Z_lt_dec z0 z); [left | right]; lia.
  Defined.

  Lemma ge_dec : rel_dec ge.

  Proof.
    intros x y. destruct (gt_dec x y).
    left. left. trivial.
    destruct (eqA_dec x y).
    left. right. trivial.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Notation "x >> y" := (gt x y) (at level 70).
  Notation "x >>= y" := (ge x y) (at level 70).

  Lemma ge_gt_eq : forall x y, x >>= y -> x >> y \/ x = y.

  Proof. destruct 1; auto. Qed.

  Lemma ge_gt_compat : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof.
    intros. destruct y. destruct x. destruct z.
    unfold gt, ge in *. destruct H. 
    simpl in H. lia.
    injection H. intro. subst z0. hyp.
    auto.
    exfalso. destruct H. auto. discr.
    exfalso. destruct H. auto. subst x.  auto.
  Qed.

  Lemma ge_gt_compat2 : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    unfold ge, gt. destruct x as [x|]; destruct y as [y|];
      try destruct z as [z|]; simpl; intuition.
    inversion H1. subst. hyp. discr.
  Qed.

  Lemma fin_ge_Zge : forall m n,
    Fin m >>= Fin n -> (m >= n)%Z.
 
  Proof. intros. inversion H; simpl in H0. lia. injection H0. lia. Qed.

  Lemma plus_inf_dec : forall m n,
    { exists p, (m = Fin p \/ n = Fin p) /\ m + n = Fin p} +
    { m + n = MinusInfBZ /\ m = MinusInfBZ /\ n = MinusInfBZ }.

  Proof.
    intros. destruct m. 
    left. destruct n.
    exists (Z.max z z0). split.
    apply Z.max_case; auto. trivial.
    exists z. auto.
    destruct n.
    left. exists z. auto.
    right. auto.
  Qed.

  Lemma mult_inf_dec : forall m n,
    {exists mi, exists ni, m = Fin mi /\ n = Fin ni /\ m * n = Fin (mi + ni)}
    + {m * n = MinusInfBZ /\ (m = MinusInfBZ \/ n = MinusInfBZ)}.

  Proof.
    intros. destruct m. destruct n.
    left. exists z. exists z0. repeat split.
    right. auto.
    right. auto.
  Qed.

  Lemma minusInf_ge_min : forall a, a >>= MinusInfBZ.

  Proof. intros. destruct a. left. simpl. trivial. right. refl. Qed.

  Lemma ge_impl_fin_ge : forall m n, (m >= n)%Z -> Fin m >>= Fin n.

  Proof.
    intros. destruct (Z_le_lt_eq_dec n m). lia.
    left. simpl. lia.
    subst n. right. refl.
  Qed.

  Lemma fin_ge_impl_ge : forall m n, Fin m >>= Fin n -> (m >= n)%Z.

  Proof.
    intros. destruct H. 
    simpl in H. lia.
    injection H. intro. subst m. lia.
  Qed.

  Ltac arctic_ord :=
    match goal with
    | H: MinusInfBZ >> Fin _ |- _ =>
        contr
    | H: MinusInfBZ >>= Fin _ |- _ =>
        destruct H; [ contr | discr ]
    | H: Fin ?m >>= Fin ?n |- _ =>
        assert ((m >= n)%Z); 
          [ apply fin_ge_impl_ge; hyp 
          | clear H; arctic_ord
          ]
    | |- Fin _ >>= MinusInfBZ => left; simpl; trivial
    | |- Fin ?m >>= Fin ?n => apply ge_impl_fin_ge
    | _ => try solve [contr | discr]
    end.

  Lemma plus_gt_compat : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord; simpl in *.
    apply Zmax_gt_compat; hyp.
    apply Z.lt_gt. apply elim_lt_Zmax_l. lia.
    apply Z.lt_gt. apply elim_lt_Zmax_r. lia.
  Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply Zmax_ge_compat; hyp.
    apply Z.le_ge. apply elim_Zmax_l. lia.
    apply Z.le_ge. apply elim_Zmax_r. lia.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    lia.
  Qed.

  Lemma arctic_plus_ge_monotone : forall (a b c : A),
    a >>= c -> Aplus a b >>= c.

  Proof.
    intros. destruct c.
    destruct a. destruct b. simpl. arctic_ord. 
    apply Z.le_ge. apply elim_Zmax_l. lia.
    trivial.
    arctic_ord.
    apply minusInf_ge_min.
  Qed.

  Lemma ge_A1_not_minusInf : forall a, a >>= A1 -> a <> MinusInfBZ.

  Proof. intros. destruct a. discr. destruct H. contr. discr. Qed.

End ArcticBZOrdSemiRingT.

Module ArcticBZOrdSemiRing := OrdSemiRing ArcticBZOrdSemiRingT.

(***********************************************************************)
(** Tropical ordered semi-ring *)

Module TropicalOrdSemiRingT <: OrdSemiRingType.
 
  Module Export SR := TropicalSemiRingT.

  Definition gt m n :=
    match m, n with
    | PlusInf, PlusInf => False
    | PlusInf, _ => True
    | TPos _, PlusInf => False
    | TPos m, TPos n => m > n
    end.

  Definition ge m n := gt m n \/ m = n.

  Lemma eq_ge_compat : forall x y, x = y -> ge x y.

  Proof. unfold ge. intuition. Qed.

  Lemma gt_irrefl : irreflexive gt.

  Proof. intros x xx. destruct x. unfold gt in xx. lia. auto. Qed.

  #[global] Instance gt_trans : Transitive gt.

  Proof.
    intros x y z xy yz. destruct x; destruct y; destruct z; (contr||auto).
    apply gt_trans with n0; auto.
  Qed.

  Lemma gt_asym x y : gt x y -> ~gt y x.

  Proof. destruct x; destruct y; simpl; lia. Qed.

  Lemma gt_dec : rel_dec gt.

  Proof.
    unfold rel_dec. intros.
    destruct x; destruct y; simpl; auto.
    destruct (gt_dec n n0); auto.
  Defined.

  Lemma gt_Fin_WF x : Acc (transp gt) (TPos x).

  Proof.
    induction x using lt_wf_ind; apply Acc_intro; destruct y; auto || contr.
  Qed.

  #[global] Hint Resolve gt_Fin_WF : core.

  Lemma gt_WF : WF gt.

  Proof with auto; try contr.
    apply wf_transp_WF. intro x.
    destruct x...
    apply Acc_intro. intros. destruct y...
  Qed.

  #[global] Instance ge_refl : Reflexive ge.

  Proof. intro m. right. trivial. Qed.

  #[global] Instance ge_trans : Transitive ge.

  Proof.
    intros x y z xy yz. destruct xy. destruct yz.
    left. apply (gt_trans x y z); hyp.
    subst y. left. hyp.
    subst x. hyp.
  Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros x y xy yx. destruct xy. destruct yx.
    absurd (gt y x). apply gt_asym. hyp. hyp.
    auto. hyp.
  Qed.

  Lemma ge_dec : rel_dec ge.

  Proof.
    intros x y. destruct (gt_dec x y).
    left. left. hyp.
    destruct (eqA_dec x y).
    left. right. hyp.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Notation "x >>= y" := (ge x y) (at level 70).
  Notation "x >> y" := (gt x y) (at level 70).

  Lemma ge_gt_eq : forall x y, x >>= y -> x >> y \/ x = y.

  Proof. destruct 1; auto. Qed.

  Lemma ge_gt_compat : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof with simpl; intuition.
    intros. 
    destruct y; destruct x; destruct z; auto...
    destruct H. simpl in *. lia. injection H. intros. subst...
    destruct H. contr. discr.
  Qed.

  Lemma ge_gt_compat2 : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    unfold ge, gt. destruct x; destruct y; destruct z; simpl; intuition;
    try discr.
    inversion H1. subst. hyp.
  Qed.

  Lemma pos_ord : forall m n,
    TPos m >>= TPos n -> Peano.ge m n.

  Proof. intros. inversion H; simpl in H0. lia. injection H0. lia. Qed.

  Lemma plus_inf_dec : forall m n,
    { exists p, (m = TPos p \/ n = TPos p) /\ m + n = TPos p} +
    { m + n = PlusInf /\ m = PlusInf /\ n = PlusInf }.

  Proof.
    intros. destruct m. 
    left. destruct n.
    exists (min n0 n). split.
    apply min_case; auto. trivial.
    exists n0. auto.
    destruct n.
    left. exists n. auto.
    right. auto.
  Qed.

  Lemma mult_inf_dec : forall m n,
    { exists mi, exists ni,
      m = TPos mi /\ n = TPos ni /\ m * n = TPos (mi + ni) } +
    { m * n = PlusInf /\ (m = PlusInf \/ n = PlusInf) }.

  Proof.
    intros. destruct m. destruct n.
    left. exists n0. exists n. repeat split. 
    right. auto.
    right. auto.
  Qed.

  Lemma ge_impl_pos_ge : forall m n, (m >= n)%nat -> TPos m >>= TPos n.

  Proof.
    intros. destruct (lt_eq_lt_dec m n) as [[m_n | m_n] | m_n].
    lia.
    subst m. right. refl.
    left. trivial.
  Qed.

  Lemma pos_ge_impl_ge : forall m n, TPos m >>= TPos n -> (m >= n)%nat.

  Proof.
    intros. destruct H. auto with arith. 
    injection H. intro. subst m. auto with arith.
  Qed.

  Ltac tropical_ord :=
    match goal with
    | H: _ >> PlusInf |- _ => contr
    | H: TPos _ >>= PlusInf |- _ =>
        destruct H; [ contr | discr ]
    | H: TPos ?m >>= TPos ?n |- _ =>
        assert ((m >= n)%nat); 
          [ apply pos_ge_impl_ge; hyp 
          | clear H; tropical_ord
          ]
    | |- PlusInf >>= TPos _ => left; simpl; trivial
    | |- TPos ?m >>= TPos ?n => apply ge_impl_pos_ge
    | _ => try solve [contr | discr]
    end.


  Lemma plus_gt_compat : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; tropical_ord.
    apply min_gt_compat; hyp.
    unfold Peano.gt. apply lt_min_intro_l. hyp.
    unfold Peano.gt. apply lt_min_intro_r. hyp.
  Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; tropical_ord.
    apply min_ge_compat; hyp.
    unfold Peano.ge. apply le_min_intro_l. hyp.
    unfold Peano.ge. apply le_min_intro_r. hyp.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    intros. destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; tropical_ord. lia.
  Qed.

  Lemma not_minusInf_ge_A1 : forall a, a <> PlusInf -> a >>= A1.

  Proof.
    intros. destruct a. destruct n.
    right. refl.
    left. simpl. lia.
    tauto.
  Qed.

  Lemma tropical_plus_inf_max : forall x, x <> PlusInf -> PlusInf >> x.

  Proof.
    intros. destruct x. simpl. auto.
    exfalso. apply H. trivial.
  Qed.

End TropicalOrdSemiRingT.

Module TropicalOrdSemiRing := OrdSemiRing TropicalOrdSemiRingT.

(***********************************************************************)
(** Semi-ring of booleans with order True > False *)

Module BOrdSemiRingT <: OrdSemiRingType.

  Module Export SR := BSemiRingT.

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

  Lemma eq_ge_compat : forall x y, x = y -> ge x y.

  Proof. unfold ge. destruct x; destruct y; auto. discr. Qed.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Notation "x >> y" := (gt x y) (at level 70).
  Notation "x >>= y" := (ge x y) (at level 70).

  #[global] Instance ge_refl : Reflexive ge.

  Proof. intro m. unfold ge. destruct m; auto. Qed.

  #[global] Instance ge_trans : Transitive ge.

  Proof. intros m n p. unfold ge. destruct m; destruct n; destruct p; auto. Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof. intros m n. unfold ge. destruct m; destruct n; tauto. Qed.

  Lemma gt_irrefl : irreflexive gt.

  Proof. intros x. unfold gt. destruct x; tauto. Qed.

  #[global] Instance gt_trans : Transitive gt.

  Proof. intros x y z. destruct x; destruct y; destruct z; tauto. Qed.

  Lemma ge_dec : rel_dec ge.

  Proof. intros x y. destruct x; destruct y; simpl; tauto. Qed.

  Lemma gt_dec : rel_dec gt.

  Proof. intros x y. destruct x; destruct y; simpl; tauto. Qed.

  Lemma gt_WF : WF gt.

  Proof.
    apply wf_transp_WF. 
    apply well_founded_lt_compat with 
      (fun x => 
        match x with
        | false => 0
        | true => 1
        end).
    destruct x; destruct y; unfold transp, gt; 
      solve [tauto | auto with arith].
  Qed.

  Lemma ge_gt_compat : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof. destruct x; destruct y; destruct z; simpl; tauto. Qed.

  Lemma ge_gt_compat2 : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof. destruct x; destruct y; destruct z; simpl; tauto. Qed.

  Lemma plus_gt_compat : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof. destruct m; destruct m'; destruct n; destruct n'; simpl; tauto. Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof. destruct m; destruct m'; destruct n; destruct n'; simpl; tauto. Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof. destruct m; destruct m'; destruct n; destruct n'; simpl; tauto. Qed.

End BOrdSemiRingT.

Module BOrdSemiRing := OrdSemiRing BOrdSemiRingT.
