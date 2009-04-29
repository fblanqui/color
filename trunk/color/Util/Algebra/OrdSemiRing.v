(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski, 2007-04-14

Semi-ring equipped with two (strict and non-strict) orders.
*)

Require Import RelDec.
Require Export SemiRing.
Require Import SN.
Require Import RelExtras.
Require Import RelMidex.
Require Import NatUtil.
Require Import LogicUtil.
Require Import Max.
Require Import ZUtil.
Require Import RelUtil.

(***********************************************************************)
(** Semi-rings equipped with orders *)

Module Type OrdSemiRingType.

  Declare Module SR : SemiRingType.
  Export SR.

  Parameter gt : relation A.
  Parameter ge : relation A.

  Parameter eq_ge_compat : forall x y, x =A= y -> ge x y.

  Notation "x >> y" := (gt x y) (at level 70).
  Notation "x >>= y" := (ge x y) (at level 70).

  Parameter ge_refl : reflexive ge.
  Parameter ge_trans : transitive ge.
  (*FIXME: to be removed *)
  (*Parameter ge_antisym : antisymmetric ge.*)

  (*Parameter gt_irrefl : irreflexive gt.*)
  Parameter gt_trans : transitive gt.

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

  Hint Resolve ge_refl (*ge_antisym*) : arith.

End OrdSemiRingType.

Module OrdSemiRing (OSR : OrdSemiRingType).

  Module Export SR := SemiRing OSR.SR.
  Export OSR.

  Add Relation A ge
    reflexivity proved by ge_refl
    transitivity proved by ge_trans
      as ge_rel.

  Add Morphism ge with signature eqA ==> eqA ==> iff as ge_mor.

  Proof.
    intuition. transitivity x. apply eq_ge_compat. symmetry. hyp.
    transitivity x0. hyp. apply eq_ge_compat. hyp.
    transitivity y. apply eq_ge_compat. hyp.
    transitivity y0. hyp. apply eq_ge_compat. symmetry. hyp.
  Qed.

  Add Relation A gt
    transitivity proved by gt_trans
      as gt_rel.

  Add Morphism gt with signature eqA ==> eqA ==> iff as gt_mor.

  Proof.
    intuition. apply ge_gt_compat2 with x0. 2: apply eq_ge_compat; hyp.
    apply ge_gt_compat with x. apply eq_ge_compat. symmetry. hyp. hyp.
    apply ge_gt_compat2 with y0. 2: apply eq_ge_compat; symmetry; hyp.
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

  Proof.
    intros. subst. apply le_refl.
  Qed.

  Lemma ge_refl : reflexive ge.

  Proof.
    intro m. unfold ge. auto with arith.
  Qed.

  Lemma ge_trans : transitive ge.

  Proof.
    intros m n p. unfold ge, Peano.ge. eauto with arith.
  Qed.

  (*Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros m n. unfold ge, Peano.ge. auto with arith.
  Qed.*)

  (*Definition gt_irrefl := Gt.gt_irrefl.*)

  Definition gt_trans := Gt.gt_trans.

  Definition ge_dec := nat_ge_dec.

  Definition gt_dec := nat_gt_dec.

  Lemma gt_WF : WF gt.

  Proof.
    apply wf_transp_WF. 
    apply well_founded_lt_compat with (fun x:nat => x). auto.
  Qed.

  Lemma ge_gt_compat : forall x y z, x >= y -> y > z -> x > z.

  Proof.
    intros. apply le_gt_trans with y; assumption.
  Qed.

  Lemma ge_gt_compat2 : forall x y z, x > y -> y >= z -> x > z.

  Proof.
    intros. apply gt_le_trans with y; assumption.
  Qed.

  Lemma plus_gt_compat : forall m n m' n',
    m > m' -> n > n' -> m + n > m' + n'.

  Proof.
    intros. omega.
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

(***********************************************************************)
(** BigN natural numbers semi-rings with natural order *)

Module BigNOrdSemiRingT <: OrdSemiRingType.

  Module Export SR := BigNSemiRingT.

  Require Import BigN.
  Open Scope bigN_scope.

  Definition gt x y := BigN.lt y x.
  Definition ge x y := BigN.le y x.

  Lemma eq_ge_compat : forall x y, eqA x y -> x >= y.

  Proof.
    intros. apply eq_le_incl. symmetry. hyp.
  Qed.

  Definition ge_refl := le_refl.

  Lemma ge_trans : transitive ge.

  Proof.
    intros m n p. unfold ge. intros. apply le_trans with n; hyp.
  Qed.

  Lemma gt_trans : transitive gt.

  Proof.
    intros m n p. unfold gt. intros. apply lt_trans with n; hyp.
  Qed.

  Lemma ge_dec : forall x y, {ge x y}+{~ge x y}.

  Proof.
    intros. unfold ge, BigN.le. case_eq (y ?= x).
    left. discr. left. discr. right. unfold not. auto.
  Qed.

  Lemma gt_dec : forall x y, {gt x y}+{~gt x y}.

  Proof.
    intros. unfold gt, BigN.lt. case_eq (y ?= x).
    right. discr. left. refl. right. discr.
  Qed.

  Definition gt_WF := wf_transp_WF lt_wf_0.

  Lemma ge_gt_compat : forall x y z, ge x y -> gt y z -> gt x z.

  Proof.
    intros. apply lt_le_trans with y; hyp.
  Qed.

  Lemma ge_gt_compat2 : forall x y z, gt x y -> ge y z -> gt x z.

  Proof.
    intros. apply le_lt_trans with y; hyp.
  Qed.

  Lemma plus_gt_compat :
    forall m n m' n', gt m m' -> gt n n' -> gt (m + n) (m' + n').

  Proof.
    intros. apply add_lt_mono; hyp.
  Qed.

  Lemma plus_ge_compat :
    forall m n m' n', ge m m' -> ge n n' -> ge (m + n) (m' + n').

  Proof.
    intros. apply add_le_mono; hyp.
  Qed.

  Lemma mult_ge_compat :
    forall m n m' n', ge m m' -> ge n n' -> ge (m * n) (m' * n').

  Proof.
    intros. apply mul_le_mono; hyp.
  Qed.

End BigNOrdSemiRingT.

Module BigNOrdSemiRing := OrdSemiRing BigNOrdSemiRingT.

(***********************************************************************)
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

  Lemma eq_ge_compat : forall x y, x = y -> ge x y.

  Proof.
    unfold ge. intuition.
  Qed.

  (*Lemma gt_irrefl : irreflexive gt.

  Proof.
    intros x xx. destruct x.
    unfold gt in xx. omega.
    auto.
  Qed.*)

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

  (*Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros x y xy yx. destruct xy. destruct yx.
    absurd (gt y x). apply gt_asym. assumption. assumption.
    auto. assumption.
  Qed.*)

  Lemma ge_dec : rel_dec ge.

  Proof.
    intros x y. destruct (gt_dec x y).
    left. left. assumption.
    destruct (eqA_dec x y).
    left. right. assumption.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Notation "x >>= y" := (ge x y) (at level 70).
  Notation "x >> y" := (gt x y) (at level 70).

  Lemma ge_gt_eq : forall x y, x >>= y -> x >> y \/ x = y.

  Proof.
    destruct 1; auto.
  Qed.

  Lemma ge_gt_compat : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof.
    intros. destruct y. destruct x. destruct z.
    unfold gt, ge in *. destruct H. 
    simpl in H. omega.
    injection H. intro. subst n0. assumption.
    auto.
    elimtype False. destruct H. auto. discriminate.
    elimtype False. destruct H. auto. subst x.  auto.
  Qed.

  Lemma ge_gt_compat2 : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    unfold ge, gt. destruct x; destruct y; destruct z; simpl; intuition.
    inversion H1. subst. hyp. discr.
  Qed.

  Lemma pos_ord : forall m n,
    Pos m >>= Pos n -> Peano.ge m n.

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
    elimtype False. omega.
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
        contradiction
    | H: MinusInf >>= Pos _ |- _ =>
        destruct H; [ contradiction | discriminate ]
    | H: Pos ?m >>= Pos ?n |- _ =>
        assert ((m >= n)%nat); 
          [ apply pos_ge_impl_ge; assumption 
          | clear H; arctic_ord
          ]
    | |- Pos _ >>= MinusInf => left; simpl; trivial
    | |- Pos ?m >>= Pos ?n => apply ge_impl_pos_ge
    | _ => try solve [contradiction | discriminate]
    end.

  Lemma plus_gt_compat : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply max_gt_compat; assumption.
    unfold Peano.gt. apply lt_max_intro_l. assumption.
    unfold Peano.gt. apply lt_max_intro_r. assumption.
  Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply max_ge_compat; assumption.
    unfold Peano.ge. apply le_max_intro_l. assumption.
    unfold Peano.ge. apply le_max_intro_r. assumption.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    omega.
  Qed.

  Lemma not_minusInf_ge_A1 : forall a, a <> MinusInf -> a >>= A1.

  Proof.
    intros. destruct a. destruct n.
    right. refl.
    left. simpl. omega.
    tauto.
  Qed.

  Lemma ge_A1_not_minusInf : forall a, a >>= A1 -> a <> MinusInf.

  Proof.
    intros. destruct a. 
    discriminate.
    destruct H. contradiction. discriminate.
  Qed.

End ArcticOrdSemiRingT.

Module ArcticOrdSemiRing := OrdSemiRing ArcticOrdSemiRingT.

(***********************************************************************)
(** Arctic below-zero ordered semi-ring *)

Module ArcticBZOrdSemiRingT <: OrdSemiRingType.

  Open Scope Z_scope.

  Module SR := ArcticBZSemiRingT.
  Export SR.

  Definition gt m n :=
    match m, n with
    | MinusInfBZ, _ => False
    | Fin _, MinusInfBZ => True
    | Fin m, Fin n => m > n
    end.

  Definition ge m n := gt m n \/ m = n.

  Lemma eq_ge_compat : forall x y, x = y -> ge x y.

  Proof.
    unfold ge. intuition.
  Qed.

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

  (*Lemma gt_irrefl : irreflexive gt.

  Proof.
    intros x xx. destruct x.
    unfold gt in xx. omega.
    auto.
  Qed.*)

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

  (*Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros m n mn nm. destruct mn; auto. destruct nm; auto.
    absurd (gt n m). apply gt_asym. assumption. assumption.
  Qed.*)

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
    destruct (eqA_dec x y).
    left. right. trivial.
    right. intro xy. destruct xy; auto.
  Defined.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Notation "x >> y" := (gt x y) (at level 70).
  Notation "x >>= y" := (ge x y) (at level 70).

  Lemma ge_gt_eq : forall x y, x >>= y -> x >> y \/ x = y.

  Proof.
    destruct 1; auto.
  Qed.

  Lemma ge_gt_compat : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof.
    intros. destruct y. destruct x. destruct z.
    unfold gt, ge in *. destruct H. 
    simpl in H. omega.
    injection H. intro. subst z0. assumption.
    auto.
    elimtype False. destruct H. auto. discriminate.
    elimtype False. destruct H. auto. subst x.  auto.
  Qed.

  Lemma ge_gt_compat2 : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    unfold ge, gt. destruct x as [x|]; destruct y as [y|];
      try destruct z as [z|]; simpl; intuition.
    inversion H1. subst. hyp. discr.
  Qed.

  Lemma fin_ge_Zge : forall m n,
    Fin m >>= Fin n -> (m >= n)%Z.
 
  Proof.
    intros. inversion H; simpl in H0. omega.
    injection H0. omega.
  Qed.

  Lemma plus_inf_dec : forall m n,
    { exists p, (m = Fin p \/ n = Fin p) /\ m + n = Fin p} +
    { m + n = MinusInfBZ /\ m = MinusInfBZ /\ n = MinusInfBZ }.

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
    {exists mi, exists ni, m = Fin mi /\ n = Fin ni /\ m * n = Fin (mi + ni)}
    + {m * n = MinusInfBZ /\ (m = MinusInfBZ \/ n = MinusInfBZ)}.

  Proof.
    intros. destruct m. destruct n.
    left. exists z. exists z0. repeat split.
    right. auto.
    right. auto.
  Qed.

  Lemma minusInf_ge_min : forall a, a >>= MinusInfBZ.

  Proof.
    intros. destruct a. left. simpl. trivial.
    right. refl.
  Qed.

  Lemma ge_impl_fin_ge : forall m n, (m >= n)%Z -> Fin m >>= Fin n.

  Proof.
    intros. destruct (Z_le_lt_eq_dec n m). omega.
    left. simpl. omega.
    subst n. right. refl.
  Qed.

  Lemma fin_ge_impl_ge : forall m n, Fin m >>= Fin n -> (m >= n)%Z.

  Proof.
    intros. destruct H. 
    simpl in H. omega.
    injection H. intro. subst m. omega.
  Qed.

  Ltac arctic_ord :=
    match goal with
    | H: MinusInfBZ >> Fin _ |- _ =>
        contradiction
    | H: MinusInfBZ >>= Fin _ |- _ =>
        destruct H; [ contradiction | discriminate ]
    | H: Fin ?m >>= Fin ?n |- _ =>
        assert ((m >= n)%Z); 
          [ apply fin_ge_impl_ge; assumption 
          | clear H; arctic_ord
          ]
    | |- Fin _ >>= MinusInfBZ => left; simpl; trivial
    | |- Fin ?m >>= Fin ?n => apply ge_impl_fin_ge
    | _ => try solve [contradiction | discriminate]
    end.

  Lemma plus_gt_compat : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord; simpl in *.
    apply Zmax_gt_compat; assumption.
    apply Zlt_gt. apply elim_lt_Zmax_l. omega.
    apply Zlt_gt. apply elim_lt_Zmax_r. omega.
  Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    apply Zmax_ge_compat; assumption.
    apply Zle_ge. apply elim_Zmax_l. omega.
    apply Zle_ge. apply elim_Zmax_r. omega.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    intros.
    destruct m; destruct n; destruct m'; destruct n'; 
      simpl; trivial; arctic_ord.
    omega.
  Qed.

  Lemma arctic_plus_ge_monotone : forall (a b c : A),
    a >>= c -> Aplus a b >>= c.

  Proof.
    intros. destruct c.
    destruct a. destruct b. simpl. arctic_ord. 
    apply Zle_ge. apply elim_Zmax_l. omega.
    trivial.
    arctic_ord.
    apply minusInf_ge_min.
  Qed.

  Lemma ge_A1_not_minusInf : forall a, a >>= A1 -> a <> MinusInfBZ.

  Proof.
    intros. destruct a. 
    discriminate.
    destruct H. contradiction. discriminate.
  Qed.

End ArcticBZOrdSemiRingT.

Module ArcticBZOrdSemiRing := OrdSemiRing ArcticBZOrdSemiRingT.

(***********************************************************************)
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

  Lemma eq_ge_compat : forall x y, x = y -> ge x y.

  Proof.
    unfold ge. destruct x; destruct y; auto. discr.
  Qed.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
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

  (*Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros m n. unfold ge. 
    destruct m; destruct n; tauto.
  Qed.*)

  (*Lemma gt_irrefl : irreflexive gt.

  Proof.
    intros x. unfold gt. destruct x; tauto.
  Qed.*)

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
    destruct x; destruct y; unfold transp, gt; 
      solve [tauto | auto with arith].
  Qed.

  Lemma ge_gt_compat : forall x y z, x >>= y -> y >> z -> x >> z.

  Proof.
    destruct x; destruct y; destruct z; simpl; tauto.
  Qed.

  Lemma ge_gt_compat2 : forall x y z, x >> y -> y >>= z -> x >> z.

  Proof.
    destruct x; destruct y; destruct z; simpl; tauto.
  Qed.

  Lemma plus_gt_compat : forall m n m' n',
    m >> m' -> n >> n' -> m + n >> m' + n'.

  Proof.
    destruct m; destruct m'; destruct n; destruct n'; simpl; tauto.
  Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m + n >>= m' + n'.

  Proof.
    destruct m; destruct m'; destruct n; destruct n'; simpl; tauto.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >>= m' -> n >>= n' -> m * n >>= m' * n'.

  Proof.
    destruct m; destruct m'; destruct n; destruct n'; simpl; tauto.
  Qed.

End BOrdSemiRingT.

Module BOrdSemiRing := OrdSemiRing BOrdSemiRingT.
