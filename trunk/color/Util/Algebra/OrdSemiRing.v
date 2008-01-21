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

  Parameter gt_WF : WF gt.

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

  Definition ge m n :=
    match m, n with
    | MinusInf, MinusInf => True
    | MinusInf, Pos _ => False
    | Pos _, MinusInf => True
    | Pos m, Pos n => m >= n
    end.

  Lemma ge_refl : reflexive ge.

  Proof.
    intro m. unfold ge. destruct m; auto with arith.
  Qed.

  Lemma ge_trans : transitive ge.

  Proof.
    intros m n p. unfold ge.
    destruct m; destruct n; destruct p; auto with arith.
    unfold Peano.ge. eauto with arith.
    tauto.
  Qed.

  Lemma ge_antisym : antisymmetric ge.

  Proof.
    intros m n. unfold ge, Peano.ge. 
    destruct m; destruct n; solve [auto with arith | tauto].
  Qed.

  Lemma ge_dec : rel_dec ge.

  Proof.
    unfold rel_dec. intros.
    destruct x; destruct y.
    destruct (nat_ge_dec n n0); auto.
    left. unfold ge. trivial.
    right. unfold ge. tauto.
    left. unfold ge. trivial.
  Defined.

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

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).
  Notation "x >= y" := (ge x y).

  Lemma pos_ord : forall m n,
    Pos m >= Pos n -> Peano.ge m n.

  Proof.
    intros. inversion H; auto with arith.
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

  Lemma plus_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m + n >= m' + n'.

  Proof.
    intros. unfold ge.
    destruct m; destruct n; destruct m'; destruct n'; simpl; trivial; 
      try solve [elimtype False; auto].
    apply max_ge_compat. assumption. assumption.    
    unfold Peano.ge in * . apply elim_max_l. assumption.
    unfold Peano.ge in * . apply elim_max_r. assumption.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m * n >= m' * n'.

  Proof.
    intros; unfold ge.
    destruct (mult_inf_dec m n) as 
      [[mi [ni [md [nd mn_pos]]]] | [mn_inf m_n]].
    rewrite mn_pos. subst m. subst n.
    destruct (mult_inf_dec m' n') as 
      [[m'i [n'i [m'd [n'd m'n'pos]]]] | [m'n'_inf m'_n']].
    rewrite m'n'pos. subst m'. subst n'.
    unfold ge in H. unfold ge in H0. omega.
    rewrite m'n'_inf. trivial.
    rewrite mn_inf.
    destruct (mult_inf_dec m' n') as 
      [[m'i [n'i [m'd [n'd m'n'pos]]]] | [m'n'_inf m'_n']].
    subst m'. subst n'. destruct m_n.
    rewrite H1 in H. elimtype False. auto.
    rewrite H1 in H0. elimtype False. auto.
    rewrite m'n'_inf. trivial.
  Qed.

End ArcticOrdSemiRingT.

Module ArcticOrdSemiRing := OrdSemiRing ArcticOrdSemiRingT.

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
