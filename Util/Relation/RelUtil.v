(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general definitions and results about relations
************************************************************************)

(* $Id: RelUtil.v,v 1.3 2006-10-24 13:59:07 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export Relations.

Implicit Arguments transp.
Implicit Arguments inclusion.
Implicit Arguments clos_refl_trans [A].
Implicit Arguments clos_trans [A].
Implicit Arguments reflexive [A].
Implicit Arguments transitive [A].
Implicit Arguments antisymmetric [A].
Implicit Arguments symmetric [A].
Implicit Arguments equiv [A].
Implicit Arguments union [A].

Section S.

Variable A : Set.

(***********************************************************************)
(* basic definitions *)

Section basic.

Definition irreflexive (R : relation A) := forall x, ~ R x x.

Definition asymmetric (R : relation A) := forall x y, R x y -> ~ R y x.

Definition clos_refl (R : relation A) x y := x = y \/ R x y.

Variable R : relation A.

Definition quasi_ordering := reflexive R /\ transitive R. (* preorder in coq *)

Record Quasi_ordering : Type := mkQuasi_ordering {
  qord_rel :> relation A;
  qord_refl : reflexive qord_rel;
  qord_trans : transitive qord_rel
}.

Definition ordering := reflexive R /\ transitive R /\ antisymmetric R.

Record Ordering : Type := mkOrdering {
  ord_rel :> relation A;
  ord_refl : reflexive ord_rel;
  ord_trans : transitive ord_rel;
  ord_antisym : antisymmetric ord_rel
}.

Definition strict_ordering := irreflexive R /\ transitive R.

Record Strict_ordering : Type := mkStrict_ordering {
  sord_rel :> relation A;
  sord_irrefl : irreflexive sord_rel;
  sord_trans : transitive sord_rel
}.

Definition strict_part x y := R x y /\ ~ R y x.

(***********************************************************************)
(* reflexive closure *)

Lemma rc_refl : reflexive (clos_refl R).

Proof.
unfold reflexive, clos_refl. auto.
Qed.

Lemma rc_trans : transitive R -> transitive (clos_refl R).

Proof.
intro. unfold transitive, clos_refl. intros. decomp H0. subst y. assumption.
decomp H1. subst z. auto. right. apply H with (y := y); assumption.
Qed.

Lemma rc_incl : inclusion R (clos_refl R).

Proof.
unfold inclusion, clos_refl. auto.
Qed.

(***********************************************************************)
(* transitive closure *)

Lemma tc_transp : forall x y, clos_trans R y x -> clos_trans (transp R) x y.

Proof.
induction 1.
apply t_step. assumption.
eapply t_trans. apply IHclos_trans2. apply IHclos_trans1.
Qed.

(***********************************************************************)
(* reflexive transitive closure *)

Lemma rtc_refl : reflexive (clos_refl_trans R).

Proof.
unfold reflexive. intro. apply rt_refl.
Qed.

Lemma rtc_trans : transitive (clos_refl_trans R).

Proof.
unfold transitive. intros. eapply rt_trans. apply H. assumption.
Qed.

Lemma rtc_split : forall x y, clos_refl_trans R x y -> x = y \/ clos_trans R x y.

Proof.
intros. elim H.
intros. right. apply t_step. assumption.
intro. left. reflexivity.
intros. destruct H1; destruct H3.
left. transitivity y0; assumption.
subst y0. right. assumption.
subst y0. right. assumption.
right. apply t_trans with (y := y0); assumption.
Qed.

Lemma rtc_transp : forall x y,
  clos_refl_trans R y x -> clos_refl_trans (transp R) x y.

Proof.
induction 1.
apply rt_step. assumption.
apply rt_refl.
eapply rt_trans. apply IHclos_refl_trans2. apply IHclos_refl_trans1.
Qed.

(***********************************************************************)
(* inclusion *)

Variable R' : relation A.

Lemma incl_transp : inclusion R R' -> inclusion (transp R) (transp R').

Proof.
unfold inclusion, transp. auto.
Qed.

Lemma incl_rtc : inclusion R R' ->
  inclusion (clos_refl_trans R) (clos_refl_trans R').

Proof.
intro. unfold inclusion. intros. elim H0; intros.
apply rt_step. apply H. assumption.
apply rt_refl.
eapply rt_trans. apply H2. assumption.
Qed.

Lemma incl_rtc_in : inclusion R R' ->
  forall x y, clos_refl_trans R x y -> clos_refl_trans R' x y.

Proof.
intros. apply incl_rtc. exact H. exact H0.
Qed.

(***********************************************************************)
(* commutation *)

Definition commut := forall x y z, R x y -> R' x z -> exists t, R y t /\ R' z t.

End basic.

(***********************************************************************)
(* monotony *)

Definition monotone (R : relation A) f := forall x y, R x y -> R (f x) (f y).

Lemma monotone_transp : forall R f, monotone R f -> monotone (transp R) f.

Proof.
unfold monotone, transp. auto.
Qed.

(***********************************************************************)
(* composition *)

Definition compose (R R' : relation A) x y := exists z, R x z /\ R' z y.

Variables R R' : relation A.

Lemma incl_comp_left :
  inclusion R R' -> inclusion (compose R' R) R -> transitive R.

Proof.
unfold transitive. intros. apply H0. unfold compose. exists y. split.
apply H. assumption. assumption.
Qed.

Lemma rc_incl_comp : transitive R -> inclusion (compose (clos_refl R) R) R.

Proof.
intro. unfold inclusion, compose, clos_refl. intros. decomp H0.
subst x0. assumption. eapply H. apply H1. assumption.
Qed.

Lemma comp_rtc_incl :
  inclusion (compose R R') R' -> inclusion (compose (clos_refl_trans R) R') R'.

Proof.
intro. unfold inclusion, compose. intros. do 2 destruct H0.
generalize H1. clear H1. elim H0; intros; auto. apply H. exists y0. auto.
Qed.

Lemma comp_rtc_incl_in : inclusion (compose R R') R' ->
  forall x y, compose (clos_refl_trans R) R' x y -> R' x y.

Proof.
intros. apply comp_rtc_incl. exact H. exact H0.
Qed.

End S.