(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-11-26

inductive definition of strong normalization
(inverse of accessibility)
************************************************************************)

Set Implicit Arguments.

Require Export RelUtil.

Section sn.

Variable (A : Set) (R : relation A).

Inductive SN : A -> Prop :=
  SN_intro : forall x, (forall y, R x y -> SN y) -> SN x.

Lemma SN_inv : forall x, SN x -> forall y, R x y -> SN y.

Proof.
  destruct 1; trivial.
Qed.

Definition WF := forall x, SN x.

End sn.

(***********************************************************************)
(* accessibility *)

Section acc.

Variable (A : Set) (R : relation A).

Lemma SN_Acc : forall x, SN (transp R) x -> Acc R x.

Proof.
induction 1. apply Acc_intro. intros. apply H0. exact H1.
Qed.

Lemma Acc_SN : forall x, Acc (transp R) x -> SN R x.

Proof.
induction 1. apply SN_intro. intros. apply H0. exact H1.
Qed.

Lemma WF_wf : WF (transp R) -> well_founded R.

Proof.
unfold well_founded. intros. apply SN_Acc. apply H.
Qed.

Lemma wf_WF : well_founded (transp R) -> WF R.

Proof.
unfold WF. intros. apply Acc_SN. apply H.
Qed.

End acc.

(***********************************************************************)
(* inclusion *)

Section incl.

Variable (A : Set) (R S : relation A).

Lemma WF_incl : R << S -> WF S -> WF R.

Proof.
unfold WF. intros. deduce (H0 x). elim H1. intros. apply SN_intro. intros.
apply H3. apply (incl_elim H). exact H4.
Qed.

End incl.

(***********************************************************************)
(* inverse relation *)

Section transp.

Variables (A : Set) (R : relation A).

Lemma WF_transp : WF R -> WF (transp (transp R)).

Proof.
intro. apply WF_incl with (S := R). unfold inclusion, transp. auto. exact H.
Qed.

End transp.

(***********************************************************************)
(* compatibility *)

Section compat.

Variable (A : Set) (E R : relation A) (Hcomp : E @ R << R).

Lemma SN_compat_inv : forall x,
  SN (R @ E) x -> forall x', E x x' -> SN (R @ E) x'.

Proof.
intros. apply SN_intro. intros. do 2 destruct H1. assert (h : (R @ E) x y).
exists x0; split. apply (incl_elim Hcomp). exists x'; split; assumption.
assumption. apply (SN_inv H). exact h.
Qed.

Lemma WF_compat_inv : WF R -> WF (R @ E).

Proof.
unfold WF. intros. deduce (H x). elim H0. intros. apply SN_intro. intros.
do 2 destruct H3. deduce (H2 _ H3). apply (SN_compat_inv H5 H4).
Qed.

End compat.

(***********************************************************************)
(* inverse image *)

Section inverse.

Variables (A B : Set) (f : A->B) (R : relation B).

Let Rof x y := R (f x) (f y).

Lemma SN_Rof : forall y, SN R y -> forall x, y = f x -> SN Rof x.

Proof.
induction 1. intros. apply SN_intro. intros.
apply (H0 (f y)). rewrite H1. exact H2. refl.
Qed.

Lemma SN_inverse : forall x, SN R (f x) -> SN Rof x.

Proof.
intros. apply (SN_Rof H). refl.
Qed.

Lemma WF_inverse : WF R -> WF Rof.

Proof.
red in |- *. intros. apply SN_inverse; auto.
Qed.

End inverse.

(***********************************************************************)
(* reflexive transitive closure *)

Section rtc.

Variable (A : Set) (R : relation A).

Lemma SN_rtc : forall x, SN R x -> forall x', R# x x' -> SN R x'.

Proof.
intros x H. induction 1. inversion H. auto. exact H. auto.
Qed.

End rtc.

(***********************************************************************)
(* transitive closure *)

Section tc.

Variable (A : Set) (R : relation A).

Lemma SN_tc : forall x, SN R x -> SN (R!) x.

Proof.
induction 1. apply SN_intro. intros. deduce (tc_split H1). do 2 destruct H2.
apply SN_rtc with (x := x0). apply H0. exact H2.
apply incl_elim with (R := R#). apply incl_rtc. apply tc_incl.
exact H3.
Qed.

Lemma WF_tc : WF R -> WF (R!).

Proof.
intros. unfold WF. intro. apply SN_tc. apply H.
Qed.

End tc.