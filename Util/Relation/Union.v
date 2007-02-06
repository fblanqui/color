(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-05

union of two wellfounded relations
*)

Set Implicit Arguments.

Require Export Lexico.

(***********************************************************************)
(** R @ S << S @ R -> WF S -> WF (R# @ S) *)

Section commut.

Variables (A : Set) (R S : relation A) (commut : R @ S << S @ R).

Lemma commut_SN_modulo : forall x, SN S x -> SN (R# @ S) x.

Proof.
induction 1. apply SN_intro. intros. deduce (commut_rtc commut H1).
do 2 destruct H2. eapply SN_modulo. apply H0. apply H2. exact H3.
Qed.

Lemma commut_WF_modulo : WF S -> WF (R# @ S).

Proof.
unfold WF. intros. apply commut_SN_modulo. apply H.
Qed.

End commut.

(***********************************************************************)
(** R @ T << T -> WF T -> WF (T @ R#) *)

Section absorb.

Variables (A : Set) (R T : relation A) (absorb : R @ T << T).

Lemma SN_modulo_r : forall x x', SN (T @ R#) x -> R# x x' -> SN (T @ R#) x'.

Proof.
intros. apply SN_intro. intros. apply (SN_inv H). do 2 destruct H1. exists x0.
intuition. apply (comp_rtc_incl absorb). exists x'. intuition.
Qed.

Lemma absorb_SN_modulo_r : forall x, SN T x -> SN (T @ R#) x.

Proof.
induction 1. apply SN_intro. intros. apply SN_intro. intros.
do 2 destruct H1. do 2 destruct H2.
assert (T x0 x1). apply (comp_rtc_incl absorb). exists y. intuition.
deduce (H0 _ H1). apply (SN_inv H6). exists x1. intuition.
Qed.

Lemma absorb_WF_modulo_r : WF T -> WF (T @ R#).

Proof.
unfold WF. intros. eapply absorb_SN_modulo_r. apply H.
Qed.

End absorb.

(***********************************************************************)
(** R @ S << S @ R -> WF R -> WF S -> WF (R U S) *)

Section union1.

Variables (A : Set) (R S : relation A) (commut : R @ S << S @ R).

Lemma WF_union : WF R -> WF S -> WF (R U S).

Proof.
intros. eapply WF_incl. apply tc_incl. eapply WF_incl. apply tc_union.
set (T := R# @ S). set (gt1 := T! @ R#). set (gt2 := R!).
eapply WF_incl. apply union_commut.
eapply WF_incl. apply lex'_intro. apply WF_lex'.
(* WF gt1 *)
unfold gt1. apply absorb_WF_modulo_r. trans (R# @ T!). comp.
apply rtc_incl. unfold T. apply rtc_comp_modulo.
apply WF_tc. unfold T. apply commut_WF_modulo. exact commut. exact H0.
(* WF gt2 *)
unfold gt2. apply WF_tc. exact H.
(* transitive gt2 *)
apply trans_intro. unfold gt2. apply tc_idem.
(* gt2 @ gt1 << gt1 *)
unfold gt1, gt2. trans ((R! @ T!) @ R#). apply comp_assoc'. comp.
trans (R# @ T!). comp. apply tc_incl_rtc. unfold T. apply rtc_comp_modulo.
Qed.

End union1.

(***********************************************************************)
(** WF (Iter_ge R n) -> WF R *)

Section iter.

Variables (A : Set) (R : relation A).

Lemma SN_Iter_ge_S : forall n x, SN (Iter_ge R (S n)) x -> SN (Iter_ge R n) x.

Proof.
induction 1. apply SN_intro. intros. deduce (Iter_ge_split H1). destruct H2.
apply SN_intro. intros. deduce (Iter_ge_split H3). destruct H4.
apply H0. exists (n+n+1). intuition. apply comp_iter. exists y. intuition.
apply H0. apply incl_elim with (R := Iter_ge R (n+n+1)). apply incl_Iter_ge.
omega. apply iter_Iter_ge. exists y. intuition.
apply H0. exact H2.
Qed.

Lemma WF_Iter_ge_S : forall n, WF (Iter_ge R (S n)) -> WF (Iter_ge R n).

Proof.
unfold WF. intros. apply SN_Iter_ge_S. apply H.
Qed.

Lemma WF_Iter_ge : forall n, WF (Iter_ge R n) -> WF R.

Proof.
induction n; intros. apply WF_incl with (Iter_ge R 0).
unfold inclusion. intros. exists 0. intuition. exact H.
apply IHn. apply WF_Iter_ge_S. exact H.
Qed.

End iter.
