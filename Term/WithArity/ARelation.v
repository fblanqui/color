(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09

general definitions and results about relations on terms
************************************************************************)

(* $Id: ARelation.v,v 1.3 2006-10-24 12:41:36 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATrs.

Notation term := (term Sig).

Require Export ASubstitution.

(***********************************************************************)
(* basic definitions and properties *)

Section basic.

Variable succ : relation term.

Definition substitution_closed :=
  forall t1 t2 s, succ t1 t2 -> succ (app s t1) (app s t2).

Definition context_closed :=
  forall t1 t2 c, succ t1 t2 -> succ (fill c t1) (fill c t2).

Definition rewrite_ordering := substitution_closed /\ context_closed.

Require Export WfUtil.

Definition reduction_ordering := wf succ /\ rewrite_ordering.

(***********************************************************************)
(* compatibility *)

Definition compatible R := forall l r : term, In (mkRule l r) R -> succ l r.

Lemma comp_rewrite_ord : forall R, rewrite_ordering -> compatible R
  -> forall t u, red R t u -> succ t u.

Proof.
intros R (Hsubs,Hcont) Hcomp t u H. redtac. subst t. subst u.
apply Hcont. apply Hsubs. apply Hcomp. exact H.
Qed.

Lemma comp_head_rewrite_ord : forall R, substitution_closed -> compatible R
  -> forall t u, hd_red R t u -> succ t u.

Proof.
intros. redtac. subst t. subst u. apply H. apply H0. assumption.
Qed.

Require Export Relations.

Lemma comp_rewrite_ord_rtc : rewrite_ordering
  -> reflexive succ -> transitive succ -> forall R, compatible R
  -> forall t u, clos_refl_trans (red R) t u -> succ t u.

Proof.
intros. elim H3; intros. eapply comp_rewrite_ord. assumption. apply H2.
assumption. apply H0. eapply H1. apply H5. assumption.
Qed.

End basic.

Record Rewrite_ordering : Type := mkRewrite_ordering {
  rew_ord_rel :> relation term;
  rew_ord_subs : substitution_closed rew_ord_rel;
  rew_ord_cont : context_closed rew_ord_rel
}.

Lemma comp_preserv : forall (succ succ' : relation term) R,
  (forall l r, In (mkRule l r) R -> succ l r -> succ' l r)
  -> compatible succ R -> compatible succ' R.

Proof.
unfold compatible. intros. apply H. assumption. apply H0. assumption.
Qed.

(***********************************************************************)
(* weak context closed *)

Section reduction_pair.

Variables succ succ_eq : relation term.

Definition weak_context_closed :=
  forall t1 t2 c, succ t1 t2 -> succ_eq (fill c t1) (fill c t2).

Definition weak_rewrite_ordering := substitution_closed succ /\ weak_context_closed.

Definition weak_reduction_ordering := wf succ /\ weak_rewrite_ordering.

(***********************************************************************)
(* reduction pairs *)

Definition left_compatible := inclusion (compose succ_eq succ) succ.

Definition reduction_pair :=
  weak_reduction_ordering /\ left_compatible
  /\ reflexive succ_eq /\ transitive succ_eq /\ rewrite_ordering succ_eq.

End reduction_pair.

Record Reduction_pair : Type := mkReduction_pair {
  rp_succ : relation term;
  rp_succ_eq : relation term;
  rp_subs : substitution_closed rp_succ;
  rp_subs_eq : substitution_closed rp_succ_eq;
  rp_cont : weak_context_closed rp_succ rp_succ_eq;
  rp_cont_eq : context_closed rp_succ_eq;
  rp_comp : inclusion (compose rp_succ_eq rp_succ) rp_succ;
  rp_succ_eq_refl : reflexive rp_succ_eq;
  rp_succ_eq_trans : transitive rp_succ_eq
}.

(***********************************************************************)
(* reflexive closure *)

Section clos_refl.

Variable succ : relation term.

Notation succ_eq := (clos_refl succ).

Lemma rc_context_closed : weak_context_closed succ succ_eq -> context_closed succ_eq.

Proof.
intro. unfold context_closed. intros. unfold clos_refl in H0. decomp H0.
subst t2. unfold clos_refl. auto. apply H. assumption.
Qed.

Lemma rc_substitution_closed :
  substitution_closed succ -> substitution_closed succ_eq.

Proof.
intro. unfold substitution_closed, clos_refl. intros. decomp H0.
subst t2. auto. right. apply H. assumption.
Qed.

Lemma rc_rewrite_ordering :
  weak_rewrite_ordering succ succ_eq -> rewrite_ordering succ_eq.

Proof.
intros (Hsubs,Hcont). split. apply rc_substitution_closed. assumption.
apply rc_context_closed. assumption.
Qed.

End clos_refl.

(***********************************************************************)
(* when succ is the strict part of succ_eq *)

Section strict.

Variables (succ_eq : relation term)
  (succ_eq_trans : transitive succ_eq).

Lemma strict_left_compatible : left_compatible (strict_part succ_eq) succ_eq.

Proof.
unfold left_compatible, inclusion, compose, strict_part. intros; split; decomp H.
eapply succ_eq_trans. apply H1. assumption.
unfold not; intro. deduce (succ_eq_trans H H1). contradiction.
Qed.

End strict.

End S.
