(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09

general definitions and results about relations on terms
************************************************************************)

(* $Id: ARelation.v,v 1.9 2006-12-05 14:39:45 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATrs.

Notation term := (term Sig).
Notation rule := (rule Sig).
Notation rules := (list rule).

(***********************************************************************)
(* basic definitions and properties *)

Section basic.

Variable succ : relation term.

Require Export ASubstitution.

Definition substitution_closed :=
  forall t1 t2 s, succ t1 t2 -> succ (app s t1) (app s t2).

Definition context_closed :=
  forall t1 t2 c, succ t1 t2 -> succ (fill c t1) (fill c t2).

Definition rewrite_ordering := substitution_closed /\ context_closed.

Require Export SN.

Definition reduction_ordering := WF succ /\ rewrite_ordering.

End basic.

Record Rewrite_ordering : Type := mkRewrite_ordering {
  rew_ord_rel :> relation term;
  rew_ord_subs : substitution_closed rew_ord_rel;
  rew_ord_cont : context_closed rew_ord_rel
}.

(***********************************************************************)
(* compatibility *)

Section compat.

Variable (succ : relation term) (R : rules).

Definition compatible := forall l r : term, In (mkRule l r) R -> succ l r.

Lemma compat_red : rewrite_ordering succ -> compatible -> red R << succ.

Proof.
unfold inclusion. intros (Hsubs,Hcont) Hcomp t u H. redtac. subst t. subst u.
apply Hcont. apply Hsubs. apply Hcomp. exact H.
Qed.

Lemma compat_hd_red :
  substitution_closed succ -> compatible -> hd_red R << succ.

Proof.
unfold inclusion. intros. redtac. subst x. subst y. apply H. apply H0.
assumption.
Qed.

End compat.

Lemma compat_red_mod_tc : forall succ R E,
  rewrite_ordering succ -> compatible succ E -> compatible succ R ->
  red_mod E R << succ!.

Proof.
intros. unfold red_mod. trans (succ# @ succ). comp.
apply incl_rtc. apply compat_red; assumption. apply compat_red; assumption.
apply rtc_step_incl_tc.
Qed.

Lemma incl_compat : forall (succ succ' : relation term) R,
  (forall l r, In (mkRule l r) R -> succ l r -> succ' l r)
  -> compatible succ R -> compatible succ' R.

Proof.
unfold compatible. intros. apply H. assumption. apply H0. assumption.
Qed.

(***********************************************************************)
(* reduction pair *)

Section reduction_pair.

Variables succ succ_eq : relation term.

Definition left_compatible := succ_eq @ succ << succ.

Lemma compat_red_mod : forall R E,
  rewrite_ordering succ -> rewrite_ordering succ_eq ->
  compatible succ_eq E -> compatible succ R ->
  left_compatible -> red_mod E R << succ.

Proof.
intros. unfold red_mod. trans (succ_eq# @ succ). comp. apply incl_rtc.
apply compat_red; assumption. destruct H0. apply compat_red; assumption.
apply comp_rtc_incl. exact H3.
Qed.

Definition reduction_pair :=
  reduction_ordering succ /\ left_compatible /\ rewrite_ordering succ_eq.

End reduction_pair.

Record Reduction_pair : Type := mkReduction_pair {
  rp_succ : relation term;
  rp_succ_eq : relation term;
  rp_subs : substitution_closed rp_succ;
  rp_subs_eq : substitution_closed rp_succ_eq;
  rp_cont : context_closed rp_succ;
  rp_cont_eq : context_closed rp_succ_eq;
  rp_comp : rp_succ_eq @ rp_succ << rp_succ;
  rp_succ_wf : WF rp_succ
}.

(***********************************************************************)
(* weak reduction pair *)

Section weak_reduction_pair.

Variables succ succ_eq : relation term.

Definition weak_context_closed :=
  forall t1 t2 c, succ t1 t2 -> succ_eq (fill c t1) (fill c t2).

Definition weak_rewrite_ordering :=
  substitution_closed succ /\ weak_context_closed.

Lemma compat_hd_red_mod : forall R E,
  weak_rewrite_ordering -> rewrite_ordering succ_eq ->
  compatible succ_eq E -> compatible succ R ->
  left_compatible succ succ_eq -> hd_red_mod E R << succ.

Proof.
intros. unfold hd_red_mod. trans (succ_eq# @ succ). comp. apply incl_rtc.
apply compat_red; assumption. destruct H. apply compat_hd_red; assumption.
apply comp_rtc_incl. exact H3.
Qed.

Definition weak_reduction_ordering := WF succ /\ weak_rewrite_ordering.

Definition weak_reduction_pair :=
  weak_reduction_ordering /\ left_compatible succ succ_eq
  /\ rewrite_ordering succ_eq.

End weak_reduction_pair.

Record Weak_reduction_pair : Type := mkWeak_reduction_pair {
  wp_succ : relation term;
  wp_succ_eq : relation term;
  wp_subs : substitution_closed wp_succ;
  wp_subs_eq : substitution_closed wp_succ_eq;
  wp_cont : weak_context_closed wp_succ wp_succ_eq;
  wp_cont_eq : context_closed wp_succ_eq;
  wp_comp : wp_succ_eq @ wp_succ << wp_succ;
  wp_succ_wf : WF wp_succ
}.

(***********************************************************************)
(* union of rewrite rules *)

Section union.

Variables R R' : rules.

Lemma red_union : red (R ++ R') << red R U red R'.

Proof.
unfold inclusion. intros. redtac. subst x. subst y.
deduce (in_app_or H). destruct H0.
left. apply red_rule. exact H0. right. apply red_rule. exact H0.
Qed.

Lemma hd_red_union : hd_red (R ++ R') << hd_red R U hd_red R'.

Proof.
unfold inclusion. intros. redtac. subst x. subst y.
deduce (in_app_or H). destruct H0.
left. apply hd_red_rule. exact H0. right. apply hd_red_rule. exact H0.
Qed.

Variables E E' : rules.

Lemma red_mod_union : red_mod E (R ++ R') << red_mod E R U red_mod E R'.

Proof.
unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
deduce (in_app_or H0). destruct H1.
left. exists (fill c (app s l)); split. assumption. apply red_rule. exact H1.
right. exists (fill c (app s l)); split. assumption. apply red_rule. exact H1.
Qed.

Lemma hd_red_mod_union :
  hd_red_mod E (R ++ R') << hd_red_mod E R U hd_red_mod E R'.

Proof.
unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
deduce (in_app_or H0). destruct H1.
left. exists (app s l); split. assumption. apply hd_red_rule. exact H1.
right. exists (app s l); split. assumption. apply hd_red_rule. exact H1.
Qed.

End union.

(***********************************************************************)
(* reflexive closure *)

Section clos_refl.

Variable succ : relation term.

Notation succ_eq := (clos_refl succ).

Lemma rc_context_closed :
  weak_context_closed succ succ_eq -> context_closed succ_eq.

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
unfold left_compatible, inclusion, compose, strict_part.
intros; split; decomp H. eapply succ_eq_trans. apply H1. assumption.
unfold not; intro. deduce (succ_eq_trans H H1). contradiction.
Qed.

End strict.

End S.

(***********************************************************************)
(* tactics *)

Ltac destruct_rp :=
  match goal with
    | h : Reduction_pair _ |- _ => destruct h
    | h : Weak_reduction_pair _ |- _ => destruct h
    | h : reduction_ordering _ |- _ => destruct h
    | h : rewrite_ordering _ |- _ => destruct h
  end.

Ltac WFtac := repeat destruct_rp; assumption.

Ltac rptac := repeat destruct_rp; try split; assumption.

Ltac incl_red :=
  match goal with
    | |- inclusion (red _) ?succ => apply compat_red
    | |- inclusion (red_mod _ _) (rp_succ ?rp) =>
      apply compat_red_mod with (succ_eq := rp_succ_eq rp)
    | |- inclusion (red_mod _ _) (wp_succ ?wp) =>
      apply compat_red_mod with (succ_eq := wp_succ_eq wp)
    | |- inclusion (red_mod _ _) ?succ => apply compat_red_mod_tc
    | |- inclusion (hd_red _) ?succ => apply compat_hd_red
    | |- inclusion (hd_red_mod _ _) (wp_succ ?wp) =>
      apply compat_hd_red_mod with (succ_eq := wp_succ_eq wp)
    | |- inclusion (hd_red_mod _ _) ?succ => eapply compat_hd_red_mod
  end; rptac.
