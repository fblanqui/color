(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09

general definitions and results about relations on terms
************************************************************************)

(* $Id: ARelation.v,v 1.6 2006-12-01 09:37:48 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATrs.

Notation term := (term Sig).
Notation rule := (rule Sig).
Notation rules := (list rule).

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

Require Export SN.

Definition reduction_ordering := WF succ /\ rewrite_ordering.

(***********************************************************************)
(* compatibility *)

Variable R : rules.

Definition compatible := forall l r : term, In (mkRule l r) R -> succ l r.

Lemma comp_rewrite_ord : rewrite_ordering -> compatible ->
  forall t u, red R t u -> succ t u.

Proof.
intros (Hsubs,Hcont) Hcomp t u H. redtac. subst t. subst u.
apply Hcont. apply Hsubs. apply Hcomp. exact H.
Qed.

Lemma comp_rewrite_ord_incl : rewrite_ordering -> compatible -> red R << succ.

Proof.
unfold inclusion. intros. apply comp_rewrite_ord; assumption.
Qed.

Lemma comp_head_rewrite_ord : substitution_closed -> compatible ->
  forall t u, hd_red R t u -> succ t u.

Proof.
intros. redtac. subst t. subst u. apply H. apply H0. assumption.
Qed.

Lemma comp_head_rewrite_ord_incl :
  substitution_closed -> compatible -> hd_red R << succ.

Proof.
unfold inclusion. intros. apply comp_head_rewrite_ord; assumption.
Qed.

End basic.

Lemma comp_mod_rewrite_ord_incl : forall succ R E,
  rewrite_ordering succ -> compatible succ E -> compatible succ R ->
  red_mod E R << succ!.

Proof.
unfold inclusion. intros. do 2 destruct H2. deduce (rtc_split H2). destruct H4.
subst x0. apply t_step. apply incl_elim with (R := red R). 2: exact H3.
apply comp_rewrite_ord_incl; assumption.
apply t_trans with (y := x0). apply incl_elim with (R := red E !).
2: exact H4. apply incl_tc. apply comp_rewrite_ord_incl; assumption.
apply t_step. apply incl_elim with (R := red R). 2: exact H3.
apply comp_rewrite_ord_incl; assumption.
Qed.

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

Definition weak_rewrite_ordering :=
  substitution_closed succ /\ weak_context_closed.

Definition weak_reduction_ordering := WF succ /\ weak_rewrite_ordering.

(***********************************************************************)
(* reduction pairs *)

Definition left_compatible := inclusion (compose succ_eq succ) succ.

Definition reduction_pair :=
  weak_reduction_ordering /\ left_compatible /\ rewrite_ordering succ_eq.

End reduction_pair.

Record Weak_reduction_pair : Type := mkWeak_reduction_pair {
  wp_succ : relation term;
  wp_succ_eq : relation term;
  wp_subs : substitution_closed wp_succ;
  wp_subs_eq : substitution_closed wp_succ_eq;
  wp_cont : weak_context_closed wp_succ wp_succ_eq;
  wp_cont_eq : context_closed wp_succ_eq;
  wp_comp : inclusion (compose wp_succ_eq wp_succ) wp_succ;
  wp_succ_wf : WF wp_succ
}.

Record Reduction_pair : Type := mkReduction_pair {
  rp_succ : relation term;
  rp_succ_eq : relation term;
  rp_subs : substitution_closed rp_succ;
  rp_subs_eq : substitution_closed rp_succ_eq;
  rp_cont : context_closed rp_succ;
  rp_cont_eq : context_closed rp_succ_eq;
  rp_comp : inclusion (compose rp_succ_eq rp_succ) rp_succ;
  rp_succ_wf : WF rp_succ
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

Variables E E' : rules.

Lemma red_mod_union : red_mod E (R ++ R') << red_mod E R U red_mod E R'.

Proof.
unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
deduce (in_app_or H0). destruct H1.
left. exists (fill c (app s l)); split. assumption. apply red_rule. exact H1.
right. exists (fill c (app s l)); split. assumption. apply red_rule. exact H1.
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
    | |- inclusion (red _) ?succ => apply comp_rewrite_ord_incl
    | |- inclusion (red_mod _ _) ?succ => apply comp_mod_rewrite_ord_incl
    | |- inclusion (hd_red _) ?succ => apply comp_head_rewrite_ord_incl
  end; rptac.
