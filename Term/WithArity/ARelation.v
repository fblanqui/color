(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09

general definitions and results about relations on terms
*)

(* $Id: ARelation.v,v 1.12 2007-02-07 12:44:06 blanqui Exp $ *)

Set Implicit Arguments.

Require Export SN.
Require Export ASubstitution.

Section S.

Variable Sig : Signature.

Notation term := (term Sig).

(***********************************************************************)
(** basic definitions and properties *)

Section basic.

Variable succ : relation term.

Definition preserv_vars := forall t u, succ t u -> incl (vars u) (vars t).

Definition substitution_closed :=
  forall t1 t2 s, succ t1 t2 -> succ (app s t1) (app s t2).

Definition context_closed :=
  forall t1 t2 c, succ t1 t2 -> succ (fill c t1) (fill c t2).

Definition rewrite_ordering := substitution_closed /\ context_closed.

Definition reduction_ordering := WF succ /\ rewrite_ordering.

End basic.

Record Rewrite_ordering : Type := mkRewrite_ordering {
  rew_ord_rel :> relation term;
  rew_ord_subs : substitution_closed rew_ord_rel;
  rew_ord_cont : context_closed rew_ord_rel
}.

(***********************************************************************)
(** reduction pair *)

Section reduction_pair.

Variables succ succ_eq : relation term.

Definition left_compatible := succ_eq @ succ << succ.

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
(** weak reduction pair *)

Section weak_reduction_pair.

Variables succ succ_eq : relation term.

Definition weak_context_closed :=
  forall t1 t2 c, succ t1 t2 -> succ_eq (fill c t1) (fill c t2).

Definition weak_rewrite_ordering :=
  substitution_closed succ /\ weak_context_closed.

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
(** reflexive closure *)

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
(** when succ is the strict part of succ_eq *)

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
(** tactics *)

Ltac destruct_rp :=
  match goal with
    | h : Reduction_pair _ |- _ => destruct h
    | h : Weak_reduction_pair _ |- _ => destruct h
    | h : reduction_ordering _ |- _ => destruct h
    | h : rewrite_ordering _ |- _ => destruct h
  end.

Ltac WFtac := repeat destruct_rp; assumption.

Ltac rptac := repeat destruct_rp; try split; assumption.
