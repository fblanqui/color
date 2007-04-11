(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-01-25
- Sebastien Hinderer, 2004-02-09

general definitions and results about relations on terms
*)

(* $Id: ACompat.v,v 1.6 2007-04-11 17:51:02 blanqui Exp $ *)

Set Implicit Arguments.

Require Export ATrs.

Section S.

Variable Sig : Signature.

Notation term := (term Sig).
Notation rule := (rule Sig).
Notation rules := (list rule).

(***********************************************************************)
(** compatibility *)

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

Lemma incl_compat : forall succ (R S : rules),
  incl R S -> compatible succ S -> compatible succ R.

Proof.
unfold compatible. intros. apply H0. apply H. exact H1.
Qed.

Lemma compat_red_mod_tc : forall succ R E,
  rewrite_ordering succ -> compatible succ E -> compatible succ R ->
  red_mod E R << succ!.

Proof.
intros. unfold red_mod. trans (succ# @ succ). comp.
apply incl_rtc. apply compat_red; assumption. apply compat_red; assumption.
apply rtc_step_incl_tc.
Qed.

Lemma compatible_app : forall succ R R',
  compatible succ R -> compatible succ R' -> compatible succ (R ++ R').

Proof.
  intros succ R R' Rsucc R'succ l r lr. destruct (in_app_or lr).
  apply Rsucc. assumption. 
  apply R'succ. assumption.
Qed.

(***********************************************************************)
(** reduction pair *)

Section reduction_pair.

Variables succ succ_eq : relation term.

Lemma compat_red_mod : forall R E,
  rewrite_ordering succ -> rewrite_ordering succ_eq ->
  compatible succ_eq E -> compatible succ R ->
  absorb succ succ_eq -> red_mod E R << succ.

Proof.
intros. unfold red_mod. trans (succ_eq# @ succ). comp. apply incl_rtc.
apply compat_red; assumption. destruct H0. apply compat_red; assumption.
apply comp_rtc_incl. exact H3.
Qed.

End reduction_pair.

(***********************************************************************)
(** weak reduction pair *)

Section weak_reduction_pair.

Variables succ succ_eq : relation term.

Lemma compat_hd_red_mod : forall R E,
  substitution_closed succ -> rewrite_ordering succ_eq ->
  compatible succ_eq E -> compatible succ R ->
  absorb succ succ_eq -> hd_red_mod E R << succ.

Proof.
intros. unfold hd_red_mod. trans (succ_eq# @ succ). comp. apply incl_rtc.
apply compat_red; assumption. apply compat_hd_red; assumption.
apply comp_rtc_incl. exact H3.
Qed.

End weak_reduction_pair.

End S.

(***********************************************************************)
(** tactics *)

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
