(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-01-25
- Sebastien Hinderer, 2004-02-09

general definitions and results about relations on terms
*)

(* $Id: ACompat.v,v 1.8 2007-04-13 10:36:36 blanqui Exp $ *)

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

Variable succ : relation term.

Definition compat R := forall l r : term, In (mkRule l r) R -> succ l r.

Lemma compat_red : forall R,
  rewrite_ordering succ -> compat R -> red R << succ.

Proof.
intro. unfold inclusion. intros (Hsubs,Hcont) Hcomp t u H. redtac.
subst t. subst u. apply Hcont. apply Hsubs. apply Hcomp. exact H.
Qed.

Lemma compat_hd_red : forall R,
  substitution_closed succ -> compat R -> hd_red R << succ.

Proof.
unfold inclusion. intros. redtac. subst x. subst y. apply H. apply H0. exact H1.
Qed.

Lemma incl_compat : forall R S, incl R S -> compat S -> compat R.

Proof.
unfold compat. intros. apply H0. apply H. exact H1.
Qed.

Lemma compat_red_mod_tc : forall R E,
  rewrite_ordering succ -> compat E -> compat R -> red_mod E R << succ!.

Proof.
intros. unfold red_mod. trans (succ# @ succ). comp.
apply incl_rtc. apply compat_red; assumption. apply compat_red; assumption.
apply rtc_step_incl_tc.
Qed.

Lemma compat_cons : forall l r R,
  succ l r -> compat R -> compat (mkRule l r :: R).

Proof.
unfold compat. simpl. intros. destruct H1.
injection H1. intros. subst l0. subst r0. exact H.
apply H0. exact H1.
Qed.

Lemma compat_cons_elim : forall l r R,
  compat (mkRule l r :: R) -> succ l r /\ compat R.

Proof.
unfold compat. simpl. intros. split; intros; apply H; intuition.
Qed.

Lemma compat_app : forall R R',
  compat R -> compat R' -> compat (R ++ R').

Proof.
intros R R' Rsucc R'succ l r lr. destruct (in_app_or lr).
apply Rsucc. assumption. apply R'succ. assumption.
Qed.

Definition compat_rule a := match a with mkRule l r => succ l r end.

Lemma compat_lforall : forall R, lforall compat_rule R -> compat R.

Proof.
induction R; unfold compat; simpl; intros.
contradiction. intuition. subst a. exact H1.
Qed.

(***********************************************************************)
(** decidability *)

Variable succ_dec : rel_dec succ.

Function is_compat (R : rules) : bool :=
  match R with
    | nil => true
    | cons a R' =>
      match a with mkRule l r =>
        match succ_dec l r with
          | left _ => is_compat R'
          | right _ => false
        end
      end
  end.

Lemma is_compat_correct : forall R,
  is_compat R = true -> compat R /\ is_compat R = false -> ~compat R.

Proof.
induction R; simpl. intuition.
destruct a. case (succ_dec lhs rhs); intros;
  destruct H0; deduce (compat_cons_elim H0); intuition.
Qed.

Lemma is_compat_complete : forall R,
  compat R -> is_compat R = true /\ ~compat R -> is_compat R = false.

Proof.
induction R; simpl. intuition.
destruct a. intro. deduce (compat_cons_elim H). destruct H0.
case (succ_dec lhs rhs); intros; destruct H2.
apply IHR. exact H1. intuition. refl.
Qed.

End compat.

(***********************************************************************)
(** reduction pair *)

Section reduction_pair.

Variables succ succ_eq : relation term.

Lemma compat_red_mod : forall R E,
  rewrite_ordering succ -> rewrite_ordering succ_eq ->
  compat succ_eq E -> compat succ R ->
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
  compat succ_eq E -> compat succ R ->
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
