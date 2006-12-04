(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-12-01

termination by using compatible reduction orderings
************************************************************************)

(* $Id: ARedOrd.v,v 1.6 2006-12-04 12:53:52 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ARelation.

Notation term := (term Sig).
Notation rule := (rule Sig).
Notation rules := (list rule).

Ltac WF_incl succ := apply WF_incl with (S := succ); [idtac | WFtac].

(***********************************************************************)
(* Manna-Ness theorem (1970) *)

Section manna_ness.

Variables (R : rules) (succ : relation term).

Lemma manna_ness : reduction_ordering succ -> compatible succ R -> WF (red R).

Proof.
intros. WF_incl succ. incl_red.
Qed.

End manna_ness.

(***********************************************************************)
(* an extension for proving the well-foundedness of relations of the form:
several steps of R1 followed by a step of R2 *)

Section manna_ness2.

Variables R E : rules.

Lemma manna_ness2_incl : forall rp : Reduction_pair Sig,
  compatible (rp_succ_eq rp) E -> compatible (rp_succ rp) R ->
  inclusion (red_mod E R) (rp_succ rp).

Proof.
intros. unfold red_mod. apply incl_trans with
  (S := compose (clos_refl_trans (rp_succ_eq rp)) (rp_succ rp)).
apply incl_comp. apply incl_rtc. incl_red. incl_red.
apply comp_rtc_incl. exact (rp_comp rp).
Qed.

Lemma manna_ness2 : forall rp : Reduction_pair Sig,
  compatible (rp_succ_eq rp) E -> compatible (rp_succ rp) R -> WF (red_mod E R).

Proof.
intros. WF_incl (rp_succ rp). apply manna_ness2_incl; auto.
Qed.

End manna_ness2.

(***********************************************************************)
(* an extension for proving the well-foundedness of relations of the form:
several steps of R1 followed by a -head- step of R2 *)

Section manna_ness2_head.

Variables R E : rules.

Lemma manna_ness2_head_incl : forall wp : Weak_reduction_pair Sig,
  compatible (wp_succ_eq wp) E -> compatible (wp_succ wp) R ->
  inclusion (hd_red_mod E R) (wp_succ wp).

Proof.
intros. unfold hd_red_mod. apply incl_trans with
  (S := compose (clos_refl_trans (wp_succ_eq wp)) (wp_succ wp)).
apply incl_comp. apply incl_rtc. incl_red. incl_red.
apply comp_rtc_incl. exact (wp_comp wp).
Qed.

Lemma manna_ness2_head : forall wp : Weak_reduction_pair Sig,
  compatible (wp_succ_eq wp) E -> compatible (wp_succ wp) R ->
  WF (hd_red_mod E R).

Proof.
intros. WF_incl (wp_succ wp). apply manna_ness2_head_incl; auto.
Qed.

End manna_ness2_head.

(***********************************************************************)
(* rule elimination *)

Section rule_elimination.

Variables R R' E E' : rules.

Lemma rule_elimination : forall rp : Reduction_pair Sig,
  compatible (rp_succ_eq rp) E -> compatible (rp_succ rp) E' ->
  compatible (rp_succ_eq rp) R -> compatible (rp_succ rp) R' ->
  WF (red_mod E R) -> WF (red_mod (E ++ E') (R ++ R')).

Proof.
intros. set (succ := rp_succ rp). set (succ_eq := rp_succ_eq rp).
set (er := red_mod E R). set (F := E ++ E').
(* h0 *)
assert (h0 : er << succ_eq!). unfold er, succ_eq. incl_red.
(* h1 *)
assert (h1 : red F # << succ # @ red E #).
trans ((red E U red E')#). apply incl_rtc. unfold F. apply red_union.
trans (red_mod E E' # @ red E #). unfold red_mod. apply rtc_union.
comp. apply incl_rtc. unfold succ. apply manna_ness2_incl; assumption.
(* h2 *)
assert (h2 : red_mod F (R ++ R') << succ# @ er U succ!).
trans (red_mod F R U red_mod F R'). apply red_mod_union. union.
(* left *)
unfold red_mod. trans ((succ # @ red E #) @ red R). comp. exact h1.
trans (succ # @ (red E # @ red R)). apply comp_assoc.
(* right *)
trans ((succ # @ red E #) @ red R'). unfold red_mod. comp. exact h1.
trans (succ # @ (red E # @ red R')). apply comp_assoc.
trans (succ # @ succ). comp.
trans (red_mod E R'). unfold succ.
apply manna_ness2_incl; assumption. apply rtc_step_incl_tc.
(* h3 *)
set (gt := succ! @ succ_eq#). assert (h3 : red_mod F (R ++ R') << er U gt).
trans (succ# @ er U succ!). exact h2.
trans ((er U succ! @ er) U succ!). union. apply rtc_comp.
trans (er U (succ! @ er U succ!)). apply union_assoc. union.
trans (succ! @ er%). apply union_fact2. unfold gt. comp.
apply incl_rc_rtc. exact h0.
(* h4 *)
assert (h4 : succ_eq# @ succ! << succ!).
apply comp_incl_tc. apply comp_rtc_incl. rptac.
(* lexico *)
Require Import Lexico. eapply WF_incl with (S := lex' gt (er!)).
trans (er U gt). exact h3. trans (er! U gt). union.
apply tc_incl. trans (gt U er!). apply union_commut.
apply lex'_intro. apply lex'_WF.
(* WF gt *)
unfold gt. apply WF_compat_inv. exact h4. apply WF_tc. WFtac.
(* WF er! *)
apply WF_tc. exact H3.
(* er! trans *)
apply tc_trans.
(* compat *)
apply comp_tc_incl. trans (succ_eq! @ gt). comp. exact h0.
apply comp_tc_incl. unfold gt.
trans ((succ_eq @ succ!) @ succ_eq#). apply comp_assoc'.
comp. apply comp_incl_tc. rptac.
Qed.

End rule_elimination.

End S.
