(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-12-01

termination by using compatible reduction orderings
*)

(* $Id: AMannaNess.v,v 1.12 2008-09-24 10:20:55 joerg Exp $ *)

Set Implicit Arguments.

Require Export ACompat.

Section S.

Variable Sig : Signature.

Notation term := (term Sig).
Notation rule := (rule Sig).
Notation rules := (list rule).

Ltac WF_incl succ := apply WF_incl with (S := succ); [idtac | WFtac].

(***********************************************************************)
(** Manna-Ness theorem (1970) *)

Section manna_ness.

Variables (R : rules) (succ : relation term).

Lemma manna_ness : reduction_ordering succ -> compat succ R -> WF (red R).

Proof.
intros. WF_incl succ. incl_red.
Qed.

End manna_ness.

(***********************************************************************)
(** an extension for proving the well-foundedness of relations of the form:
several steps of R1 followed by a step of R2 *)

Section manna_ness_mod.

Variables R E : rules.

Lemma manna_ness_mod : forall rp : Reduction_pair Sig,
  compat (rp_succ_eq rp) E -> compat (rp_succ rp) R -> WF (red_mod E R).

Proof.
intros. WF_incl (rp_succ rp). incl_red.
Qed.

End manna_ness_mod.

(***********************************************************************)
(** an extension for proving the well-foundedness of relations of the form:
several steps of R1 followed by a -head- step of R2 *)

Section manna_ness_hd_mod.

Variables R E : rules.

Lemma manna_ness_hd_mod : forall wp : Weak_reduction_pair Sig,
  compat (wp_succ_eq wp) E -> compat (wp_succ wp) R -> WF (hd_red_mod E R).

Proof.
intros. WF_incl (wp_succ wp). incl_red.
Qed.

End manna_ness_hd_mod.

(***********************************************************************)
(** rule elimination *)

Section rule_elimination.

Variables R R' : rules.

Section mod.

Variables E E' : rules.

Require Import Lexico.

Lemma rule_elimination_mod : forall rp : Reduction_pair Sig,
  compat (rp_succ_eq rp) E -> compat (rp_succ rp) E' ->
  compat (rp_succ_eq rp) R -> compat (rp_succ rp) R' ->
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
comp. apply incl_rtc. unfold succ. incl_red.
(* h2 *)
assert (h2 : red_mod F (R ++ R') << succ# @ er U succ!).
trans (red_mod F R U red_mod F R'). apply red_mod_union. union.
(* left *)
unfold red_mod. trans ((succ # @ red E #) @ red R). comp. exact h1. assoc.
(* right *)
trans ((succ # @ red E #) @ red R'). unfold red_mod. comp. exact h1. assoc.
trans (succ # @ succ). comp.
trans (red_mod E R'). unfold succ. incl_red. apply rtc_step_incl_tc.
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
eapply WF_incl with (S := lex' gt (er!)).
trans (er U gt). exact h3. trans (er! U gt). union.
apply tc_incl. trans (gt U er!). apply union_commut.
apply lex'_intro. apply WF_lex'.
(* WF gt *)
unfold gt. apply WF_compat_inv. exact h4. apply WF_tc. WFtac.
(* WF er! *)
apply WF_tc. exact H3.
(* er! trans *)
apply tc_trans.
(* compat *)
apply comp_tc_incl. trans (succ_eq! @ gt). comp. exact h0.
apply comp_tc_incl. unfold gt. assoc. comp. apply comp_incl_tc. rptac.
Qed.

Lemma weak_rule_elimination_mod : forall wp : Weak_reduction_pair Sig,
  compat (wp_succ_eq wp) E ->
  compat (wp_succ_eq wp) R -> compat (wp_succ wp) R' ->
  WF (hd_red_mod E R) -> WF (hd_red_mod E (R ++ R')).

Proof.
intros. set (succ := wp_succ wp). set (succ_eq := wp_succ_eq wp).
set (er := hd_red_mod E R). set (er' := hd_red_mod E R').
apply WF_incl with (S := lex' succ (er!)).
trans (er U succ). trans (er U er'). unfold er, er'. apply hd_red_mod_union.
union. unfold er', succ. incl_red.
trans (succ U er). apply union_commut.
trans (succ U er!). union. apply tc_incl.
apply lex'_intro. apply WF_lex'. WFtac. apply WF_tc. exact H2. apply tc_trans.
apply comp_tc_incl. trans (succ_eq! @ succ). comp. unfold er.
trans (red_mod E R). apply hd_red_mod_incl_red_mod. incl_red.
apply comp_tc_incl. rptac.
Qed.

Lemma weak_rule_elimination_mod_min : forall wp : Weak_reduction_pair Sig,
  compat (wp_succ_eq wp) E ->
  compat (wp_succ_eq wp) R -> compat (wp_succ wp) R' ->
  WF (hd_red_mod_min E R) -> WF (hd_red_mod_min E (R ++ R')).

Proof.
  intros. set (succ := wp_succ wp). set (succ_eq := wp_succ_eq wp).
  set (er := hd_red_mod_min E R). set (er' := hd_red_mod_min E R').
  apply WF_incl with (S := lex' succ (er!)).
  trans (er U succ). trans (er U er'). unfold er, er'. apply hd_red_mod_min_union.
  union. unfold er', succ. incl_red.
  trans (succ U er). apply union_commut.
  trans (succ U er!). union. apply tc_incl.
  apply lex'_intro. apply WF_lex'. WFtac. apply WF_tc. exact H2. apply tc_trans.
  apply comp_tc_incl. trans (succ_eq! @ succ). comp. unfold er.
  trans (red_mod E R). apply incl_trans with (hd_red_mod E R).
  apply hd_red_mod_min_incl. apply hd_red_mod_incl_red_mod. incl_red.
  apply comp_tc_incl. rptac.
Qed.

End mod.

Lemma rule_elimination : forall rp : Reduction_pair Sig,
  compat (rp_succ_eq rp) R -> compat (rp_succ rp) R' ->
  WF (red R) -> WF (red (R ++ R')).

Proof.
intros. eapply WF_incl. apply red_incl_red_mod.
change (WF (red_mod (nil++nil) (R++R'))). eapply rule_elimination_mod.
unfold compat. simpl. intuition.
unfold compat. simpl. intuition.
apply H. apply H0.
eapply WF_incl. apply red_mod_empty_incl_red. exact H1.
Qed.

Lemma weak_rule_elimination : forall wp : Weak_reduction_pair Sig,
  compat (wp_succ_eq wp) R -> compat (wp_succ wp) R' ->
  WF (hd_red R) -> WF (hd_red (R ++ R')).

Proof.
intros. eapply WF_incl. apply hd_red_incl_hd_red_mod.
change (WF (hd_red_mod (nil++nil) (R++R'))). eapply weak_rule_elimination_mod.
unfold compat. simpl. intuition.
unfold compat. simpl. intuition.
apply H0. eapply WF_incl. simpl. apply hd_red_mod_empty_incl_hd_red. exact H1.
Qed.

End rule_elimination.

(*Lemma rule_filter : forall (rp : Reduction_pair Sig)
  f (h : forall x y, f x y = true -> rp_succ rp x y) RR',
  let f_rule a := match a with mkRule l r => f l r end in
  let (R', R) := partition f_rule RR' in
  compat (rp_succ_eq rp) R -> WF (red R) -> WF (red RR').*)

End S.
