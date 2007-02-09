(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-05

union of two wellfounded relations
*)

Set Implicit Arguments.

Require Export SN.

(***********************************************************************)
(** R @ S << S @ R -> WF R -> WF S -> WF (R U S) *)

Section commut.

Variables (A : Set) (R S : relation A) (commut : R @ S << S @ R).

Require Export Lexico.

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
unfold gt1, gt2. assoc. comp. trans (R# @ T!). comp. apply tc_incl_rtc.
unfold T. apply rtc_comp_modulo.
Qed.

End commut.
