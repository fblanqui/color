(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09
- Frederic Blanqui, 2005-02-17

termination by using compatible reduction orderings
************************************************************************)

(* $Id: ARedOrd.v,v 1.2 2006-10-19 14:51:51 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ARelation.

Notation term := (term Sig).
Notation rule := (rule Sig).
Notation rules := (list rule).

(***********************************************************************)
(* Manna-Ness theorem (1970) *)

Section manna_ness.

Variables (R : rules) (succ : relation term).

Lemma manna_ness : reduction_ordering succ -> compatible succ R -> wf (red R).

Proof.
intros (Hwf, (Hsubst, Hcont)) Hcomp.
apply wf_incl with (R2 := transp succ). 2: exact Hwf.
apply incl_transp. unfold inclusion. apply comp_rewrite_ord.
split; [exact Hsubst | exact Hcont]. exact Hcomp.
Qed.

End manna_ness.

(***********************************************************************)
(* an extension for proving the well-foundedness of relations of the form:
several steps of R1 followed by a step of R2 *)

Section manna_ness2.

Variables R1 R2 : rules.

Let R t v := exists u, clos_refl_trans (red R1) t u /\ red R2 u v.

Variables (succ succ_eq : relation term)
  (succ_eq_refl : reflexive succ_eq) (succ_eq_trans : transitive succ_eq)
  (succ_eq_incl : inclusion succ succ_eq)
  (compat : inclusion (compose succ_eq succ) succ).

Lemma manna_ness2 : reduction_ordering succ -> rewrite_ordering succ_eq
  -> compatible succ_eq R1 -> compatible succ R2 -> wf R.

Proof.
intros (Hwf, Hsucc) Hsucceq Hcompeq Hcomp. unfold well_founded. intro.
generalize (Hwf a). intro. elim H. clear a H. intros. apply Acc_intro. intros.
unfold transp, R in H1. decomp H1. apply H0. unfold transp.
apply compat. unfold compose. exists x0. split. eapply comp_rewrite_ord_rtc.
assumption. assumption. assumption. apply Hcompeq. assumption.
eapply comp_rewrite_ord. assumption. apply Hcomp. assumption.
Qed.

End manna_ness2.

(***********************************************************************)
(* an extension for proving the well-foundedness of relations of the form:
several steps of R1 followed by a -head- step of R2 *)

Section manna_ness2_head.

Variables R1 R2 : rules.

Let R t v := exists u, clos_refl_trans (red R1) t u /\ hd_red R2 u v.

Variables (succ succ_eq : relation term)
  (succ_eq_refl : reflexive succ_eq) (succ_eq_trans : transitive succ_eq)
  (succ_eq_incl : inclusion succ succ_eq)
  (compat : inclusion (compose succ_eq succ) succ).

Lemma manna_ness2_head : wf succ -> substitution_closed succ
  -> rewrite_ordering succ_eq -> compatible succ_eq R1
  -> compatible succ R2 -> wf R.

Proof.
intros Hwf Hsucc Hsucceq Hcompeq Hcomp. unfold well_founded. intro.
generalize (Hwf a). intro. elim H. clear a H. intros. apply Acc_intro. intros.
unfold transp, R in H1. decomp H1. apply H0. unfold transp.
apply compat. unfold compose. exists x0. split. eapply comp_rewrite_ord_rtc.
assumption. assumption. assumption. apply Hcompeq. assumption.
eapply comp_head_rewrite_ord. assumption. apply Hcomp. assumption.
Qed.

End manna_ness2_head.

End S.
