(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-19
- Sebastien Hinderer, 2004-02-25

well-founded monotone interpretations
************************************************************************)

(* $Id: AWFMInterpretation.v,v 1.3 2006-10-24 12:57:11 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).

Require Export AInterpretation.
Require Export WfUtil.

(***********************************************************************)
(* well-founded interpretations *)

Variable (I : interpretation Sig) (R : relation (domain I)).

Definition IR t1 t2 :=
  forall xint, R (term_int xint t1) (term_int xint t2).

Require Export ARelation.

Lemma IR_substitution_closed : substitution_closed IR.

Proof.
unfold transp, substitution_closed, IR. intros t1 t2 s H xint0.
do 2 rewrite substitutionLemma. apply (H (beta xint0 s)).
Qed.

Definition monotone := forall f, Vmonotone (fint I f) R.

Lemma IR_context_closed : monotone -> context_closed IR.

Proof.
unfold transp, context_closed, IR. intros.
generalize (H0 xint). clear H0. intro. induction c.
simpl. exact H0.
simpl fill. do 2 rewrite term_int_fun.
do 2 (rewrite Vmap_cast; rewrite Vmap_app). simpl. apply H. exact IHc.
Qed.

Lemma IR_wf : wf R -> wf IR.

Proof.
intro. set (xint := fun x:nat => some_elt I).
apply wf_incl with (R2 := fun t1 t2 =>
  transp R (term_int xint t1) (term_int xint t2)).
unfold inclusion, transp. auto.
apply wf_inverse_image with (f := term_int xint). exact H.
Qed.

Lemma IR_reduction_ordering : monotone -> wf R -> reduction_ordering IR.

Proof.
split. apply IR_wf. exact H0. split. apply IR_substitution_closed.
apply IR_context_closed. exact H.
Qed.

End S.
