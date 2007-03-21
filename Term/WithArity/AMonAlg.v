(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03

  This file contains a definition of weakly monotone algebra and extended monotone
algebra and some results concerning them, based on:

References:
-  J. Endrullis, J. Waldmann and H. Zantema, "Matrix Interpretations for Proving
   Termination of Term Rewriting", Proceedings of the 3rd International Joint
   Conference (IJCAR 2006), 2006.
*)

Require Import AWFMInterpretation.

Module Type WeaklyMonotoneAlgebra.

  Parameter Sig: Signature.
    
  (* 
     A weakly monotone algebra consist of:
     - interpretation [I]
     - [gt] and [ge] relations
     along with the following conditions:
     - [IM]: [I] is monotone with respect to [gt]
     - [gt_wf]: [gt] is well-founded
     - [gt_ge_compat]: compatibility between [gt] and [ge]
  *)
  Parameter I: interpretation Sig.
  
  Parameter gt: relation (domain I).
  
  Parameter ge: relation (domain I).
  
  Parameter monotone_ge: monotone I ge.

  Parameter gt_wf: WF gt.

  Parameter gt_ge_compat: absorb gt ge.

End WeaklyMonotoneAlgebra.

Module Type ExtendedMonotoneAlgebra.

  Declare Module WMA: WeaklyMonotoneAlgebra.
  Export WMA.

  (* Extended monotone algebra needs to have strictly montone interpretations *)
  Parameter monotone_gt: monotone I gt.

End ExtendedMonotoneAlgebra.

Module MonotoneAlgebraResults (WMA : WeaklyMonotoneAlgebra).

  Export WMA.
  Require Import ACompat.

  Definition IR_gt := IR I gt.
  Definition IR_ge := IR I ge.

  Notation term := (term Sig).
  Notation rule := (rule Sig).
  Notation rules := (list rule).

  Lemma absorb_gt_ge : absorb IR_gt IR_ge.

  Proof.
    intros x z xz val.
    apply gt_ge_compat.
    destruct xz as [y [ge_xy gt_yz]].
    exists (term_int val y). split; auto.
  Qed.

  Lemma IR_rewrite_ordering : forall succ, monotone I succ -> rewrite_ordering (IR I succ).

  Proof.
    split.
    apply IR_substitution_closed.
    apply IR_context_closed.
    assumption.
  Qed.

  Lemma ma_ge_rewrite_ordering : rewrite_ordering IR_ge.

  Proof.
    unfold IR_ge. apply IR_rewrite_ordering.
    exact monotone_ge.
  Qed.

  Section Termination.

    Variable R E : rules.

    Lemma ma_compat_hd_red_mod : 
      compatible IR_gt R ->
      compatible IR_ge E ->
      WF (hd_red_mod E R).

    Proof.
      intros. apply WF_incl with IR_gt.
      apply compat_hd_red_mod with IR_ge; trivial.
      unfold IR_gt. apply IR_substitution_closed.
      exact ma_ge_rewrite_ordering.
      exact absorb_gt_ge.
      unfold IR_gt. apply IR_WF. exact gt_wf.
    Qed.

  End Termination.

End MonotoneAlgebraResults.

Module ExtendedMonotoneAlgebraResults (EMA: ExtendedMonotoneAlgebra).

  Module MAR := MonotoneAlgebraResults EMA.WMA.
  Export MAR.
  Export EMA.

  Require Import ACompat.

  Lemma ma_gt_rewrite_ordering : rewrite_ordering IR_gt.

  Proof.
    unfold IR_gt. apply IR_rewrite_ordering.
    exact monotone_gt.
  Qed.

  Section Termination.

    Variable R E : rules.

    Lemma ma_compat_red_mod : 
      compatible IR_gt R ->
      compatible IR_ge E ->
      WF (red_mod E R).

    Proof.
      intros. apply WF_incl with IR_gt.
      apply compat_red_mod with IR_ge; trivial.
      exact ma_gt_rewrite_ordering.
      exact ma_ge_rewrite_ordering.
      exact absorb_gt_ge.
      unfold IR_gt. apply IR_WF. exact gt_wf.
    Qed.

  End Termination.

End ExtendedMonotoneAlgebraResults.
