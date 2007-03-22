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

(***********************************************************************)
(** * Module type specifying a weakly monotone algebra.                *)
(***********************************************************************)
Module Type MonotoneAlgebraType.

  Parameter Sig: Signature.
    
  (**
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

End MonotoneAlgebraType.

(***********************************************************************)
(** * Module type specifying an extended weakly monotone algebra.      *)
(***********************************************************************)
Module Type ExtendedMonotoneAlgebraType.

  Declare Module MA: MonotoneAlgebraType.
  Export MA.

  (** Extended monotone algebra is a wekaly monotone algebra in which every operation
      is monotone with respect to [gt] *)
  Parameter monotone_gt: monotone I gt.

End ExtendedMonotoneAlgebraType.

(***********************************************************************)
(** * Functor with a theory of weakly monotone algebras                *)
(***********************************************************************)
Module MonotoneAlgebraResults (MA : MonotoneAlgebraType).

  Export MA.
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

(**********************************************************************)
(** top termination (for DP setting) criterion with monotone algebras *)
  Section TopTermination.

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

  End TopTermination.

(**********************************************************)
(** criterion for modular removal of rules for relative top
    termination with monotone algebras *)
  Section ModularTopTermination.

    Variable R R' E : rules.

    (* Modular removal of rules *)
    Lemma ma_modular_hd_red_mod :
      WF (hd_red_mod E R') ->
      compatible IR_gt R ->
      compatible IR_ge (R' ++ E) ->
      WF (hd_red_mod E (R ++ R')).

    Proof.
      intros. unfold hd_red_mod.
      apply WF_incl with (red E# @ (hd_red R' U hd_red R)).
      comp. trans (hd_red (R' ++ R)). 
      apply hd_red_swap. apply hd_red_union.
      apply wf_rel_mod_simpl. assumption.
      apply WF_incl with (hd_red_mod (R' ++ E) R).
      unfold hd_red_mod. comp. apply incl_rtc. 
      trans (red R' U red E). apply incl_union. apply hd_red_incl_red. intuition.
      apply red_union_inv.
      apply ma_compat_hd_red_mod; trivial.
    Qed.

  End ModularTopTermination.

End MonotoneAlgebraResults.

(***********************************************************************)
(** * Functor with a theory of extended monotone algebras              *)
(***********************************************************************)
Module ExtendedMonotoneAlgebraResults (EMA: ExtendedMonotoneAlgebraType).

  Module MAR := MonotoneAlgebraResults EMA.MA.
  Export MAR.
  Export EMA.

  Require Import ACompat.

  Lemma ma_gt_rewrite_ordering : rewrite_ordering IR_gt.

  Proof.
    unfold IR_gt. apply IR_rewrite_ordering.
    exact monotone_gt.
  Qed.

(**********************************************************)
(** relative termination criterion with monotone algebras *)
  Section RelativeTermination.

    Variable R E : rules.

    (* Termination in one go *)
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

  End RelativeTermination.

(**********************************************************)
(** criterion for modular removal of rules for relative 
    termination with monotone algebras *)
  Section ModularRelativeTermination.

    Variable R E R' E' : rules.

    (* Modular removal of rules *)
    Lemma ma_modular_red_mod :
      WF (red_mod E' R') ->
      compatible IR_gt (R  ++ E ) ->
      compatible IR_ge (R' ++ E') ->
      WF (red_mod (E ++ E') (R ++ R')).

    Proof.
      intros. unfold red_mod.
      apply WF_incl with ((red E' U red E)# @ (red R' U red R)).
      comp. apply incl_rtc. 
      trans (red (E' ++ E)). apply red_swap. apply red_union. 
      trans (red (R' ++ R)). apply red_swap. apply red_union.
      apply wf_rel_mod. fold (red_mod E' R'). assumption.
      apply WF_incl with (red_mod (R' ++ E') (R ++ E)).
      unfold red_mod. comp. 
      apply incl_rtc. apply red_union_inv. apply red_union_inv.
      apply ma_compat_red_mod; trivial.
    Qed.

  End ModularRelativeTermination.

End ExtendedMonotoneAlgebraResults.
