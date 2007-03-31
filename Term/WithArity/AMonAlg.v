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

Require Export AWFMInterpretation.

(***********************************************************************)
(** * Module type specifying a weakly monotone algebra.                *)
(***********************************************************************)
Module Type MonotoneAlgebraType.

  Parameter Sig : Signature.
    
  (**
     A weakly monotone algebra consist of:
     - interpretation [I]
     - [succ] and [succeq] relations
     along with the following conditions:
     - [IM]: [I] is monotone with respect to [succ]
     - [succ_wf]: [succ] is well-founded
     - [succ_succeq_compat]: compatibility between [succ] and [succeq]
     - [succ_dec] ([succeq_dec]): decidability of [succ] ([succeq])
  *)
  Parameter I : interpretation Sig.
  
  Notation A := (domain I).

  Parameter succ : relation A.
  
  Parameter succeq : relation A.
  
  Parameter monotone_succeq : monotone I succeq.

  Parameter succ_wf : WF succ.

  Parameter succ_succeq_compat : absorb succ succeq.

  (** For certification of concrete examples we need some subrelations of 
      [succ] and [succeq] that are decidable *)

  Notation IR_succ := (IR I succ).
  Notation IR_succeq := (IR I succeq).
  Notation term := (term Sig).

  Parameters (succ' : relation term) (succeq' : relation term).
  Parameters (succ'_sub : succ' << IR_succ) (succeq'_sub : succeq' << IR_succeq).
  Parameters (succ'_dec : rel_dec succ') (succeq'_dec : rel_dec succeq').

End MonotoneAlgebraType.

(***********************************************************************)
(** * Module type specifying an extended weakly monotone algebra.      *)
(***********************************************************************)
Module Type ExtendedMonotoneAlgebraType.

  Declare Module MA : MonotoneAlgebraType.
  Export MA.

  (** Extended monotone algebra is a wekaly monotone algebra in which every operation
      is monotone with respect to [succ] *)
  Parameter monotone_succ : monotone I succ.

End ExtendedMonotoneAlgebraType.

(***********************************************************************)
(** * Functor with a theory of weakly monotone algebras                *)
(***********************************************************************)
Module MonotoneAlgebraResults (MA : MonotoneAlgebraType).

  Export MA.
  Require Import ACompat.

  Notation IR_succ := (IR I succ).
  Notation IR_succeq := (IR I succeq).

  Notation term := (term Sig).
  Notation rule := (rule Sig).
  Notation rules := (list rule).

  Lemma absorb_succ_succeq : absorb IR_succ IR_succeq.

  Proof.
    intros x z xz val.
    apply succ_succeq_compat.
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

  Lemma ma_succeq_rewrite_ordering : rewrite_ordering IR_succeq.

  Proof.
    apply IR_rewrite_ordering.
    exact monotone_succeq.
  Qed.


(**********************************************************************)
(** top termination (for DP setting) criterion with monotone algebras *)
  Section TopTermination.

    Variable R E : rules.

    Lemma ma_compat_hd_red_mod : 
      compatible IR_succ R ->
      compatible IR_succeq E ->
      WF (hd_red_mod E R).

    Proof.
      intros. apply WF_incl with IR_succ.
      apply compat_hd_red_mod with IR_succeq; trivial.
      apply IR_substitution_closed.
      exact ma_succeq_rewrite_ordering.
      exact absorb_succ_succeq.
      apply IR_WF. exact succ_wf.
    Qed.

  End TopTermination.

End MonotoneAlgebraResults.

(***********************************************************************)
(** * Functor with a theory of extended monotone algebras              *)
(***********************************************************************)
Module ExtendedMonotoneAlgebraResults (EMA : ExtendedMonotoneAlgebraType).

  Module MAR := MonotoneAlgebraResults EMA.MA.
  Export MAR.
  Export EMA.

  Require Import ACompat.

  Lemma ma_succ_rewrite_ordering : rewrite_ordering IR_succ.

  Proof.
    apply IR_rewrite_ordering.
    exact monotone_succ.
  Qed.

(**********************************************************)
(** relative termination criterion with monotone algebras *)
  Section RelativeTermination.

    Variable R E : rules.

    (* Termination in one go *)
    Lemma ma_compat_red_mod : 
      compatible IR_succ R ->
      compatible IR_succeq E ->
      WF (red_mod E R).

    Proof.
      intros. apply WF_incl with IR_succ.
      apply compat_red_mod with IR_succeq; trivial.
      exact ma_succ_rewrite_ordering.
      exact ma_succeq_rewrite_ordering.
      exact absorb_succ_succeq.
      apply IR_WF. exact succ_wf.
    Qed.

  End RelativeTermination.

(**********************************************************)
(** results and tactics for proving relative termination 
    of concrete examples. *)
  Section RelativeTerminationCriterion.

    Definition rule_partition R (R_dec : rel_dec R) (r : rule Sig) := 
      partition_by_rel R_dec (lhs r, rhs r).
    Implicit Arguments rule_partition [R].

    Definition part_succeq := rule_partition succeq'_dec.
    Definition part_succ := rule_partition succ'_dec.

    Variable R E : rules.

    Lemma ma_relative_termination : 
      let E_gt := partition part_succ E in
      let E_ge := partition part_succeq (snd E_gt) in
      let R_gt := partition part_succ R in
      let R_ge := partition part_succeq (snd R_gt) in
        snd R_ge = nil ->
        snd E_ge = nil ->
        WF (red_mod (fst E_ge) (fst R_ge)) ->
        WF (red_mod E R).

    Proof.
    Admitted.

  End RelativeTerminationCriterion.

(**********************************************************)
(** results and tactics for proving termination (as a special
    case of relative termination) of concrete examples. *)
  Section TerminationCriterion.

    Variable R : rules.

    Lemma ma_termination : 
      let R_gt := partition part_succ R in
      let R_ge := partition part_succeq (snd R_gt) in
        snd R_ge = nil ->
        WF (red (fst R_ge)) ->
        WF (red R).

    Proof.
    Admitted.

  End TerminationCriterion.

End ExtendedMonotoneAlgebraResults.
