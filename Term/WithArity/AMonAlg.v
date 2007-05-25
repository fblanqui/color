(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03

  This file contains a definition of weakly monotone algebra and
  extended monotone algebra and some results concerning them, based
  on:

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
  Parameters (succ'_sub : succ' << IR_succ)
    (succeq'_sub : succeq' << IR_succeq).
  Parameters (succ'_dec : rel_dec succ') (succeq'_dec : rel_dec succeq').

End MonotoneAlgebraType.

(***********************************************************************)
(** * Module type specifying an extended weakly monotone algebra.      *)
(***********************************************************************)

Module Type ExtendedMonotoneAlgebraType.

  Declare Module MA : MonotoneAlgebraType.
  Export MA.

  (** Extended monotone algebra is a wekaly monotone algebra in which
  every operation is monotone with respect to [succ] *)
  Parameter monotone_succ : monotone I succ.

End ExtendedMonotoneAlgebraType.

(***********************************************************************)
(** * Functor with a theory of weakly monotone algebras                *)
(***********************************************************************)

Module MonotoneAlgebraResults (MA : MonotoneAlgebraType).

  Export MA.
  Require Import ACompat.

  (*Notation IR_succ := (IR I succ).
  Notation IR_succeq := (IR I succeq).*)

  Notation term := (@term Sig).
  Notation rule := (@rule Sig).
  Notation rules := (@list rule).

  Lemma absorb_succ_succeq : absorb IR_succ IR_succeq.

  Proof.
    intros x z xz val.
    apply succ_succeq_compat.
    destruct xz as [y [ge_xy gt_yz]].
    exists (term_int val y). split; auto.
  Qed.

  Lemma IR_rewrite_ordering : forall succ,
    monotone I succ -> rewrite_ordering (IR I succ).

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

  Section RelativeTopTermination.

    Variable R E : rules.

    Lemma ma_compat_hd_red_mod : 
      compat IR_succ R ->
      compat IR_succeq E ->
      WF (hd_red_mod E R).

    Proof.
      intros. apply WF_incl with IR_succ.
      apply compat_hd_red_mod with IR_succeq; trivial.
      apply IR_substitution_closed.
      exact ma_succeq_rewrite_ordering.
      exact absorb_succ_succeq.
      apply IR_WF. exact succ_wf.
    Qed.

  End RelativeTopTermination.

(**********************************************************)
(** results and tactics for proving relative top termination 
    of concrete examples. *)

  Section RelativeTopTerminationCriterion.

    Definition part_succeq := rule_partition succeq'_dec.
    Definition part_succ := rule_partition succ'_dec.

    Variable R E : rules.

    Lemma partition_succ_compat : forall R,
      compat IR_succ (fst (partition part_succ R)).

    Proof.
      clear R. intros R l r lr.
      apply succ'_sub. apply partition_by_rel_true with MA.term succ'_dec.
      apply rule_partition_left with R. assumption.
    Qed.

    Lemma partition_succeq_compat_fst : forall R,
      compat IR_succeq (fst (partition part_succeq R)).

    Proof.
      clear R. intros R l r lr.
      apply succeq'_sub. apply partition_by_rel_true with MA.term succeq'_dec.
      apply rule_partition_left with R. assumption.
    Qed.

    Lemma partition_succeq_compat_snd : forall R,
      snd (partition part_succeq R) = nil ->
      compat IR_succeq (snd (partition part_succ R)).

    Proof.
      clear R. intros R Rpart l r lr.
      apply succeq'_sub. apply partition_by_rel_true with MA.term succeq'_dec.
      apply rule_partition_left with R. fold part_succeq.
      deduce (partition_complete part_succeq (mkRule l r) R).
      simpl in H. rewrite Rpart in H. destruct H.
      apply partition_inright with part_succ. assumption.
      assumption. destruct H.
    Qed.

    Lemma ma_relative_top_termination :
      let E_ge := partition part_succeq E in
      let R_gt := partition part_succ R in
      let R_ge := partition part_succeq R in
        snd R_ge = nil ->
        snd E_ge = nil ->
        WF (hd_red_mod E (snd R_gt)) ->
        WF (hd_red_mod E R).

    Proof.
      intros. unfold hd_red_mod.
      set (Rgt := fst R_gt) in *. set (Rge := snd R_gt) in *.
      apply WF_incl with (red E # @ (hd_red Rge U hd_red Rgt)).
      comp.
      unfold Rge, Rgt, R_ge, R_gt. apply hd_rule_partition_complete.
      apply wf_rel_mod_simpl. fold (red_mod E Rge). assumption.
      apply WF_incl with (hd_red_mod (Rge ++ E) Rgt).
      unfold hd_red_mod. comp.
      apply incl_rtc.
      trans (red Rge U red E). union. apply hd_red_incl_red.
      apply red_union_inv.
      apply ma_compat_hd_red_mod; trivial.
      unfold Rgt, R_gt, part_succ. apply partition_succ_compat.
      apply compat_app.
      unfold Rge, R_gt. apply partition_succeq_compat_snd. assumption.
      apply incl_compat with (fst E_ge ++ snd E_ge). unfold incl. intros.
      apply in_or_app. unfold E_ge. apply partition_complete. exact H2.
      rewrite H0. rewrite <- app_nil_end.
      unfold E_ge. apply partition_succeq_compat_fst.
    Qed.

  End RelativeTopTerminationCriterion.

(**********************************************************)
(** tactics *)

  Ltac partition R := normalize (snd (partition part_succ R)).

  Ltac do_prove_termination lemma R :=
    apply lemma; [vm_compute; trivial | vm_compute; trivial | partition R].

  Ltac prove_termination :=  
    match goal with
    | |- WF (hd_red_mod _ ?R) =>
      do_prove_termination ma_relative_top_termination R
    | _ => fail "Unsupported termination problem type"
   end.

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
      compat IR_succ R ->
      compat IR_succeq E ->
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

    Lemma rule_partition_left : forall R (R_dec : rel_dec R) l r rs,
      In (mkRule l r) (fst (partition (rule_partition R_dec) rs)) ->
      partition_by_rel R_dec (l, r) = true.

    Proof.
      intros. unfold rule_partition in H.
      set (w := partition_left
        (fun r => partition_by_rel R_dec (lhs r, rhs r))). simpl in w.
      change l with (lhs (mkRule l r)). change r with (rhs (mkRule l r)).
      apply w with rs. assumption.
    Qed.

    Definition part_succeq := rule_partition succeq'_dec.
    Definition part_succ := rule_partition succ'_dec.

    Variable R E : rules.

    Lemma partition_succ_compat : forall R,
      compat IR_succ (fst (partition part_succ R)).

    Proof.
      clear R. intros R l r lr.
      apply succ'_sub. apply partition_by_rel_true with term succ'_dec.
      apply rule_partition_left with R. assumption.
    Qed.

    Lemma partition_succeq_compat : forall R,
      snd (partition part_succeq R) = nil ->
      compat IR_succeq (snd (partition part_succ R)).

    Proof.
      clear R. intros R Rpart l r lr.
      apply succeq'_sub. apply partition_by_rel_true with term succeq'_dec.
      apply rule_partition_left with R. fold part_succeq.
      deduce (partition_complete part_succeq (mkRule l r) R).
      simpl in H. rewrite Rpart in H. destruct H.
      apply partition_inright with part_succ. assumption.
      assumption. destruct H.
    Qed.

    Lemma ma_relative_termination : 
      let E_gt := partition part_succ E in
      let E_ge := partition part_succeq E in
      let R_gt := partition part_succ R in
      let R_ge := partition part_succeq R in
        snd R_ge = nil ->
        snd E_ge = nil ->
        WF (red_mod (snd E_gt) (snd R_gt)) ->
        WF (red_mod E R).

    Proof.
      intros. unfold red_mod.
      set (Egt := fst E_gt) in *. set (Ege := snd E_gt) in *.
      set (Rgt := fst R_gt) in *. set (Rge := snd R_gt) in *.
      apply WF_incl with ((red Ege U red Egt)# @ (red Rge U red Rgt)).
      comp. apply incl_rtc. 
      unfold Ege, Egt, E_ge, E_gt. apply rule_partition_complete.
      unfold Rge, Rgt, R_ge, R_gt. apply rule_partition_complete.
      apply wf_rel_mod. fold (red_mod Ege Rge). assumption.
      apply WF_incl with (red_mod (Rge ++ Ege) (Rgt ++ Egt)).
      unfold red_mod. comp. 
      apply incl_rtc. apply red_union_inv. apply red_union_inv.
      apply ma_compat_red_mod; trivial.
      apply compat_app.
      unfold Rgt, R_gt, part_succ. apply partition_succ_compat.
      unfold Egt, E_gt, part_succ. apply partition_succ_compat.
      apply compat_app.
      unfold Rge, R_gt. apply partition_succeq_compat. assumption.
      unfold Ege, E_gt. apply partition_succeq_compat. assumption.
    Qed.

  End RelativeTerminationCriterion.

(**********************************************************)
(** results and tactics for proving termination (as a special
    case of relative termination) of concrete examples. *)

  Section TerminationCriterion.

    Variable R : rules.

    Lemma ma_termination :       
      let R_gt := partition part_succ R in
      let R_ge := partition part_succeq R in
        snd R_ge = nil ->
        WF (red (snd R_gt)) ->
        WF (red R).

    Proof.
      intros. apply WF_incl with (red_mod nil R). apply red_incl_red_mod.
      apply ma_relative_termination. assumption. trivial.
      simpl. apply WF_incl with (red (snd (partition part_succ R))).
      apply red_mod_empty_incl_red. assumption.
    Qed.

  End TerminationCriterion.

(**********************************************************)
(** tactics *)

  Ltac do_prove_termination lemma := 
    apply lemma; [solve [vm_compute; trivial] | idtac].

  Ltac prove_termination :=  
    match goal with
    | |- WF (red ?R) => do_prove_termination ma_termination
    | |- WF (red_mod _ _) => do_prove_termination ma_relative_termination
    | _ => MAR.prove_termination
   end.

End ExtendedMonotoneAlgebraResults.
