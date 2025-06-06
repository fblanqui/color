(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03

  This file contains a definition of weakly monotone algebra and
  extended monotone algebra and some results concerning them, based
  on:

References:
  J. Endrullis, J. Waldmann and H. Zantema,
  "Matrix Interpretations for Proving Termination of Term Rewriting",
  Proceedings of the 3rd International Joint Conference (IJCAR 2006), 2006.
*)

From CoLoR Require Import ATrs RelUtil SN ListUtil ARelation LogicUtil.
From CoLoR Require Export AWFMInterpretation.

Import List.

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

     An extended monotone algebra additionaly requires that every 
   operation is monotone with respect to [succ] but we demand
   it as an extra hypothesis in respective theorems (dealing with
   extended monotone algebras).
  *)
  Parameter I : interpretation Sig.
  
  Notation A := (domain I).

  Parameter succ : relation A.
  Parameter succeq : relation A.

  Parameter refl_succeq : reflexive succeq.
  Parameter trans_succ : transitive succ.
  Parameter trans_succeq : transitive succeq.
  
  Parameter monotone_succeq : monotone I succeq.

  Parameter succ_wf : WF succ.

  Parameter succ_succeq_compat : absorbs_left succ succeq.

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
(** * Functor with a theory of weakly monotone algebras                *)
(***********************************************************************)

From CoLoR Require Import ACompat.

Module MonotoneAlgebraResults (MA : MonotoneAlgebraType).

  Export MA.

  Notation term := (@term Sig).
  Notation rule := (@rule Sig).
  Notation rules := (@list rule).

  Lemma absorb_succ_succeq : absorbs_left IR_succ IR_succeq.

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
    hyp.
  Qed.

  Lemma ma_succeq_rewrite_ordering : rewrite_ordering IR_succeq.

  Proof.
    apply IR_rewrite_ordering.
    exact monotone_succeq.
  Qed.

  Definition part_succeq := rule_partition succeq'_dec.
  Definition part_succ := rule_partition succ'_dec.

  Lemma partition_succ_compat : forall R,
    compat IR_succ (fst (partition part_succ R)).

  Proof.
    intros R l r lr.
    apply succ'_sub. apply partition_by_rel_true with MA.term succ'_dec.
    apply rule_partition_left with R. hyp.
  Qed.

(**********************************************************)
(** relative termination criterion with monotone algebras *)

  Section RelativeTermination.

    Variable R E : rules.

    (* Termination in one go *)
    Lemma ma_compat_red_mod : 
      monotone I succ ->
      compat IR_succ R ->
      compat IR_succeq E ->
      WF (red_mod E R).

    Proof.
      intros. apply WF_incl with IR_succ.
      apply compat_red_mod with IR_succeq; trivial.
      apply IR_rewrite_ordering; trivial.
      exact ma_succeq_rewrite_ordering.
      exact absorb_succ_succeq.
      apply IR_WF. exact succ_wf.
    Qed.

  End RelativeTermination.

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
(** results and tactics for proving relative termination 
    of concrete examples. *)

  Section RelativeTerminationCriterion.

    Variable R E : rules.

    Lemma partition_succeq_compat : forall R,
      snd (partition part_succeq R) = nil ->
      compat IR_succeq (snd (partition part_succ R)).

    Proof.
      clear R. intros R Rpart l r lr.
      apply succeq'_sub. apply partition_by_rel_true with MA.term succeq'_dec.
      apply rule_partition_left with R. fold part_succeq.
      ded (partition_complete part_succeq (mkRule l r) R).
      simpl in H. rewrite Rpart in H. destruct H.
      apply partition_inright with part_succ. hyp.
      hyp. destruct H.
    Qed.

    Lemma ma_relative_termination : 
      let E_gt := partition part_succ E in
      let E_ge := partition part_succeq E in
      let R_gt := partition part_succ R in
      let R_ge := partition part_succeq R in
        monotone I succ ->
        snd R_ge = nil ->
        snd E_ge = nil ->
        WF (red_mod (snd E_gt) (snd R_gt)) ->
        WF (red_mod E R).

    Proof.
      intros. unfold red_mod.
      set (Egt := fst E_gt) in *. set (Ege := snd E_gt) in *.
      set (Rgt := fst R_gt) in *. set (Rge := snd R_gt) in *.
      apply WF_incl with ((red Egt U red Ege)# @ (red Rgt U red Rge)).
      comp. apply rtc_incl. apply rule_partition_complete. 
      apply rule_partition_complete.
      apply wf_rel_mod. fold (red_mod Ege Rge). hyp.
      apply WF_incl with (red_mod (Rge ++ Ege) (Rgt ++ Egt)).
      unfold red_mod. comp. 
      apply rtc_incl. apply red_union_inv. apply red_union_inv.
      apply ma_compat_red_mod; trivial.
      apply compat_app.
      unfold Rgt, R_gt, part_succ. apply partition_succ_compat.
      unfold Egt, E_gt, part_succ. apply partition_succ_compat.
      apply compat_app.
      unfold Rge, R_gt. apply partition_succeq_compat. hyp.
      unfold Ege, E_gt. apply partition_succeq_compat. hyp.
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
        monotone I succ ->
        snd R_ge = nil ->
        WF (red (snd R_gt)) ->
        WF (red R).

    Proof.
      intros. apply WF_incl with (red_mod nil R). apply red_incl_red_mod.
      apply ma_relative_termination. hyp. hyp. trivial.
      simpl. apply WF_incl with (red (snd (partition part_succ R))).
      apply red_mod_empty_incl_red. hyp.
    Qed.

  End TerminationCriterion.

(**********************************************************)
(** results and tactics for proving relative top termination 
    of concrete examples. *)

  Section RelativeTopTerminationCriterion.

    Variable R E : rules.

    Lemma partition_succeq_compat_fst : forall R,
      compat IR_succeq (fst (partition part_succeq R)).

    Proof.
      clear R. intros R l r lr.
      apply succeq'_sub. apply partition_by_rel_true with MA.term succeq'_dec.
      apply rule_partition_left with R. hyp.
    Qed.

    Lemma partition_succeq_compat_snd : forall R,
      snd (partition part_succeq R) = nil ->
      compat IR_succeq (snd (partition part_succ R)).

    Proof.
      clear R. intros R Rpart l r lr.
      apply succeq'_sub. apply partition_by_rel_true with MA.term succeq'_dec.
      apply rule_partition_left with R. fold part_succeq.
      ded (partition_complete part_succeq (mkRule l r) R).
      simpl in H. rewrite Rpart in H. destruct H.
      apply partition_inright with part_succ. hyp.
      hyp. destruct H.
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
      apply WF_incl with (red E # @ (hd_red Rgt U hd_red Rge)).
      comp. incl_trans (hd_red Rgt U hd_red Rge).
      apply hd_rule_partition_complete.
      apply wf_rel_mod_simpl. fold (red_mod E Rge). hyp.
      apply WF_incl with (hd_red_mod (Rge ++ E) Rgt).
      unfold hd_red_mod. comp.
      apply rtc_incl.
      incl_trans (red Rge U red E). union. apply hd_red_incl_red.
      apply red_union_inv.
      apply ma_compat_hd_red_mod; trivial.
      unfold Rgt, R_gt, part_succ. apply partition_succ_compat.
      apply compat_app.
      unfold Rge, R_gt. apply partition_succeq_compat_snd. hyp.
      apply incl_compat with (fst E_ge ++ snd E_ge). unfold incl. intros.
      apply in_or_app. unfold E_ge. apply partition_complete. exact H2.
      rewrite H0, app_nil_r.
      unfold E_ge. apply partition_succeq_compat_fst.
    Qed.

  End RelativeTopTerminationCriterion.

(**********************************************************)
(** tactics *)

  Ltac partition R := norm (snd (partition part_succ R)).

  Ltac do_prove_termination prove_int_monotonicity lemma R :=
    apply lemma;
      match goal with
      | |- monotone _ _ => prove_int_monotonicity
      | |- WF _ => partition R
      | |- _ = _ => refl
      | _ => first
        [ solve [vm_compute; trivial]
	| idtac
        | fail 10 "Failed to deal with generated goal"
        ]
      end.

  Ltac prove_termination prove_int_monotone :=
    let prove := do_prove_termination prove_int_monotone in
    match goal with
    | |- WF (red ?R) => 
            prove ma_termination R
    | |- WF (red_mod _ ?R) => 
            prove ma_relative_termination R
    | |- WF (hd_red_mod _ ?R) => 
            prove ma_relative_top_termination R 
    | |- WF (hd_red_Mod _ ?R) =>
	    eapply WF_incl;[try apply hd_red_mod_of_hd_red_Mod;
			try apply hd_red_mod_of_hd_red_Mod_int | idtac];
	    prove ma_relative_top_termination R 
    | _ => fail 10 "Unsupported termination problem type"
   end.

End MonotoneAlgebraResults.
