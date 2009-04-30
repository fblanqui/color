(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-05-17

RPO employed for proving termination of concrete examples (after
converting varyadic terms to terms with arities).
*)

Require Import ATrs.
Require Import VPrecedence.
Require Import VRPO_Status.
Require Import VRPO_Results.
Require Import VTerm_of_ATerm.
Require Import ListUtil.
Require Import Preorder.
Require Import SN.
Require Import RelUtil.
Require Import ARelation.
Require Import Arith.

Set Implicit Arguments.

Module Type TRPO.

  Parameter Sig : ASignature.Signature.
  Parameter stat : Sig -> status_name.
  Parameter prec : Sig -> nat.

End TRPO.

Module RPO_Prover (R : TRPO).

  Export R.

  Notation term := (@ATerm.term Sig).
  Notation terms := (list term).
  Notation rule := (@ATrs.rule Sig).
  Notation rules := (@list rule).

  Module VPrecedence <: VPrecedenceType.

    Definition Sig := VSig_of_ASig Sig.

    Definition leF f g := prec f <= prec g.

    Definition ltF := ltA Sig leF.
    Definition eqF := eqA Sig leF.

    Lemma ltF_wf : well_founded ltF.

    Proof.
      unfold ltF, ltA, eqA, leF.
      apply WF_transp_wf. unfold transp.
      apply WF_incl with (fun x y => prec x > prec y).
      intros p q pq. destruct pq.
      destruct (lt_eq_lt_dec (prec p) (prec q)) as [[pq | pq] | pq]; intuition.
      intro x. apply (@SN_Rof Sig nat prec gt) with (prec x); trivial.
      apply Acc_transp_SN. apply Acc_incl with lt. intuition. apply lt_wf.
    Qed.

    Lemma leF_dec : rel_dec leF.

    Proof.
      intros x y. unfold ltF, ltA, leF, eqA.
      destruct (le_lt_dec (prec x) (prec y)); intuition.
    Defined.

    Lemma leF_preorder : preorder Sig leF.

    Proof.
      unfold leF. intuition.
    Qed.

    Infix "=F=" := eqF (at level 50).
    Infix "<F" := ltF (at level 50).
    Infix "<=F" := leF (at level 50).

  End VPrecedence.

  Module VRPO := RPO_Model VPrecedence.
  Module VRPO_Results := RPO_Results VRPO.

  Section TerminationCriterion.

    Variable R : rules.

    Definition arpo := Rof (transp VRPO.lt) (@vterm_of_aterm Sig).

    Lemma arpo_dec : rel_dec arpo.

    Proof.
      intros p q.
      destruct (VRPO_Results.rpo_lt_dec (vterm_of_aterm q) (vterm_of_aterm p));
        intuition.
    Defined.

    Lemma arpo_wf : WF arpo.

    Proof.
      intro x. unfold arpo. set (t := vterm_of_aterm x).
      apply SN_Rof with t; trivial. apply Acc_transp_SN. 
      apply Acc_incl with VRPO.lt. intuition.
      apply VRPO_Results.wf_lt.
    Qed.

    Lemma arpo_subst_closed : ARelation.substitution_closed arpo.

    Proof.
      unfold substitution_closed, arpo, Rof, transp. 
      intros t u s tu. do 2 rewrite vterm_subs.
      apply VRPO_Results.lt_subst_closed. 
      unfold VRPO.tau, VRPO.RPO.mytau. intros. destruct (VRPO.RPO.status f). 
      apply VRPO.RPO.S.LO.lex_homomorphic. assumption. assumption.
      apply VRPO.RPO.S.mul_status_homomorphic. assumption. assumption.
      assumption.
    Qed.
      
    Lemma arpo_context_closed : context_closed arpo.

    Proof.
      unfold context_closed, arpo, Rof, transp. 
      intros. induction c.
      simpl. assumption. 
      simpl AContext.fill. do 2 rewrite vterm_fun.
      apply VRPO_Results.monotonic_lt.
      do 2 rewrite vterms_cast. do 2 rewrite vterms_app. simpl.
      apply one_less_cons with i (vterm_of_aterm (AContext.fill c t2))
        (vterm_of_aterm (AContext.fill c t1)). assumption.
      rewrite element_at_app_r; rewrite vterms_length; auto.
      rewrite <- minus_n_n; trivial.
      rewrite replace_at_app_r; rewrite vterms_length; auto.
      rewrite <- minus_n_n; trivial.
    Qed.

    Require Import ACompat.

    Definition part_rpo := rule_partition arpo_dec.

    Lemma arpo_rewrite_ordering : rewrite_ordering arpo.

    Proof.
      constructor. apply arpo_subst_closed. apply arpo_context_closed.
    Qed.

    Lemma rpo_termination : 
      let R_gt := partition part_rpo R in
        snd R_gt = nil -> 
        WF (ATrs.red R).

    Proof.
      intros. apply WF_incl with arpo.
      apply compat_red. apply arpo_rewrite_ordering.
      apply rule_partition_compat with arpo_dec. assumption.
      apply arpo_wf.
    Qed.

    Lemma arpo_self_absorb : absorb arpo arpo.

    Proof.
      unfold absorb, arpo, Rof, transp. intros t u tu.
      destruct tu as [s [ts su]]. 
      apply VRPO_Results.lt_trans with (vterm_of_aterm s); assumption.
    Qed.

    Variable E : rules.

    Lemma rpo_rel_termination :
      let R_gt := partition part_rpo R in
      let E_gt := partition part_rpo E in
        snd R_gt = nil ->
        snd E_gt = nil ->
        WF (ATrs.red_mod E R).

    Proof.
      intros. apply WF_incl with arpo.
      apply compat_red_mod with arpo. 
      apply arpo_rewrite_ordering.
      apply arpo_rewrite_ordering.
      apply rule_partition_compat with arpo_dec. assumption.
      apply rule_partition_compat with arpo_dec. assumption.
      apply arpo_self_absorb.
      apply arpo_wf.
    Qed.

    Lemma rpo_rel_top_termination :
      let R_gt := partition part_rpo R in
      let E_gt := partition part_rpo E in
        snd R_gt = nil ->
        snd E_gt = nil ->
      WF (ATrs.hd_red_mod E R).

    Proof.
      intros. apply WF_incl with (ATrs.red_mod E R).
      apply hd_red_mod_incl_red_mod.
      apply rpo_rel_termination; assumption.
    Qed.

  End TerminationCriterion.

  Ltac prove_termination :=
    match goal with
    | |- WF (ATrs.red ?R) => apply rpo_termination; vm_compute; trivial
    | |- WF (ATrs.red_mod ?E ?R) => apply rpo_rel_termination; vm_compute; trivial
    | |- WF (ATrs.hd_red_mod ?E ?R) => apply rpo_rel_top_termination; vm_compute; trivial
    | _ => fail "Unsupported problem for RPO"
   end.

End RPO_Prover.
