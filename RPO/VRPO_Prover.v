(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-05-17

  RPO employed for proving termination of concrete examples.
*)

Require Import ATrs.
Require Import VPrecedence.
Require Import VRPO_Status.
Require Import VRPO_Results.
Require Import VTerm_of_ATerm.

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
      unfold ltF, ltA, eqA, leF. simpl.
      apply WF_wf. 
      (*apply WF_incl with (fun f g => f > g).*)
    Admitted.

    Lemma ltF_dec : rel_dec ltF.

    Proof.
    Admitted.

    Lemma leF_preorder : preorder Sig leF.

    Proof.
    Admitted.

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

    Lemma Acc_transp_transp : forall (A : Set) (R : relation A), 
      forall x, Acc R x -> Acc (transp (transp R)) x.

    Proof.
    Admitted.

    Lemma arpo_wf : WF arpo.

    Proof.
      intro x. unfold arpo. set (t := vterm_of_aterm x).
      apply SN_Rof with t; trivial.
      apply Acc_SN. apply Acc_transp_transp.
      apply VRPO_Results.wf_lt.
    Qed.

    Lemma arpo_subst_closed : substitution_closed arpo.

    Proof.
      intro t. 
    Admitted.

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

  End TerminationCriterion.

End RPO_Prover.
