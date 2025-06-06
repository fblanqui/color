(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-12-01

termination by using compatible reduction orderings
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs SN ARelation RelUtil ACompat LogicUtil.
From Stdlib Require Import List.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig).
  Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** Manna-Ness theorem (1970) *)

  Lemma manna_ness (R : rules) succ :
    reduction_ordering succ -> compat succ R -> WF (red R).

  Proof.
    intros. destruct H. apply (WF_incl succ). apply compat_red; auto. hyp.
  Qed.

(***********************************************************************)
(** an extension for proving the well-foundedness of relations of the form:
several steps of R1 followed by a step of R2 *)

  Lemma manna_ness_mod (R E : rules) (rp : Reduction_pair Sig) :
    compat (rp_succ_eq rp) E -> compat (rp_succ rp) R -> WF (red_mod E R).

  Proof.
    intros. apply (WF_incl (rp_succ rp)). destruct rp; simpl in *.
    apply compat_red_mod with rp_succ_eq; try split; hyp. destruct rp; hyp.
  Qed.

(***********************************************************************)
(** an extension for proving the well-foundedness of relations of the form:
several steps of R1 followed by a -head- step of R2 *)

  Lemma manna_ness_hd_mod (R E : rules) (wp : Weak_reduction_pair Sig) :
    compat (wp_succ_eq wp) E -> compat (wp_succ wp) R -> WF (hd_red_mod E R).

  Proof.
    intros. apply (WF_incl (wp_succ wp)). destruct wp; simpl in *.
    apply compat_hd_red_mod with wp_succ_eq; try split; hyp. destruct wp; hyp.
  Qed.

(***********************************************************************)
(** rule elimination *)

  Section rule_elimination.

    Variables R Rgt Rge : rules.

    Section mod.

      Variables E Egt Ege : rules.

      Lemma rule_elimination_mod : forall rp : Reduction_pair Sig,
        compat (rp_succ    rp) Rgt ->
        compat (rp_succ_eq rp) Rge -> 
        compat (rp_succ    rp) Egt ->
        compat (rp_succ_eq rp) Ege ->
        WF (red_mod Ege Rge) ->
        WF (red_mod (Egt ++ Ege) (Rgt ++ Rge)).

      Proof with auto.
        intros. apply WF_incl with ((red Egt U red Ege)# @ (red Rgt U red Rge)).
        comp. apply rtc_incl. incl_trans (red Egt U red Ege)...
        apply red_union.
        apply red_union.
        apply wf_rel_mod...
        apply WF_incl with ((red (Rge ++ Ege)# @ (red (Rgt ++ Egt)))).
        comp. apply rtc_incl. apply red_union_inv.
        apply red_union_inv.
        apply manna_ness_mod with rp; apply compat_app...
      Qed.

      Lemma rule_elimination_hd_mod : forall wp : Weak_reduction_pair Sig,
        compat (wp_succ_eq wp) E ->
        compat (wp_succ_eq wp) Rge -> 
        compat (wp_succ wp   ) Rgt ->
        WF (hd_red_mod E Rge) -> 
        WF (hd_red_mod E (Rgt ++ Rge)).

      Proof with auto.
        intros. apply WF_incl with (red E # @ (hd_red Rgt U hd_red Rge)).
        comp. apply hd_red_union. 
        apply wf_rel_mod_simpl...
        apply WF_incl with (hd_red_mod (Rge ++ E) Rgt).
        comp. apply rtc_incl.
        incl_trans (red Rge U red E). union. apply hd_red_incl_red.
        apply red_union_inv.
        apply manna_ness_hd_mod with wp...
        apply compat_app...
      Qed.

    End mod.

    Lemma rule_elimination : forall rp : Reduction_pair Sig,
      compat (rp_succ_eq rp) Rge -> 
      compat (rp_succ rp   ) Rgt ->
      WF (red Rge) -> 
      WF (red (Rgt ++ Rge)).

    Proof with auto.
      intros. eapply WF_incl. apply red_incl_red_mod.
      change (nil (A:=rule)) with (nil (A:=rule) ++ nil).
      apply rule_elimination_mod with rp...
      apply compat_empty. apply compat_empty.
      apply WF_incl with (red Rge)... apply red_mod_empty_incl_red.
    Qed.

    Lemma rule_elimination_hd_red : forall wp : Weak_reduction_pair Sig,
      compat (wp_succ_eq wp) Rge -> 
      compat (wp_succ wp   ) Rgt ->
      WF (hd_red Rge) -> 
      WF (hd_red (Rgt ++ Rge)).

    Proof with auto.
      intros. eapply WF_incl. apply hd_red_incl_hd_red_mod.
      apply rule_elimination_hd_mod with wp...
      apply compat_empty.
      apply WF_incl with (hd_red Rge)... apply hd_red_mod_empty_incl_hd_red.
    Qed.

  End rule_elimination.

End S.
