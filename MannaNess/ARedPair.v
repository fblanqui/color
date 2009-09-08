(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-07-03

rule elimination with reduction pairs
*)

Set Implicit Arguments.

Require Import ATrs.
Require Import LogicUtil.
Require Import ARelation.
Require Import RelUtil.
Require Import SN.
Require Import ListUtil.
Require Import AMannaNess.
Require Import ACompat.
Require Import BoolUtil.

(***********************************************************************)
(** module type for reduction pairs *)

Module Type WeakRedPair.

  Parameter Sig : Signature.

  Notation term := (@term Sig).

  Parameter succ : relation term.
  Parameter wf_succ : WF succ.
  Parameter sc_succ : substitution_closed succ.

  Parameter bsucc : term -> term -> bool.
  Parameter bsucc_sub : rel bsucc << succ.

  Parameter succeq : relation term.
  Parameter sc_succeq : substitution_closed succeq.
  Parameter cc_succeq : context_closed succeq.
  Parameter refl_succeq : reflexive succeq.

  Parameter succ_succeq_compat : absorb succ succeq.

  Parameter bsucceq : term -> term -> bool.
  Parameter bsucceq_sub : rel bsucceq << succeq.

End WeakRedPair.

(***********************************************************************)
(** properties of reduction pairs *)

Module WeakRedPairProps (Import WP : WeakRedPair).

  Notation rule := (rule Sig). Notation rules := (rules Sig).

  Definition wp := mkWeak_reduction_pair
    sc_succ sc_succeq cc_succeq succ_succeq_compat wf_succ.

  Section S.

    Lemma WF_wp_hd_red_mod : forall E R,
      forallb (brule bsucceq) E = true ->
      forallb (brule bsucceq) R = true ->
      WF (hd_red_mod E (filter (brule (neg bsucc)) R)) ->
      WF (hd_red_mod E R).

    Proof.
      intros. set (Rge := filter (brule (neg bsucc)) R).
      set (Rgt := removes (@eq_rule_dec Sig) Rge R).
      apply WF_incl with (hd_red_mod E (Rgt ++ Rge)).
      apply hd_red_mod_incl. refl. apply incl_removes_app.
      apply rule_elimination_hd_mod with (wp:=wp).
      (* E << succeq *)
      intros l r h. apply bsucceq_sub. rewrite forallb_forall in H.
      change (brule bsucceq (mkRule l r) = true). apply H. hyp.
      (* Rge << succeq *)
      apply incl_compat with R. unfold Rge. apply filter_incl.
      (* R << succeq *)
      intros l r h. apply bsucceq_sub. rewrite forallb_forall in H0.
      change (brule bsucceq (mkRule l r) = true). apply H0. hyp.
      (* Rgt << succ *)
      intros l r h. unfold Rgt in h. rewrite In_removes in h. destruct h.
      unfold Rge in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
      destruct H3. contradiction. destruct H3. clear H3.
      apply bsucc_sub. unfold rel. unfold brule, neg in H4. simpl in H4.
      rewrite negb_lr in H4. hyp.
      (* WF (hd_red_mod E Rge) *)
      hyp.
    Qed.

    Variable cc_succ : context_closed succ.

    Definition rp := mkReduction_pair
      sc_succ sc_succeq cc_succ cc_succeq succ_succeq_compat wf_succ.

    Lemma WF_rp_red_mod : forall E R,
      forallb (brule bsucceq) E = true ->
      forallb (brule bsucceq) R = true ->
      WF (red_mod (filter (brule (neg bsucc)) E)
                  (filter (brule (neg bsucc)) R)) ->
      WF (red_mod E R).

    Proof.
      intros. set (Rge := filter (brule (neg bsucc)) R).
      set (Ege := filter (brule (neg bsucc)) E).
      set (Rgt := removes (@eq_rule_dec Sig) Rge R).
      set (Egt := removes (@eq_rule_dec Sig) Ege E).
      apply WF_incl with (red_mod (Egt ++ Ege) (Rgt ++ Rge)).
      apply red_mod_incl; apply incl_removes_app.
      apply rule_elimination_mod with (rp:=rp).
      (* Rgt << succ *)
      intros l r h. unfold Rgt in h. rewrite In_removes in h. destruct h.
      unfold Rge in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
      destruct H3. contradiction. destruct H3. clear H3.
      apply bsucc_sub. unfold rel. unfold brule, neg in H4. simpl in H4.
      rewrite negb_lr in H4. hyp.
      (* Rge << succeq *)
      apply incl_compat with R. unfold Rge. apply filter_incl.
      (* R << succeq *)
      intros l r h. apply bsucceq_sub. rewrite forallb_forall in H0.
      change (brule bsucceq (mkRule l r) = true). apply H0. hyp.
      (* Egt << succ *)
      intros l r h. unfold Egt in h. rewrite In_removes in h. destruct h.
      unfold Ege in H3. rewrite (notIn_filter _ (@eq_rule_dec Sig)) in H3.
      destruct H3. contradiction. destruct H3. clear H3.
      apply bsucc_sub. unfold rel. unfold brule, neg in H4. simpl in H4.
      rewrite negb_lr in H4. hyp.
      (* Ege << succeq *)
      apply incl_compat with E. unfold Ege. apply filter_incl.
      (* E << succeq *)
      intros l r h. apply bsucceq_sub. rewrite forallb_forall in H.
      change (brule bsucceq (mkRule l r) = true). apply H. hyp.
      (* WF (hd_red_mod Ege Rge) *)
      hyp.
    Qed.

    Lemma WF_rp_red : forall R,
      forallb (brule bsucceq) R = true ->
      WF (red (filter (brule (neg bsucc)) R)) ->
      WF (red R).

    Proof.
      intros. rewrite <- red_mod_empty. apply WF_rp_red_mod. refl. hyp.
      simpl. rewrite red_mod_empty. hyp.
    Qed.

  End S.

  Ltac do_prove_termination prove_cc_succ lemma :=
    apply lemma;
      match goal with
      | |- context_closed _ => solve [prove_cc_succ]
      | |- WF _ => idtac
      | |- _ = _ => solve [check_eq]
      | _ => fail "Failed to deal with generated goal"
      end.

  Ltac prove_termination prove_cc_succ :=
    let prove := do_prove_termination prove_cc_succ in
    match goal with
    | |- WF (red _) => prove WF_rp_red
    | |- WF (red_mod _ _) => prove WF_rp_red_mod
    | |- WF (hd_red_mod _ _) => prove WF_wp_hd_red_mod
    | |- WF (hd_red_Mod _ _) =>
      try rewrite int_red_incl_red;
        try rewrite hd_red_mod_of_hd_red_Mod;
          prove_termination prove_cc_succ
    | _ => fail "Unsupported termination problem type"
   end.

End WeakRedPairProps.

(***********************************************************************)
(** reduction pair associated to a monotone algebra *)

Require Import AMonAlg.

Module WP_MonAlg (Import MA : MonotoneAlgebraType) <: WeakRedPair.

  Definition Sig := Sig.

  Definition succ := IR I succ.
  Definition wf_succ := IR_WF I succ_wf.
  Definition sc_succ := @IR_substitution_closed _ _ MA.succ.

  Definition bsucc := brel succ'_dec.

  Lemma bsucc_sub : rel bsucc << succ.

  Proof.
    intros t u. unfold rel, bsucc, brel. case (succ'_dec t u); intros.
    apply succ'_sub. hyp. discr.
  Qed.

  Definition succeq := IR I succeq.
  Definition sc_succeq := @IR_substitution_closed _ _ MA.succeq.
  Definition cc_succeq := @IR_context_closed _ _ _ monotone_succeq.
  Definition refl_succeq := @IR_reflexive _ _ _ refl_succeq.

  Lemma succ_succeq_compat : absorb succ succeq.

  Proof.
    intros x z xz val. apply succ_succeq_compat.
    destruct xz as [y [ge_xy gt_yz]]. exists (term_int val y). split; auto.
  Qed.

  Definition bsucceq := brel succeq'_dec.

  Lemma bsucceq_sub : rel bsucceq << succeq.

  Proof.
    intros t u. unfold rel, bsucceq, brel. case (succeq'_dec t u); intros.
    apply succeq'_sub. hyp. discr.
  Qed.

End WP_MonAlg.

(***********************************************************************)
(** reduction pair associated to an argument filtering without projections *)

Require Import AFilter.

Module Type Filter.

  Variable Sig : Signature.

  Variable pi : forall f, vector bool (@arity Sig f).

  Declare Module WP : WeakRedPair with Definition Sig := filter_sig pi.

End Filter.

Module WP_Filter (Import F : Filter) <: WeakRedPair.

  Definition Sig := Sig.

  Import WP.

  Definition succ := filter_ord succ.
  Definition wf_succ := WF_filter wf_succ.
  Definition sc_succ := filter_subs_closed sc_succ.

  Definition bsucc t u := bsucc (filter pi t) (filter pi u).

  Lemma bsucc_sub : rel bsucc << succ.

  Proof.
    intros t u h. apply bsucc_sub. hyp.
  Qed.

  Definition succeq := filter_ord succeq.
  Definition sc_succeq := filter_subs_closed sc_succeq.
  Definition cc_succeq := filter_cont_closed refl_succeq cc_succeq.
  
  Lemma refl_succeq : reflexive succeq.

  Proof.
    intro x. unfold succeq. apply refl_succeq.
  Qed.

  Lemma succ_succeq_compat : absorb succ succeq.

  Proof.
    unfold absorb, succ, succeq. intros t v [u [h1 h2]].
    unfold filter_ord in *. apply succ_succeq_compat. exists (filter pi u).
    auto.
  Qed.

  Definition bsucceq t u := bsucceq (filter pi t) (filter pi u).

  Lemma bsucceq_sub : rel bsucceq << succeq.

  Proof.
    intros t u h. apply bsucceq_sub. hyp.
  Qed.

End WP_Filter.

(***********************************************************************)
(** reduction pair associated to an argument filtering with projections only *)

Require Import AProj.

Module Type Proj.

  Variable Sig : Signature.

  Variable pi : forall f : Sig, option {k | k < arity f}.

  Declare Module WP : WeakRedPair with Definition Sig := Sig.

End Proj.

Module WP_Proj (Import P : Proj) <: WeakRedPair.

  Definition Sig := Sig.

  Import WP.

  Definition succ := proj_ord pi succ.
  Definition wf_succ := WF_proj pi wf_succ.
  Definition sc_succ := proj_subs_closed pi sc_succ.

  Definition bsucc t u := bsucc (proj pi t) (proj pi u).

  Lemma bsucc_sub : rel bsucc << succ.

  Proof.
    intros t u h. apply bsucc_sub. hyp.
  Qed.

  Definition succeq := proj_ord pi succeq.
  Definition sc_succeq := proj_subs_closed pi sc_succeq.
  Definition cc_succeq := proj_cont_closed pi refl_succeq cc_succeq.
  
  Lemma refl_succeq : reflexive succeq.

  Proof.
    intro x. unfold succeq. apply refl_succeq.
  Qed.

  Lemma succ_succeq_compat : absorb succ succeq.

  Proof.
    unfold absorb, succ, succeq. intros t v [u [h1 h2]].
    unfold proj_ord in *. apply succ_succeq_compat. exists (proj pi u).
    auto.
  Qed.

  Definition bsucceq t u := bsucceq (proj pi t) (proj pi u).

  Lemma bsucceq_sub : rel bsucceq << succeq.

  Proof.
    intros t u h. apply bsucceq_sub. hyp.
  Qed.

End WP_Proj.
