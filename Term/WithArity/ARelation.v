(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09

general definitions and results about relations on terms
*)

Set Implicit Arguments.

From CoLoR Require Import SN ASubstitution ATerm RelUtil AContext LogicUtil
     VecUtil NaryFunction.
From Stdlib Require Import List.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig).

(***********************************************************************)
(** basic definitions *)

  Section basic.

    Variable R : relation term.

    Definition preserve_vars := forall t u, R t u -> incl (vars u) (vars t).

    Definition substitution_closed :=
      forall t1 t2 s, R t1 t2 -> R (sub s t1) (sub s t2).

    Definition context_closed :=
      forall t1 t2 c, R t1 t2 -> R (fill c t1) (fill c t2).

    Definition rewrite_ordering := substitution_closed /\ context_closed.

    Definition reduction_ordering := WF R /\ rewrite_ordering.

  End basic.

  Record Rewrite_ordering : Type := mkRewrite_ordering {
    rew_ord_rel :> relation term;
    rew_ord_subs : substitution_closed rew_ord_rel;
    rew_ord_cont : context_closed rew_ord_rel
  }.

(***********************************************************************)
(** closure by substitution *)

  Lemma substitution_closed_rtc : forall R,
    substitution_closed R -> substitution_closed (R #).

  Proof.
    intros R h t u s. induction 1. apply rt_step. apply h. hyp.
    apply rt_refl. apply rt_trans with (sub s y); hyp.
  Qed.

  Lemma substitution_closed_transp : forall R,
    substitution_closed R -> substitution_closed (transp R).

  Proof.
    intros R hR t u s. unfold transp. apply hR.
  Qed.

(***********************************************************************)
(** closure by context *)

  Lemma context_closed_rtc : forall R, context_closed R -> context_closed (R #).

  Proof.
    intros R h t u c. induction 1. apply rt_step. apply h. hyp.
    apply rt_refl. apply rt_trans with (fill c y); hyp.
  Qed.

  Lemma context_closed_tc : forall R, context_closed R -> context_closed (R !).

  Proof.
    intros R h t u c. induction 1. apply t_step. apply h. hyp.
    apply t_trans with (fill c y); hyp.
  Qed.

  Lemma context_closed_comp : forall R S,
    context_closed R -> context_closed S -> context_closed (R @ S).

  Proof.
    intros R S hR hS t v c [u [h1 h2]]. exists (fill c u). split.
    apply hR. hyp. apply hS. hyp.
  Qed.

  Lemma context_closed_fun : forall R, context_closed R ->
    forall f i v1 t u j v2 (e : i+S j=arity f),
      R t u -> R (Fun f (Vcast (Vapp v1 (Vcons t v2)) e))
                 (Fun f (Vcast (Vapp v1 (Vcons u v2)) e)).

  Proof.
    intros. set (c := Cont f e v1 Hole v2). change (R (fill c t) (fill c u)).
    apply H. hyp.
  Qed.

  Lemma Vmonotone_context_closed : forall R,
    (forall f : Sig, Vmonotone (Fun f) R R) <-> context_closed R.

  Proof.
    split; intro.
    unfold context_closed. induction c; simpl; intros. hyp. apply H. auto.
    unfold Vmonotone, Vmonotone_i, RelUtil.monotone. intros.
    set (c := Cont f H0 vi Hole vj). change (R (fill c x) (fill c y)).
    apply H. hyp.
  Qed.

(***********************************************************************)
(** reduction pair *)

  Section reduction_pair.

    Variables R E : relation term.

    Definition reduction_pair :=
      reduction_ordering R /\ absorbs_left R E /\ rewrite_ordering E.

  End reduction_pair.

(*FIXME: defined as weak_reduction_pair + something*)
  Record Reduction_pair : Type := mkReduction_pair {
    rp_succ : relation term;
    rp_succ_eq : relation term;
    rp_subs : substitution_closed rp_succ;
    rp_subs_eq : substitution_closed rp_succ_eq;
    rp_cont : context_closed rp_succ;
    rp_cont_eq : context_closed rp_succ_eq;
    rp_absorb : absorbs_left rp_succ rp_succ_eq;
    rp_succ_wf : WF rp_succ
  }.

(***********************************************************************)
(** weak reduction pair *)

  Section weak_reduction_pair.

    Variables R E : relation term.

    Definition weak_context_closed :=
      forall t1 t2 c, R t1 t2 -> E (fill c t1) (fill c t2).

    Definition weak_rewrite_ordering :=
      substitution_closed R /\ weak_context_closed.

    Definition weak_reduction_ordering := WF R /\ weak_rewrite_ordering.

    Definition weak_reduction_pair :=
      weak_reduction_ordering /\ absorbs_left R E /\ rewrite_ordering E.

  End weak_reduction_pair.

  Record Weak_reduction_pair : Type := mkWeak_reduction_pair {
    wp_succ : relation term;
    wp_succ_eq : relation term;
    wp_subs : substitution_closed wp_succ;
    wp_subs_eq : substitution_closed wp_succ_eq;
    wp_cont_eq : context_closed wp_succ_eq;
    wp_absorb : absorbs_left wp_succ wp_succ_eq;
    wp_succ_wf : WF wp_succ
  }.

(***********************************************************************)
(** reflexive closure *)

  Section clos_refl.

    Variable R : relation term.

    Notation E := (R %).

    Lemma rc_context_closed :
      weak_context_closed R E -> context_closed E.

    Proof.
      intro. unfold context_closed. intros. unfold clos_refl, union in H0.
      decomp H0. subst t2. unfold clos_refl, union. auto. apply H. hyp.
    Qed.

    Lemma rc_substitution_closed :
      substitution_closed R -> substitution_closed E.

    Proof.
      intro. unfold substitution_closed, clos_refl, union. intros. decomp H0.
      subst t2. auto. right. apply H. hyp.
    Qed.

    Lemma rc_rewrite_ordering :
      weak_rewrite_ordering R E -> rewrite_ordering E.

    Proof.
      intros (Hsubs,Hcont). split. apply rc_substitution_closed. hyp.
      apply rc_context_closed. hyp.
    Qed.

  End clos_refl.

(***********************************************************************)
(** when R is the strict part of E *)

  Section strict.

    Variables (E : relation term) (E_trans : transitive E).

    Notation R := (strict_part E).

    Lemma absorb_strict : absorbs_left R E.

    Proof.
      unfold absorbs_left, inclusion, RelUtil.compose, strict_part.
      intros; split; decomp H. eapply E_trans. apply H1. hyp.
      unfold not; intro. ded (E_trans H H1). contr.
    Qed.

  End strict.

(***********************************************************************)
(** subterm relation *)

  Lemma substitution_closed_subterm_eq : substitution_closed (@subterm_eq Sig).

  Proof.
    intros t u s h. destruct h as [C h]. subst. rewrite sub_fill.
    exists (subc s C). refl.
  Qed.

  Lemma substitution_closed_subterm : substitution_closed (@subterm Sig).

  Proof.
    intros t u s h. destruct h as [C h]. destruct h as [C0 h]. subst.
    rewrite sub_fill.
    exists (subc s C). split; try refl. destruct C. simpl. auto. discr.
  Qed.

End S.
