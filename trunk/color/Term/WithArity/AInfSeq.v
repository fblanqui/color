(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-05-06

Properties of infinite sequences of terms. Uses classical logic, the
axiom of indefinite description, and the axiom WF_notIS for
WF_absorb. *)

Set Implicit Arguments.

Require Import RelUtil ATrs LogicUtil ACalls SN InfSeq NatLeast List
  IndefiniteDescription.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig).
  Notation subterm_eq := (@subterm_eq Sig).
  Notation supterm_eq := (@supterm_eq Sig).

(*****************************************************************************)
(** minimal non-terminating subterm *)

  Section NT_min.

    Variables (R : relation term) (t : term) (ht : NT R t).

    Lemma NT_min_intro : exists u, subterm_eq u t /\ NT_min R u.

    Proof.
      set (P := fun n => exists u, subterm_eq u t /\ size u = n /\ NT R u).
      assert (exP : exists n, P n). exists (size t). exists t. split.
      apply subterm_eq_refl. intuition.
      destruct (ch_min P exP) as [n [[Pn nleP] nmin]].
      destruct Pn as [u [ut [un hu]]]. subst n. exists u. unfold NT_min.
      intuition. rename u0 into v.
      assert (size u <= size v). apply nleP. exists v. intuition.
      eapply subterm_eq_trans. apply subterm_strict. apply H. hyp.
      ded (subterm_size H). omega.
    Qed.

    Definition min_term :=
      projT1 (constructive_indefinite_description _ NT_min_intro).

    Lemma NT_min_term : NT_min R min_term.

    Proof.
      unfold min_term. destruct (constructive_indefinite_description
      (fun u : term => subterm_eq u t /\ NT_min R u) NT_min_intro) as [u hu].
      simpl. intuition.
    Qed.

    Lemma subterm_min_term : subterm_eq min_term t.

    Proof.
      unfold min_term. destruct (constructive_indefinite_description
      (fun u : term => subterm_eq u t /\ NT_min R u) NT_min_intro) as [u hu].
      simpl. intuition.
    Qed.

  End NT_min.

(*****************************************************************************)
(** general boolean conditions for which [WF (hd_red_mod R D)] is
equivalent to [WF (hd_red_Mod (int_red R #) D)] *)

  Section WF_hd_red_mod_from_WF_hd_red_Mod_int.

    Variables R D : rules Sig.

    Variable hyp1 : forallb (@is_notvar_lhs Sig) R = true.

    Lemma undef_red_is_int_red : forall t u, red R t u ->
      undefined R t = true -> int_red R t u /\ undefined R u = true.

    Proof.
      intros t u tu ht. unfold undefined in ht. destruct t. discr.
      redtac. destruct l.
      rewrite forallb_forall in hyp1. ded (hyp1 _ lr). discr.
      ded (fun_eq_fill xl). decomp H.
      subst. simpl in xl. Funeqtac. rewrite (lhs_fun_defined lr) in ht. discr.
      split. rewrite xl, yr. exists (Fun f0 v0). exists r. exists c. exists s.
      intuition. subst. discr.
      subst. simpl. hyp.
    Qed.

    Lemma undef_rtc_red_is_rtc_int_red : forall t u, red R # t u ->
      undefined R t = true -> int_red R # t u /\ undefined R u = true.

    Proof.
      induction 1.
      intro hx. ded (undef_red_is_int_red H hx). intuition.
      intuition.
      intuition. apply rt_trans with y; auto.
    Qed.

    Variable hyp2 : forallb (undefined_rhs R) D = true.

    Lemma WF_hd_red_Mod_int :
      WF (hd_red_Mod (int_red R #) D) -> WF (hd_red_mod R D).

    Proof.
      rewrite forallb_forall in hyp1, hyp2.
      intro wf. unfold hd_red_mod. apply WF_mod_rev2. apply WF_mod_rev in wf.
      intro t. generalize (wf t). induction 1.
      apply SN_intro. intros z [y [xy yz]]. apply H0. exists y. intuition.
      assert (hy : undefined R y = true). redtac. generalize (hyp2 _ lr).
      unfold undefined_rhs. simpl. unfold undefined. subst. destruct r.
      discr. simpl. auto.
      destruct (undef_rtc_red_is_rtc_int_red yz hy). hyp.
    Qed.

  End WF_hd_red_mod_from_WF_hd_red_Mod_int.

End S.
