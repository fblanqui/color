(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-05-06

Properties of infinite sequences of terms. Uses classical logic, the
axiom of indefinite description, and the axiom WF_notIS for
WF_absorb. *)

Set Implicit Arguments.

Require Import RelUtil ATrs LogicUtil ACalls SN InfSeq NatLeast List
  IndefiniteDescription ClassicalChoice ProofIrrelevance.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig).
  Notation subterm_eq := (@subterm_eq Sig).
  Notation supterm_eq := (@supterm_eq Sig).

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

(*****************************************************************************)
(** subtype of minimal non-terminating terms *)

  Section NTM.

    Variable R : relation term.

    Record NTM : Type := mkNTM {
      NTM_val :> term;
      NTM_prop :> NT_min R NTM_val }.

  End NTM.

(*****************************************************************************)
(** getting a minimal non-terminating subterm *)

  Section NT_min.

    Variables (R : relation term) (t : term) (ht : NT R t).

    Lemma NT_min_intro : exists u, subterm_eq u t /\ NT_min R u.

    Proof.
      set (P := fun n => exists u, subterm_eq u t /\ size u = n /\ NT R u).
      assert (exP : exists n, P n). exists (size t). exists t. intuition.
      destruct (ch_min exP) as [n [[Pn nleP] nmin]].
      destruct Pn as [u [ut [un hu]]]. subst n. exists u. unfold NT_min, min.
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

    Lemma subterm_eq_min_term : subterm_eq min_term t.

    Proof.
      unfold min_term. destruct (constructive_indefinite_description
      (fun u : term => subterm_eq u t /\ NT_min R u) NT_min_intro) as [u hu].
      simpl. intuition.
    Qed.

  End NT_min.

(*****************************************************************************)
(** getting a minimal infinite (R @ supterm_eq)-sequence from an
infinite R-sequence *)

  Section ISMin.

    Variable R : relation term.

    Definition Rsup : relation (NTM R) := R @ supterm_eq.

    (* every minimal non-terminating term admits an Rsup-reduct that is a
    minimal non-terminating term too *)
    Lemma Rsup_left_total : forall t, exists u, Rsup t u.

    Proof.
      intros [t [[f [h0 hf]] ht]].
      exists (mkNTM (NT_min_term (NT_IS_elt 1 hf))).
      unfold Rsup. simpl. exists (f 1). subst t. intuition.
      apply subterm_eq_min_term.
    Qed.

    Lemma ISMin_intro : forall f,
      IS R f -> exists g, IS (R @ supterm_eq) g /\ Min R g.

    Proof.
      intros f hf. set (Min' := fun f : nat -> NTM R =>
        forall i x, subterm x (f i) -> forall g, g 0 = x -> ~IS R g).
      cut (exists g : nat -> NTM R, IS Rsup g /\ Min' g).
      intros [g [h1 h2]]. exists (fun i => g i). intuition.
      destruct (choice _ Rsup_left_total) as [next hnext].
      set (a := mkNTM (NT_min_term (NT_IS_elt 0 hf))).
      exists (iter a next). split.
      apply IS_iter. apply hnext.
      intros i x hx g g0 hg. destruct (iter a next i) as [t [[h [h0 hh]] ht]].
      simpl in hx. ded (ht _ hx). absurd (NT R x). hyp. exists g. intuition.
    Qed.

  End ISMin.

(*****************************************************************************)
(** getting a minimal infinite (hd_red_mod R (dp R))-sequence from an
infinite R-sequence *)

  Require Import ADP VecUtil IS_NotSN ASN BoolUtil.

  Section ISMinDP.

    Variable R : rules Sig.

    Variable hyp1 : forallb (@is_notvar_lhs Sig) R = true.
    Variable hyp2 : rules_preserve_vars R.

    Lemma min_dp : forall t u v, NT_min (red R) t -> hd_red R t u ->
      subterm_eq v u -> NT_min (red R) v -> hd_red (dp R) t v.

    Proof.
      intros t u v ht tu vu hv. redtac. subst.
      (* forall x, ~NT (red R) (s x) *)
      assert (hs : forall x, In x (vars l) -> ~NT (red R) (s x)).
      intros x vx nx. assert (hx : subterm (Var x) l).
      destruct (in_vars_subterm_eq vx) as [c hx]. destruct c.
      rewrite forallb_forall in hyp1. ded (hyp1 _ lr). rewrite hx in H. discr.
      exists (Cont f e v0 c v1). intuition. discr.
      ded (subterm_sub s hx). destruct ht as [ht1 ht2].
      ded (ht2 _ H). contradiction.
      (* end assert *)
      destruct (subterm_eq_sub_elim vu) as [w [hw1 hw2]]. destruct w.
      (* w = Var n *)
      assert (hn : In n (vars l)). eapply hyp2. apply lr.
      eapply subterm_eq_vars. apply hw1. simpl. auto.
      destruct hv as [hv1 hv2]. absurd (NT (red R) v).
      rewrite <- SN_notNT. eapply subterm_eq_sn. rewrite SN_notNT.
      apply hs. apply hn. hyp. hyp.
      (* w = Fun f v0 *)
      subst. exists l. exists (Fun f v0). exists s. intuition.
      eapply dp_intro. apply lr.
      (* In (Fun f v0) (calls R r) *)
      apply subterm_in_calls. 2: hyp. case_eq (defined f R). refl.
      destruct hv as [hv1 hv2].
      absurd (NT (red R) (sub s (Fun f v0))). 2: hyp.
      rewrite <- SN_notNT. apply sn_args_sn_fun. hyp. hyp.
      apply Vforall_intro. intros a ha. rewrite SN_notNT.
      apply hv2. apply subterm_fun. hyp.
      (* nebg_subterm l (Fun f v0) = true *)
      unfold negb_subterm. rewrite negb_ok. 2: apply bsubterm_ok. intro h.
      destruct ht as [ht1 ht2]. absurd (NT (red R) (sub s (Fun f v0))).
      apply ht2. apply subterm_sub. hyp. destruct hv as [hv1 hv2]. hyp.
    Qed.

  End ISMinDP.

End S.
