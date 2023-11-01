(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-05-06

Properties of infinite sequences of terms. Uses classical logic, the
axiom of indefinite description, and the axiom WF_notIS for
WF_absorb. *)

Set Implicit Arguments.

From Coq Require Import IndefiniteDescription ClassicalChoice ProofIrrelevance
     Lia.
From CoLoR Require Import RelUtil ATrs LogicUtil ACalls SN InfSeq LeastNat
     ListUtil BoundNat NatUtil VecUtil ADP NotSN_IS ASN BoolUtil ClassicUtil.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig).
  Notation subterm_eq := (@subterm_eq Sig).
  Notation supterm_eq := (@supterm_eq Sig).

(*****************************************************************************)
(** general boolean conditions for which [WF (hd_red_mod R D)] is
equivalent to [WF (hd_red_Mod (int_red R #) D)] *)

  Section WF_hd_red_mod_of_WF_hd_red_Mod_int.

    Variables R D : rules Sig.

    Lemma undef_red_is_int_red :
      forall (hyp1 : forallb (@is_notvar_lhs Sig) R = true),
      forall t u, red R t u ->
      undefined R t = true -> int_red R t u /\ undefined R u = true.

    Proof.
      intros hyp1 t u tu ht. unfold undefined in ht. destruct t. discr.
      redtac. destruct l.
      rewrite forallb_forall in hyp1. ded (hyp1 _ lr). discr.
      ded (fun_eq_fill xl). decomp H.
      subst. simpl in xl. Funeqtac. rewrite (lhs_fun_defined lr) in ht. discr.
      split. rewrite xl, yr. ex (Fun f0 t0) r c s. split_all. congruence.
      subst. hyp.
    Qed.

    Lemma undef_rtc_red_is_rtc_int_red
      (hyp1 : forallb (@is_notvar_lhs Sig) R = true) :
      forall t u, red R # t u ->
      undefined R t = true -> int_red R # t u /\ undefined R u = true.

    Proof.
      induction 1; intro hx.
      ded (undef_red_is_int_red hyp1 H hx). intuition.
      split_all. refl.
      split_all. apply rt_trans with y; tauto. tauto.
    Qed.

    Lemma WF_hd_red_Mod_int :
      forall (hyp1 : forallb (@is_notvar_lhs Sig) R = true)
             (hyp2 : forallb (undefined_rhs R) D = true),
      WF (hd_red_Mod (int_red R #) D) -> WF (hd_red_mod R D).

    Proof.
      intros hyp1 hyp2.
      intro wf. unfold hd_red_mod. apply WF_mod_rev2. apply WF_mod_rev in wf.
      intro t. gen (wf t). induction 1.
      apply SN_intro. intros z [y [xy yz]]. apply H0. exists y. split_all.
      assert (hy : undefined R y = true). redtac.
      rewrite forallb_forall in hyp2. gen (hyp2 _ lr).
      unfold undefined_rhs. simpl. unfold undefined. subst. destruct r.
      discr. simpl. auto.
      destruct (undef_rtc_red_is_rtc_int_red hyp1 yz hy). hyp.
    Qed.

  End WF_hd_red_mod_of_WF_hd_red_Mod_int.

(*****************************************************************************)
(** subtype of minimal non-terminating terms *)

  Section NTM.

    Variable R : relation term.

    Record NTM : Type := mkNTM {
      NTM_val :> term;
      NTM_prop :> NT_min R NTM_val }.

  End NTM.

(*****************************************************************************)
(** get a minimal non-terminating subterm *)

  Section NT_min.

    Variables (R : relation term) (t : term) (ht : NT R t).

    Lemma NT_min_intro : exists u, subterm_eq u t /\ NT_min R u.

    Proof.
      set (P := fun n => exists u, subterm_eq u t /\ size u = n /\ NT R u).
      assert (exP : exists n, P n). ex (size t) t. split_all. refl.
      destruct (ch_min exP) as [n [[Pn nleP] nmin]].
      destruct Pn as [u [ut [un hu]]]. subst n. exists u. unfold NT_min, min.
      split_all. rename u0 into v.
      assert (size u <= size v). apply nleP. exists v. split_all.
      eapply subterm_eq_trans. apply subterm_strict. apply H. hyp.
      ded (subterm_size H). lia.
    Qed.

    Definition min_term :=
      proj1_sig (constructive_indefinite_description _ NT_min_intro).

    Lemma NT_min_term : NT_min R min_term.

    Proof.
      unfold min_term. destruct (constructive_indefinite_description
      (fun u : term => subterm_eq u t /\ NT_min R u) NT_min_intro) as [u hu].
      simpl. tauto.
    Qed.

    Lemma subterm_eq_min_term : subterm_eq min_term t.

    Proof.
      unfold min_term. destruct (constructive_indefinite_description
      (fun u : term => subterm_eq u t /\ NT_min R u) NT_min_intro) as [u hu].
      simpl. tauto.
    Qed.

    Definition min_NTM := mkNTM NT_min_term.

  End NT_min.

(*****************************************************************************)
(** get a minimal infinite (R @ supterm_eq)-sequence from an infinite
R-sequence *)

  Section IS_Min_supterm.

    Variable R : relation term.

    Definition Rsup : relation (NTM R) := R @ supterm_eq.

    Lemma Rsup_left_total : forall t, exists u, Rsup t u.

    Proof.
      intros [t [[f [h0 hf]] ht]]. exists (min_NTM (NT_IS_elt 1 hf)).
      unfold Rsup. simpl. exists (f 1). subst t. split_all.
      apply subterm_eq_min_term.
    Qed.

    Lemma IS_Min_supterm : forall f,
      IS R f -> exists g, IS (R @ supterm_eq) g /\ Min R g.

    Proof.
      intros f hf. set (Min' := fun f : nat -> NTM R =>
        forall i x, subterm x (f i) -> forall g, g 0 = x -> ~IS R g).
      cut (exists g : nat -> NTM R, IS Rsup g /\ Min' g).
      intros [g [h1 h2]]. exists (fun i => g i). split_all.
      destruct (choice _ Rsup_left_total) as [next hnext].
      set (a := min_NTM (NT_IS_elt 0 hf)). exists (iter a next). split.
      apply IS_iter. hyp.
      intros i x hx g g0 hg. destruct (iter a next i) as [t [[h [h0 hh]] ht]].
      simpl in hx. ded (ht _ hx). absurd (NT R x). hyp. exists g. tauto.
    Qed.

  End IS_Min_supterm.

(*****************************************************************************)
(** get an infinite (red R)-sub-sequence from an infinite
(int_red R)-sequence *)

  Lemma NT_int_red_subterm_NT_red : forall (R : rules Sig) f,
    IS (int_red R) f -> exists u, subterm u (f 0) /\ NT (red R) u.

  Proof.
    intros R f hf. subst. ded (hf 0). redtac. destruct c. cong.
    simpl in xl. clear yr lr cne r.
    (* forall i, exists v, f i = Fun f1 v *)
    assert (h : forall i, exists v, f i = Fun f0 v).
    induction i0. fo. clear xl s t0 c t e j i l.
    destruct IHi0 as [w hw]. ded (hf i0). redtac. destruct c. cong.
    simpl in xl, yr. rewrite hw in xl. Funeqtac. rewrite yr.
    exists (Vcast (Vapp t (Vcons (fill c (sub s r)) t0)) e). refl.
    clear xl s t0 c t e j i l. destruct (choice _ h) as [v hv]. clear h.
    (* forall i, exists k, exists hk : k < arity f0,
       int_red_pos_at k (f i) (f (S i)) *)
    assert (h : forall i, exists k, exists hk : k < arity f0,
      int_red_pos_at R k (f i) (f (S i))).
    intro i. ded (hf i). apply int_red_pos_eq in H. destruct H as [k H].
    cut (int_red_pos_at R k (f i) (f (S i))). 2: hyp.
    intro H'. destruct H as [g [hk [w [e H]]]]. rewrite hv in e. Funeqtac.
    exists k. exists hk. hyp. destruct (choice _ h) as [k hk]. clear h.
    (* infinite constant sub-sequence *)
    set (As := nats_decr_lt (arity f0)).
    assert (h : forall i, In (k i) As). intro i. destruct (hk i) as [hi ri].
    unfold As. rewrite <- In_nats_decr_lt. hyp.
    destruct (finite_codomain eq_nat_dec h) as [a [g [h1 [h2 h3]]]]. clear h As.
    assert (ha : a < arity f0). rewrite <- (h2 0). destruct (hk (g 0)). hyp.
    (* monotony of g *)
    assert (me : forall x y, x <= y -> g x <= g y). intros x y xy.
    destruct (lt_dec x y). ded (monS Nat.lt_trans h1). ded (H _ _ l). lia.
    assert (x=y). lia. subst. refl.
    (* forall j, j < g 0 -> k j <> a *)
    assert (hg0 : forall j, j < g 0 -> k j <> a).
    intros j hj e. destruct (h3 _ e) as [l hl]. subst.
    destruct (le_dec 0 l). ded (me _ _ l0). lia. lia.
    (* forall i j, g i < j < g (S i) -> k j <> a *)
    assert (hg : forall i j, g i < j < g (S i) -> k j <> a).
    intros i j hj e. destruct (h3 _ e) as [l hl]. subst.
    destruct (ge_dec i l). ded (me _ _ g0). lia.
    destruct (ge_dec l (S i)). ded (me _ _ g0). lia. lia.
    (* Vnth (v 0) ha = Vnth (v (g 0)) ha *)
    assert (h0 : Vnth (v 0) ha = Vnth (v (g 0)) ha).
    cut (forall l, l <= g 0 -> Vnth (v 0) ha = Vnth (v l) ha).
    intro h. apply h. refl.
    induction l; simpl. refl. intro h. rewrite IHl. 2: lia.
    destruct (hk l) as [_ r]. destruct r as [f' [hi [ts [e [w [p1 p2]]]]]].
    rewrite hv in e, p2. Funeqtac. Funeqtac. rewrite H, H0.
    rewrite Vnth_replace_neq. refl. apply (hg0 l). lia.
    (* forall i, Vnth (v (S (g i))) ha = Vnth (v (g (S i))) ha *)
    assert (h : forall i, Vnth (v (S (g i))) ha = Vnth (v (g (S i))) ha).
    intro i. ded (h1 i). cut (forall l, l < g (S i) - g i ->
      Vnth (v (S (g i))) ha = Vnth (v (S (g i) + l)) ha).
    intro hi. assert (e : g (S i) = S (g i) + (g (S i) - g i - 1)). lia.
    rewrite e. apply hi. clear e. clear -H; lia.
    induction l; intro. rewrite Nat.add_0_r. refl.
    assert (hl : l < g (S i) - g i). clear -H0; lia. rewrite (IHl hl).
    rewrite Nat.add_succ_r. simpl. set (x := S (g i + l)).
    destruct (hk x) as [_ r]. destruct r as [f' [hi [ts [e [w [p1 p2]]]]]].
    rewrite hv in e, p2. Funeqtac. Funeqtac. rewrite H1, H2.
    rewrite Vnth_replace_neq. refl. apply (hg i). unfold x. clear -H0; lia.
    (* [Vnth (v 0) ha] is a subterm of [f 0] *)
    exists (Vnth (v 0) ha). split.
    rewrite hv. apply subterm_fun. apply Vnth_in.
    (* [Vnth (v 0) ha] is non-terminating *)
    exists (fun i => Vnth (v (g i)) ha). split. sym. hyp.
    intro i. rewrite <- h. destruct (hk (g i)) as [_ r].
    destruct r as [f' [hi [ts [e [w [p1 p2]]]]]].
    rewrite hv in e, p2. Funeqtac. Funeqtac. rewrite H, H0.
    rewrite Vreplace_pi with (h2:=ha). 2: apply h2. rewrite Vnth_replace.
    rewrite Vnth_eq with (h2:=hi). 2: sym; apply h2. hyp.
  Qed.

(*****************************************************************************)
(** get a minimal infinite (hd_red_mod R (dp R))-sequence from a
minimal infinite R-sequence *)

  Section IS_Min_dp.

    Variable R : rules Sig.

    Variable hyp1 : forallb (@is_notvar_lhs Sig) R = true.
    Variable hyp2 : rules_preserve_vars R.

    Lemma min_hd_red_dp : forall t u v, NT_min (red R) t -> hd_red R t u ->
      subterm_eq v u -> NT_min (red R) v -> hd_red (dp R) t v.

    Proof.
      intros t u v ht tu vu hv. redtac. subst.
      (* forall x, ~NT (red R) (s x) *)
      assert (hs : forall x, In x (vars l) -> ~NT (red R) (s x)).
      intros x vx nx. assert (hx : subterm (Var x) l).
      destruct (in_vars_subterm_eq vx) as [c hx]. destruct c.
      rewrite forallb_forall in hyp1. ded (hyp1 _ lr). rewrite hx in H. discr.
      exists (Cont f e t c t0). split_all. discr.
      ded (subterm_sub s hx). destruct ht as [ht1 ht2].
      ded (ht2 _ H). contr.
      destruct (subterm_eq_sub_elim vu) as [w [hw1 hw2]]. destruct w.
      (* w = Var n *)
      assert (hn : In n (vars l)). eapply hyp2. apply lr.
      eapply subterm_eq_vars. apply hw1. simpl. auto.
      destruct hv as [hv1 hv2]. absurd (NT (red R) v).
      rewrite <- SN_notNT_eq. eapply subterm_eq_sn. rewrite SN_notNT_eq.
      eapply hs. apply hn. hyp. hyp.
      (* w = Fun f v0 *)
      subst. ex l (Fun f t) s. split_all. eapply dp_intro. apply lr.
      (* In (Fun f v0) (calls R r) *)
      apply subterm_in_calls. 2: hyp. case_eq (defined f R); intro H. refl.
      destruct hv as [hv1 hv2].
      absurd (NT (red R) (sub s (Fun f t))). 2: hyp.
      rewrite <- SN_notNT_eq. apply sn_args_sn_fun. hyp. hyp.
      apply Vforall_intro. intros a ha. rewrite SN_notNT_eq.
      apply hv2. apply subterm_fun. hyp.
      (* nebg_subterm l (Fun f t) = true *)
      unfold negb_subterm. rewrite negb_ok. 2: apply bsubterm_ok. intro h.
      destruct ht as [ht1 ht2]. absurd (NT (red R) (sub s (Fun f t))).
      apply ht2. apply subterm_sub. hyp. destruct hv as [hv1 hv2]. hyp.
    Qed.

    Definition Rdp : relation (NTM (red R)) := hd_red_Mod (int_red R #) (dp R).

    Lemma Rdp_left_total : forall t, exists u, Rdp t u.

    Proof.
      intros [t [[f [h0 hf]] ht]]. subst.
      (* f has a top reduct *)
      destruct (classic (IS (int_red R) f)).
      destruct (NT_int_red_subterm_NT_red H). ded (ht x). intuition.
      unfold IS in H. rewrite not_forall_eq in H.
      set (k := proj1_sig (ch_min H)).
      assert (hk : hd_red R (f k) (f (S k))). ded (hf k).
      destruct (red_split H0). hyp. ded (ch_minP _ H). contr.
      assert (hk' : int_red R # (f 0) (f k)).
      cut (forall i, i <= k -> int_red R # (f 0) (f i)).
      intro h. apply h. refl.
      induction i; intro hi. apply rt_refl. apply rt_trans with (f i).
      apply IHi. lia. apply rt_step. apply NNPP. intro h.
      assert (k <= i). apply is_min_ch. hyp. lia.
      (* (f k) is minimal *)
      assert (NT_min (red R) (f k)). split.
      exists (fun i => f (i+k)). intuition. intro i. apply hf.
      eapply int_red_rtc_min. apply hk'. hyp.
      (* take the minimal non-terminating subterm of [f (S k)] *)
      assert (NT (red R) (f (S k))). apply NT_IS_elt. hyp.
      exists (min_NTM H1). exists (mkNTM H0). simpl. intuition.
      eapply min_hd_red_dp. hyp. apply hk. apply subterm_eq_min_term.
      apply NT_min_term.
    Qed.

    Lemma IS_Min_dp : forall f, IS (red R) f ->
      exists g, IS (hd_red_Mod (int_red R #) (dp R)) g /\ Min (red R) g.

    Proof.
      intros f hf. set (Min' := fun f : nat -> NTM (red R) =>
        forall i x, subterm x (f i) -> forall g, g 0 = x -> ~IS (red R) g).
      cut (exists g : nat -> NTM (red R), IS Rdp g /\ Min' g).
      intros [g [h1 h2]]. exists (fun i => g i). intuition.
      destruct (choice _ Rdp_left_total) as [next hnext].
      set (a := min_NTM (NT_IS_elt 0 hf)). exists (iter a next). split.
      apply IS_iter. hyp.
      intros i x hx g g0 hg. destruct (iter a next i) as [t [[h [h0 hh]] ht]].
      simpl in hx. ded (ht _ hx). absurd (NT (red R) x). hyp.
      exists g. intuition.
    Qed.

  End IS_Min_dp.

End S.
