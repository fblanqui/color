(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha & Frederic Blanqui, 2010-04-06

Subterm criterion from:

Tyrolean Termination Tool: Techniques and Features
Nao Hirokawa and Aart Middeldorp
Information and Computation 205(4), pp. 474 – 511, 2007

Uses classical logic and the axiom of indefinite description.
*)

Set Implicit Arguments.

Require Import ATrs ASimpleProj RelUtil List ARelation LogicUtil NatUtil
  VecUtil InfSeq ASN SN ClassicUtil BoolUtil ListUtil ASubterm ADP.

Section S.

  Variable Sig : Signature.

  Notation supterm := (@supterm Sig).
  Notation supterm_eq := (@supterm_eq Sig).

(***********************************************************************)
(** assumptions *)

  Variables (pi : Sig -> nat) (Hpi : valid pi).

  Notation proj := (proj Hpi).

  Definition ge := proj_ord Hpi supterm_eq.
  Definition gt := proj_ord Hpi supterm.

  Section prop.

    Variables M D : rules Sig.

    Variable hyp1 : forall l r, In (mkRule l r) D -> ge l r.

    Variable hyp2 : exists l, exists r, In (mkRule l r) D /\ gt l r.

    Variable hyp3 : forall l r,
      In (mkRule l r) D -> is_notvar_lhs (mkRule l r) =  true.

(***********************************************************************)
(** properties of the projected subterm ordering *)

    Lemma supterm_proj : forall t u s, gt t u -> gt (sub s t) (sub s u).

    Proof.
      intros t u s. unfold gt, proj_ord, transp.
      case t. simpl. intro. case u. simpl. intros.
      destruct H. destruct H. destruct (var_eq_fill H0). tauto.
      intros. rewrite proj_sub_fun.
      destruct H. destruct H. destruct (var_eq_fill H0). tauto.
      intros. destruct u. rewrite proj_sub_fun.
      generalize (substitution_closed_subterm s H); intros.
      apply (@subterm_trans_eq1 _ _ (sub s (Var n)) _); auto. simpl.
      apply subterm_eq_proj.
      repeat rewrite proj_sub_fun. apply substitution_closed_subterm. auto.
    Qed.

    Lemma supterm_eq_proj : forall l r s,
      In (mkRule l r) D -> ge (sub s l) (sub s r).

    Proof.
      intros l r s Dlr. unfold ge. generalize (hyp1 _ _ Dlr); intro.
      case_eq (beq_term (proj l) (proj r)). Focus 2.
      assert (proj l <> proj r).
      intro. rewrite (proj2 (beq_term_ok _ _) H1) in H0. discr.
      apply subterm_strict. apply supterm_proj. apply subterm_noteq. hyp.
      intro. apply H1. symmetry. hyp.
      generalize (proj1 (beq_term_ok _ _) H0). clear H0; intros.
      unfold proj_ord, transp. generalize (hyp3 _ _ Dlr). destruct l.
      unfold is_notvar_lhs. simpl. intros. discr.
      intros. destruct r. rewrite proj_sub_fun, H0. simpl.
      apply subterm_eq_proj.
      clear H1. repeat rewrite proj_sub_fun. rewrite H0. refl.
    Qed.

    Lemma int_red_proj : forall t u,
      int_red M # t u -> red M # (proj t) (proj u).

    Proof.
      induction 1. 2: apply rt_refl.
      Focus 2. apply (@rtc_trans _ _ _ (proj y) _); auto.
      destruct H as [l H]. destruct H as [r H]. destruct H as [c H].
      destruct H as [s H]. destruct H as [c_nH H]. destruct H as [Mlr H].
      destruct H as [Ht Hu]. destruct c. intuition. rewrite Ht, Hu. simpl.
      case (zerop (arity f)); intro Hf0.
      assert (arity f <> 0). rewrite <- e. omega. absurd_arith.
      repeat rewrite Vnth_cast. repeat rewrite Vnth_app.
      destruct (le_gt_dec i (pi f)). repeat rewrite Vnth_cons.
      destruct (lt_ge_dec 0 (pi f - i)). apply rt_refl.
      apply rt_step. apply red_rule. hyp. apply rt_refl.
    Qed.

(***********************************************************************)
(** main lemma *)

    Lemma subterm_criterion_IS : forall f g, ~ISModMin M D f g.

    Proof.
      intros f g HM. destruct HM as [HisM hmin]. destruct hmin as [hmin HsT].
      destruct HsT as [Rsf Rsg]. unfold InfRuleApp in hmin.
      unfold ISMod in HisM. destruct hyp2 as [l H0]. destruct H0 as [r H0].
      destruct H0 as [Dlr Glr].

      pose (f0 := fun i => proj (f i)). pose (g0 := fun i => proj ( g i)).
      pose (P := fun i x => i <= x /\ supterm (g0 x) (f0 (S x))).

      assert (HexP : forall i, exists j, P i j).
      destruct (hmin (mkRule l r) Dlr) as [h h_def].
      assert (hMj : forall j, j <= h j).
      induction 0. omega. apply lt_le_S. apply (le_lt_trans _ _ _ IHj).
      destruct (h_def j). auto. intro i. exists (h i). unfold P. split.
      apply hMj.
      destruct (h_def i) as [_ Dlr_i]. destruct Dlr_i as [l' H].
      destruct H as [r' H].
      destruct H as [s H]. destruct H as [Elr H]. destruct H as [Egi Efi].
      destruct Elr as [Elr |]; try tauto. symmetry in Elr.
      rewrite <- rule_eq in Elr.
      simpl in Elr. destruct Elr. subst. unfold f0, g0. rewrite Efi, Egi.
      apply supterm_proj. auto.

      assert (ISMfg0 : ISMod (red M #) (red M # U supterm) f0 g0).
      intro i. unfold f0, g0. split. apply int_red_proj. apply (proj1 (HisM i)).
      destruct (HisM i) as [_ [l' [r' [s [Dlr' [Eg Ef]]]]]]. rewrite Eg, Ef.
      destruct (supterm_eq_proj l' r' s Dlr') as [C HC].
      destruct C. simpl in HC. rewrite HC. left. apply rtc_refl.
      right. exists (Cont f1 e v C v0); split; auto. discr.
      destruct (ISMod_union ISMfg0 HexP (@rtc_trans _ (red M)))
        as [f1 [g1 Hfg1]].

      pose (TrS := (transp_trans (@subterm_trans Sig))).
      assert (HT : supterm @ (red M !) @ supterm << (red M !) @ supterm).
      intros x y Hxy. destruct Hxy as [z Hxy]. destruct Hxy as [Hxz Szy].
      destruct ((commut_tc_inv (@supterm_red _ _)) _ _ Hxz) as [u Hxu].
      exists u; split. exact (proj1 Hxu). apply (@subterm_trans _ _ z _); auto.
      exact (proj2 Hxu).

      destruct (trc_ISMod (proj1 Hfg1) (@NIS_supterm Sig) TrS) as [f2 [g2 HF]].
      destruct HF as [HF1 [[k Hk] HF]]. generalize (ISOfISMod_spec HF1 HT).
      set (h := ISOfISMod HF1 HT). intros ISM.
      assert (Hhk : (h (S 0)) = g1 k). unfold ISOfISMod; simpl. auto.
      set (h0 := fun i => h (S i)). assert (ISM0 : IS (red M !) h0). intro.
      apply (ISM (S i)). destruct (IS_tc ISM0) as [h1 Hh1].

      destruct (proj1 ((proj2 Hfg1) k)) as [k' Hk'].

      cut (subterm (proj (g k')) (g k')). intros HT0.
      apply (Rsg _ _ HT0 h1). rewrite (proj2 Hh1). unfold h0. rewrite Hhk, Hk'.
      auto. intuition. destruct (proj1 Hfg1 k) as [_ HT0]. rewrite Hk' in HT0.
      unfold g0 in HT0. destruct (g k'). simpl in HT0. destruct HT0 as [? HT0].
      simpl in HT0. destruct (var_eq_fill (proj2 HT0)). tauto. generalize HT0.
      simpl.
      case (zerop (arity f3)); intros Hf30 HT1. destruct HT1 as [c HT1].
      destruct (fun_eq_fill (proj2 HT1)) as [HT2 | HT2]. tauto.
      destruct HT2 as [i [j [HT2 _]]].
      assert (arity f3 <> 0). rewrite <- HT2. omega. absurd_arith.
      apply subterm_fun. apply Vnth_in.
    Qed.

  End prop.

(***********************************************************************)
(** WARNING: we use the following axiom *)

Axiom WF_IS_DP : forall Sig (M D : rules Sig), D [= dp M ->
  ~WF (hd_red_mod M D) -> exists f, exists g, ISModMin M D f g.

(***********************************************************************)
(** theorem with boolean conditions *)

  Definition bge x y := bsupterm_eq (proj x) (proj y).
  Definition bgt x y := bsupterm (proj x) (proj y).

  (*REMOVE?
  Lemma bge_ok : forall x y, bge x y = true <-> ge x y.

  Proof.
    intros x y. apply bsubterm_eq_ok.
  Qed.

  Lemma bgt_ok : forall x y, bgt x y = true <-> gt x y.

  Proof.
    intros x y. apply bsubterm_ok.
  Qed.*)

  Require Import IS_NotSN.

  Lemma subterm_criterion_WF : forall M D1 D2,
    D1 ++ D2 [= dp M ->
      forallb (brule bge) (D1 ++ D2) = true ->
      forallb (brule bgt) D1 = true ->
      forallb (@is_notvar_lhs Sig) (D1 ++ D2) = true -> 
      WF (hd_red_mod M D2) -> WF (hd_red_mod M (D1 ++ D2)).

  Proof.
    intros M D1 D2 H b1 b2 b3 h. destruct D1 as [|a D1]. auto.
    assert (h1 : forall l r, In (mkRule l r) (a :: D1 ++ D2) -> ge l r).
    intros l r lr. generalize (proj1 (forallb_forall _ _) b1 _ lr).
    unfold brule. simpl. apply (proj1 (bsubterm_eq_ok _ _)).
    assert (h2 : exists l, exists r, In (mkRule l r) (a :: D1 ++ D2) /\ gt l r).
    exists (lhs a). exists (rhs a). simpl. split.
    left. apply (proj1 (rule_eq _ _)). simpl. auto.
    generalize (proj1 (forallb_forall _ _) b2 a (in_eq a _)). unfold brule.
    apply (proj1 (bsubterm_ok _ _)).
    assert (h3 : forall l r, In (mkRule l r) (a :: D1 ++ D2) ->
      is_notvar_lhs (mkRule l r) = true).
    intros. apply (proj1 (forallb_forall _ _) b3). auto.
    ded (@subterm_criterion_IS M _ h1 h2 h3). clear -H0 H.
    apply NNPP. intro h. destruct (WF_IS_DP H h) as [f [g hfg]].
    ded (H0 f g). contr.
  Qed.

  Lemma subterm_criterion : forall M D, D [= dp M ->
    forallb (brule bge) D = true ->
    forallb (@is_notvar_lhs Sig) D = true ->
    WF (hd_red_mod M (filter (brule (neg bgt)) D)) ->
    WF (hd_red_mod M D).

  Proof.
    intros M D H b2 b3. set (De := filter (brule (neg bgt)) D).
    pose (Dt := filter (brule bgt) D).
    assert (i : hd_red_mod M D << hd_red_mod M (Dt ++ De)).
    apply hd_red_Mod_incl. refl. intros d hd. apply in_or_app.
    case_eq (brule (neg bgt) d). right. apply (proj2 (filter_In _ _ _)).
    intuition.
    left. apply (proj2 (filter_In _ _ _)). split; try hyp. unfold brule in H0.
    generalize (proj1 (negb_lr _ _) H0). auto.
    intro he. apply (WF_incl i). apply subterm_criterion_WF; auto.
    intro; rewrite in_app; unfold Dt, De; intro T.
    destruct T as [T|T]; apply H; rewrite filter_In in T; destruct T; auto.
    apply (proj2 (forallb_forall _ _)). intros x hx.
    apply (proj1 (forallb_forall _ _) b2 x). destruct (in_app_or hx) as [h|h].
    unfold Dt in h. rewrite filter_In in h. destruct h. hyp.
    unfold De in h. rewrite filter_In in h. destruct h. hyp.
    apply (proj2 (forallb_forall _ _)). intros x hx.
    unfold Dt in hx. rewrite filter_In in hx. destruct hx. hyp.
    apply (proj2 (forallb_forall _ _)). intros x hx.
    apply (proj1 (forallb_forall _ _) b3 x). destruct (in_app_or hx) as [h|h].
    unfold Dt in h. rewrite filter_In in h. destruct h. hyp.
    unfold De in h. rewrite filter_In in h. destruct h. hyp.
  Qed.

End S.

Implicit Arguments subterm_criterion [Sig pi D].

(***********************************************************************)
(** tactics *)

Require Import ListDec.

Ltac subterm_crit S p_ok := apply (subterm_criterion p_ok);
  [ incl (@beq_rule_ok S)
  | check_eq || fail 10 "a left-hand side is a variable"
  | check_eq || fail 10 "error in subterm criterion application"
  | hd_red_mod].
