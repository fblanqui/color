(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

The beta-reduction relation of simply typed lambda-calculus
is introduced in this file.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras TermsRed TermsConv LogicUtil.
From Stdlib Require Import Setoid PeanoNat Lia.

Module TermsBeta (Sig : TermsSig.Signature).

  Module Export TR := TermsRed.TermsRed Sig.

  Definition beta_subst : forall M (Mapp: isApp M)
    (MLabs: isAbs (appBodyL Mapp)),
    correct_subst (absBody MLabs) {x/(lift (appBodyR Mapp) 1)}.

  Proof.
    intros M Mapp MLabs.
    apply one_var_subst_correct.
    rewrite lift_type.
    rewrite absBody_env.
    unfold decl, VarD; simpl.
    intros A' eqT.
    inversion eqT.
    destruct M as [EM PtM TM TypM].
    destruct TypM; try contr.
    rewrite (@abs_type (appBodyL Mapp) MLabs A B); trivial.
    rewrite lift_env.
    rewrite absBody_env.
    unfold liftedEnv, finalSeg; simpl.
    rewrite initialSeg_full; try solve [auto with datatypes | lia].
    unfold decl; apply env_comp_cons.
    rewrite appBodyL_env.
    rewrite appBodyR_env.
    apply env_comp_refl.
    auto.
  Defined.

  Lemma beta_env : forall M (Mapp: isApp M) (MLabs: isAbs (appBodyL Mapp)),
    env (subst (beta_subst M Mapp MLabs)) = None :: env M.

  Proof.
    intros.
    rewrite subst_env; simpl.
    unfold subst_ran; simpl.
    rewrite lift_env; simpl.
    unfold liftedEnv; simpl.
    rewrite absBody_env; simpl.
    rewrite appBodyL_env; simpl.
    rewrite finalSeg_full; simpl.
    rewrite appBodyR_env; simpl.
    rewrite env_sub_empty.
    rewrite env_sum_double; trivial.
  Qed.

  Lemma beta_lowering : forall M (Mapp: isApp M) (MLabs: isAbs (appBodyL Mapp)),
    env (subst (beta_subst M Mapp MLabs)) |= 0 :! .

  Proof. intros. rewrite beta_env. right; trivial. Qed.

  Inductive BetaStep : relation Term :=
  | Beta: forall M (Mapp: isApp M) (MLabs: isAbs (appBodyL Mapp)),
      BetaStep M
      (lower (subst (beta_subst M Mapp MLabs)) (beta_lowering M Mapp MLabs)).

  Definition BetaReduction := Reduction BetaStep.

  Notation "M -b-> N" := (BetaReduction M N) (at level 30).

  Lemma beta_type: forall M (Mapp: isApp M) (MLabs: isAbs (appBodyL Mapp)),
    absType MLabs = type (appBodyR Mapp).

  Proof.
    intros.
    destruct M as [??? typingM].
    destruct typingM; try contr.
    assert (type (appBodyL Mapp) = A --> B).
    trivial.
    rewrite (abs_type (appBodyL Mapp) MLabs H); trivial.
  Qed.

  Lemma beta_notFunS: forall M N, M -b-> N -> isFunS M -> False.

  Proof.
    intros M N MN.
    term_inv M.
    unfold Tr in MN.
    inversion MN; term_inv M.
    inversion H; try_solve.
  Qed.

  Lemma beta_direct_funApp : forall M (Mapp: isApp M)
    (MLabs: isAbs (appBodyL Mapp)), isFunS (appHead M) -> False.

  Proof.
    intros M Mapp MLabs Mhead.
    absurd (isFunS (appHead M)); trivial.
    rewrite (appHead_app M Mapp) in Mhead.
    assert (MLnotApp: ~isApp (appBodyL Mapp)).
    apply abs_isnot_app; trivial.
    rewrite (appHead_notApp (appBodyL Mapp) MLnotApp) in Mhead.
    exfalso. term_inv (appBodyL Mapp).
  Qed.

  Lemma app_beta_isapp : forall M N f,
    M -b-> N -> term (appHead M) = ^f -> isApp N.

  Proof.
    intro M; term_inv M.
     (* function symbol *)
    intros; exfalso.
    apply beta_notFunS with Tr N; trivial.
    unfold Tr; auto with terms.
     (* application *)
    intros N f MbN Mhead.
    inversion MbN; try solve [contr | trivial].
     (* direct beta step *)
    exfalso. inversion H.
    apply beta_direct_funApp with Tr I; eauto with terms.
  Qed.

  Lemma app_beta_headSymbol : forall M N f, M -b-> N -> term (appHead M) = ^f ->
    term (appHead N) = ^f.

  Proof.
    destruct M as [E Pt T TypM].
    induction TypM; simpl; intros N f' Nbeta Mhead; try discr;
      inversion Nbeta; try contr.
    inversion H; contr.
     (* 1) direct beta reduction (left applicant - abstraction) *)
    inversion H. exfalso.
    apply beta_direct_funApp with (buildT (TApp TypM1 TypM2)) Mapp0;
      eauto with terms.
     (* 2) beta reduction in left part of application *)
    term_inv N.
    unfold Tr.
    rewrite appHead_app_explicit.
    apply IHTypM1 with (N := @appBodyL (buildT (TApp T1 T2)) I).
    simpl; trivial.
    rewrite appHead_app_explicit in Mhead; trivial.
     (* 3) beta reduction in right part of application *)
    term_inv N.
    rewrite <- Mhead.
    unfold Tr.
    rewrite !appHead_app_explicit.
    congruence.
  Qed.

  Lemma app_beta_funS : forall M N,
    isFunS (appHead M) -> M -b-> N -> isFunS (appHead N).

  Proof.
    intros.
    destruct (funS_fun (appHead M) H) as [f Mf].
    apply funS_is_funS with f.
    apply (app_beta_headSymbol H0 Mf).
  Qed.

  Lemma app_beta_args : forall M N f,
    isApp M -> M -b-> N -> term (appHead M) = ^f ->
    exists l, exists el, isArg (fst el) M /\ isArg (snd el) N
      /\ fst el -b-> snd el /\
      appArgs M = fst l ++ fst el::snd l /\ appArgs N = fst l ++ snd el::snd l.

  Proof.
    destruct M as [E Pt T TypM].
    induction TypM; try solve [intros; inversion H].
    intros N f Mapp MbetaN Mhead.
    inversion MbetaN; try contr.
    inversion H. exfalso.
    apply beta_direct_funApp with (buildT (TApp TypM1 TypM2)) Mapp1;
      eauto with terms.
     (* -) beta in left argument *)
    simpl in *.
    rewrite (appHead_app (buildT (TApp TypM1 TypM2)) I) in Mhead; 
      trivial.
    case (isApp_dec (buildT TypM1)).
    intro M1app.
     (*   - M = @(@(...), _) *)
    destruct (IHTypM1 (appBodyL Napp) f) 
      as [[al ar] [[tl tr] [tlM [trN [tltr [Margs Nargs]]]]]];
      simpl in *; trivial.
    exists (al, ar ++ appBodyR Napp::nil); exists (tl, tr); 
      repeat split; simpl; trivial.
    apply appArg_left with I; trivial.
    apply appArg_left with Napp; trivial.
    rewrite (appArgs_app (buildT (TApp TypM1 TypM2)) I); simpl.
    rewrite Margs; rewrite H0.
    rewrite <- app_assoc; auto with datatypes.
    rewrite (appArgs_app N Napp); simpl.
    rewrite Nargs.
    rewrite <- app_assoc; auto with datatypes.
     (*   - M = @(_, _) *)
    intro M1nApp; simpl in *.
    rewrite appHead_notApp in Mhead; simpl in Mhead. exfalso.
    apply beta_notFunS with (buildT TypM1) (appBodyL Napp); 
      eauto with terms.
    trivial.
     (* -) beta in right argument *)
    term_inv N.
    exists (appArgs (buildT TypM1), nil(A:=Term)).
    exists (buildT TypM2, buildT T2); repeat split; simpl; trivial.
    apply appArg_right with I; trivial.
    apply appArg_right with I; trivial.
    rewrite appArgs_app with (buildT (TApp TypM1 TypM2)) I; trivial.
    rewrite appArgs_app with Tr I.
    rewrite H0; trivial.
  Qed.

  Lemma app_beta_args_eq : forall M N Q f,
    isApp M -> M -b-> N -> term (appHead M) = ^f ->
    isArg Q N -> (isArg Q M \/ (exists2 Mb, Mb -b-> Q & isArg Mb M)).

  Proof.
    intros M N Q f Mapp MbN Mhead QargN.
    destruct (app_beta_args Mapp MbN Mhead) as 
      [[al ar] [[tl tr] [tlM [trN [tltr [Margs Nargs]]]]]];
      simpl in * .
    unfold isArg in QargN; rewrite Nargs in QargN.
    destruct (in_app_or QargN).
    left.
    unfold isArg; rewrite Margs; auto with datatypes.
    inversion H.
    right; exists tl.
    rewrite <- H0; trivial.
    unfold isArg; rewrite Margs; auto with datatypes.
    left.
    unfold isArg; rewrite Margs; auto with datatypes.
  Qed.

  Lemma beta_funS_normal : forall M N, isFunS M -> ~(M -b-> N).

  Proof. intros M N Mf MN. inversion MN; inversion H; term_inv M. Qed.

  Lemma beta_var_normal : forall M N, isVar M -> ~(M -b-> N).

  Proof. intros M N Mvar MN. inversion MN; inversion H; term_inv M. Qed.

  Lemma betaStep_env_preserving : forall M N, BetaStep M N -> env M = env N.

  Proof.
    intros.
    inversion H.
    rewrite lower_env.
    rewrite beta_env.
    unfold loweredEnv, finalSeg; simpl.
    rewrite initialSeg_full; trivial.
    lia.
  Qed.

  Lemma beta_env_preserving : forall M N, M -b-> N -> env M = env N.

  Proof.
    intros.
    apply Red_env_preserving with BetaStep; trivial.
    apply betaStep_env_preserving.
  Qed.

  Lemma betaStep_type_preserving : forall M N, BetaStep M N -> type M = type N.

  Proof.
    intros.
    inversion H.
    rewrite lower_type.
    rewrite subst_type.
    destruct M as [ME MPt MT M].
    destruct M; try contr.
    assert (MlT: type (appBodyL Mapp0) = A --> B); [simpl; trivial | idtac].
    rewrite (absBody_type (appBodyL Mapp0) MLabs MlT); simpl; trivial.
  Qed.

  Lemma subject_reduction : forall M N, M -b-> N -> type M = type N.

  Proof.
    intros.
    apply Red_type_preserving with BetaStep; trivial.
    apply betaStep_type_preserving.
  Qed.

  Lemma beta_monotonous : monotonous BetaReduction.

  Proof. unfold BetaReduction; apply red_monotonous. Qed.

  Lemma betaStep_conv_comp_aux : forall M M' N N' Q, M ~(Q) M' -> N ~(Q) N' ->
    BetaStep M N -> env M' = env N' -> BetaStep M' N'.

  Proof.
    intros M M' N N' Q MQM' NQN' MN M'N'env.
    inversion MN.
    assert (M'app: isApp M').
    assert (MM' : M ~ M') by (exists Q; trivial).
    rewrite <- MM'; trivial.
    assert (M'Labs: isAbs (appBodyL M'app)).
    setoid_replace (appBodyL M'app) with (appBodyL Mapp0); trivial.
    apply app_conv_app_left.
    sym; exists Q; trivial.
    replace N' with (lower (subst (beta_subst M' M'app M'Labs)) 
      (beta_lowering M' M'app M'Labs)).
    constructor.
    rewrite terms_lift_eq with (lower (subst (beta_subst M' M'app M'Labs))
      (beta_lowering M' M'app M'Labs)) N'; trivial.
    apply term_eq.
    autorewrite with terms datatypes using unfold liftedEnv, loweredEnv; simpl.
    rewrite M'N'env; trivial.
    rewrite prelift_prelower.
    autorewrite with terms.
    rewrite <- lift_term.
    apply (@presubst_singleton_conv_sim 
      (term (absBody MLabs)) (term (absBody M'Labs))
      (lift (appBodyR Mapp0) 1) (lift (appBodyR M'app) 1) (envSubst_lift1 Q)
      (term (lift N 1)) (term (lift N' 1))
    ).
    destruct Q; simpl; trivial.
    assert (Conv: (absBody MLabs) ~(envSubst_lift1 Q) (absBody M'Labs)).
    apply abs_conv_absBody_aux.
    apply app_conv_app_left_aux; trivial.
    destruct Conv; trivial.
    apply terms_conv_conv_lift.
    apply app_conv_app_right_aux; trivial.
    assert (Conv: (lift N 1) ~(envSubst_lift1 Q) (lift N' 1)).
    apply terms_conv_conv_lift; trivial.
    destruct Conv; trivial.
    rewrite <- H0.
    rewrite prelift_prelower.
    autorewrite with terms using trivial.
  Qed.

  Lemma beta_conv_comp : forall M M' N N' Q,
    M ~(Q) M' -> N ~(Q) N' -> M -b-> N -> env M' = env N' -> M' -b-> N'.

  Proof.
    intros.
    unfold BetaReduction.
    apply red_conv_comp with M N Q; trivial.
    intros.
    apply betaStep_conv_comp_aux with M0 N0 Q0; trivial.
  Qed.

  Lemma subst_at0 : forall M G (MG: correct_subst M (None :: lift_subst G 1)),
    env M |= 0 :! -> env (subst MG) |= 0 :! .

  Proof.
    intros.
    rewrite subst_env.
    destruct (env M).
    rewrite subst_ran_cons_none.
    destruct (subst_empty_dec G); simpl.
    rewrite subst_ran_lifted_empty; trivial.
    rewrite subst_ran_lifted_ne; solve [trivial | constructor 2; trivial].
    destruct o.
    destruct H; try_solve.
    simpl.
    rewrite subst_ran_cons_none.
    destruct (subst_empty_dec G); simpl.
    rewrite subst_ran_lifted_empty; trivial.
    rewrite subst_ran_lifted_ne; solve [trivial | constructor 2; trivial].
  Qed.

  Lemma subst_envs_comp_cons : forall G,
    subst_envs_comp G -> subst_envs_comp (None :: G).

  Proof.
    intros.
    intros i j Ti Tj Gi Gj.
    destruct i; destruct j.
    try_solve.
    inversion Gi.
    inversion Gj.
    apply (H i j).
    inversion Gi; trivial.
    inversion Gj; trivial.
  Qed.

  Lemma correct_subst_lift : forall M N G (M0: env M |= 0 :!),
    correct_subst N G -> N = lower M M0 ->
    correct_subst M (None :: lift_subst G 1).

  Proof.
    intros ???? [envNG domNG ranNG] H.
    rewrite H in domNG.
    rewrite H in ranNG.
    rewrite lower_env in domNG.
    rewrite lower_env in ranNG.
    clear H.
    constructor.
    apply subst_envs_comp_cons.
    apply lifted_subst_envs_comp; trivial.
    destruct (env M).
    apply env_comp_empty.
    destruct o.
    destruct M0; try_solve.
    simpl.
    rewrite subst_dom_lifted.
    apply env_comp_cons; auto.
    unfold loweredEnv in domNG.
    simpl in domNG.
    rewrite finalSeg_cons in domNG; trivial.
    simpl.
    rewrite subst_ran_cons_none.
    rewrite subst_dom_lifted.
    destruct (subst_empty_dec G).
    rewrite subst_ran_lifted_empty; trivial.
    simpl; apply env_comp_sym; apply env_comp_empty.
    rewrite subst_ran_lifted_ne; trivial.
    simpl.
    destruct (env M).
    apply env_comp_empty.
    destruct o.
    destruct M0; try_solve.
    apply env_comp_cons; auto.
    unfold loweredEnv in ranNG.
    simpl in ranNG.
    rewrite finalSeg_cons in ranNG; trivial.
  Qed.

  Lemma lower_subst_aux : forall M G i, env M |= i :! ->
    presubst_aux (prelower_aux (term M) i) i (copy i None ++ G) = 
    prelower_aux (presubst_aux (term M) i
      (copy i None ++ None :: lift_subst G 1)) i.

  Proof.
    destruct M as [E Pt TM M].
    induction M; intros G i Mi; unfold prelower, presubst; simpl.
     (* variable *)
    destruct (Compare_dec.le_gt_dec i x); simpl.
    destruct (eq_nat_dec i x).
     (*   - x = i *)
    rewrite e in Mi.
    exfalso; eapply varD_UD_absurd; eauto.
     (*   - x > i *)
    destruct x; simpl. lia.
    replace (copy i None ++ None :: lift_subst G 1) with 
      ((None :: copy i None) ++ lift_subst G 1).
    simpl.
    repeat rewrite nth_app_right; rewrite copy_length; try lia.
    destruct (varSubst_dec G (x - i)) as [[T GT] | Gn].
    rewrite GT, (nth_lift_subst_s G 1 (x - i) GT), !lift_term, <- prelift_fold.
    apply prelower_prelift.
    set (w := var_notSubst_lift 1 Gn).
    inversion Gn; inversion w; rewrite H; rewrite H0; simpl;
      destruct (Compare_dec.le_gt_dec i (S x)); 
	solve [trivial | lia].
    rewrite <- list_app_first_last.
    rewrite <- copy_add; trivial.
    rewrite app_nil_r; trivial.
     (*   - x < i *)
    rewrite !nth_app_left, nth_copy_in.
    simpl.
    destruct (Compare_dec.le_gt_dec i x); trivial.
    lia.
    lia.
    rewrite copy_length; lia.
    rewrite copy_length; lia.
     (* function symbol *)
    trivial.
     (* abstraction *)
    set (w := IHM G (S i)).
    simpl in w.
    rewrite w; trivial.
     (* application *)
    rewrite IHM1; trivial.
    rewrite IHM2; trivial.
  Qed.

  Lemma lower_subst : forall M N G (M0: env M |= 0 :!) (MG: correct_subst N G)
    (MG': correct_subst M (None :: lift_subst G 1))
    (MG'0: env (subst MG') |= 0 :! := (subst_at0 G MG' M0)),
    N = lower M M0 -> subst MG = lower (subst MG') MG'0.

  Proof.
    intros.
    apply term_eq; autorewrite with terms; rewrite H; autorewrite with terms.

    destruct M as [envM ???].
    autorewrite with terms using simpl.
    unfold loweredEnv; simpl.
    destruct (subst_empty_dec G).
    destruct envM; simpl.
    autorewrite with terms; trivial.
    autorewrite with terms datatypes; trivial.
    destruct o; autorewrite with datatypes; trivial.
    destruct envM; simpl.
    autorewrite with datatypes terms.
    destruct (subst_ran G); trivial.
    destruct o; autorewrite with datatypes terms using simpl; trivial.

    unfold presubst, prelower.
    apply (lower_subst_aux M G M0).
  Qed.

  Lemma lower_eq : forall M N (M0: env M |= 0 :!) (N0: env N |= 0 :!), M = N ->
    lower M M0 = lower N N0.

  Proof.
    intros.
    apply term_eq.
    rewrite !lower_env; rewrite H; trivial.
    rewrite !lower_term; rewrite H; trivial.
  Qed.

  Lemma subst_single_eq : forall M M' P P' (MP: correct_subst M {x/P})
    (MP': correct_subst M' {x/P'}), M = M' -> P = P' -> subst MP = subst MP'.

  Proof.
    intros.
    apply term_eq.
    rewrite !subst_env, H, H0; trivial.
    rewrite !subst_term, H, H0; trivial.
  Qed.

  Lemma double_subst_aux : forall M P G i
    (PG: correct_subst P (None :: lift_subst G 1)),
    presubst_aux (presubst_aux M i (copy i None ++ {x/P}))
    i (copy (S i) None ++ lift_subst G 1) =
    presubst_aux (presubst_aux M i (copy (S i) None ++ lift_subst G 1))
    i (copy i None ++ {x/subst PG}).

  Proof.
    induction M; unfold presubst; intros; simpl.

    destruct (Compare_dec.gt_eq_gt_dec i x) as [[x_gt_i | x_eq_i] | x_lt_i].
    rewrite nth_beyond; autorewrite with terms datatypes; simpl; try lia.
    replace (None :: copy i None ++ lift_subst G 1) with 
      (copy (S i) None ++ lift_subst G 1); trivial.
    rewrite nth_app_right; autorewrite with terms datatypes; try lia.
    destruct (varSubst_dec G (x - S i)) as [[T GT] | Gn].
    rewrite (var_subst_lift 1 GT), !lift_term, <- prelift_fold,
      presubst_beyond; trivial.
    autorewrite with datatypes using simpl; try lia.
    destruct (var_notSubst_lift 1 Gn); rewrite H; 
      replace (%x) with (prelift (%0) x); trivial;
      rewrite presubst_beyond; solve 
	[ trivial
	| autorewrite with datatypes using simpl; try lia
	].

    rewrite x_eq_i.
    rewrite nth_app_right; autorewrite with datatypes using try lia.
    rewrite Nat.sub_diag; simpl.
    replace (None :: copy x None ++ lift_subst G 1) with 
      (copy (S x) None ++ lift_subst G 1); trivial.
    rewrite nth_app_left; autorewrite with datatypes terms using simpl;
      try lia.
    rewrite nth_app_right; autorewrite with datatypes terms using simpl;
      try lia.
    rewrite Nat.sub_diag; simpl.
    autorewrite with terms.
    rewrite <- presubst_prelift_comm; simpl.
    rewrite subst_lift_subst; simpl.
    rewrite lift_subst_distr.
    rewrite lift_empty_subst.
    rewrite <- copy_add; trivial.

    replace (None :: copy i None ++ lift_subst G 1) with 
      (copy (S i) None ++ lift_subst G 1); trivial.
    rewrite !nth_app_left; autorewrite with terms datatypes using simpl;
      try lia.
    replace (None :: copy i None ++ lift_subst G 1) with 
      (copy (S i) None ++ lift_subst G 1); trivial.
    replace (None :: copy i (None (A:=Term)))
      with (copy (S i) (None (A:=Term))); trivial.
    rewrite !nth_app_left; autorewrite with terms datatypes using simpl;
      try lia.
    rewrite nth_app_left; autorewrite with terms datatypes using trivial.

    trivial.
    replace (None :: copy i None ++ {x/P}) with 
      (copy (S i) None ++ {x/P}); trivial.
    replace (None :: None :: copy i None ++ lift_subst G 1) with 
      (copy (S (S i)) None ++ lift_subst G 1); trivial.
    replace (None :: copy i None ++ {x/subst PG}) with 
      (copy (S i) None ++ {x/subst PG}); trivial.
    rewrite (IHM P G (S i) PG); trivial.
    replace (None :: copy i None ++ lift_subst G 1) with 
      (copy (S i) None ++ lift_subst G 1); trivial.
    rewrite <- IHM1.
    rewrite <- IHM2.
    trivial.
  Qed.

  Lemma double_subst : forall M G P (MP: correct_subst M {x/P}) 
    (MPG: correct_subst (subst MP) (None :: lift_subst G 1))
    (MG: correct_subst M (None :: lift_subst G 1))
    (PG: correct_subst P (None :: lift_subst G 1)) 
    (MGP: correct_subst (subst MG) {x/subst PG}), subst MPG = subst MGP.

  Proof.
    intros.
    apply term_eq.

    autorewrite with terms.
    cut (tail (env M) [+] tail (env P) [-] subst_dom G [+] subst_ran G =
      tail (env M) [-] subst_dom G [+] subst_ran G [+] 
      (tail (env P) [-] subst_dom G [+] subst_ran G)).
    destruct (subst_empty_dec G).
    (*SLOW*)destruct (env M); destruct (env P); try destruct o;
      try destruct o0; simpl; (autorewrite with terms using simpl); try_solve.
    (*VERY SLOW*)destruct (env M); destruct (env P); try destruct o;
      try destruct o0; simpl; (autorewrite with terms using simpl); 
      try destruct (subst_ran G); try destruct (subst_dom G);
      try destruct e; try destruct o; try destruct o0; try_solve.
    rewrite env_sum_assoc.
    rewrite <- (env_sum_assoc (subst_ran G)).
    rewrite env_sum_remove_double.
    rewrite <- env_sum_assoc.
    rewrite env_sub_move; trivial.

    autorewrite with terms datatypes.
    unfold presubst.
    set (w := double_subst_aux (term M) G 0 PG).
    simpl in w; trivial.
  Qed.

  Lemma double_lift : forall M G
    (CS: correct_subst (lift M 1) (None :: lift_subst G 1))
    (CS': correct_subst M G), subst CS = lift (subst CS') 1.

  Proof.
    intros.
    apply term_eq.
    destruct (subst_empty_dec G); 
      autorewrite with terms datatypes using unfold liftedEnv; simpl; trivial.
    autorewrite with terms.
    replace (None :: lift_subst G 1) with (copy (S 0) None ++ lift_subst G 1);
    trivial.
    apply presubst_prelift_comm.
  Qed.

  Lemma subst_on_beta : forall M (Mapp: isApp M) (MLabs: isAbs (appBodyL Mapp))
    G (CS: correct_subst M G)
    (CSin: correct_subst (absBody MLabs) (None :: lift_subst G 1))
    (CSapp: isApp (subst CS) := app_subst_app Mapp CS)
    (CSLabs: isAbs (appBodyL CSapp)),
    subst CSin = absBody CSLabs.

  Proof.
    intros; apply term_eq.

    assert (absType MLabs = absType CSLabs).
    apply type_eq_absType_eq. 
    unfold CSapp; apply type_appBodyL_subst.
    destruct (subst_empty_dec G); autorewrite with terms using unfold decl;
      try_solve.

    autorewrite with terms datatypes using simpl.
    rewrite (absBody_term (appBodyL CSapp) CSLabs (A := absType MLabs)
      (Pt := presubst (term (absBody MLabs)) (None :: lift_subst G 1)));
      trivial.
    rewrite (appBodyL_term (subst CS) (PtL := \absType MLabs => 
      presubst (term (absBody MLabs)) (None::lift_subst G 1)) 
      (PtR := presubst (term (appBodyR Mapp)) G)); trivial.
    autorewrite with terms.
    rewrite (app_term M Mapp).
    rewrite (abs_term (appBodyL Mapp) MLabs).
    unfold presubst; simpl.
    rewrite subst_lift_subst; trivial.
  Qed.

  Lemma beta_lower_subst : forall M N G (Mapp: isApp M)
    (MLabs: isAbs (appBodyL Mapp)) 
    (MN: correct_subst M G) (NS: correct_subst N G)
    (MNS_app: isApp (subst MN) := app_subst_app Mapp MN) 
    (MNS_Labs: isAbs (appBodyL MNS_app)),
    N = lower (subst (beta_subst M Mapp MLabs)) (beta_lowering M Mapp MLabs) ->
    subst NS = lower (subst (beta_subst (subst MN) MNS_app MNS_Labs)) 
      (beta_lowering (subst MN) MNS_app MNS_Labs).

  Proof.
    intros.
    set (s0 := correct_subst_lift (subst (beta_subst M Mapp MLabs)) 
      (beta_lowering M Mapp MLabs) NS H).
    rewrite (lower_subst (beta_lowering M Mapp MLabs) NS s0 H).
    apply lower_eq.
    assert (s1: correct_subst (absBody MLabs) (None :: lift_subst G 1)).
    inversion MN; inversion NS; inversion s0; prove_correct_subst.
    assert
      (s2: correct_subst (lift (appBodyR Mapp) 1) (None :: lift_subst G 1)).
    inversion MN; inversion NS; inversion s0; prove_correct_subst.
    assert (s3: correct_subst (subst s1) {x/subst s2}).
    constructor.
    apply subst_envs_comp_single.
    assert (forall E, {x/type (appBodyR Mapp)} [<->] Some (absType MLabs) :: E).
    intro; apply env_comp_cons.
    auto with terms.
    left; rewrite beta_type; trivial.
    destruct (subst_empty_dec G); autorewrite with terms using simpl; auto.
    destruct (subst_empty_dec G);
      autorewrite with terms datatypes using simpl; auto with terms.
    rewrite (double_subst G (beta_subst M Mapp MLabs) s0 s1 s2 s3).
    apply term_eq.
    destruct (subst_empty_dec G);
      autorewrite with datatypes terms using simpl; trivial.
    autorewrite with datatypes terms using simpl.
    assert (Leq: presubst (term (absBody MLabs)) (None :: lift_subst G 1) = 
      term (absBody MNS_Labs)).
    cut (term (subst s1) = term (absBody MNS_Labs)).
    autorewrite with terms.
    intro; rewrite H0; trivial.
    rewrite (subst_on_beta Mapp MLabs MN s1 MNS_Labs); trivial.
    assert (R'eq: subst (subst_appR_c Mapp MN) = appBodyR MNS_app).
    destruct (app_subst Mapp MN).
    rewrite <- H1.
    rewrite (app_proof_irr (subst MN) (app_subst_app Mapp MN) MNS_app); trivial.
    assert (Req: subst s2 = lift (appBodyR MNS_app) 1).
    rewrite (double_lift s2 (subst_appR_c Mapp MN)).
    rewrite R'eq; trivial.
    try_solve.
  Qed.

  Lemma betaStep_subst_stable : forall M N G (MS: correct_subst M G)
    (NS: correct_subst N G), BetaStep M N -> BetaStep (subst MS) (subst NS).

  Proof.
    intros M N G MS NS MN.
    inversion MN.
    set (MNS_app := app_subst_app Mapp0 MS).
    assert (MNS_Labs: isAbs (appBodyL MNS_app)).
    eapply abs_isAbs.
    assert (MS_term : term (subst MS) = presubst_aux (term (appBodyL Mapp0)) 
      0 G [presubst_aux (term (appBodyR Mapp0)) 0 G]).
    rewrite subst_term; term_inv M.
    rewrite (appBodyL_term (subst MS) MS_term).
    rewrite (abs_term (appBodyL Mapp0) MLabs).
    simpl; eauto.
    rewrite (beta_lower_subst Mapp0 MLabs MS NS MNS_Labs); auto.
    constructor.
  Qed.

  Lemma beta_subst_stable : forall M N G (MS: correct_subst M G)
    (NS: correct_subst N G), M -b-> N -> subst MS -b-> subst NS.

  Proof.
    destruct M as [E Pt T M]; induction M; intros.

     (* variable *)
    absurd (buildT (TVar v) -b-> N); trivial.
    apply beta_var_normal; simpl; trivial.

     (* function symbol *)
    absurd (buildT (TFun E f) -b-> N); trivial.
    apply beta_funS_normal; simpl; trivial.

     (* abstraction *)
    inversion H; try_solve.
    inversion H0; try_solve.
    clear Mabs.
    assert (Mabs: isAbs (buildT (TAbs M))).
    simpl; trivial.
    destruct (abs_subst Mabs MS) as [Ms_type Ms_body].
    destruct (abs_subst Nabs NS) as [Ns_type Ns_body].
    constructor 4 with (abs_subst_abs Mabs MS) (abs_subst_abs Nabs NS).
    rewrite Ms_type; rewrite Ns_type; trivial.
    rewrite Ms_body; rewrite Ns_body.
    apply IHM; trivial.

     (* application *)
    inversion H; try_solve.
     (*  - beta reduction *)
    constructor 1.
    apply betaStep_subst_stable; trivial.

     (*  - reduction in left argument *)
    clear Mapp; assert (Mapp: isApp (buildT (TApp M1 M2))); simpl; trivial.
    destruct (app_subst Mapp MS) as [Ml Mr].
    destruct (app_subst Napp NS) as [Nl Nr].
    constructor 2 with (app_subst_app Mapp MS) (app_subst_app Napp NS).
    rewrite Ml; rewrite Nl; apply IHM1; trivial.
    rewrite Mr; rewrite Nr; trivial.
    apply term_eq.
    rewrite !subst_env, <- H1; trivial.
    rewrite !subst_term, <- H1; trivial.

     (*  - reduction in right argument *)
    clear Mapp; assert (Mapp: isApp (buildT (TApp M1 M2))); simpl; trivial.
    destruct (app_subst Mapp MS) as [Ml Mr].
    destruct (app_subst Napp NS) as [Nl Nr].
    constructor 3 with (app_subst_app Mapp MS) (app_subst_app Napp NS).
    rewrite Mr; rewrite Nr; apply IHM2; trivial.
    rewrite Ml; rewrite Nl; trivial.
    apply term_eq.
    rewrite !subst_env, <- H1; trivial.
    rewrite !subst_term, <- H1; trivial.
  Qed.

  Lemma beta_abs_reduct : forall M (Mabs: isAbs M) N, M -b-> N ->
    exists Nabs: isAbs N, absBody Mabs -b-> absBody Nabs.

  Proof.
    intros M Mabs N MN.
    inversion MN; term_inv M; try_solve.
    inversion H; try_solve.
    exists Nabs; trivial.
  Qed.

  Lemma beta_app_reduct : forall M N (Mapp: isApp M),
    M -b-> N ->
    (exists MLabs: isAbs (appBodyL Mapp),
      N = lower (subst (beta_subst M Mapp MLabs)) (beta_lowering M Mapp MLabs))
    \/ exists Napp: isApp N, 
      (appBodyL Mapp  =   appBodyL Napp /\ appBodyR Mapp -b-> appBodyR Napp)
      \/ (appBodyL Mapp -b-> appBodyL Napp /\ appBodyR Mapp  =   appBodyR Napp).

  Proof.
    intros M N Mapp MN.
    inversion MN; term_inv M; try_solve.
    left; inversion H.
    exists MLabs.
    rewrite (app_proof_irr Tr Mapp Mapp1); trivial.
    right; exists Napp; fo.
    right; exists Napp; fo.
  Qed.

  Lemma beta_var_consistent : forall M N,
    M -b-> N -> envSubset (activeEnv N) (activeEnv M).

  Proof.
    intros.
    apply red_var_consistent with BetaStep; trivial.
    clear M N H; intros M N MN.
    destruct MN.
    rewrite activeEnv_lower.
    rewrite (activeEnv_app M Mapp).
    rewrite (activeEnv_abs (appBodyL Mapp) MLabs).
    destruct (isVarDecl_dec (activeEnv (absBody MLabs)) 0) as [[B Ml0] | Mln].
    assert (Mlb0: exists A, activeEnv (absBody MLabs) |= 0 := A).
    exists B; trivial.
    rewrite (singleton_subst_activeEnv_subst (beta_subst M Mapp MLabs)
      (singletonSubst_cond (lift (appBodyR Mapp) 1)) Mlb0).
    rewrite (activeEnv_lift (appBodyR Mapp) 1).
    simpl; autorewrite with datatypes using unfold loweredEnv; simpl.
    apply env_subset_refl.
    rewrite (singleton_subst_activeEnv_noSubst (beta_subst M Mapp MLabs) Mln
      (singletonSubst_cond (lift (appBodyR Mapp) 1))); trivial.
    unfold loweredEnv; autorewrite with datatypes using simpl.
    apply env_subset_sum_l.
    simpl.
    apply env_comp_subset with (tail (env (subst (beta_subst M Mapp MLabs)))) 
      (env (appBodyR Mapp)).
    autorewrite with terms datatypes using simpl; auto with terms.
    apply env_subset_tail; apply activeEnv_subset.
    apply activeEnv_subset.
    rewrite finalSeg1_tail.
    apply env_subset_refl.
  Qed.

  Lemma betaStep_dec: forall M N, {BetaStep M N} + {~BetaStep M N}.

  Proof.
    intros.
    destruct (isApp_dec M) as [Mapp | Mnapp].
    destruct (isAbs_dec (appBodyL Mapp)) as [MLabs | MLnabs].
    destruct (eq_Term_dec N (lower (subst (beta_subst M Mapp MLabs))
      (beta_lowering M Mapp MLabs))).
    left; rewrite e; constructor.
    right; intro MN; inversion MN.
    apply n; rewrite <- H0.
    apply term_eq.
    autorewrite with terms using trivial.
    autorewrite with terms using trivial.
    replace (absBody MLabs0) with (absBody MLabs).
    replace (appBodyR Mapp1) with (appBodyR Mapp); trivial.
    term_inv M.
    apply absBody_eq; term_inv M.
    right; intro MN; inversion MN.
    absurd (isAbs (appBodyL Mapp1)); trivial.
    replace (appBodyL Mapp1) with (appBodyL Mapp); trivial.
    term_inv M.
    right; intro MN; inversion MN; try_solve.
  Qed.

  Lemma beta_dec: forall M N, {M -b-> N} + {~ M -b-> N}.

  Proof.
    intros; unfold BetaReduction.
    apply red_dec.
    apply betaStep_dec.
  Qed.

End TermsBeta.
