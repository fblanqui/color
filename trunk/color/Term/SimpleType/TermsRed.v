(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Formalization of reductions of simply-typed lambda terms.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras TermsSubstConv.

Module TermsRed (Sig : TermsSig.Signature).

  Module Export TSC := TermsSubstConv.TermsSubstConv Sig.

  Inductive Reduction (R: relation Term) : Term -> Term -> Prop :=
  | RedStep: forall M N, 
      R M N -> 
      Reduction R M N
  | RedAppL: forall M N (Mapp: isApp M) (Napp: isApp N),
      Reduction R (appBodyL Mapp) (appBodyL Napp) ->
      appBodyR Mapp = appBodyR Napp ->
      Reduction R M N
  | RedAppR: forall M N (Mapp: isApp M) (Napp: isApp N),
      Reduction R (appBodyR Mapp) (appBodyR Napp) ->
      appBodyL Mapp = appBodyL Napp ->
      Reduction R M N
  | RedAbs: forall M N (Mabs: isAbs M) (Nabs: isAbs N), 
      absType Mabs = absType Nabs ->
      Reduction R (absBody Mabs) (absBody Nabs) ->
      Reduction R M N.

  Lemma red_monotonous : forall R, monotonous (Reduction R).

  Proof.
    intro R.
    apply monotonicity_criterion.
    intros; apply RedAppL with Mapp M'app; trivial.
    intros; apply RedAppR with Mapp M'app; trivial.
    intros; apply RedAbs with Nabs N'abs; trivial.
  Qed.

  Section conv_comp.

    Variable R : relation Term.
    Notation Red := (Reduction R).

    Variable R_conv_comp : forall M N M' N' Q,
      M ~(Q) M' -> N ~(Q) N' -> R M N -> env M' = env N' -> R M' N'.

    Variable R_type_preserving: forall M N, R M N -> type M = type N.

    Variable R_env_preserving: forall M N, R M N -> env M = env N.
   
    Lemma Red_env_preserving : forall M N, Red M N -> env M = env N.

    Proof.
      intros M N MN.
      induction MN; try solve [term_inv M; term_inv N].
      apply R_env_preserving; trivial.
      term_inv M; term_inv N; inversion IHMN; trivial.
    Qed.

    Lemma Red_type_preserving : forall M N, Red M N -> type M = type N.

    Proof.
      intros M N MN.
      induction MN; try solve [term_inv M; term_inv N].
      apply R_type_preserving; trivial.
    Qed.

    Lemma red_conv_comp : forall M N, Red M N ->
      forall M' N' Q, M ~(Q) M' -> N ~(Q) N' -> env M' = env N' -> Red M' N'.

    Proof.
      induction 1; intros.
      constructor.
      apply R_conv_comp with M N Q; trivial.

      assert (M'app: isApp M').
      assert (H'1 : M ~ M') by (exists Q; trivial).
      rewrite <- H'1; trivial.
      assert (N'app: isApp N').
      assert (H'2 : N ~ N') by (exists Q; trivial).
      rewrite <- H'2; trivial.
      constructor 2 with M'app N'app; trivial.
      apply IHReduction with Q.
      apply app_conv_app_left_aux; trivial.
      apply app_conv_app_left_aux; trivial.
      autorewrite with terms using trivial.
      apply term_eq.
      autorewrite with terms using trivial.      
      apply conv_term_unique with (term (appBodyR Mapp)) Q.
      destruct (app_conv_app_right_aux Mapp M'app H1); trivial.
      rewrite H0.
      destruct (app_conv_app_right_aux Napp N'app H2); trivial.

      assert (M'app: isApp M').
      assert (H'1 : M ~ M') by (exists Q; trivial).
      rewrite <- H'1; trivial.
      assert (N'app: isApp N').
      assert (H'2 : N ~ N') by (exists Q; trivial).
      rewrite <- H'2; trivial.
      constructor 3 with M'app N'app; trivial.
      apply IHReduction with Q.
      apply app_conv_app_right_aux; trivial.
      apply app_conv_app_right_aux; trivial.
      autorewrite with terms using trivial.
      apply term_eq.
      autorewrite with terms using trivial.
      apply conv_term_unique with (term (appBodyL Mapp)) Q.
      destruct (app_conv_app_left_aux Mapp M'app H1); trivial.
      rewrite H0.
      destruct (app_conv_app_left_aux Napp N'app H2); trivial.

      assert (M'abs: isAbs M').
      assert (H'1 : M ~ M') by (exists Q; trivial).
      rewrite <- H'1; trivial.
      assert (N'abs: isAbs N').
      assert (H'2 : N ~ N') by (exists Q; trivial).
      rewrite <- H'2; trivial.
      assert (absType M'abs = absType N'abs).
      rewrite <- abs_conv_absType with M M' Mabs M'abs.
      rewrite <- abs_conv_absType with N N' Nabs N'abs.
      trivial.
      exists Q; trivial.
      exists Q; trivial.
      constructor 4 with M'abs N'abs; trivial.
      apply IHReduction with (envSubst_lift1 Q).
      apply abs_conv_absBody_aux; trivial.
      apply abs_conv_absBody_aux; trivial.
      autorewrite with terms.
      congruence.
    Qed.

  End conv_comp.

  Section var_comp.

    Variable R : relation Term.
    Notation Red := (Reduction R).

    Variable step_var_consistent : forall M N,
      R M N -> envSubset (activeEnv N) (activeEnv M).

    Lemma red_var_consistent : forall M N,
      Red M N -> envSubset (activeEnv N) (activeEnv M).

    Proof.
      induction 1; intros.

      apply step_var_consistent; trivial.

      rewrite (activeEnv_app M Mapp).
      rewrite (activeEnv_app N Napp).
      rewrite H0.
      apply env_subset_sum_req; trivial.

      rewrite (activeEnv_app M Mapp).
      rewrite (activeEnv_app N Napp).
      rewrite H0.
      apply env_subset_sum_leq; trivial.
      rewrite <- H0.
      apply activeEnv_app_comp.

      rewrite (activeEnv_abs M Mabs).
      rewrite (activeEnv_abs N Nabs).
      intros x A D.
      apply varD_tail.
      apply IHReduction.
      apply varD_tail_rev; trivial.
   Qed.

  End var_comp.

  Section Decidability.

    Variable R : relation Term.
    Notation Red := (Reduction R).

    Variable step_dec : forall M N, {R M N} + {~R M N}.

    Lemma red_dec : forall M N, {Red M N} + {~Red M N}.

    Proof.
      intro M.
      apply well_founded_induction_type with (R := subterm)
        (P := fun M => forall N, {Red M N} + {~Red M N}).
      apply subterm_wf.
      clear M; intros M IH N.
      destruct (step_dec M N).
      left; apply RedStep; trivial.
      destruct (isApp_dec M) as [Mapp | Mnapp].
      destruct (isApp_dec N) as [Napp | Nnapp].
      destruct (IH (appBodyL Mapp) (appBodyL_subterm M Mapp) (appBodyL Napp)).
      destruct (eq_Term_dec (appBodyR Mapp) (appBodyR Napp)).
      left; apply RedAppL with Mapp Napp; trivial.
      destruct (IH (appBodyR Mapp) (appBodyR_subterm M Mapp) (appBodyR Napp)).
      destruct (eq_Term_dec (appBodyL Mapp) (appBodyL Napp)).
      left; apply RedAppR with Mapp Napp; trivial.
      right; intro MN; inversion MN; try_solve.
      apply n0; term_inv M; term_inv N.
      apply n1; term_inv M; term_inv N.
      term_inv M.
      right; intro MN; inversion MN; try_solve.
      apply n0; term_inv M; term_inv N.
      apply n1; term_inv M; term_inv N.
      term_inv M.
      destruct (IH (appBodyR Mapp) (appBodyR_subterm M Mapp) (appBodyR Napp)).
      destruct (eq_Term_dec (appBodyL Mapp) (appBodyL Napp)).
      left; apply RedAppR with Mapp Napp; trivial.
      right; intro MN; inversion MN; try_solve.
      apply n0; term_inv M; term_inv N.
      apply n1; term_inv M; term_inv N.
      term_inv M.
      right; intro MN; inversion MN; try_solve.
      apply n0; term_inv M; term_inv N.
      apply n1; term_inv M; term_inv N.
      term_inv M.
      right; intro MN; inversion MN; try_solve.
      term_inv M.
      destruct (isAbs_dec M) as [Mabs | Mnabs].
      destruct (isAbs_dec N) as [Nabs | Nnabs].
      destruct (IH (absBody Mabs) (absBody_subterm M Mabs) (absBody Nabs)).
      destruct (eq_SimpleType_dec (absType Mabs) (absType Nabs)).
      left; apply RedAbs with Mabs Nabs; trivial.
      right; intro MN; inversion MN; try_solve.
      apply n0; term_inv M; term_inv N.
      right; intro MN; inversion MN; try_solve.
      apply n0; term_inv M; term_inv N.
      right; intro MN; inversion MN; try_solve.
      right; intro MN; inversion MN; try_solve.
    Qed.

  End Decidability.

End TermsRed.
