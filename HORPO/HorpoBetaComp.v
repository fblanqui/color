(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

    Some computability results for horpo union beta.
************************************************************************)

Set Implicit Arguments.
Require Import RelExtras.
Require Import ListExtras.
Require Computability.
Require Horpo.

Module HorpoBetaComp (S : TermsSig.Signature) (Prec : Horpo.Precedence with Module S := S).

  Module Comp := Computability.Computability S Prec.

  Export Comp.
  Import List.

  Definition HB M N := M >> N \/ M -b-> N.
  Definition HB_lt := transp Term HB.
  Definition HB_mul_lt := MultisetLT HB.
  
  Notation "X -HB-> Y" := (HB X Y) (at level 55).
  Notation "X <-HB- Y" := (HB_lt X Y) (at level 55).
  Definition HBtrans := clos_trans Term HB.
  Notation "X -HB*-> Y" := (HBtrans X Y) (at level 55).

  Definition Terms := list Term.
  Definition CompHB := Computable HB.
  Definition CompTerms (Ts: Terms) := AllComputable HB Ts.
  Definition CompSubst (G: Subst) := forall Q, In (Some Q) G -> CompHB Q.

  Definition WFterms := { Ts: Terms | CompTerms Ts }.
  Definition WFterms_to_mul (Ts: WFterms) : Multiset := list2multiset (proj1_sig Ts).
  Coercion WFterms_to_mul: WFterms >-> Multiset.
  Definition HB_WFterms_lt (M N: WFterms) := HB_mul_lt M N.

  Hint Unfold HB HB_lt HB_mul_lt CompHB CompTerms CompHB: horpo.

  Lemma HB_type_preserving : forall M N, M -HB-> N -> type M = type N.

  Proof.
    intros M N MN.
    inversion MN.
    apply horpo_type_preserving; trivial.
    apply subject_reduction; trivial.
  Qed.

  Lemma HB_env_preserving : forall M N, M -HB-> N -> env M = env N.

  Proof.
    intros M N MN.
    inversion MN.
    apply horpo_env_preserving; trivial.
    apply beta_env_preserving; trivial.
  Qed.

  Lemma HB_algebraic_preserving : forall M N, algebraic M -> M -HB-> N -> algebraic N.

  Proof.
    intros M N Mnorm MN.
    inversion MN.
    inversion H; trivial.
    apply beta_algebraic_preserving with M; trivial.
  Qed.

  Lemma HB_var_normal : forall M N, isVar M -> ~M -HB-> N.

  Proof.
    intros M N Mvar MN.
    inversion MN.
    apply (horpo_var_normal Mvar H).
    apply (beta_var_normal Mvar H).
  Qed.

  Lemma HB_app_reduct : forall M N (Mapp: isApp M), M -HB-> N ->
    ~isFunApp M \/ isArrowType (type M) ->
    (exists MLabs: isAbs (appBodyL Mapp), 
      N = lower (subst (beta_subst M Mapp MLabs)) (beta_lowering M Mapp MLabs)) \/
    exists Napp: isApp N, 
      (appBodyL Mapp   =   appBodyL Napp /\ appBodyR Mapp -HB-> appBodyR Napp) \/
      (appBodyL Mapp -HB-> appBodyL Napp /\ appBodyR Mapp   =   appBodyR Napp) \/
      (appBodyL Mapp -HB-> appBodyL Napp /\ appBodyR Mapp -HB-> appBodyR Napp).

  Proof.
    intros.
    destruct H.
    right.
    destruct (horpo_app_reduct Mapp H0 H) as [Napp Mred]; exists Napp; firstorder.
    destruct (beta_app_reduct Mapp H) as [[MLabs NL] | [Napp Mred]].
    left; exists MLabs; trivial.
    right; exists Napp; firstorder.
  Qed.

  Lemma HB_abs_reduct : forall M (Mabs: isAbs M) N, M -HB-> N ->
    exists Nabs: isAbs N, absBody Mabs -HB-> absBody Nabs.

  Proof.
    intros.
    destruct H.
    destruct (horpo_abs_reduct Mabs H); firstorder.
    destruct (beta_abs_reduct Mabs H); firstorder.
  Qed.

  Lemma HB_conv_comp : forall M N M' N' Q, M ~(Q) M' -> N ~(Q) N' -> M -HB-> N -> env M' = env N' ->
    M' -HB-> N'.

  Proof.
    intros.
    destruct H1.
    constructor 1.
    apply horpo_conv_comp with M N Q; trivial.
    constructor 2.
    apply beta_conv_comp with M N Q; trivial.
  Qed.

  Lemma HB_subst_stable : forall M N G (MS: correct_subst M G) (NS: correct_subst N G),
    algebraicSubstitution G -> M -HB-> N -> subst MS -HB-> subst NS.

  Proof.
    intros; destruct H0.
    set (w := horpo_subst_stable MS NS H); firstorder.
    set (w := beta_subst_stable MS NS H0); firstorder.
  Qed.

  Lemma HB_var_consistent : forall M N, M -HB-> N -> envSubset (activeEnv N) (activeEnv M).

  Proof.
    intros.
    destruct H.
    apply horpo_var_consistent; trivial.
    apply beta_var_consistent; trivial.
  Qed.

  Lemma HB_monotonous : algebraic_monotonicity HB.

  Proof.
    intro T; intros.
    destruct H3.
    constructor 1.
    apply horpo_monotonous; trivial.
    constructor 2.
    apply (monotonicity_algebraicMonotonicity beta_monotonous); trivial.
  Qed.  

  Hint Resolve HB_type_preserving HB_env_preserving HB_algebraic_preserving HB_var_normal 
               HB_app_reduct HB_abs_reduct HB_monotonous HB_conv_comp 
               HB_subst_stable HB_var_consistent : horpo_beta.

  Lemma HB_comp_imp_acc : forall M, CompHB M -> AccR HB M.

  Proof.
    intros M Mcomp.
    apply comp_imp_acc; eauto with horpo_beta.
  Qed.

  Lemma HB_comp_step_comp : forall M N, CompHB M -> M -HB-> N -> CompHB N.

  Proof.
    intros M N Mcomp MN.
    unfold CompHB; apply comp_step_comp with M; eauto with horpo_beta.
  Qed.

  Lemma HB_comp_manysteps_comp : forall M N, CompHB M -> M -HB*-> N -> CompHB N.

  Proof.
    intros M N Mcomp M_N.
    unfold CompHB; apply comp_manysteps_comp with M; eauto with horpo_beta.
  Qed.

  Lemma HB_comp_pflat : forall N Ns, isPartialFlattening Ns N -> algebraic N ->
    AllComputable HB Ns -> CompHB N.

  Proof.
    intros N Ns NsN Nnorm NsC; unfold CompHB.
    apply comp_pflat with Ns; trivial.
  Qed.

  Lemma HB_neutral_comp_step : forall M, algebraic M -> isNeutral M ->
    (CompHB M <-> (forall N, M -HB-> N -> CompHB N)).

  Proof.
    intros M Mneutral; unfold CompHB.
    apply neutral_comp_step; eauto with horpo_beta.
  Qed.

  Lemma CompHB_morph_aux : forall x1 x2 : Term, x1 ~ x2 -> CompHB x1 -> CompHB x2.

  Proof.
    intros t t' teqt' H_t.
    unfold CompHB.
    apply Computable_morph_aux with t; eauto with horpo_beta.
  Qed.

  Add Morphism CompHB : CompHB_morph.

  Proof.
    intros; split; apply CompHB_morph_aux; auto using terms_conv_sym.
  Qed.

  Lemma HB_comp_conv: forall M M', CompHB M -> M ~ M' -> CompHB M'.

  Proof.
    intros.
    rewrite <- H0; trivial.
  Qed.

  Lemma HB_var_comp : forall M, isVar M -> CompHB M.

  Proof.
    intros M Mvar; unfold CompHB.
    apply var_comp; eauto with horpo_beta.
  Qed.

  Lemma HB_comp_abs : forall M (Mabs: isAbs M), algebraic M ->
    (forall G (cs: correct_subst (absBody Mabs) G) T, isSingletonSubst T G -> CompHB T ->
      CompHB (subst cs)) -> CompHB M.

  Proof.
    intros M Mnorm Mabs H; unfold CompHB.
    eapply comp_abs; eauto with horpo_beta.
  Qed.

  Lemma HB_comp_lift : forall N, CompHB N -> CompHB (lift N 1).

  Proof.
    intros.
    setoid_replace (lift N 1) with N; trivial.
    apply terms_conv_sym; apply terms_lift_conv.
  Qed.

  Lemma HB_comp_app : forall M (Mapp: isApp M), CompHB (appBodyL Mapp) -> CompHB (appBodyR Mapp) ->
    CompHB M.

  Proof.
    intros M Mapp Ml Mr; unfold CompHB.
    apply comp_app with Mapp; trivial.
  Qed.

  Lemma HB_comp_algebraic : forall M, CompHB M -> algebraic M.

  Proof.
    intros.
    apply comp_algebraic with HB; trivial.
  Qed.

  Lemma HB_comp_units_comp : forall M, (forall N, isAppUnit N M -> CompHB N) -> CompHB M.

  Proof.
    intros M Munits; unfold CompHB.
    apply comp_units_comp; trivial. 
  Qed.

End HorpoBetaComp.
