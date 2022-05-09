(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

This file provides definition of computability due to Tait and Girard
and introduces, as Variable, some computability properties.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras PairLex Horpo LogicUtil AccUtil.
From Coq Require Import Setoid Morphisms Basics.

Module Computability (S : TermsSig.Signature) 
                     (Prec : Horpo.Precedence with Module S := S).

  Module Export H := Horpo.Horpo S Prec.

Section Computability_def.
  
  Variable R : relation Term.
  Notation "X <-R- Y" := (R Y X) (at level 50).
  Notation "X -R-> Y" := (R X Y) (at level 50).
  Let Rtrans := clos_trans R.
  Notation "X -R*-> Y" := (Rtrans X Y) (at level 50).

  Definition AccR := Acc (transp R).

  Fixpoint ComputableS (M: Term) (T: SimpleType) : Prop :=
    algebraic M /\
    type M = T /\
    match T with
    | #T => AccR M
    | TL --> TR => 
      forall P (Papp: isApp P) (PL: (appBodyL Papp) ~ M)
	(typeL: type P = TR) (typeR: type (appBodyR Papp) = TL),
	algebraic (appBodyR Papp) ->
	ComputableS (appBodyR Papp) TL ->
	ComputableS P TR
    end.

  Definition Computable M := ComputableS M (type M).
      
  Definition AllComputable Ts := forall T, In T Ts -> Computable T.

  Lemma CompBasic : forall M, isBaseType M.(type) -> algebraic M -> AccR M ->
    Computable M.

  Proof.
    intro M; term_type_inv M; split; trivial.
    split; trivial.
  Qed.

  Lemma CompArrow : forall M, algebraic M -> isArrowType (type M) ->
    (forall N (Napp: isApp N), (appBodyL Napp) ~ M ->
      algebraic (appBodyR Napp) ->
      Computable (appBodyR Napp) -> Computable N) ->
    Computable M.

  Proof.
    intros [E Pt [?|A1 A2] Typ];try_solve; intros.
    hnf; intros; split; trivial.
    split; trivial.
    intros; unfold Computable in H1.
    rewrite <- typeL.
    apply H1 with Papp; trivial.
    rewrite (@app_typeR P A1 A2 Papp); trivial.
    rewrite (terms_conv_eq_type PL); trivial.
  Qed.

  Lemma CompCase : forall M, Computable M ->
    { isBaseType M.(type) /\ AccR M /\ algebraic M } +
    { isArrowType M.(type) /\ algebraic M /\
      forall N (Napp: isApp N), algebraic (appBodyR Napp) ->
        Computable (appBodyR Napp) ->
	(appBodyL Napp) ~ M -> Computable N }.

  Proof.
    intro M. (*term_type_inv M.*)
    destruct M as [E Pt A0 Typ]. revert Typ. destruct A0; intro Typ; try_solve; 
      intro; unfold Computable in H; simpl in H; inversion H.
    inversion H1; left; do 2 split; trivial.
    right; do 2 split; trivial.
    intros N Napp Nnorm NR NL.
    unfold Computable.
    term_inv N.
    set (w := terms_conv_eq_type NL).
    inversion w.
    inversion H1.
    apply H5 with Napp; trivial.
    unfold Computable in NR.
    rewrite <- H3; trivial.
  Qed.

  Lemma CompCaseBasic : forall M, Computable M -> isBaseType M.(type) -> AccR M.

  Proof.
    intros M Mcomp Mbase.
    destruct (CompCase M Mcomp) as [[_ [Macc _]] | [Marr _]].
    trivial.
    destruct (type M); contr.
  Qed.

  Lemma CompCaseArrow : forall M, Computable M -> isArrowType M.(type) ->
    forall N (Napp: isApp N), algebraic (appBodyR Napp) ->
      Computable (appBodyR Napp) ->
      (appBodyL Napp) ~ M -> Computable N.

  Proof.
    intros M Mcomp Marr.
    destruct (CompCase M Mcomp) as [[Mbase _] | [_ [_ H]]].
    destruct (type M); contr.
    trivial.
  Qed.

  Lemma comp_algebraic : forall M, Computable M -> algebraic M.

  Proof.
    intros.
    unfold Computable in H; destruct (type M); simpl in H; destruct H; trivial.
  Qed.
    
Section Computability_theory.
  
  Variable R_type_preserving : forall M N, M -R-> N -> type M = type N.


  Variable R_env_preserving : forall M N, M -R-> N -> env M = env N.

  Variable R_var_consistent : forall M N, M -R-> N ->
    envSubset (activeEnv N) (activeEnv M).

  Variable R_algebraic_preserving : forall M N, algebraic M -> M -R-> N ->
    algebraic N.

  Variable R_var_normal : forall M N, isVar M -> ~M -R-> N.

  Variable R_conv_comp : forall M N M' N' Q, M ~(Q) M' -> N ~(Q) N' ->
    M -R-> N -> env M' = env N' -> M' -R-> N'.

  Variable R_app_reduct : forall M N (Mapp: isApp M),
      ~isFunApp M \/ isArrowType (type M) -> (* x-man, use algebraic *)
      M -R-> N ->
      (exists MLabs: isAbs (appBodyL Mapp),
	N = lower (subst (beta_subst M Mapp MLabs)) (beta_lowering M Mapp MLabs)
      )
      \/
      exists Napp: isApp N, 
	(appBodyL Mapp  =   appBodyL Napp /\ appBodyR Mapp -R-> appBodyR Napp) \/
	(appBodyL Mapp -R-> appBodyL Napp /\ appBodyR Mapp  =   appBodyR Napp) \/
	(appBodyL Mapp -R-> appBodyL Napp /\ appBodyR Mapp -R-> appBodyR Napp).

  Variable R_monotonous : algebraic_monotonicity R.

  Variable R_subst_stable : forall M N G (MS: correct_subst M G)
    (NS: correct_subst N G),
    algebraicSubstitution G -> M -R-> N -> subst MS -R-> subst NS.

  Variable R_abs_reduct : forall M (Mabs: isAbs M) N, M -R-> N ->
    exists Nabs: isAbs N, absBody Mabs -R-> absBody Nabs.

  #[local] Hint Resolve R_type_preserving R_env_preserving R_var_normal : comp.

  Lemma R_right_app_monotonous : forall M N M' N' (M'app: isApp M')
    (N'app: isApp N'),
    algebraic M -> M -R-> N -> appBodyL M'app = M -> appBodyL N'app = N ->
    appBodyR M'app = appBodyR N'app -> algebraic (appBodyR M'app) -> M' -R-> N'.

  Proof.
    intros.
    term_inv M'; term_inv N'.
    (* compat: variables are A0, A1 before coq 8.15 but A, A0 after *)
    try (rename A0 into A1; rename A into A0).
    assert (EE0: E = E0).
    replace E with (env M).
    replace E0 with (env N).
    apply R_env_preserving; trivial.
    rewrite <- H2; trivial.
    rewrite <- H1; trivial.
    set (Lpos := PAppL T2 (PThis (buildT T1))).
    assert (W: {P: PlaceHolder Lpos | proj1_sig2 P = M}).
    assert (env (buildT (TApp T1 T2) // Lpos) = env M).
    rewrite <- H1; trivial.
    assert (type (buildT (TApp T1 T2) // Lpos) = type M).
    rewrite <- H1; trivial.
    exists (exist2
      (fun T => env (buildT (TApp T1 T2) // Lpos) = env T) 
      (fun T => type (buildT (TApp T1 T2) // Lpos) = type T)
      M H5 H6
    ); trivial.
    assert (W': {P: PlaceHolder Lpos | proj1_sig2 P = N}).
    assert (env (buildT (TApp T1 T2) // Lpos) = env N).
    rewrite <- H2; trivial.
    assert (type (buildT (TApp T1 T2) // Lpos) = type N).
    simpl.
    replace (A0 --> B) with (type M).
    apply R_type_preserving; trivial.
    rewrite <- H1; trivial.
    exists (exist2
      (fun T => env (buildT (TApp T1 T2) // Lpos) = env T) 
      (fun T => type (buildT (TApp T1 T2) // Lpos) = type T)
      N H5 H6
    ); trivial.
    replace Tr with (swap (proj1_sig W)); destruct W; simpl in * .
    replace Tr0 with (swap (proj1_sig W')); destruct W'; simpl in * .
    apply R_monotonous; simpl; trivial.
    apply algebraic_app with I; trivial.
    simpl; rewrite H1; trivial.
    rewrite e; trivial.
    rewrite e0; trivial.
    apply R_algebraic_preserving with M; trivial.
    apply algebraic_arrowType; trivial.
    rewrite H1; trivial.
    rewrite e, e0; trivial.
    apply term_eq.
    rewrite swap_env_eq; trivial.
    rewrite swap_term_is; simpl; trivial.
    rewrite e0, <- H2; simpl.
    change PtR with (term (buildT T2)).
    rewrite H3; trivial.
    apply term_eq.
    rewrite swap_env_eq; trivial.
    rewrite swap_term_is; simpl; trivial.
    rewrite e, <- H1; trivial.
  Qed.

  Lemma R_conv_to : forall M N M', M -R-> N -> M ~ M' ->
    exists N', M' -R-> N' /\ N ~ N'.

  Proof.
    intros.
    destruct H0.
    destruct (envSub_min_ex H0) as [x' [MM' [x'min xx']]].    
    destruct (term_build_conv_sim N MM') as [N' [M'N' NN']]; trivial.
    apply R_env_preserving; trivial.
    apply R_var_consistent; trivial.
    exists N'; split.
    apply R_conv_comp with M N x'; trivial.
    exists x'; trivial.
  Qed.

  Lemma base_step_base : forall M N, isBaseType (type M) -> M -R-> N ->
    isBaseType (type N).

  Proof. intros M N Mbase MN. rewrite <- (R_type_preserving MN); trivial. Qed.

  Lemma base_comp_step_comp : forall M N, isBaseType (type M) ->
    Computable M -> M -R-> N -> Computable N.

  Proof.
    intros M N Mbase Mcomp MN.
    apply CompBasic.
    apply base_step_base with M; trivial.
    apply R_algebraic_preserving with M; trivial.
    apply comp_algebraic; trivial.
    unfold AccR; apply Acc_inv with M; auto.
    apply CompCaseBasic; trivial.
  Qed.

  Lemma acc_app_acc_L : forall M (Mapp: isApp M), algebraic (appBodyL Mapp) ->
    algebraic (appBodyR Mapp) -> AccR M -> AccR (appBodyL Mapp).

  Proof.
    intros; unfold AccR.
    apply Acc_mimic with M (fun M N => 
      exists Mapp: isApp M, 
	algebraic (appBodyL Mapp) /\
	algebraic (appBodyR Mapp) /\
	appBodyL Mapp = N); 
      try solve [trivial | exists Mapp; split; trivial].
    unfold transp; clear H H0 H1 M Mapp; intros M M' MM' N' M'N'.
    destruct MM' as [Mapp [MLnorm [MRnorm MM']]].

     (* term M = @(M', Mr) and M' -R-> N' *)
     (* build term N = @(N', Mr)          *)
    assert (envOk: env N' = env (appBodyR Mapp)).
    term_inv M.
    replace E with (env M').
    sym; auto with comp.
    rewrite <- MM'; auto.
    assert (typArrow: isArrowType (type N')).
    rewrite <- (R_type_preserving M'N'), <- MM'; term_inv M.
    assert (typCorrect: type_left (type N') = type (appBodyR Mapp)).
    rewrite <- (R_type_preserving M'N'), <- MM'; term_inv M.
    set (Ncond := Build_appCond N' (appBodyR Mapp) envOk typArrow typCorrect).
    set (N := buildApp Ncond).
    exists N.
    
     (* use monotonicity to show that: M -R-> N *)
    set (Napp := buildApp_isApp Ncond).
    apply R_right_app_monotonous with M' N' Mapp Napp; trivial.
    rewrite <- MM'; trivial.
    unfold N, Napp; rewrite buildApp_Lok; trivial.
    unfold N, Napp; rewrite buildApp_Rok; trivial.
    exists (buildApp_isApp Ncond); split.
    unfold N; rewrite buildApp_Lok; trivial.
    apply R_algebraic_preserving with M'; trivial.
    rewrite <- MM'; trivial.
    simpl; split.
    unfold N; rewrite buildApp_Rok; trivial.
    unfold N; rewrite buildApp_Lok; trivial.
    
    exists Mapp; split; trivial.
    split; trivial.
  Qed.

  Lemma comp_app : forall M (Mapp: isApp M), Computable (appBodyL Mapp) ->
    Computable (appBodyR Mapp) -> Computable M.

  Proof.
    intros M; term_inv M.
    intros TrApp T1c T2c.
    apply CompCaseArrow with (buildT T1) I; auto with terms_eq.
    apply comp_algebraic; trivial.
  Qed.

  Lemma AccR_morph_aux :
    forall x1 x2 : Term, x1 ~ x2 -> AccR x1 -> AccR x2.

  Proof.
    intros M M' M'M AccM'; unfold AccR.
    apply Acc_homo with (x := M) (R := transp R) (morphism := terms_conv);
      trivial.
    unfold transp; intros x y x' x'x xy.
    destruct (R_conv_to (M':=x') xy (terms_conv_sym x'x)) as [y' [x'y' yy']].
    exists y'; trivial.
    apply terms_conv_sym; trivial.
  Qed.

  #[global] Instance AccR_morph : Proper (terms_conv ==> iff) AccR.

  Proof.
    intros M M' M'M.
    split; apply AccR_morph_aux; auto using terms_conv_sym.
  Qed.

  Lemma Computable_morph_aux : forall x1 x2 : Term, x1 ~ x2 ->
    (Computable x1 -> Computable x2).

  Proof.
    intro M.
    term_type_inv M; intros M' MM' Mcomp.

     (* base type *)
    apply CompBasic.
    rewrite <- (terms_conv_eq_type MM'); try_solve.
    rewrite <- MM'; apply comp_algebraic; trivial.    
    rewrite <- MM'.
    apply CompCaseBasic; simpl; trivial.

     (* arrow type *)
    apply CompArrow.
    rewrite <- MM'; apply comp_algebraic; trivial.
    rewrite <- (terms_conv_eq_type MM'); try_solve.
    intros N Napp Nnorm NR NL.
    apply (CompCaseArrow Mcomp I N Napp NR NL).
    apply terms_conv_trans with M'; auto with terms_eq.
  Qed.

  #[global] Instance Computable_morph : Proper (terms_conv ==> iff) Computable.

  Proof.
    intros t t' teqt'; split; apply Computable_morph_aux;
      auto using terms_conv_sym.
  Qed.

  Lemma comp_lift_comp M n : Computable M -> Computable (lift M n).

  Proof. intro. rewrite <- (terms_lift_conv M n); trivial. Qed.

  Lemma apply_var_comp : forall M A B, Computable M -> type M = A --> B ->
    (forall P, type P = A -> algebraic P -> isNeutral P ->
      (forall S, P -R-> S -> Computable S) -> Computable P) ->
    exists Mx, exists Mx_app: isApp Mx,
      (appBodyL Mx_app) ~ M /\ term (appBodyR Mx_app) = %(length (env M)) /\
      env Mx = env M ++ Some A :: EmptyEnv /\ Computable Mx.

  Proof.
    intros M C D Mcomp MT IH.
    destruct (apply_variable M) as [Mx [Mx_app [MxL [MxR Mx_env]]]].
    rewrite MT; simpl; trivial.
    exists Mx; exists Mx_app; split; trivial.
    repeat split; trivial.
    rewrite MT in Mx_env; try_solve.
    apply comp_app with Mx_app.
    rewrite MxL; trivial.
    apply IH.
    apply app_typeR with D.
    rewrite <- terms_conv_eq_type with M (appBodyL Mx_app); trivial.
    term_inv Mx; destruct T2; try_solve.
    apply terms_conv_sym; trivial.
    apply algebraic_var; apply var_is_var with (length (env M)); trivial.
    apply var_neutral.
    eapply var_is_var; eauto.
    intros S RS.
    absurd (appBodyR Mx_app -R-> S); auto with comp.
    apply R_var_normal.
    apply var_is_var with (length (env M)); try_solve.
  Qed.

  Lemma comp_step_comp : forall M N, Computable M -> M -R-> N -> Computable N.

  Proof.
    assert (forall A M N, type M = A -> Computable M -> M -R-> N -> Computable N).    
    intro B.
    induction B.
     (* induction base *)
    intros M N MT Mcomp MN.
    apply base_comp_step_comp with M; trivial.
    rewrite MT; auto with terms.
     (* (induction case) 
        M: U --> V   M computable   M -R-> N
        To prove: N computable
        
        By def. N computable if (N S) computable for computable S: U
        (M S) computable by def. of computability
        (M S) -R-> (N S) by monotonicity
        Now (N S) computable by IH(ii) and we are done
     *)
    intros M N Marr Mcomp MN.
    apply CompArrow.
    apply R_algebraic_preserving with M; trivial.
    apply comp_algebraic; trivial.
    rewrite <- (R_type_preserving MN), Marr; simpl; trivial.
    intros N'S N'S_app N'S_L N'S_Rnorm N'S_R.
    set (N' := appBodyL N'S_app) in * .
    set (S := appBodyR N'S_app) in * .
    destruct (terms_conv_sym N'S_L) as [Q NQN'].
    destruct (envSub_min_ex NQN') as [Q' [NQ'N' [Q'minN _]]].
    destruct (term_build_conv_rel M (R_var_consistent MN) NQ'N') as 
      [Q'' [Q''Q' [M' [MM' M'env]]]]; trivial.
    assert (N'S_M'_env: envSubset (env N'S) (env M')).
    rewrite <- (appBodyL_env N'S N'S_app); trivial.
    assert (N''S't: env M' |- term N'S := type N'S).
    apply typing_ext_env with (env N'S); trivial.
    exact (typing N'S).
    set (N''S' := buildT N''S't).
    assert (NS_conv: N'S ~ N''S').
    apply terms_conv_criterion; trivial.
    simpl; apply env_subset_comp; trivial.
    set (N''S'_app := proj1 (isApp_morph NS_conv) N'S_app).
    set (SS' := app_conv_app_right N'S_app N''S'_app NS_conv); fold S in SS'.
    set (N'' := appBodyL N''S'_app) in * .
    set (S' := appBodyR N''S'_app) in * .
    set (typeMM' := terms_conv_eq_type (conv_by MM')).
    assert (M'S'_envOk: env M' = env S').
    unfold S'; rewrite appBodyR_env; trivial.
    assert (M'S'_Marr: isArrowType (type M')).
    rewrite <- typeMM', Marr; simpl; trivial.
    assert (M'S'_typeOk: type_left (type M') = type S').
    rewrite <- typeMM', (R_type_preserving MN), <- (terms_conv_eq_type N'S_L).
    set (w := app_conv_app_right N'S_app N''S'_app NS_conv).
    unfold S'; rewrite <- (terms_conv_eq_type w).
    term_inv N'S.
    set (M'S'_cond := Build_appCond M' S' M'S'_envOk M'S'_Marr M'S'_typeOk).
    set (M'S' := buildApp M'S'_cond).
    set (M'S'_app := buildApp_isApp M'S'_cond).
    set (M'S'_L := buildApp_Lok M'S'_cond).
    set (M'S'_R := buildApp_Rok M'S'_cond).
    assert (M'N': M' -R-> N'').
    apply R_conv_comp with M N Q''; trivial.
    apply terms_conv_diff_env with N'; trivial.
    apply terms_conv_extend_subst with Q'; trivial.
    unfold N', N''; apply term_appBodyL_eq; trivial.
    unfold N', N''.
    apply equiv_term_activeEnv.
    apply term_appBodyL_eq; trivial.
    rewrite !appBodyL_env.
    apply env_comp_sym; apply env_subset_comp; trivial.
    unfold N''; rewrite appBodyL_env; trivial.
    rewrite NS_conv.
    apply IHB2 with M'S'; unfold M'S'.
    rewrite buildApp_type; simpl.
    rewrite <- typeMM', Marr; trivial.
    apply CompCaseArrow with M' (buildApp_isApp M'S'_cond); trivial.
    assert (MeqM' :  M ~ M') by (exists Q''; trivial).
    rewrite <- MeqM'; trivial.
    rewrite M'S'_R; simpl; trivial.
    rewrite <- (algebraic_morph SS'); trivial.
    rewrite M'S'_R; simpl; trivial.
    rewrite <- SS'; trivial.
    rewrite M'S'_L; apply terms_conv_refl.
    apply R_right_app_monotonous with M' N'' M'S'_app N''S'_app; trivial.
    rewrite <- (conv_by MM').
    apply comp_algebraic; trivial.
    unfold M'S'_app; rewrite M'S'_R.
    simpl; rewrite <- SS'; trivial.
    intros. apply H with (type M) M; trivial.
  Qed.

  Lemma comp_prop : forall A,
    ( (* (i) *)
    forall M, type M = A -> Computable M -> AccR M 
    ) /\
    ( (* (ii) *)
    forall P, type P = A -> algebraic P -> isNeutral P ->
      (forall S, P -R-> S -> Computable S) -> Computable P).

  Proof.
    intro B.
    induction B.
     (* induction base *)
    split.
    intros M MT Mcomp.
     (* (i) *)
    apply CompCaseBasic; trivial.
    rewrite MT; auto with terms.
     (* (ii) *)
    intros P Pbase Pnorm Pneutral PScomp.
    assert (P_base: isBaseType (type P)).
    rewrite Pbase; auto with terms.
    apply CompBasic; trivial.
    constructor.
    intros S RS.
    apply CompCaseBasic.
    apply PScomp; trivial.
    apply base_step_base with P; trivial.

     (* induction step *)
    destruct IHB1 as [IH_L1 IH_L2].
    destruct IHB2 as [IH_R1 IH_R2].
    split.

     (* (i)
       M: U -> V   M computable
       To prove: M accessible

       take variable x: U
       x is variable so by IH(iii) it is computable
       so by definition of computability (M x):V is computable
       by IH(i) (M x):U is strongly normalizable
       so M is strongly normalizable (app_acc)
     *)
    intros M Marr Mcomp.
    destruct (apply_var_comp M Mcomp Marr)
      as [Mx [Mx_app [MxL [_ [_ Mxcomp]]]]]; trivial.
    rewrite <- MxL.
    apply acc_app_acc_L; trivial.
    rewrite MxL; apply comp_algebraic; trivial.
    apply algebraic_appBodyR.
    apply comp_algebraic; trivial.
    apply IH_R1; trivial.
    apply app_typeL_type with B1 Mx_app; trivial.
    rewrite <- terms_conv_eq_type with M (appBodyL Mx_app); trivial.
    apply terms_conv_sym; trivial.

     (* (ii)
        P: U -> V,  P neutral,  forall S, P -R-> S, S computable
        To prove: P computable

        by definition P computable if for every computable S, @(P S) computable
        By (i) S is accessible so do induction on S.
        We have three possibilities by R_app_reduct:
        @(P, S) -R-> @(P', S) but P' computable
          since every reduct of P is computable
        @(P, S) -R-> @(P, S') S' computable by (ii) and use IH
        @(P, S) -R-> @(P', S') combination of two above cases
        In any way we conclude that every reduct of @(P, S) is computable
        and we are done
     *)
    intros P Parr Palg Pneutral PScomp.
    apply CompArrow; trivial.
    rewrite Parr; simpl; trivial.
    intros N Napp NL NRnorm NR. 
     (* inductive argument *)
    assert (Hyp: 
      forall W,
	Computable W ->
	type W = B1 ->
	forall N (Napp: isApp N),
	  (appBodyL Napp) ~ P ->
	  appBodyR Napp = W ->
	  Computable N
    ).
    intros W Wcomp Wtyp.
    assert (Wacc: Acc (transp R) W).
    apply IH_L1; trivial.
    cut (type W = B1); trivial.
    cut (Computable W); trivial.
    cut (algebraic P); trivial.
    apply Acc_rect with (R := transp R)(P :=
      fun W =>
	algebraic P ->
	Computable W ->
	type W = B1 ->
	forall N (Napp: isApp N),
	  (appBodyL Napp) ~ P ->
	  appBodyR Napp = W ->
	  Computable N
    ); trivial.
    clear N NRnorm Napp NL NR W Wcomp Wtyp Wacc.
    intros W _ IH Pnorm Wcomp Wtype N Napp NL NR.
    apply IH_R2; trivial.
    apply app_typeL_type with B1 Napp; trivial.
    rewrite (terms_conv_eq_type NL); trivial.
    apply algebraic_app with Napp.
    rewrite NL; trivial.
    rewrite NR; apply comp_algebraic; trivial.    
    apply app_neutral; trivial.
    intros S NS.
    destruct (R_app_reduct (N:=S) Napp) as 
      [NLabs_red | [Sapp [[Leq Rgt] | [[Lgt Req] | [Lgt Rgt]]]]]; trivial.
    left.
    apply algebraic_app_notFunApp with Napp.
    rewrite NL; trivial.
    rewrite NR; apply comp_algebraic; trivial.
    destruct NLabs_red.
    absurd (isAbs P); trivial.
    rewrite <- NL; trivial.

     (* @(M, N) -> @(M, N') *)
    apply IH with (appBodyR Sapp) Sapp; trivial.
    unfold transp; simpl.
    rewrite <- NR; trivial.
    apply comp_step_comp with (appBodyR Napp); trivial.
    rewrite NR; trivial.
    rewrite <- (R_type_preserving Rgt), NR; trivial.
    rewrite <- Leq; trivial.

     (* @(M, N) -> @(M', N) *)
    apply comp_app with Sapp.
    destruct (R_conv_to (M':=P) Lgt NL) as [S' [PS' SLS']].
    rewrite SLS'.
    apply PScomp; trivial.
    rewrite <- Req, NR; trivial.

     (* @(M, N) -> @(M', N') *)
    apply comp_app with Sapp.
    destruct (R_conv_to (M':=P) Lgt NL) as [S' [PS' SLS']].
    rewrite SLS'.
    apply PScomp; trivial.
    apply comp_step_comp with W; trivial.
    rewrite <- NR; trivial.

     (* application of above result *)
    apply Hyp with (appBodyR Napp) Napp; trivial.
    apply app_typeR with B2.
    rewrite (terms_conv_eq_type NL); trivial.
  Qed.

  Lemma comp_imp_acc : forall M, Computable M -> AccR M.

  Proof.
    intros M MC.
    destruct (comp_prop (type M)) as [P1 P2].
    apply P1; trivial.
  Qed.

  Lemma comp_manysteps_comp : forall M N, Computable M -> M -R*-> N ->
    Computable N.

  Proof.
    intros M N Mcomp M_rew_N.
    induction M_rew_N.
    apply comp_step_comp with x; trivial.
    auto.
  Qed.

  Lemma neutral_comp_step : forall M, algebraic M -> isNeutral M ->
    (Computable M <-> (forall N, M -R-> N -> Computable N)).

  Proof.
    intros M Mneutral.
    destruct (comp_prop (type M)) as [P1 P2].
    split.
     (* => *)
    intros Mcomp N MN.
    apply comp_step_comp with M; trivial.
     (* <= *)
    intros MNcomp.
    apply P2; trivial.
  Qed.

  Lemma var_comp : forall M, isVar M -> Computable M.

  Proof.
    intros M Mvar.
    assert (Mneutral: isNeutral M).
    term_inv M.
    apply (proj2 (neutral_comp_step (algebraic_var M Mvar) Mneutral)).
    intros N MN.
    absurd (M -R-> N); trivial.
    apply R_var_normal; trivial.
  Qed.

  Lemma comp_units_comp : forall M, (forall N, isAppUnit N M -> Computable N) ->
    Computable M.

  Proof.
    destruct M as [E Pt T TypM]; induction TypM; intro compUnits;
      try solve [apply compUnits; compute; auto].
    apply comp_app with I; simpl.
    apply IHTypM1.
    intros N NunitL; apply compUnits.
    apply appUnit_left with I; trivial.
    apply compUnits.
    red.
    rewrite (appUnits_app (buildT (TApp TypM1 TypM2)) I).
    auto with datatypes.
  Qed.

  Lemma comp_pflat : forall N Ns, isPartialFlattening Ns N ->
    AllComputable Ns -> Computable N.

  Proof.
    intro N.
    case (isApp_dec N).
     (* N is application *)
    destruct N as [E Pt T TypN]; induction TypN; try contr.
    intros Napp Ns Ns_pflat Ns_comp.
    unfold isPartialFlattening in Ns_pflat.
    repeat (destruct Ns; [contr | idtac]).
    rewrite (appUnits_app (buildT (TApp TypN1 TypN2)) I) in Ns_pflat.
    simpl in Ns_pflat.
    destruct Ns.
     (*   - partial flatteing of the form @(@(...), _) *)
    destruct (app_inj_tail (appUnits t) (appUnits (buildT TypN1)) 
      t0 (buildT TypN2)) as [t_L t0_R]; trivial.
    apply comp_app with I; simpl.
    rewrite <- (eq_units_eq_terms t (buildT TypN1) t_L).
    apply Ns_comp; auto with datatypes.
    rewrite <- t0_R.
    apply Ns_comp; auto with datatypes.
     (*   - 'longer' partial flattening, @(@(...), _, ..., _) *)
    destruct (@list_drop_last Term ((appUnits t) ++ t0::nil) 
      (t1::Ns) (appUnits (buildT TypN1)) (buildT TypN2)) as [x xIn leq].
    rewrite list_app_first_last; trivial.
    auto with datatypes.
    apply comp_app with I; simpl.
    set (pf := t::t0::x).
    case (isApp_dec (buildT TypN1)).
    intro N1app; apply IHTypN1 with pf; trivial.
    unfold isPartialFlattening; simpl.
    rewrite <- list_app_first_last; trivial.
    unfold pf; intros p pIn.
    apply Ns_comp.
    assert (inc: incl (t::t0::x) (t::t0::t1::Ns)).
    repeat (apply incl_cons; auto with datatypes).
    apply inc; trivial.
    intro N1napp.
    rewrite (appUnits_notApp (buildT TypN1)) in Ns_pflat; trivial.
    simpl in Ns_pflat.
    assert (N1_in: In (buildT TypN1) (t0::x)).
    rewrite (appUnits_notApp (buildT TypN1)) in leq; trivial.
    apply list_app_last with (appUnits t) (nil (A:=Term)).
    rewrite <- list_app_first_last; trivial.
    auto with datatypes.
    apply Ns_comp.
    destruct (in_inv N1_in).
    rewrite H; auto with datatypes.
    auto with datatypes.
    assert (N2_in: In (buildT TypN2) (t1::Ns)).
    apply list_app_last with 
      (appUnits t ++ t0::nil) (appUnits (buildT TypN1)).
    rewrite list_app_first_last; trivial.
    auto with datatypes.
    apply Ns_comp; auto with datatypes.
     (* N is not an application *)
    intros N_nApp Ns Ns_pflat Ns_comp.
    absurd (isApp N); trivial.
    apply partialFlattening_app with Ns; trivial.
  Qed.

  Definition CompTerm := { T: Term | Computable T }.
  Definition R_Comp (T1 T2: CompTerm) := proj1_sig T1 -R-> proj1_sig T2.
  Definition CompTerm_eq (T1 T2: CompTerm) := proj1_sig T1 = proj1_sig T2.
  Definition TermsPairLex := LexProd_Lt CompTerm_eq R_Comp R_Comp.

  #[global] Instance R_Comp_morph : Proper (CompTerm_eq ==> CompTerm_eq ==> impl) R_Comp.

  Proof.
    intros [a ac] [b bc] ab [c cc] [d dc] cd;
    unfold R_Comp, CompTerm_eq in *; simpl in *; intro h; subst. hyp.
  Qed.

  Definition SetTheory_Comp : Setoid_Theory CompTerm CompTerm_eq.

  Proof.
    constructor; unfold Reflexive, Symmetric, Transitive.
    constructor.
    intros; inversion H.
    unfold CompTerm_eq; auto.
    intros; inversion H; inversion H0.
    unfold CompTerm_eq; trans (proj1_sig y); trivial.
  Defined.

  Lemma well_founded_R_comp : well_founded (transp R_Comp).

  Proof.
    set (w := Acc_ind (R := transp R) (fun M =>
      forall T,
	proj1_sig T = M ->
	Acc (transp R_Comp) T
    )).
    intro T.
    apply w with (proj1_sig T); trivial.
    intros; constructor; intros.
    eapply H0 with (proj1_sig y); trivial.
    unfold R_Comp, transp in * .
    rewrite <- H1; trivial.
    apply comp_imp_acc.
    destruct T; trivial.
  Qed.

  Lemma comp_abs_ind : forall (P: CompTerm * CompTerm)
    W (Wapp: isApp W) (WLabs: isAbs (appBodyL Wapp)),
    (forall G (cs: correct_subst (absBody WLabs) G) T, isSingletonSubst T G -> 
      Computable T -> Computable (subst cs)) ->
    algebraic W -> absBody WLabs = proj1_sig (fst P) ->
    appBodyR Wapp = proj1_sig (snd P) -> Computable W.

  Proof.
    intro P.
    apply well_founded_ind with (R := TermsPairLex) (P :=
      fun (P: CompTerm * CompTerm) =>
	forall W (Wapp: isApp W) (WLabs: isAbs (appBodyL Wapp)),
	  (forall G (cs: correct_subst (absBody WLabs) G) T,
	    isSingletonSubst T G ->
	    Computable T -> 
	    Computable (subst cs)
	  ) ->
	  algebraic W ->
	  absBody WLabs = proj1_sig (fst P) ->
	  appBodyR Wapp = proj1_sig (snd P) ->
	  Computable W
    ).
    unfold TermsPairLex.
    eapply lexprod_wf; try solve
      [ eexact SetTheory_Comp
      | unfold R_Comp; intros x x' y y' xx' yy' xy; 
	  inversion xx'; inversion yy'; trivial
      | apply well_founded_R_comp
      ]; try apply R_Comp_morph.
    clear P; intros P IH W Wapp WLabs WL_Hyp Wnorm PL PR.
    assert (WLnorm: algebraic (appBodyL Wapp)).
    apply algebraic_appBodyL; trivial.
    unfold isFunApp; intro WFapp.
    rewrite (appHead_app W Wapp), (appHead_notApp (appBodyL Wapp)
      (abs_isnot_app (appBodyL Wapp) WLabs)) in WFapp.
    term_inv (appBodyL Wapp).
    assert (WRnorm: algebraic (appBodyR Wapp)).
    apply algebraic_appBodyR; trivial.
    rewrite_rl (neutral_comp_step Wnorm (app_neutral W Wapp)).
    intros W' WW'.
    destruct P as [[PLT PLC] [PRT PRC]]; simpl in * .
    destruct (R_app_reduct (N:=W') Wapp) as [[W'abs W'beta] | 
      [W'app [[W'L_eq W'R_red] | [[W'L_red W'R_eq] | [W'L_red W'R_red]]]]];
    trivial.
    left; apply funAbs_notFunApp.
    rewrite (appHead_app W Wapp), appHead_notApp; trivial.
    term_inv (appBodyL Wapp).

     (* beta-reduction step *)
    rewrite W'beta, <- (Computable_morph (terms_lower_conv
      (subst (beta_subst W Wapp W'abs)) (beta_lowering W Wapp W'abs))),
      (abs_proof_irr (appBodyL Wapp) W'abs WLabs).
    apply WL_Hyp with (lift (appBodyR Wapp) 1).
    apply singletonSubst_cond.
    apply comp_lift_comp.
    rewrite PR; trivial.
 
     (* reduction in right argument *)
    assert (W'Labs: isAbs (appBodyL W'app)).
    rewrite <- W'L_eq; trivial.
    set (WL_W'L := absBody_eq WLabs W'Labs W'L_eq).
    assert (W'Lcomp: Computable (absBody W'Labs)).
    rewrite <- WL_W'L, PL; trivial.
    assert (W'Rcomp: Computable (appBodyR W'app)).
    apply comp_step_comp with (appBodyR Wapp); trivial.
    rewrite PR; trivial.
    set (P'L := exist W'Lcomp).
    set (P'R := exist W'Rcomp).
    apply (IH (P'L, P'R)) with W'app W'Labs; trivial.
    constructor 2.
    unfold CompTerm_eq; simpl.
    rewrite <- PL; trivial.
    unfold R_Comp; simpl; rewrite <- PR; trivial.
    intros G cs T GT Tcomp.
    assert (cs': correct_subst (absBody WLabs) G).
    destruct cs; constructor; try solve
      [ trivial
      | rewrite (absBody_eq WLabs W'Labs); trivial
      ].
    replace (subst cs) with (subst cs').
    apply WL_Hyp with T; trivial.
    apply term_eq.
    rewrite !subst_env, (absBody_eq WLabs W'Labs); trivial.
    rewrite !subst_term, (absBody_eq WLabs W'Labs); trivial.
    apply algebraic_app with W'app.
    rewrite <- W'L_eq; trivial.
    apply R_algebraic_preserving with (appBodyR Wapp); trivial.
    
     (* reduction in left argument *)
    destruct (R_abs_reduct WLabs W'L_red) as [W'Labs W'Lbody_red].
    assert (W'Lcomp: Computable (absBody W'Labs)).
    apply comp_step_comp with (absBody WLabs); trivial.
    rewrite PL; trivial.
    assert (W'Rcomp: Computable (appBodyR W'app)).
    rewrite <- W'R_eq, PR; trivial.
    set (P'L := exist W'Lcomp).
    set (P'R := exist W'Rcomp).
    apply (IH (P'L, P'R)) with W'app W'Labs; trivial.
    constructor 1.
    unfold R_Comp; simpl; rewrite <- PL; trivial.
    intros G cs T TG Tcomp.
    assert (CS: correct_subst (absBody WLabs) G).
    destruct cs; constructor; trivial.
    rewrite (R_env_preserving W'Lbody_red); trivial.
    rewrite (R_env_preserving W'Lbody_red); trivial.
    apply comp_step_comp with (subst CS).
    apply WL_Hyp with T; trivial.
    apply R_subst_stable; trivial.
    apply singletonSubst_algebraic with T; trivial.
    apply comp_algebraic; trivial.
    apply algebraic_app with W'app.
    apply R_algebraic_preserving with (appBodyL Wapp); trivial.
    rewrite <- W'R_eq; trivial.

     (* reduction in both arguments *)
    destruct (R_abs_reduct WLabs W'L_red) as [W'Labs W'Lbody_red].
    assert (W'Lcomp: Computable (absBody W'Labs)).
    apply comp_step_comp with (absBody WLabs); trivial.
    rewrite PL; trivial.
    assert (W'Rcomp: Computable (appBodyR W'app)).
    apply comp_step_comp with (appBodyR Wapp); trivial.
    rewrite PR; trivial.
    set (P'L := exist W'Lcomp).
    set (P'R := exist W'Rcomp).
    apply (IH (P'L, P'R)) with W'app W'Labs; trivial.
    constructor 1.
    unfold R_Comp; simpl; rewrite <- PL; trivial.
    intros G cs T GT Tcomp.
    assert (CS: correct_subst (absBody WLabs) G).
    destruct cs; constructor; trivial.
    rewrite (R_env_preserving W'Lbody_red); trivial.
    rewrite (R_env_preserving W'Lbody_red); trivial.
    apply comp_step_comp with (subst CS).
    apply WL_Hyp with T; trivial.
    apply R_subst_stable; trivial.
    apply singletonSubst_algebraic with T; trivial.
    apply comp_algebraic; trivial.
    apply algebraic_app with W'app.
    apply R_algebraic_preserving with (appBodyL Wapp); trivial.
    apply R_algebraic_preserving with (appBodyR Wapp); trivial.
  Qed.

   (*   Take \x.M such that for every computable T, M[x/T] is computable; 
      then \x.M is computable.

        \x.M is of arrow type.
        By def. of comp. it remains to show @(\x.M, S) comp. for comp. S
        M is comp. because M = M[x/x] and x is comp. as it is variable
        M and S are comp. so they are accessible
        Proceed by induction on pair (M, S) ordered lexicographically
          ...
   *)
  Lemma comp_abs : forall M (Mabs: isAbs M), algebraic M ->
    (forall G (cs: correct_subst (absBody Mabs) G) T, isSingletonSubst T G ->
      Computable T -> Computable (subst cs)) -> Computable M.

  Proof.
    intros M Mabs Mnorm H.
    apply CompArrow; trivial.
    term_inv M.
    intros W Wapp WL WRnorm WR.
    assert (WLabs: isAbs (appBodyL Wapp)).
    rewrite WL; trivial.
    set (TL := absBody WLabs).
    set (TR := appBodyR Wapp).
    assert (M0: env (absBody Mabs) |= 0 := absType Mabs).
    term_inv M.
    assert (TLC: Computable (absBody WLabs)).
    set (idS1 := idSubst_correct (absBody Mabs)).
    simpl; setoid_replace (absBody WLabs) with (subst (idS1))
      using relation terms_conv.
    set (S1eqS2 := idSubst_decl0 (absBody Mabs) M0).
    assert (idS2 : correct_subst (absBody Mabs) {x/buildT (TVar M0)}).
    rewrite <- S1eqS2; trivial.
    replace (subst idS1) with (subst (idS2)).
    apply H with (buildT (TVar M0)).
    apply singletonSubst_cond.
    apply var_comp; simpl; trivial.
    apply term_eq.
    rewrite !subst_env, S1eqS2; trivial.
    rewrite !subst_term, S1eqS2; trivial.
    unfold idS1; rewrite (idSubst_neutral (absBody (M:=M) Mabs)).
    apply abs_conv_absBody; trivial.
    set (PL := exist TLC).
    set (PR := exist WR).
    apply comp_abs_ind with (Wapp := Wapp) (WLabs := WLabs) (P := (PL, PR));
      trivial.
    intros.
    destruct WL. 
    set (WLM := abs_conv_absBody_aux WLabs Mabs H2).
    destruct (isVarDecl_dec (activeEnv (absBody WLabs)) 0) as [[B DB] | ND].    
    destruct (envSub_min_ex WLM) as [Q [Qconv [Qmin Qext]]].
    assert (Q00: envSub Q 0 0).
    destruct (terms_conv_activeEnv Qconv DB).
    assert (x0 = 0).
    apply envSub_Lok with (envSubst_lift1 x) 0.
    apply (Qext 0 x0); trivial.
    destruct x; simpl; trivial.
    rewrite H4 in H3; trivial.
    destruct (conv_subst_singleton_build Q00 Qconv Qmin H0 cs) as 
      [Q' [G' [T' [MG' [T'G' [Q'Q GG']]]]]].
    set (Conv :=
      conv_subst_conv cs MG' (terms_conv_extend_subst Qconv Q'Q) GG').
    assert (Conv' : terms_conv (subst cs) (subst MG')) by (exists Q'; trivial).
    rewrite Conv'.
    apply H with T'; trivial.
    setoid_replace T' with T using relation terms_conv; trivial.
    apply terms_conv_sym; exists Q'; trivial.
    apply singletonSubst_conv with G G'; trivial.
    rewrite <- (uneffective_singleton_subst_conv cs H0 ND); trivial.
    apply algebraic_app with Wapp; trivial.
    rewrite WL; trivial.
  Qed.

End Computability_theory.

End Computability_def.

End Computability.
