(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

This file is the development of the proof of well-foundedness of the
higher-order recursive path ordering due to Jouannaud and Rubio.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras Horpo Computability PairLex
  HorpoComp LogicUtil.
From CoLoR Require SN.

Module HorpoWf (S : TermsSig.Signature) 
               (Prec : Horpo.Precedence with Module S := S).

  Module Export HC := HorpoComp.HorpoComp S Prec.

  Lemma acc_mul_acc_wfmul_aux : forall (M: Multiset), 
    Acc horpo_mul_lt M ->
    forall (WM: WFterms), M = WM -> Acc H_WFterms_lt WM.

  Proof.
    intros M AccM.
    apply Acc_ind with
      (R := MultisetLT horpo)
      (P := fun M => forall (WM: WFterms), 
                       M = WFterms_to_mul WM -> Acc H_WFterms_lt WM).
    intros x acc_mul acc_WM WM x_WM.
    constructor.
    intros y y_lt_WM.
    apply acc_WM with (WFterms_to_mul y).
    rewrite x_WM.
    trivial.
    trivial.
    trivial.
  Qed.

  Lemma acc_mul_acc_wfterms : forall (WM: WFterms), 
    Acc horpo_mul_lt WM -> Acc H_WFterms_lt WM.

  Proof.
    intros WM acc_WM.
    apply acc_mul_acc_wfmul_aux with (WFterms_to_mul WM); trivial.
  Qed.

  Lemma wf_MulLt_WFterms : well_founded H_WFterms_lt.

  Proof.
    unfold well_founded; intro W.
    destruct W as [Ts CompTs].
    apply acc_mul_acc_wfterms.
    unfold horpo_mul_lt; apply mOrd_acc.
    class.
    intros x x_comp.
    assert (xComp: CompH x).
    apply CompTs.
    destruct (member_multiset_list Ts x_comp).
    unfold eqA in H0; unfold TermsEqset.eqA in H0; rewrite H0; trivial.
    apply horpo_comp_imp_acc; trivial.
  Qed.

  Module H_WFmul_ord <: Ord.

    Module SetWF <: SetA.
      Definition A := WFterms.
    End SetWF.
    Module S := Eqset_def SetWF.
    Definition A := WFterms.
    Definition gtA := transp H_WFterms_lt.
    Definition gtA_eqA_compat := Eqset_def_gtA_eqA_compat gtA.

  End H_WFmul_ord.

  Module Lex := PairLex.LexicographicOrder Prec.P.O H_WFmul_ord.
  Import Lex.

  Lemma compTerms : forall M N Ns, M [>>] Ns -> CompTerms (appArgs M) ->
    (forall n, In n Ns -> subterm n N) -> 
    (forall N', subterm N' N -> M >> N' -> CompH N') ->
    CompTerms Ns.

  Proof.
    intros M N Ns M_red_Ns argsMcomp Ns_sub_N IH.
    induction M_red_Ns as 
      [ M 
      | M Th Tt M_red_Th M_red_Tt IHargs
      | M Th Tt Marg_red_Th M_red_Tt IHargs
      ]; unfold CompTerms.
     (*     case: list of arguments of N empty *)
    intros x in_x_nil; absurd (In x nil); auto.
     (*     case: head of arguments of N has the same type as M *)
     (*           and horpo holds between M and head of N *)
    intros x x_Th_Tt; case x_Th_Tt; intro xT.
    rewrite <- xT.
    apply IH.
    apply Ns_sub_N; auto with datatypes.
    trivial.
    fold (In x Tt) in xT; apply IHargs; auto with datatypes.
     (*     case: head of arguments of N has different type than M *)
     (*           and horpo holds between some argument of M and   *)
     (*           head of N *)
    intros x x_Th_Tt; case x_Th_Tt; intro xT.
    rewrite <- xT.
    destruct Marg_red_Th as [M' M'arg M'_red_Th].
    destruct M'_red_Th as [M' Th M_red_Th | M'].
    unfold CompH; apply horpo_comp_step_comp with M'.
    apply argsMcomp; trivial.
    trivial.
    apply argsMcomp; trivial.
    fold (In x Tt) in xT; apply IHargs; auto with datatypes.
  Qed.

  Lemma arg_mul_arg : forall m M, m in (list2multiset (appArgs M)) -> isArg m M.

  Proof.
    intros m M m_in_M.
    destruct (member_multiset_list (appArgs M) m_in_M) as 
      [m' m'_in_M m_m'].
    unfold eqA in m_m'; unfold TermsEqset.eqA in m_m'; rewrite m_m'; trivial.
  Qed.

  Lemma argsComp_appComp_aux :
    forall Px: pair,
      (forall Py: pair, Py <lex Px ->
	forall M, algebraic M -> term (appHead M) = ^fst Py -> 
          appArgs M = proj1_sig (snd Py) -> CompH M) ->
    forall M N,
      algebraic M -> term (appHead M) = ^fst Px -> appArgs M = proj1_sig (snd Px) ->
      (forall N', subterm N' N -> M >> N' -> CompH N') ->
      M >> N -> CompH N.

  Proof.
    intros Px IH_out M N Mnorm Mhead Margs IH_in MN.
    destruct Px as [f fArgs]; simpl in * .
     (* 1) order by horpo *)
    destruct MN as [M N eqTypeMN eqEnvMN _ Nnorm horpoMN].
    destruct horpoMN as 
      [ M N _ Msub 
      | M N f' g Mhead' Nhead f'_gt_g Margs_gt_N
      | M N f' Mhead' Nhead argsM_mul_argsN
      | M N Ns Napp Ns_flat_N Margs_Ns
      | M N Mapp' Napp Mhead' Margs_mul_Nargs
      | M N Mabs Nabs _
      | M N MNbeta
      ].
     (* 1a) HSub *)
    destruct Msub as [M' M'arg M'_ge_N].
    assert (M'comp: CompH M').
    apply (proj2_sig fArgs); rewrite <- Margs; exact M'arg.
    destruct M'_ge_N as [M' N M'_N | M'].
    unfold CompH; apply horpo_comp_step_comp with M'; auto with horpo.
    trivial.
     (* 1b) HFun *)
     (*    all arguments of N computable *)
    assert (argsNcomp: CompTerms (appArgs N)).
    apply compTerms with M N; trivial.
    rewrite Margs; exact (proj2_sig fArgs).
    intros; apply appUnit_subterm; auto with terms.
    term_inv N.
    set (Nmul := exist argsNcomp).
     (*    so we can use outer induction hypothesis *)
    apply IH_out with (Py := (g, Nmul)); auto with terms.
    assert (ff': f = f'); [congruence | idtac].
    constructor 1; rewrite ff'; auto with terms.
     (* 1c) HMul *)
     (*    first show that all agrumens of N are computable *)
    inversion argsM_mul_argsN as [aM aN argsM_horpo_argsN aMdef aNdef].
    assert (argsNcomp: CompTerms (appArgs N)).
    unfold CompTerms; intros n n_arg_N.
    assert (n_in_N: n in (list2multiset (appArgs N))).
    apply member_list_multiset; trivial.
    destruct (mOrd_elts_ge argsM_horpo_argsN n_in_N) 
       as [m m_in_M [m_gt_n | m_eq_n]].
     (*    for every argument of N, say n, we have argument of M *)
     (*    which:                                                *)
     (*    -/ either in one step rewrites by horpo to n          *)
    apply horpo_comp_step_comp with m.
    apply (proj2_sig fArgs); rewrite <- Margs.
    apply arg_mul_arg; trivial.
    trivial.
     (*    -/ or is equal to n *)
    unfold eqA in m_eq_n; unfold TermsEqset.eqA in m_eq_n; rewrite <- m_eq_n.
    apply (proj2_sig fArgs); rewrite <- Margs.
    apply arg_mul_arg; trivial.
     (*   now we prove the goal by outer induction hypothesis *)
    set (Nmul := exist argsNcomp).
    assert (NfApp: isFunApp N).
    unfold isFunApp;  apply funS_is_funS with f'; trivial.
    apply IH_out with (Py := (f', Nmul)); auto with terms.
    constructor 2.
    assert (ff': f = f'); [congruence | rewrite ff'; auto with sets].
    unfold H_WFmul_ord.gtA, H_WFterms_lt, WFterms_to_mul, 
           horpo_mul_lt,  MultisetLT, transp.
    simpl; apply mOrd_inclusion with horpo.
    intros x y x_y; trivial.
    rewrite <- Margs; trivial.
     (* 1d) HAppFlat *)
    assert (Ns_comp: CompTerms Ns).
    apply compTerms with M N; trivial.
    rewrite Margs; exact (proj2_sig fArgs).
    intros; apply partialFlattening_subterm with Ns; trivial.
    unfold CompH; apply horpo_comp_pflat with Ns; trivial.
     (* 1e) HApp *)
    absurd (isFunApp M); eauto with terms.
     (* 1f) HAbs *) 
    rewrite appHead_notApp in Mhead; term_inv M.
     (* 1g) HBeta *)
     (*    M & N are applications *)
    assert (Napp: isApp N).
    apply app_beta_isapp with M f; trivial.
    assert (Mapp: isApp M).
    term_inv M.
    apply beta_notFunS with Tr N; unfold Tr; auto with terms.
     (*    we show that all arguments of N accessible *)
    assert (NargsComp: CompTerms (appArgs N)).
    unfold CompTerms; intros P P_arg_N.
    case (app_beta_args_eq P Mapp MNbeta Mhead P_arg_N).
     (*    -/ because they are either arguments of original M *)
    intro Parg.
    apply (proj2_sig fArgs P).
    rewrite <- Margs; exact Parg.
     (*    -/ or they are result of internal beta reduction on *)
     (*       one of arguments of M *)
    destruct 1 as [Mb Mb_P M_Mb].
    unfold CompH; apply horpo_comp_step_comp with Mb.
    apply (proj2_sig fArgs); rewrite <- Margs; trivial.
    apply beta_imp_horpo; trivial.
    apply algebraic_arg with M; trivial.
     (* Finally we show that N' Computable using induction hypothesis *)
    set (Nmul := exist NargsComp).
    fold CompH; 
      apply IH_out with (Py := (f, Nmul))(M := N); 
      auto with terms.
     (* Lexicographic order holds on second coordinate *)
    constructor 2.
    auto with sets.
    destruct (app_beta_args Mapp MNbeta Mhead) as 
      [[al ar] [[tl tr] [tlM [trN [tltr [Mb_args Nb_args]]]]]].
    unfold H_WFmul_ord.gtA, transp, H_WFterms_lt, horpo_mul_lt, 
      MultisetLT, transp, WFterms_to_mul; simpl in * .
    rewrite <- Margs, Mb_args, Nb_args.
    apply mulOrd_oneElemDiff.
    apply horpo_eq_compat'.
    refl.
    apply beta_imp_horpo; trivial. apply algebraic_arg with M; trivial.
    apply app_beta_headSymbol with M; trivial.
  Qed.

  Lemma argsComp_appComp_ind : forall (P: pair) M,
    algebraic M -> term (appHead M) = Fun (fst P) -> 
    appArgs M = proj1_sig (snd P) -> CompH M.

  Proof.
     (* induction on pair *)
    intro P.
    apply well_founded_ind with
      (R := LexProd_Lt)
      (P := fun (Px: pair) =>
         forall M,
	   algebraic M ->
           term (appHead M) = Fun (fst Px) ->
           appArgs M = proj1_sig (snd Px) ->
         CompH M).
    apply lexprod_wf.
    apply Prec.Ord_wf.
    apply wf_MulLt_WFterms.
    clear P.
    intros P IH_out M Mnorm Mhead Margs.
    assert (Mneutral: isNeutral M).
    term_inv M.
    rewrite_rl (horpo_neutral_comp_step Mnorm Mneutral).
    intros N; fold CompH.
    apply well_founded_ind with
      (R := subterm)
      (P := fun (N: Term) =>
         M >> N -> CompH N).
    apply subterm_wf.
    clear N.
    intros N IH_in M_red_N.
    apply argsComp_appComp_aux with P M; trivial.
  Qed.

  Lemma argsComp_appComp : forall M, algebraic M -> isFunS (appHead M) ->
    (forall P, isArg P M -> CompH P) -> CompH M.

  Proof.
    intros M Mnorm Mhead argsComp.
    set (Args := @exist _ (fun Ts: Terms => CompTerms Ts) _ argsComp).
    assert (Mf: exists f, term (appHead M) = ^f).
    set (MH := appHead M) in *.
    term_inv MH.
    exists f; trivial.
    destruct Mf as [f Mhead_f].
    apply argsComp_appComp_ind with (P := (f, Args))(M := M); trivial.
  Qed.

  Lemma subst_comp : forall M G (MG: correct_subst M G), 
    algebraic M -> CompSubst G -> algebraicSubstitution G -> 
    CompH (subst MG).

  Proof.
     (* induction on structure of Pt *)
    intro M.
    apply well_founded_ind with
      (R := subterm)
      (P := fun (M: Term) =>
         forall G (MG: correct_subst M G),
	   algebraic M ->
           CompSubst G ->
	   (forall i T, G |-> i/T -> algebraic T) ->
           CompH (subst MG)).
    apply subterm_wf.
    clear M; intros M IH G MG Mnorm Gcomp Gnorm.
    destruct M as [E Pt TM TypM]; simpl in * .
    destruct Pt as [?|?|A0 ?|??].
     (* variable *)
    assert (Mvar: isVar (buildT TypM)).
    dependent inversion TypM; simpl; trivial.
    destruct (var_subst MG) as [[T [p GpT MGterm]] | MG_M]; trivial.
     (*   - variable substituted *)
    apply horpo_comp_conv with T.
    apply Gcomp; trivial.
    apply nth_some_in with p; trivial.
    apply terms_conv_criterion; auto.
    apply env_comp_sym.
    apply subst_env_compat with p; trivial.
     (*   - variable not substituted *)
    apply horpo_var_comp; trivial.
    apply var_is_var with x; trivial.
     (* function symbol *)
    assert (termMG: term (subst MG) = term (buildT TypM)).
    apply funS_presubst.
    apply funS_is_funS with f; trivial.
    apply argsComp_appComp; term_inv (subst MG).
    apply funS_algebraic.
    simpl; inversion termMG.
    replace (f_type f) with (type (buildT TypM)).
    apply algebraic_funS; trivial.
    apply funS_is_funS with f; trivial.
    destruct TypM; try_solve.
    apply funS_is_funS with f; trivial.

     (* abstraction *)
    assert (Mabs: isAbs (buildT TypM)).
    apply abs_isAbs with A0 Pt; trivial.
    unfold CompH; apply horpo_comp_abs with (abs_subst_abs Mabs MG).
    apply algebraic_subst; trivial.
    intros S CS T TS Tcomp.
    destruct (abs_subst Mabs MG) as [MG_type MG_body].
    set (CS_Mbody := subst_abs_c Mabs MG).
    assert (CSj : correct_subst (absBody Mabs) 
             (Some T :: lift_subst G 1)).
    rewrite MG_body in CS.
    apply subst_disjoint_c with (subst_abs_c Mabs MG); trivial.
    apply singleton_correct_single with S; trivial.
    assert (CS_all: correct_subst (subst CS_Mbody) S).
    rewrite MG_body in CS; trivial.
    assert (S_Sj: subst CS = subst CSj).
    rewrite (subst_eq CS CS_all); trivial.
    set (CS_all' := singleton_correct_single CS_all TS).
    rewrite <- (singleton_subst CS_all' CS_all TS).
    apply subst_disjoint.
    rewrite S_Sj.
    apply IH.
    apply absBody_subterm.
    apply algebraic_absBody; trivial.
    intros Q Qin.
    case (in_inv Qin).
    intro Q_P.
    inversion Q_P; rewrite <- H0; trivial.
    intro Q_G.
    destruct (in_lift_subst Q G 1 Q_G) as [W W_G Q_lift_W].
    rewrite Q_lift_W.
    unfold CompH; apply horpo_comp_lift.
    apply Gcomp; trivial.
    intros i W SW.
    destruct i.
    inversion SW.
    rewrite <- H0; apply horpo_comp_algebraic; trivial.
    inversion SW.
    destruct (var_subst_lift_rev G 1 H0) as [W' [GW' WW']].
    rewrite WW'.
    apply algebraic_lift.
    apply (Gnorm i); trivial.

     (* application *)    
    set (M := buildT TypM) in * .
    assert (Mapp: isApp M).
    eapply app_isApp; simpl; trivial.
    destruct (app_subst Mapp MG) as [SL SR].
    destruct (isFunApp_dec M).

     (*   - function application *)
    apply argsComp_appComp.
    apply algebraic_subst; trivial.
    apply funS_head_subst; trivial.
    intros P Parg.
    destruct (list_In_nth (tail (appUnits (subst MG))) P Parg) as [p unit_p].
    assert (nth_error (appUnits (subst MG)) (S p) = Some P).
    destruct (appUnits (subst MG)); trivial.
    destruct p; try_solve.
    destruct (appUnits_subst_rev (S p) MG i H) as [P' [MP' PP']].
    rewrite PP'.
    assert (P'arg_aux: nth_error (tail (appUnits M)) p = Some P').
    inversion MP'.
    clear PP'; destruct (appUnits M); try_solve.
    assert (P'arg: isArg P' M).
    unfold isArg, appArgs.
    apply nth_some_in with p; trivial.
    apply IH; trivial.
    apply appUnit_subterm; trivial.
    apply appArg_is_appUnit; trivial.
    apply algebraic_arg with M; trivial.
    
     (*   - non-functional application *)
    unfold CompH; apply horpo_comp_app with (app_subst_app Mapp MG).
    rewrite SL.
    apply IH; trivial.
    apply appBodyL_subterm.
    apply algebraic_appBodyL; trivial.
    rewrite SR.
    apply IH; trivial.
    apply appBodyR_subterm.
    apply algebraic_appBodyR; trivial.
  Qed.

  Lemma horpo_beta_wf : forall M, algebraic M -> SN.SN horpo M.

  Proof.
    intros M Mnorm.
    apply SN.Acc_transp_SN.
    apply horpo_comp_imp_acc.
    assert (Mid_comp: CompH (subst (emptySubst_correct M))).
    apply subst_comp; trivial.
    red; contr.
    intros p T; destruct p; try_solve.
    rewrite <- (emptySubst_neutral (emptySubst_correct M)); trivial.
    apply emptySubst_empty.
  Qed.

End HorpoWf.
