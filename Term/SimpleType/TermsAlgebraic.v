(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Algebraic terms (functions with arity; simple output type of a function
assumed) encoded via lambda-terms.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras TermsEta LogicUtil.
From Coq Require Import Morphisms.

Module TermsAlgebraic (Sig : TermsSig.Signature).

  Module Export TE := TermsEta.TermsEta Sig.

  Inductive algebraic: Term -> Prop :=
  | AlgVar: forall M,
       isVar M ->
       algebraic M
  | AlgAbs: forall M (Mabs: isAbs M),
       algebraic (absBody Mabs) ->
       algebraic M
  | AlgApp: forall M,
       isApp M ->
       ~isFunApp M ->
       (forall M', isAppUnit M' M -> algebraic M') ->
       algebraic M
  | AlgFunApp: forall M,
       isFunApp M ->
       isBaseType (type M) ->
       (forall M', isArg M' M -> algebraic M') ->       
       algebraic M.

  Lemma algebraic_morph_aux :
    forall x1 x2 : Term, x1 ~ x2 -> (algebraic x1 -> algebraic x2).

  Proof.
    intro t.
    apply well_founded_ind with (R := subterm) (P := fun t =>
      forall s, t ~ s -> algebraic t -> algebraic s).
    apply subterm_wf.
    clear t; intros t IH s ts t_alg.
    inversion t_alg.
    apply AlgVar.
    rewrite <- ts; trivial.
    set (s_abs := proj1 (isAbs_morph ts) Mabs).
    apply AlgAbs with s_abs; trivial.
    apply IH with (absBody Mabs); trivial.
    apply absBody_subterm.
    apply abs_conv_absBody; trivial.
    apply AlgApp.
    rewrite <- ts; trivial.
    rewrite <- ts; trivial.
    intros.
    destruct (terms_conv_sym ts) as [Q st].
    destruct (appUnit_conv_appUnit M' st) as [N' [N't M'N']]; trivial.
    apply IH with N'.
    apply appUnit_subterm; trivial.
    apply terms_conv_sym; exists Q; trivial.
    apply H1; trivial.
    apply AlgFunApp.
    rewrite <- ts; trivial.
    rewrite <- (terms_conv_eq_type ts); trivial.
    intros.
    destruct (terms_conv_sym ts) as [Q st].
    destruct (appArg_conv_appArg M' st) as [N' [N't M'N']]; trivial.
    apply IH with N'.
    apply arg_subterm; trivial.
    apply terms_conv_sym; exists Q; trivial.
    apply H1; trivial.
  Qed.

  Global Instance algebraic_morph : Proper (terms_conv ==> iff) algebraic.

  Proof.
    intros a b ab. intuition.
    eapply algebraic_morph_aux. apply ab. hyp.
    eapply algebraic_morph_aux. apply (terms_conv_sym ab). hyp.
  Qed.

  Lemma algebraic_funApp_datatype :
    forall M, algebraic M -> isFunApp M -> isBaseType (type M).

  Proof. unfold isFunApp; intros. inversion H; term_inv M. Qed.

  Lemma algebraic_arrowType :
    forall M, algebraic M -> isArrowType (type M) -> ~isFunApp M.

  Proof.
    intros.
    assert (forall T, isBaseType T -> isArrowType T -> False).
    destruct T; try_solve.
    unfold isFunApp.
    inversion H; try_solve; fo; term_inv M.
  Qed.

  Lemma algebraic_absBody : forall M (Mabs: isAbs M),
      algebraic M -> algebraic (absBody Mabs).

  Proof. intros; inversion H; term_inv M. Qed.

  Lemma algebraic_arg : forall M Marg (Mapp: isApp M),
      algebraic M -> isArg Marg M -> algebraic Marg.

  Proof.
    intros; destruct (isApp_dec M); try_solve. inversion H; term_inv M.
  Qed.

  Lemma algebraic_appBodyL : forall M (Mapp: isApp M),
      ~isFunApp M -> algebraic M -> algebraic (appBodyL Mapp).

  Proof.
    intros M Mapp Mhead Malg.
    inversion Malg; term_inv M.
    destruct (isApp_dec (buildT T1)).
    apply AlgApp; trivial.
    unfold isFunApp in * .
    rewrite (appHead_app Tr I) in Mhead; trivial.
    intros.
    apply H1.
    apply appUnit_left with I; trivial.
    apply H1.    
    apply appUnit_left with I; simpl.
    unfold isAppUnit; rewrite appUnits_notApp; auto with datatypes.
  Qed.

  Lemma algebraic_appBodyR : forall M (Mapp: isApp M),
      algebraic M -> algebraic (appBodyR Mapp). 

  Proof.
    intros; inversion H; term_inv M.
    apply H2.
    apply appUnit_right with I; trivial.
    apply H2.
    apply appArg_right with I; trivial.
  Qed.

  Lemma algebraic_appUnits : forall M, algebraic M -> ~isFunApp M ->
    forall M', isAppUnit M' M -> algebraic M'.

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm) (P := fun M =>
      algebraic M ->
      ~isFunApp M ->
      forall M',
	isAppUnit M' M ->
	algebraic M').
    apply subterm_wf.
    clear M; intros M IH Malg Mnfa M' M'M.
    destruct (isApp_dec M) as [Mapp | Mnapp].
    destruct (appUnit_app M' M Mapp M'M).
    rewrite H.
    apply algebraic_appBodyR; trivial.
    apply IH with (appBodyL Mapp); trivial.
    apply appBodyL_subterm.
    apply algebraic_appBodyL; trivial.
    apply notFunApp_left_inv; trivial.
    unfold isAppUnit in M'M.
    rewrite (appUnits_notApp M Mnapp) in M'M.
    inversion M'M; try_solve.
  Qed.

  Lemma algebraic_app : forall M (Mapp: isApp M), algebraic (appBodyL Mapp) ->
    algebraic (appBodyR Mapp) -> algebraic M.

  Proof.
    intros M Mapp ML MR.
    destruct (isFunApp_dec M).
    assert (~isApp (appBodyL Mapp) -> isFunS (appBodyL Mapp)).
    intro Lnapp.
    unfold isFunApp in i.
    rewrite (appHead_app M Mapp) in i; simpl.
    rewrite (appHead_notApp (appBodyL Mapp)) in i; trivial.
    inversion ML; try solve [term_inv M | term_inv (appBodyL Mapp)].
    absurd (isFunApp (appBodyL Mapp)); trivial.
    unfold isFunApp in * .
    rewrite (appHead_app M Mapp) in i; trivial.
    apply AlgApp; trivial.
    intros.
    destruct (appUnit_app M' M Mapp H).
    rewrite H0; trivial.
    apply algebraic_appUnits with (appBodyL Mapp); trivial.
    apply  notFunApp_left_inv; trivial.
  Qed.

  Lemma algebraic_var : forall M (Mvar: isVar M), algebraic M.

  Proof. intros; apply AlgVar; trivial. Qed.

  Lemma algebraic_lift : forall M i, algebraic M -> algebraic (lift M i).

  Proof. intros. rewrite <- (terms_lift_conv M i); trivial. Qed.

  Lemma algebraic_lower : forall M Me, algebraic M -> algebraic (lower M Me).

  Proof. intros. rewrite <- (terms_lower_conv M Me); trivial. Qed.

  Lemma algebraic_app_notFunApp : forall M (Mapp: isApp M),
      algebraic (appBodyL Mapp) -> algebraic (appBodyR Mapp) -> ~isFunApp M.

  Proof.
    intros; intro i.
    assert (~isApp (appBodyL Mapp) -> isFunS (appBodyL Mapp)).
    intro Lnapp.
    unfold isFunApp in i.
    rewrite (appHead_app M Mapp) in i; simpl.
    rewrite (appHead_notApp (appBodyL Mapp)) in i; trivial.
    inversion H; try solve [term_inv M | term_inv (appBodyL Mapp)].
    absurd (isFunApp (appBodyL Mapp)); trivial.
    unfold isFunApp in * .
    rewrite (appHead_app M Mapp) in i; trivial.
  Qed.

  Lemma algebraic_funS M : algebraic M -> isFunS M -> isBaseType (type M).

  Proof. intros; inversion H; term_inv M. Qed.

  Lemma funS_algebraic: forall M,
      isBaseType (type M) -> isFunS M -> algebraic M.
  
  Proof. intros; apply AlgFunApp; term_inv M. Qed.

  Definition algebraicSubstitution G := forall p T, G |-> p/T -> algebraic T.

  Lemma singletonSubst_algebraic : forall G T,
      isSingletonSubst T G -> algebraic T -> algebraicSubstitution G.

  Proof.
    intros; intros p M D.
    destruct H.
    destruct p.
    replace M with T; trivial.
    inversion H; inversion D; try_solve.
    set (hint := H1 p).
    inversion D; inversion hint; try_solve.
  Qed.

  Lemma algebraicSubstitution_cons_none : forall G,
      algebraicSubstitution G -> algebraicSubstitution (None :: G).

  Proof.
    intros; intros p M D.
    destruct p.
    inversion D.
    apply (H p); trivial.
  Qed.

  Lemma algebraicSubstitution_cons_some : forall G T, algebraicSubstitution G ->
    algebraic T -> algebraicSubstitution (Some T :: G).

  Proof.
    intros; intros p M D.
    destruct p.
    inversion D.
    rewrite <- H2; trivial.
    apply (H p); trivial.
  Qed.

  Lemma algebraicSubstitution_cons_rev : forall G T,
      algebraicSubstitution (T :: G) -> algebraicSubstitution G.

  Proof. intros; intros p M D. apply (H (S p)); trivial. Qed.

  Lemma algebraicSubstitution_lifted : forall G i,
      algebraicSubstitution G -> algebraicSubstitution (lift_subst G i).

  Proof.
    induction G; trivial.
    intros i aG.
    destruct a; simpl.
    apply algebraicSubstitution_cons_some.
    apply IHG.
    apply algebraicSubstitution_cons_rev with (Some t); trivial.
    apply algebraic_lift.
    apply (aG 0); fo.
    apply algebraicSubstitution_cons_none.
    apply IHG; trivial.
    apply algebraicSubstitution_cons_rev with (None (A:=Term)); trivial.
  Qed.

  Lemma notFunApp_subst : forall M G (MG: correct_subst M G),
      isApp M -> algebraicSubstitution G -> ~isFunApp M -> ~isFunApp (subst MG).

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm) (P := fun M =>
      forall G (MG: correct_subst M G),
	isApp M ->
	algebraicSubstitution G ->
	~isFunApp M ->
	~isFunApp (subst MG)
    ).
    apply subterm_wf.
    clear M; intros M IH G MG Mapp Galg Mnfa MGfa.
    destruct (app_subst Mapp MG).
    set (MGapp := app_subst_app Mapp MG).
    destruct (term_case (appBodyL Mapp)) as [[[MLvar | MLfun] | MLabs] | MLapp].
     (* variable *)
    destruct (var_subst (subst_appL_c Mapp MG)) as 
      [[T [y GyT MGterm]] | MGterm]; trivial.
    absurd (isBaseType (type (appBodyL MGapp))).
    assert (forall W (Wapp: isApp W), ~isBaseType (type (appBodyL Wapp))).
    intros; term_inv W.
    apply H1.
    apply algebraic_funApp_datatype.
    apply algebraic_morph_aux with T. trivial.
    apply terms_conv_criterion.
    rewrite appBodyL_env.
    apply env_comp_sym.
    apply subst_env_compat with y; trivial.
    rewrite <- MGterm; rewrite <- H; trivial.
    apply (Galg y); trivial.
    apply isFunApp_left; trivial.
    absurd (isFunS (appHead (subst MG))).
    assert (forall W, isVar W -> ~isFunS W).
    intro W; term_inv W.
    apply H1.
    rewrite (appHead_app (subst MG) MGapp).
    assert (isVar (appBodyL MGapp)).
    assert (forall W, isVar W -> exists x, term W = %x).
    intro W; term_inv W.
    exists x; trivial.
    destruct (H2 (appBodyL Mapp) MLvar).
    apply var_is_var with x.
    unfold MGapp; rewrite H.
    rewrite MGterm; trivial.
    rewrite appHead_notApp; trivial.
    assert (forall W, isVar W -> ~isApp W).
    intro W; term_inv W.
    apply H3; trivial.
    trivial.
     (* function symbol *)
    absurd (isFunApp M); trivial.
    unfold isFunApp in * .
    rewrite (appHead_app M Mapp); simpl.
    rewrite (appHead_notApp (appBodyL Mapp)); trivial.
    assert (forall W, isFunS W -> ~isApp W).
    intro W; term_inv W.
    apply H1; trivial.
     (* abstraction *)
     unfold isFunApp in * .
    rewrite (appHead_app (subst MG) MGapp) in MGfa.
    rewrite (appHead_notApp (appBodyL MGapp)) in MGfa.
    unfold MGapp in MGfa; rewrite H in MGfa.
    assert (forall W, isFunS W -> isAbs W -> False).
    intro W; term_inv W.
    apply H1 with (subst (subst_appL_c Mapp MG)); trivial.
    apply abs_subst_abs; trivial.
    apply abs_isnot_app; trivial.
    unfold MGapp.
    rewrite H.
    apply abs_subst_abs; trivial.
       (* appplication *)
    absurd (isFunApp (appBodyL MGapp)); trivial.
    unfold MGapp; rewrite H.
    apply IH; trivial.
    apply appBodyL_subterm.
    apply notFunApp_left_inv; trivial.
    apply isFunApp_left; trivial.
  Qed.

  Lemma algebraic_subst : forall M G (MG: correct_subst M G),
      algebraic M -> algebraicSubstitution G -> algebraic (subst MG).

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm) (P := fun M =>
      forall G (MG: correct_subst M G),
	algebraic M ->
	algebraicSubstitution G ->
	algebraic (subst MG)).
    apply subterm_wf.
    clear M; intros M IH G MG Malg Galg.    
    term_inv M.
     (* variable *)
    destruct (var_subst MG I) as [[W [p GpW MGterm]] | MGterm].
    apply (@algebraic_morph_aux W (subst MG)).
    apply terms_conv_criterion; auto.
    apply env_comp_sym.
    apply subst_env_compat with p; trivial.
    apply (Galg p); trivial.
    apply AlgVar.
    apply var_is_var with x; rewrite MGterm; trivial.
     (* function symbol *)
    inversion Malg; try_solve.
    set (MGfunS := funS_subst_funS MG I).
    apply AlgFunApp; autorewrite with terms; trivial.
    apply funS_funApp; trivial.
    unfold isArg; rewrite appArgs_notApp; try_solve.
    assert (forall M, isFunS M -> ~isApp M).
    intro W; term_inv W.
    apply H3; trivial.
     (* abstraction *)
    apply AlgAbs with (abs_subst_abs (M:=Tr) I MG).
    destruct (abs_subst (M:=Tr) I MG).
    rewrite H0.
    apply IH; trivial.
    apply absBody_subterm.
    inversion Malg; try_solve.
    apply algebraicSubstitution_cons_none.
    apply algebraicSubstitution_lifted; trivial.
     (* application *)
    destruct (isFunApp_dec Tr).
     (*  - functional application *)
    apply AlgFunApp.
    apply funApp_subst_funApp; trivial.
    inversion Malg; try_solve.
    rewrite subst_type; simpl; trivial.    
    intros.
    destruct (subst_arg_rev M' MG H) as 
      [[Marg [MargM [MG' MargMG']]] | [p [T [Targ [TargT [GpT M'Targ_term]]]]]].
    rewrite MargMG'.
    apply IH; trivial.
    apply arg_subterm; trivial.
    apply algebraic_arg with Tr; simpl; trivial. 
    assert (M'Targ: M' ~ Targ).
    apply terms_conv_criterion; trivial.
    rewrite (appUnit_env Targ T).
    rewrite (appUnit_env M' (subst MG)).
    apply subst_env_compat with p; trivial.
    apply appArg_is_appUnit; trivial.
    apply appArg_is_appUnit; trivial.
    rewrite M'Targ.
    apply algebraic_arg with T; trivial.
    apply appArg_app with Targ; trivial.    
    apply (Galg p); trivial.
     (*   - non-functional application *)
    destruct (app_subst (M:=Tr) I MG).
    apply algebraic_app with (app_subst_app (M:=Tr) I MG).
    rewrite H.
    apply IH; trivial.
    apply appBodyL_subterm.
    apply algebraic_appBodyL; trivial.
    rewrite H0.
    apply IH; trivial.
    apply appBodyR_subterm.
    apply algebraic_appBodyR; trivial.
  Qed.

  Lemma betaStep_algebraic_preserving :
    forall M N, algebraic M -> BetaStep M N -> algebraic N.

  Proof.
    intros.
    inversion H0.
    apply algebraic_lower.
    apply algebraic_subst.
    apply algebraic_absBody.
    apply algebraic_appBodyL; trivial.
    unfold isFunApp in * .
    assert (isAbs (appHead M)).
    rewrite (appHead_app M Mapp0).
    rewrite (appHead_notApp (appBodyL Mapp0)); trivial.
    apply abs_isnot_app; trivial.
    term_inv (appHead M).
    apply singletonSubst_algebraic with (lift (appBodyR Mapp0) 1).
    apply singletonSubst_cond.
    apply algebraic_lift.
    apply algebraic_appBodyR; trivial.
  Qed.

  Lemma beta_algebraic_preserving :
    forall M N, algebraic M -> M -b-> N -> algebraic N.

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm) (P := fun M =>
      forall N,
	algebraic M ->
	M -b-> N ->
	algebraic N).
    apply subterm_wf.
    clear M; intros M IH N Malg MN.
    inversion MN.
     (* beta-step *)
    apply betaStep_algebraic_preserving with M; trivial.
     (* application - left *)
    destruct (isFunApp_dec M) as [Mfa | Mnfa].
     (*   - functional application *)
    apply AlgFunApp; trivial.
    unfold isFunApp in * .
    term_inv N.
    apply app_beta_funS with M; trivial.
    rewrite <- (subject_reduction MN).
    apply algebraic_funApp_datatype; trivial.
    intros N' N'N.
    destruct (funS_fun (appHead M) Mfa) as [f Mf].
    destruct (app_beta_args_eq N' Mapp MN Mf) 
      as [M'M | [M' M'N' M'M]]; trivial.
    apply algebraic_arg with M; trivial.
    apply IH with M'; trivial.
    apply arg_subterm; trivial.
    apply algebraic_arg with M; trivial.
     (*   - non-functional application *)
    apply algebraic_app with Napp.
    apply IH with (appBodyL Mapp); trivial.
    apply appBodyL_subterm.
    apply algebraic_appBodyL; trivial.
    rewrite <- H0.
    apply algebraic_appBodyR; trivial.
     (* application - right *)
    destruct (isFunApp_dec M) as [Mfa | Mnfa]; 
      inversion Malg; try solve [term_inv M].
     (*   - functional application *)
    apply AlgFunApp.
    unfold isFunApp in * .
    rewrite appHead_app with N Napp.
    rewrite <- H0.
    rewrite <- appHead_app; trivial.
    rewrite <- (subject_reduction MN); trivial.
    unfold isArg; rewrite (appArgs_app N Napp); intros.
    destruct (in_app_or H7).
    apply H5.
    apply appArg_left with Mapp.
    simpl; rewrite H0; trivial.
    inversion H8; try_solve.
    rewrite <- H9.
    apply IH with (appBodyR Mapp); trivial.
    apply appBodyR_subterm.
    apply algebraic_appBodyR; trivial.
     (*   - non-functional application *)
    apply AlgApp; trivial.
    apply (notFunApp_left_eq M Mapp N Napp); trivial.
    unfold isAppUnit; rewrite (appUnits_app N Napp); intros.
    destruct (in_app_or H7).
    apply H5.
    apply appUnit_left with Mapp.
    simpl; rewrite H0; trivial.
    inversion H8; try_solve.
    rewrite <- H9.
    apply IH with (appBodyR Mapp); trivial.    
    apply appBodyR_subterm.
    apply algebraic_appBodyR; trivial.
     (* abstraction *)
    apply AlgAbs with Nabs.
    apply IH with (absBody Mabs); trivial.
    apply absBody_subterm.
    inversion Malg; term_inv M.
  Qed.

  Lemma algebraic_dec: forall M, {algebraic M} + {~algebraic M}.

  Proof.
    intro M.
    apply well_founded_induction with (R := subterm)
      (P := fun M => {algebraic M} + {~algebraic M}).
    apply subterm_wf.
    clear M; intros M IH.
    destruct (term_case M) as [[[Mvar | Mfun] | Mabs] | Mapp].
    left; apply AlgVar; trivial.
    destruct (baseType_dec (type M)).
    left; apply AlgFunApp; term_inv M.
    assert (forall T, isBaseType T -> isArrowType T -> False).
    destruct T; trivial. 
    right; intro Marg; inversion Marg; term_inv M.
    apply H with (f_type f); trivial.
    destruct (IH (absBody Mabs) (absBody_subterm M Mabs)).
    left; apply AlgAbs with Mabs; trivial.
    right; intro Malg; inversion Malg; term_inv M.
    destruct (isFunApp_dec M) as [Mfapp | Mnfapp].
    destruct (baseType_dec (type M)).
    destruct (list_dec_all (fun M => algebraic M) (appArgs M)).
    intros; apply IH.
    apply arg_subterm; trivial.
    left; apply AlgFunApp; trivial.
    right; intro Marg; inversion Marg; try solve [term_inv M].
    destruct e as [l [lM lalg]].
    absurd (algebraic l); trivial.
    apply H1; trivial.
    right; intro Marg; inversion Marg; term_inv M.
    destruct B; try_solve.
    destruct (list_dec_all (fun M => algebraic M) (appUnits M)).
    intros; apply IH.
    apply appUnit_subterm; trivial.
    left; apply AlgApp; trivial.
    right; intro Marg; inversion Marg; term_inv M.
    destruct e as [l [lM lalg]].
    absurd (algebraic l); trivial.
    apply H1; trivial.
  Qed.

  Section Monotonicity.

    Variable R : relation Term.

    Notation "X -R-> Y" := (R X Y) (at level 50).

    Definition algebraic_monotonicity := 
      forall T (pos: Pos T) (Mpos: PlaceHolder pos) (Npos: PlaceHolder pos)
	(M := proj1_sig2 Mpos) (N := proj1_sig2 Npos),
	algebraic T -> algebraic M -> algebraic N -> ~isFunApp (T // pos) ->
        M -R-> N -> swap Mpos -R-> swap Npos.

    Lemma monotonicity_algebraicMonotonicity :
      monotonous R -> algebraic_monotonicity.

    Proof.
      unfold monotonous, algebraic_monotonicity; intros. apply H; trivial.
    Qed.

    Lemma algebraic_swap_this : forall M (pos: Pos M) (MP: PlaceHolder pos)
      (P := proj1_sig2 MP), pos = PThis M -> algebraic P -> algebraic (swap MP).

    Proof.
      intros.
      destruct pos; try_solve.
      replace (swap MP) with P; trivial.
      apply term_eq.
      rewrite swap_env_eq; destruct MP; try_solve.
      rewrite swap_term_is; try_solve.
    Qed.

    Lemma algebraic_swap_abs :
      forall M (pos: Pos M) (MP: PlaceHolder pos) (P := proj1_sig2 MP),
        (forall Min (pos: Pos Min) (MP: PlaceHolder pos) (P := proj1_sig2 MP), 
	    subterm Min M -> ~isFunApp (Min // pos) -> algebraic Min ->
            algebraic P -> algebraic (swap MP)) ->
        pos <> PThis M -> isAbs M -> ~isFunApp (M // pos) -> algebraic M ->
        algebraic P -> algebraic (swap MP).

    Proof.
      intros.
      destruct pos; try_solve.
      assert (MPabs: isAbs (swap MP)).
      apply swap_abs.
      apply AlgAbs with MPabs.
      destruct (placeHolder_abs MP) as [MPin MPeq].
      rewrite <- (swap_in_abs (TAbs AbsB) MPin); trivial.
      apply H; trivial.
      change (buildT AbsB) with (@absBody (buildT (TAbs AbsB)) I).
      apply absBody_subterm.
      inversion H3; try_solve.
      rewrite MPeq; trivial.
    Qed.

    Lemma algebraic_swap_notFunApp :
      forall M (pos: Pos M) (MP: PlaceHolder pos) (P := proj1_sig2 MP),
        (forall Min (pos: Pos Min) (MP: PlaceHolder pos) (P := proj1_sig2 MP),
            subterm Min M -> ~isFunApp (Min // pos) -> algebraic Min ->
            algebraic P -> algebraic (swap MP)) ->
        pos <> PThis M -> ~isFunApp M -> ~isFunApp (M // pos) ->
        (forall M', isAppUnit M' M -> algebraic M') -> algebraic P ->
        (forall M', isAppUnit M' (swap MP) -> algebraic M').

    Proof.
      induction pos; intros MP P IH Pthis Mnfa Mpnfa Mualg Palg M' M'unit;
        try_solve.

      assert (MPabs: isAbs (swap MP)).
      apply swap_abs.
      unfold isAppUnit in M'unit.
      rewrite appUnits_notApp in M'unit.
      inversion M'unit; try_solve.
      rewrite <- H.
      apply algebraic_swap_abs; try_solve.
      apply Mualg.
      unfold isAppUnit.
      rewrite appUnits_notApp; auto with datatypes.
      term_inv (swap MP).

      set (Lapp := swap_left_app MP).
      destruct (placeHolder_appL MP) as [MLP ML].
      set (SL := swap_in_appL MLP MP Lapp ML).
      unfold isAppUnit in M'unit.
      rewrite (appUnits_app (swap MP) Lapp) in M'unit.
      destruct (in_app_or M'unit).
      destruct (posThis_dec pos).
      apply algebraic_appUnits with P; trivial.
      apply algebraic_arrowType; trivial.
      unfold P; destruct MP; simpl.
      rewrite <- e1; rewrite e; simpl; trivial.
      rewrite <- SL in H.
      replace (swap MLP) with P in H; trivial.
      apply term_eq.
      rewrite swap_env_eq.
      unfold P; destruct MP; simpl.
      rewrite <- e0; rewrite e; trivial.
      rewrite swap_term_is; rewrite ML.
      unfold P; destruct MP; simpl.
      rewrite e; trivial.
      apply IHpos with MLP; trivial.
      intros; apply IH; trivial.
      apply AppLsub with I; constructor; trivial.
      change (buildT AppL) with (@appBodyL (buildT (TApp AppL AppR)) I).
      apply notFunApp_left_inv; trivial.
      intros; apply Mualg.
      apply appUnit_left with I; trivial.
      rewrite ML; trivial.
      rewrite SL; trivial.
      inversion H; try_solve.
      apply Mualg.
      rewrite <- H0.
      rewrite (appBodyR_swap_in_appL MLP MP); trivial.
      change (buildT AppR) with (@appBodyR (buildT (TApp AppL AppR)) I).
      apply appUnit_right with I; trivial.

      set (Rapp := swap_right_app MP).
      destruct (placeHolder_appR MP) as [MRP MR].
      set (SR := swap_in_appR MRP MP Rapp MR).
      unfold isAppUnit in M'unit.
      rewrite (appUnits_app (swap MP) Rapp) in M'unit.
      destruct (in_app_or M'unit).
      apply Mualg.
      apply appUnit_left with I; simpl.
      rewrite <- (appBodyL_swap_in_appR MRP MP Rapp MR); trivial.
      inversion H; try_solve.
      rewrite <- H0; rewrite <- SR.
      apply IH; trivial.
      change (buildT AppR) with (@appBodyR (buildT (TApp AppL AppR)) I).
      apply appBodyR_subterm.
      apply Mualg.
      apply appUnit_right with I; trivial.
      rewrite MR; trivial.
    Qed.

    Lemma algebraic_swap_isFunApp :
      forall M (pos: Pos M) (MP: PlaceHolder pos) (P := proj1_sig2 MP),
        (forall Min (pos: Pos Min) (MP: PlaceHolder pos) (P := proj1_sig2 MP),
            subterm Min M -> ~isFunApp (Min // pos) -> algebraic Min ->
            algebraic P -> algebraic (swap MP)) ->
        isFunApp M -> ~isFunApp (M // pos) ->
        (forall M', isArg M' M -> algebraic M') ->
        algebraic P -> (forall M', isArg M' (swap MP) -> algebraic M').

    Proof.
      induction pos; intros MP P IH Mnfa Mpnfa Mualg Palg M' M'arg; try_solve.

      set (Lapp := swap_left_app MP).
      destruct (placeHolder_appL MP) as [MLP ML].
      set (SL := swap_in_appL MLP MP Lapp ML).
      unfold isArg in M'arg.
      rewrite (appArgs_app (swap MP) Lapp) in M'arg.
      destruct (in_app_or M'arg).
      apply IHpos with MLP; trivial.
      intros; apply IH; trivial.
      apply AppLsub with I; constructor; trivial.
      change (buildT AppL) with (@appBodyL (buildT (TApp AppL AppR)) I).
      apply isFunApp_left; trivial.
      intros; apply Mualg.
      apply appArg_left with I; trivial.
      rewrite ML; trivial.
      rewrite SL; trivial.
      inversion H; try_solve.
      apply Mualg.
      rewrite <- H0.
      rewrite (appBodyR_swap_in_appL MLP MP); trivial.
      change (buildT AppR) with (@appBodyR (buildT (TApp AppL AppR)) I).
      apply appArg_right with I; trivial.

      set (Rapp := swap_right_app MP).
      destruct (placeHolder_appR MP) as [MRP MR].
      set (SR := swap_in_appR MRP MP Rapp MR).
      unfold isArg in M'arg.
      rewrite (appArgs_app (swap MP) Rapp) in M'arg.
      destruct (in_app_or M'arg).
      apply Mualg.
      apply appArg_left with I; simpl.
      rewrite <- (appBodyL_swap_in_appR MRP MP Rapp MR); trivial.
      inversion H; try_solve.
      rewrite <- H0; rewrite <- SR.
      apply IH; trivial.
      change (buildT AppR) with (@appBodyR (buildT (TApp AppL AppR)) I).
      apply appBodyR_subterm.
      apply Mualg.
      apply appArg_right with I; trivial.
      rewrite MR; trivial.
    Qed.

    Lemma algebraic_swap_app : forall M (pos: Pos M) (MP: PlaceHolder pos)
      (P := proj1_sig2 MP),
      (forall Min (pos: Pos Min) (MP: PlaceHolder pos) (P := proj1_sig2 MP),
	subterm Min M -> ~isFunApp (Min // pos) -> algebraic Min ->
        algebraic P -> algebraic (swap MP)
      ) ->
      pos <> PThis M -> ~isFunApp (M // pos) -> isApp M -> algebraic M ->
      algebraic P -> algebraic (swap MP).

    Proof.
      intros.
      destruct (isFunApp_dec M).
      apply AlgFunApp; trivial.
      apply swap_isFunApp; trivial.
      rewrite swap_type_eq.
      inversion H3; term_inv M.
      intros. apply (algebraic_swap_isFunApp MP); trivial.
      inversion H3; term_inv M.
      apply AlgApp; trivial.
      apply app_swap_app; trivial.
      apply swap_not_funApp; trivial.
      fold P; inversion H4; term_inv P.
      intros. apply (algebraic_swap_notFunApp MP); trivial.
      inversion H3; term_inv M.
    Qed.

    Lemma algebraic_swap : forall M (pos: Pos M) (MP: PlaceHolder pos)
      (P := proj1_sig2 MP),
      ~isFunApp (M // pos) -> algebraic M -> algebraic P -> algebraic (swap MP).

    Proof.
      intro M.
      apply well_founded_ind with (R := subterm) (P := fun M =>
        forall (pos: Pos M) (MP: PlaceHolder pos)
          (P := proj1_sig2 MP),
          ~isFunApp (M // pos) ->
          algebraic M ->
          algebraic P ->
          algebraic (swap MP)).
      apply subterm_wf.
      clear M; intros M IH pos MP P Mnfa Malg Palg.
      induction pos.
      apply algebraic_swap_this; trivial.
      apply algebraic_swap_abs; try_solve.
      apply algebraic_swap_app; try_solve.
      apply algebraic_swap_app; try_solve.
    Qed.

    Lemma algebraic_swap_funApp : forall T (pos: Pos T) 
        (Mpos: PlaceHolder pos) (Npos: PlaceHolder pos) 
	(M := proj1_sig2 Mpos) (N := proj1_sig2 Npos),
	~isFunApp (T // pos) -> isFunApp T ->
	exists l t (tp: Pos t) (ph: PlaceHolder tp * PlaceHolder tp),
          isArg t T /\ ~isFunApp (t // tp) /\
          proj1_sig2 (fst ph) = M /\ proj1_sig2 (snd ph) = N /\
	  appHead (swap Mpos) = appHead (swap Npos) /\
	  appArgs (swap Mpos) = fst l ++ (swap (fst ph)) :: snd l /\
	  appArgs (swap Npos) = fst l ++ (swap (snd ph)) :: snd l.

    Proof.
      induction pos; intros; try_solve.

      set (Lapp := swap_left_app Mpos).
      set (Rapp := swap_left_app Npos).
      destruct (placeHolder_appL Mpos) as [MLpos ML].
      destruct (placeHolder_appL Npos) as [NLpos NL].
      destruct (IHpos MLpos NLpos) as [[l r]
        [T [TP [[PHL PHR] [Targ [Tnfa [TM [TN [MNhead [Margs Nargs]]]]]]]]]];
        trivial.
      change (buildT AppL) with (appBodyL (M:=buildT (TApp AppL AppR)) I).
      apply isFunApp_left; trivial.
      set (SL := swap_in_appL MLpos Mpos Lapp ML).
      set (SR := swap_in_appL NLpos Npos Rapp NL).
      exists (l, r ++ appBodyR Lapp::nil); simpl in * .
      exists T; exists TP; exists (PHL, PHR).
      repeat split; simpl; trivial.
      apply appArg_left with I; trivial.
      rewrite TM; trivial.
      rewrite TN; trivial.
      rewrite appHead_app with (swap Mpos) Lapp.
      rewrite appHead_app with (swap Npos) Rapp.
      rewrite <- SL; rewrite <- SR; trivial.
      rewrite appArgs_app with (swap Mpos) Lapp.
      rewrite <- SL; rewrite Margs.
      rewrite app_ass; auto with datatypes.
      rewrite appArgs_app with (swap Npos) Rapp.
      rewrite <- SR; rewrite Nargs.
      rewrite (appBodyR_swap_in_appL MLpos Mpos); trivial.
      rewrite (appBodyR_swap_in_appL NLpos Npos); trivial.
      rewrite app_ass; auto with datatypes.

      set (Lapp := swap_right_app Mpos).
      set (Rapp := swap_right_app Npos).
      destruct (placeHolder_appR Mpos) as [MLpos ML].
      destruct (placeHolder_appR Npos) as [NLpos NL].
      set (SL := swap_in_appR MLpos Mpos Lapp ML).
      set (SR := swap_in_appR NLpos Npos Rapp NL).
      exists (appArgs (appBodyL Lapp), nil (A:=Term)).
      exists (buildT AppR); exists pos; exists (MLpos, NLpos).
      repeat split; simpl; trivial.
      apply appArg_right with I; trivial.
      rewrite appHead_app with (swap Mpos) Lapp.
      rewrite appHead_app with (swap Npos) Rapp.
      rewrite (appBodyL_swap_in_appR MLpos Mpos); trivial.
      rewrite (appBodyL_swap_in_appR NLpos Npos); trivial.
      rewrite appArgs_app with (swap Mpos) Lapp.
      rewrite <- SL; trivial.
      rewrite appArgs_app with (swap Npos) Rapp.
      rewrite (appBodyL_swap_in_appR NLpos Npos); trivial.
      rewrite (appBodyL_swap_in_appR MLpos Mpos); trivial.
      rewrite <- SR; trivial.
    Qed.

    Definition appMonCond := forall M M' (Mapp: isApp M) (M'app: isApp M'),
        algebraic M -> algebraic M' ->
	(
          ~isFunApp M /\ ~isFunApp M' /\ 
	  appBodyL Mapp -R-> appBodyL M'app /\
          appBodyR Mapp  =   appBodyR M'app
	) \/
	(
          ~isFunApp M /\ ~isFunApp M' /\
          appBodyL Mapp  =   appBodyL M'app /\
          appBodyR Mapp -R-> appBodyR M'app
	) \/
	(
	  isFunApp M /\ appHead M = appHead M' /\
	  exists ll, exists m, exists m',
	    appArgs M  = fst ll ++ m  :: snd ll /\
	    appArgs M' = fst ll ++ m' :: snd ll /\
	    m -R-> m'
	) ->
	M -R-> M'.

    Definition absMonCond :=  forall N N' (Nabs: isAbs N) (N'abs: isAbs N'),
        algebraic (absBody Nabs) -> algebraic (absBody N'abs) ->
	absType Nabs = absType N'abs ->
	absBody Nabs -R-> absBody N'abs ->
	N -R-> N'.

    Lemma algebraic_monotonicity_criterion :
      appMonCond -> absMonCond -> algebraic_monotonicity.

    Proof.
       intros CApp CAbs T; revert CApp CAbs.
       apply well_founded_ind with (R := subterm) (P := fun T =>
         appMonCond ->
         absMonCond ->
         forall (pos: Pos T) (Mpos Npos: PlaceHolder pos)
           (M := proj1_sig2 Mpos) (N := proj1_sig2 Npos),
           algebraic T ->
           algebraic M ->
           algebraic N ->
           ~isFunApp (T // pos) ->
           M -R-> N ->
           swap Mpos -R-> swap Npos).
       apply subterm_wf.
       clear T; intros T IH CApp CAbs pos Mpos Npos M N Talg Malg 
         Nalg Tpos MN.
       induction pos.

        (* PThis *)
       replace (swap Mpos) with (proj1_sig2 Mpos).
       replace (swap Npos) with (proj1_sig2 Npos).
       trivial.
       apply term_eq; trivial.
       rewrite swap_env_eq; destruct Npos; try_solve.
       rewrite swap_term_is; try_solve.
       apply term_eq; trivial.
       rewrite swap_env_eq; destruct Mpos; try_solve.
       rewrite swap_term_is; try_solve.

        (* PAbs *)
       set (Labs := swap_abs Mpos).
       set (Rabs := swap_abs Npos).
       apply CAbs with Labs Rabs.
       apply algebraic_absBody.
       apply algebraic_swap; trivial.
       apply algebraic_absBody.
       apply algebraic_swap; trivial.
       apply type_eq_absType_eq.
       do 2 rewrite swap_type_eq; trivial.
       destruct (placeHolder_abs Mpos) as [MLpos ML].
       destruct (placeHolder_abs Npos) as [NLpos NL].
       replace (absBody Labs) with (swap MLpos).
       replace (absBody Rabs) with (swap NLpos).
       apply IH; trivial.
       change (buildT AbsB) with (@absBody (buildT (TAbs AbsB)) I).
       apply absBody_subterm.
       change (buildT AbsB) with (@absBody (buildT (TAbs AbsB)) I).
       apply algebraic_absBody; trivial.
       rewrite ML; trivial.
       rewrite NL; trivial.
       rewrite ML; rewrite NL; trivial.
       apply swap_in_abs; trivial.
       apply TAbs; trivial.
       apply swap_in_abs; trivial.
       apply TAbs; trivial.

        (* PAppL *)
       set (Lapp := swap_left_app Mpos).
       set (Rapp := swap_left_app Npos).
       apply CApp with Lapp Rapp.
       apply algebraic_swap; trivial.
       apply algebraic_swap; trivial.
       destruct (isFunS_dec (appHead (buildT (TApp AppL AppR)))).
       right; right; split.
       apply swap_isFunApp; trivial.
       destruct (algebraic_swap_funApp Mpos Npos) as [[l r]
         [T [TP [[PHL PHR] [Targ [Tnfa [TM [TN [MNhead [Margs Nargs]]]]]]]]]];
         trivial.
       split; simpl in *; trivial.
       ex (l, r) (swap PHL) (swap PHR); repeat split; trivial.
       apply IH; trivial.
       apply arg_subterm; trivial.
       apply algebraic_arg with (buildT (TApp AppL AppR)); simpl; trivial.
       rewrite TM; trivial.
       rewrite TN; trivial.
       rewrite TM; rewrite TN; trivial.
       left; repeat split.
       apply swap_not_funApp; try_solve; fold M.
       inversion Malg; term_inv M.
       apply swap_not_funApp; try_solve; fold N.
       inversion Nalg; term_inv N.
       destruct (placeHolder_appL Mpos) as [MLpos ML].
       destruct (placeHolder_appL Npos) as [NLpos NL].
       replace (appBodyL Lapp) with (swap MLpos).
       replace (appBodyL Rapp) with (swap NLpos).
       apply IH; trivial.
       change (buildT AppL) with (@appBodyL (buildT (TApp AppL AppR)) I).
       apply appBodyL_subterm; trivial.
       change (buildT AppL) with (@appBodyL (buildT (TApp AppL AppR)) I).
       apply algebraic_appBodyL; trivial.
       rewrite ML; trivial.
       rewrite NL; trivial.
       rewrite ML; rewrite NL; trivial.
       apply swap_in_appL; trivial.
       apply swap_in_appL; trivial.
       apply swap_appR_eq. 

        (* PAppR *)
       set (Lapp := swap_right_app Mpos).
       set (Rapp := swap_right_app Npos).
       apply CApp with Lapp Rapp.
       apply algebraic_swap; trivial.
       apply algebraic_swap; trivial.
       destruct (isFunS_dec (appHead (buildT (TApp AppL AppR)))).
       right; right; split.
       apply swap_isFunApp; trivial.
       destruct (algebraic_swap_funApp Mpos Npos) as [[l r]
         [T [TP [[PHL PHR] [Targ [Tnfa [TM [TN [MNhead [Margs Nargs]]]]]]]]]];
         trivial.
       repeat split; simpl in *; trivial.
       ex (l, r) (swap PHL) (swap PHR); repeat split; trivial.
       apply IH; trivial.
       apply arg_subterm; trivial.
       apply algebraic_arg with (buildT (TApp AppL AppR)); simpl; trivial.
       rewrite TM; trivial.
       rewrite TN; trivial.
       rewrite TM; rewrite TN; trivial.
       right; left; repeat split.
       apply swap_not_funApp; try_solve; fold M.
       inversion Malg; term_inv M.
       apply swap_not_funApp; try_solve; fold N.
       inversion Nalg; term_inv N.
       apply swap_appL_eq. 
       destruct (placeHolder_appR Mpos) as [MLpos ML].
       destruct (placeHolder_appR Npos) as [NLpos NL].
       replace (appBodyR Lapp) with (swap MLpos).
       replace (appBodyR Rapp) with (swap NLpos).
       apply IH; trivial.
       change (buildT AppR) with (@appBodyR (buildT (TApp AppL AppR)) I).
       apply appBodyR_subterm; trivial.
       change (buildT AppR) with (@appBodyR (buildT (TApp AppL AppR)) I).
       apply algebraic_appBodyR; trivial.
       rewrite ML; trivial.
       rewrite NL; trivial.
       rewrite ML; rewrite NL; trivial.
       apply swap_in_appR; trivial.
       apply swap_in_appR; trivial.
     Qed.

  End Monotonicity.

  Definition AlgTerm := { T: Term | algebraic T }.

  Definition algTerm (T: AlgTerm) : Term := proj1_sig T.

  Coercion algTerm: AlgTerm >-> Term.

  Module AlgTermsSet <: SetA.
    Definition A := AlgTerm.
  End AlgTermsSet.

  Module AlgTermsEqset <: Eqset := Eqset_def AlgTermsSet.

End TermsAlgebraic.
