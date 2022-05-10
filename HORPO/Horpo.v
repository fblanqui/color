(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

This file introduces definition of the higher-order
recursive path ordering due to Jouannaud and Rubio.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras RelUtil Terms MultisetOrder
     PairLex MultisetList MultisetTheory AccUtil LogicUtil.
From Coq Require Import Morphisms Basics.

Module Type Precedence.

  Declare Module S : TermsSig.Signature.
  Declare Module Export P : Poset with Definition A := S.FunctionSymbol.

  Parameter Ord_wf : well_founded (transp gtA).
  Parameter Ord_dec : forall a b, {gtA a b} + {~gtA a b}.

End Precedence.

Module Horpo (S : TermsSig.Signature)
             (Prec : Precedence with Module S := S).

  Module Export T := Terms.Terms S.

  Module MSetCore := MultisetList.MultisetList TermsEqset_dec.
  Module Export MSet := MultisetTheory.Multiset MSetCore.

  Module Export MSetOrd := MultisetOrder.MultisetOrder MSetCore.

  Module Import Lex := PairLex.LexicographicOrder Subterm_Ord Subterm_Ord.

  Definition TermMul := Multiset.
  Implicit Type TM : TermMul.

  Definition TermList := list Term.
  Implicit Type TL : TermList.

  Notation "f >#> g" := (Prec.P.O.gtA f g) (at level 30).
  Reserved Notation "M >-> N" (at level 30).
  Reserved Notation "M >> N" (at level 30).
  Reserved Notation "M >>= N" (at level 30).
  Reserved Notation "M {>>} N" (at level 30).
  Reserved Notation "M [>>] N" (at level 30).
  
  Inductive horpoArgs : Term -> TermList -> Prop :=

  | HArgsNil: forall M, M [>>] nil

  | HArgsConsEqT: forall M N TL, M >> N -> M [>>] TL -> M [>>] (N :: TL)

  | HArgsConsNotEqT: forall M N TL,
    (exists2 M', isArg M' M & M' >>= N) -> M [>>] TL -> M [>>] (N :: TL)
    where "M [>>] N" := (horpoArgs M N)

  with prehorpo : relation Term :=

  | HSub: forall M N,
    isFunApp M -> (exists2 M', isArg M' M & M' >>= N) -> M >-> N

  | HFun: forall M N f g,
    term (appHead M) = ^f -> term (appHead N) = ^g -> f >#> g ->
    M [>>] (appArgs N) -> M >-> N

  | HMul: forall M N f,
    term (appHead M) = ^f -> term (appHead N) = ^f ->
    list2multiset (appArgs M) {>>} list2multiset (appArgs N) -> M >-> N

  | HAppFlat: forall M N Ns,
    isFunApp M -> isPartialFlattening Ns N -> M [>>] Ns -> M >-> N

  | HApp: forall M N (MApp: isApp M) (NApp: isApp N), 
    ~isFunApp M -> ~isFunApp N ->
    {{appBodyL MApp, appBodyR MApp}} {>>} {{appBodyL NApp, appBodyR NApp}} ->
    M >-> N

  | HAbs: forall M N (MAbs: isAbs M) (NAbs: isAbs N),
    absBody MAbs >> absBody NAbs -> M >-> N

  | HBeta: forall M N, 
    M -b-> N -> M >-> N

    where "M >-> N" := (prehorpo M N)

  with horpo : relation Term :=

  | Horpo: forall M N,
    type M = type N -> env M = env N -> algebraic M -> algebraic N ->
    M >-> N -> M >> N 
    where "M >> N" := (horpo M N)

  with horpoMul : relation TermMul :=

  | HMulOrd: forall (M N: TermMul),
    MSetOrd.MultisetGT horpo M N -> M {>>} N
    where "M {>>} N" := (horpoMul M N)

  with horpoRC : relation Term :=

  | horpoRC_step: forall M N, M >> N -> M >>= N

  | horpoRC_refl: forall M, M >>= M

    where "M >>= N" := (horpoRC M N).

  Notation "M >>* N" := (clos_trans horpo M N) (at level 30).

  Scheme horpoArgs_Ind := Minimality for horpoArgs Sort Prop
    with prehorpo_Ind  := Minimality for prehorpo  Sort Prop
    with horpo_Ind     := Minimality for horpo     Sort Prop.

  #[global] Hint Constructors horpoRC horpo prehorpo horpoArgs : horpo.

  Lemma horpo_prehorpo : forall M N, M >> N -> M >-> N.

  Proof.
    intros; inversion H; trivial.
  Qed.

  Lemma horpo_type_preserving : forall M N, M >> N -> type M = type N.

  Proof.
    intros; inversion H; trivial.
  Qed.

  Lemma horpo_RC_type_preserving : forall M N, M >>= N -> type M = type N.

  Proof.
    intros. inversion H. apply horpo_type_preserving; trivial. trivial.
  Qed.

  Lemma horpo_env_preserving : forall M N, M >> N -> env M = env N.

  Proof.
    intros; inversion H; trivial.
  Qed.

  Lemma horpo_algebraic_left : forall M N, M >> N -> algebraic M.

  Proof.
    intros. destruct H. hyp.
  Qed.

  Lemma horpo_algebraic_right : forall M N, M >> N -> algebraic N.

  Proof.
    intros. destruct H. hyp.
  Qed.

  Lemma horpo_RC_env_preserving : forall M N, M >>= N -> env M = env N.

  Proof.
    intros. inversion H. apply horpo_env_preserving; trivial. trivial.
  Qed.

  Lemma horpo_eq_compat : forall M M' N N',
    M = M' -> N = N' -> M >> N -> M' >> N'.

  Proof. intros; rewrite <- H, <- H0; trivial. Qed.

  Global Instance horpo_eq_compat' : Proper (eq ==> eq ==> impl) horpo.

  Proof.
    intros a b ab c d cd ac. eapply horpo_eq_compat. apply ab. apply cd. hyp.
  Qed.

  Lemma prehorpo_var_normal : forall N M, isVar M -> ~ (M >-> N).

  Proof.
    intro N.
    apply well_founded_ind with
      (R := subterm)
      (P := fun N => forall M, isVar M -> ~(M >-> N)).
    apply subterm_wf.
    clear N; intros N IH M Mvar MN.
    induction MN; term_inv M.
    inversion H; inversion H0; try_solve. 
  Qed.

   (* Variable is not bigger than any term *)
  Lemma horpo_var_normal : forall M N, isVar M -> ~(M >> N).

  Proof.
    intros M N Mvar MN.
    destruct MN.
    absurd (M >-> N); trivial.
    apply prehorpo_var_normal; trivial.
  Qed.

  Lemma term_neq_type : forall M N, type M <> type N -> M <> N.

  Proof.
    intros; intro MN.
    absurd (type M = type N); trivial.
    rewrite MN; trivial.
  Qed.

  Lemma horpo_RC : forall M N, M >>= N -> M >> N \/ M = N.

  Proof.
    intros; inversion H; fo.
  Qed.

  Lemma horpo_algebraic_preserving : forall M N, algebraic M -> 
    M >> N -> algebraic N.

  Proof.
    intros M N Mnorm MN. inversion MN. inversion H; trivial.
  Qed.

  Lemma beta_imp_horpo : forall M N, algebraic M -> M -b-> N -> M >> N.

  Proof.
    intros. constructor; try hyp.
    apply subject_reduction. hyp.
    apply beta_env_preserving. hyp.
    apply beta_algebraic_preserving with M; hyp.
    apply HBeta. hyp.
  Qed.

  Lemma horpo_app_inv : forall M N (Mapp: isApp M) (Napp: isApp N),
    ~isFunApp M -> algebraic M ->
    ~isFunApp N -> algebraic N ->
    appBodyL Mapp >>= appBodyL Napp /\
    appBodyR Mapp >>= appBodyR Napp /\
    (appBodyL Mapp >> appBodyL Napp \/ appBodyR Mapp >> appBodyR Napp) ->
    M >> N.

  Proof.
    intros. destruct H3 as [Leq [Req LRgt]].
    constructor; trivial.
    apply app_type_eq with Mapp Napp; trivial.
    apply horpo_RC_type_preserving. hyp.
    apply horpo_RC_type_preserving. hyp.
    rewrite <- appBodyL_env with M Mapp, <- appBodyL_env with N Napp.
    apply horpo_RC_env_preserving. hyp.
    apply HApp with Mapp Napp; trivial.
    constructor. destruct LRgt.
    apply pair_mOrd_left; try_solve.
    inversion Req; intuition.
    apply pair_mOrd_right; try_solve.
    inversion Leq; intuition.
  Qed.

  Lemma horpo_app : forall M N (Mapp: isApp M) (Napp: isApp N),
    type M = type N ->
    {{appBodyL Mapp, appBodyR Mapp}} {>>} {{appBodyL Napp, appBodyR Napp}} ->
    appBodyL Mapp >>= appBodyL Napp /\
    appBodyR Mapp >>= appBodyR Napp /\
    (appBodyL Mapp >> appBodyL Napp \/ appBodyR Mapp >> appBodyR Napp).

  Proof.
    assert (Htyp: forall M N, M >> N \/ M = N -> type M = type N).
    intros.
    destruct H.
    apply horpo_type_preserving; trivial.
    rewrite H; trivial.
    intros.
    inversion H0.
    term_inv M; term_inv N.
    (* compat: variables are A0, A1 before coq 8.15 but A, A0 after *)
    try (rename A0 into A1; rename A into A0).
    destruct (pair_mOrd horpo_eq_compat' H1) as
      [o1 | [o2 | [o3 | o4]]].
     (* Ml:Nl Ml:Nr *)
    absurd (A1 = A1 --> B0).
    apply type_discr.
    replace (A1 --> B0) with (A0 --> B).
    replace A1 with (A0 --> B); trivial.
    fold (type (buildT T1)).
    fold (type (buildT T4)).
    apply Htyp; try_solve.
    fold (type (buildT T1)).
    fold (type (buildT T3)).
    apply Htyp; try_solve.
     (* Mr:Nl Mr:Nr *)
    absurd (A1 = A1 --> B0).
    apply type_discr.
    replace (A1 --> B0) with A0.
    replace A1 with A0; trivial.
    fold (type (buildT T2)).
    fold (type (buildT T4)).
    apply Htyp; try_solve.
    fold (type (buildT T2)).
    fold (type (buildT T3)).
    apply Htyp; try_solve.
     (* Ml:Nl Mr:Nr *)
    destruct o3 as [c1 [c2 c3]].
    repeat split.
    destruct c1.
    left; trivial.
    unfold eqA in H4; unfold TermsEqset.eqA in H4.
    rewrite H4; right.
    destruct c2.
    left; trivial.
    unfold eqA in H4; unfold TermsEqset.eqA in H4.
    rewrite H4; right.
    destruct c3; try_solve.
     (* Mr:Nl Ml:Nr *)
    absurd (A0 = (A0 --> B) --> B0).
    apply type_discr2.
    replace (A0 --> B) with A1.
    fold (type (buildT T2)).
    fold (type (buildT T3)).
    apply Htyp; try_solve.
    fold (type (buildT T1)).
    fold (type (buildT T4)).
    sym.
    apply Htyp; try_solve.
  Qed.

  Lemma horpo_app_reduct : forall M N (Mapp: isApp M), M >> N ->
    ~isFunApp M \/ isArrowType (type M) ->
    (exists MLabs: isAbs (appBodyL Mapp), 
      N = lower (subst (beta_subst M Mapp MLabs)) (beta_lowering M Mapp MLabs)) \/
    exists Napp: isApp N, 
      (appBodyL Mapp =  appBodyL Napp /\ appBodyR Mapp >> appBodyR Napp) \/
      (appBodyL Mapp >> appBodyL Napp /\ appBodyR Mapp =  appBodyR Napp) \/
      (appBodyL Mapp >> appBodyL Napp /\ appBodyR Mapp >> appBodyR Napp).

  Proof.
    intros.
    destruct H.
    assert (~isFunApp M).
    destruct H0; trivial.
    apply algebraic_arrowType; trivial.
    destruct H4; try_solve.
    absurd (isFunApp M); trivial.
    unfold isFunApp; apply funS_is_funS with f; trivial.
    absurd (isFunApp M); trivial.
    unfold isFunApp; apply funS_is_funS with f; trivial.
    right. exists NApp.
    inversion H7.
    rewrite (app_proof_irr M Mapp MApp).
    destruct (horpo_app M N MApp NApp H) as [LL [RR [Ls | Rs]]]; trivial.
    inversion RR.
    right; right; split; trivial.
    right; left; split; trivial.
    inversion LL.
    right; right; split; trivial.
    left; split; trivial.
    term_inv M.
    destruct (beta_app_reduct Mapp H4) as [[MLabs NL] | [Napp Mred]].
    left. exists MLabs. trivial.
    assert (appBodyL Mapp -b-> appBodyL Napp -> appBodyL Mapp >> appBodyL Napp).
    apply beta_imp_horpo. apply algebraic_appBodyL; try_solve.
    assert (appBodyR Mapp -b-> appBodyR Napp -> appBodyR Mapp >> appBodyR Napp).
    apply beta_imp_horpo. apply algebraic_appBodyR; try_solve.
    right; exists Napp; fo.
  Qed.

  Lemma horpo_abs_reduct : forall M (Mabs: isAbs M) N, M >> N ->
    exists Nabs: isAbs N, absBody Mabs >> absBody Nabs.

  Proof.
    intros.
    destruct H.
    destruct H3; try solve [term_inv M; try_solve | destruct H3; try_solve].
    exists NAbs.
    constructor; trivial.
    term_inv M; term_inv N.
    term_inv M; term_inv N.
    apply algebraic_absBody; trivial.
    apply algebraic_absBody; trivial.
    rewrite (abs_proof_irr M Mabs MAbs); destruct H3; trivial.
    destruct (beta_abs_reduct Mabs H3); try_solve.
    exists x. apply beta_imp_horpo; try_solve.
    apply algebraic_absBody. hyp.
  Qed.

  Lemma horpo_args_conv : forall M N Ms Ns Q, M ~(Q) N ->
    (forall MsX, In MsX Ms -> env MsX = env M) ->
    (forall NsX, In NsX Ns -> env NsX = env N) ->
    conv_list Ms Ns Q ->
    (forall L L' R R', (subterm L M \/ (L = M /\ In R Ms)) ->
      L ~(Q) L' -> R ~(Q) R' -> L >> R -> env L' = env R' -> L' >> R'
    ) -> M [>>] Ms -> N [>>] Ns.

  Proof.
    induction Ms; intros Ns Q MN Ms_env Ns_env MsNs IH MMs.
    inversion MsNs.
    constructor.
    inversion MsNs.
    assert (IHrest: forall L L' R R',
      subterm L M \/ (L = M /\ In R Ms) ->
      L ~(Q) L' ->
      R ~(Q) R' ->
      L >> R ->
      env L' = env R' ->
      L' >> R').
    intros.
    apply IH with L R; trivial.
    destruct H4; auto.
    right; destruct H4; split; auto with datatypes.
    inversion MMs.
    constructor 2.
    apply IH with M a; auto with datatypes.
    rewrite <- (Ns_env y); trivial.
    rewrite <- H2; auto with datatypes.
    apply IHMs with Q; trivial.
    intros; apply Ms_env; auto with datatypes.
    intros; apply Ns_env; rewrite <- H2; auto with datatypes.
    constructor 3.
    destruct H7 as [M' M'arg M'ord].
    destruct (conv_arg M' MN) as [W [WN M'W]]; trivial.
    exists W; auto.
    destruct M'ord.
    constructor 1.
    apply IH with M1 N1; auto with datatypes.
    left; apply arg_subterm; trivial.
    rewrite (appUnit_env W N); auto with terms.
    sym; apply Ns_env; rewrite <- H2; auto with datatypes.
    replace W with y.
    constructor 2.
    apply term_eq.
    rewrite (appUnit_env W N); auto with terms.
    apply Ns_env; rewrite <- H2; auto with datatypes.
    apply conv_term_unique with (term M1) Q; fo.
    apply IHMs with Q; auto with datatypes.
    intros; apply Ns_env; rewrite <- H2; auto with datatypes.
  Qed.

  Lemma horpo_conv_comp_aux : forall M N M' N' Q,
    (forall L L' R R' Q, (subterm L M \/ (L = M /\ subterm R N)) ->
      L ~(Q) L' -> R ~(Q) R' -> L >> R -> env L' = env R' -> L' >> R'
    ) -> M ~(Q) M' -> N ~(Q) N' -> M >> N -> env M' = env N' -> M' >> N'.

  Proof.
    intros M N M' N' Q IH MM' NN' MN M'N'.
    destruct MN as [M N MNtype MNenv Mnorm Nnorm M_N].
    constructor; trivial.
    rewrite <- (terms_conv_eq_type (conv_by MM')),
      <- (terms_conv_eq_type (conv_by NN')).
    trivial.
    rewrite <- (conv_by MM'); trivial.
    rewrite <- (conv_by NN'); trivial.
    destruct M_N as 
      [ M N MFapp Cond 
      | M N f g Mf Ng f_g M_Nargs
      | M N f Mf Nf MNargs 
      | M N Ns Mfapp NsN MNs 
      | M N Mapp Napp Mnfapp Nnfapp LL 
      | M N Mabs Nabs MN 
      | M N MNbeta].

     (* case HSub *)
    destruct Cond as [Msub Msub_arg Cond].
    destruct (conv_arg Msub MM') as [Nsub [Nsub_arg MN]]; trivial.
    constructor 1.
    rewrite <- (conv_by MM'); trivial.
    exists Nsub; trivial.
    destruct Cond as [Msub N Msub_N | Msub].
    constructor.
    apply (IH Msub Nsub N N' Q); trivial.
    left; apply arg_subterm; trivial.
    rewrite (appUnit_env Nsub M'); auto with terms.
    replace N' with Nsub.
    constructor 2.
    apply term_eq.
    rewrite (appUnit_env Nsub M'); auto with terms.
    apply conv_term_unique with (term Msub) Q; fo.

     (* case HFun *)
    constructor 2 with f g; trivial.
    destruct (appHead_conv MM').
    rewrite Mf in H; inversion H; trivial.
    destruct (appHead_conv NN').
    rewrite Ng in H; inversion H; trivial.
    apply horpo_args_conv with M (appArgs N) Q; trivial.
    intros; rewrite (appUnit_env MsX N); auto with terms.
    intros; rewrite (appUnit_env NsX N'); auto with terms.
    apply appArgs_conv; trivial.
    intros.
    apply IH with L R Q; trivial.
    destruct H; auto.
    right; destruct H; split; trivial.
    apply arg_subterm; trivial.
  
     (* case HMul *)
    constructor 3 with f.
    destruct (appHead_conv MM').
    rewrite Mf in H; inversion H; trivial.
    destruct (appHead_conv NN').
    rewrite Nf in H; inversion H; trivial.
    constructor.
    assert (arg_env: forall x y, isArg x M' -> isArg y N' -> env x = env y).
    intros.
    rewrite (@appUnit_env x M'), (@appUnit_env y N'); trivial.
    apply appArg_is_appUnit; trivial.
    apply appArg_is_appUnit; trivial.
    apply mord_list_sim
      with (fun L R => L ~(Q) R) (appArgs M) (appArgs N); auto.
    apply horpo_eq_compat'.
    unfold order_compatible.
    intros; split; intro.
    apply IH with x y Q; try_solve.
    left; apply arg_subterm; trivial.
    apply term_eq; try_solve.
    apply conv_term_unique with (term y) Q.
    unfold eqA in H5; unfold TermsEqset.eqA in H5; rewrite <- H5.
    destruct H1; trivial.
    destruct H4; trivial.
    unfold eq_compat; intros.
    apply term_eq.
    rewrite (appUnit_env y M'), (appUnit_env y' N'); trivial.
    apply appArg_is_appUnit; trivial.
    apply appArg_is_appUnit; trivial.
    apply conv_term_unique with (term x) Q; destruct H2; destruct H3; trivial.
    apply appArgs_conv; trivial.
    apply appArgs_conv; trivial.
    inversion MNargs; trivial.

     (* case HAppFlat *)
    destruct (partialFlattening_conv Ns NN') as [Ns' [Ns'N' NsNs']]; trivial.
    constructor 4 with Ns'; trivial.
    rewrite <- (conv_by MM'); trivial.
    apply horpo_args_conv with M Ns Q; trivial.
    intros; rewrite (partialFlattening_env N Ns); auto.
    intros; rewrite (partialFlattening_env N' Ns'); auto.
    intros.
    apply IH with L R Q; trivial.
    destruct H; auto.
    right; destruct H; split; trivial.
    apply partialFlattening_subterm with Ns; trivial.

     (* HApp *)
    assert (M'app: isApp M').
    assert (MeqM' : M ~ M') by (exists Q; trivial).
    rewrite <- MeqM'; trivial.
    assert (N'app: isApp N').
    assert (NeqN' : N ~ N') by (exists Q; trivial).
    rewrite <- NeqN'; trivial.
    assert (L_L: appBodyL Mapp >> appBodyL Napp ->
      appBodyL M'app >> appBodyL N'app).
    intro MN.
    apply IH with (appBodyL Mapp) (appBodyL Napp) Q; trivial.
    left; apply appBodyL_subterm.
    apply app_conv_app_left_aux; trivial.
    apply app_conv_app_left_aux; trivial.
    autorewrite with terms using trivial.
    assert (R_R: appBodyR Mapp >> appBodyR Napp ->
      appBodyR M'app >> appBodyR N'app).
    intro MN.
    apply IH with (appBodyR Mapp) (appBodyR Napp) Q; trivial.
    left; apply appBodyR_subterm.
    apply app_conv_app_right_aux; trivial.
    apply app_conv_app_right_aux; trivial.
    autorewrite with terms using trivial.
    constructor 5 with M'app N'app.
    intro M'fapp.
    absurd (isFunApp M); trivial.
    assert (MeqM' : M ~ M') by (exists Q; trivial).
    rewrite MeqM'; trivial.
    intro N'fapp.
    absurd (isFunApp N); trivial.
    assert (NeqN' : N ~ N') by (exists Q; trivial).
    rewrite NeqN'; trivial.
    set (w := horpo_eq_compat).
    destruct (horpo_app M N Mapp Napp MNtype LL) as [left [right [Lred | Rred]]].
    constructor; apply pair_mOrd_left; trivial.
    apply horpo_eq_compat'.
    apply L_L; trivial.
    apply horpo_RC.
    inversion right.
    left; apply R_R; trivial.
    replace (appBodyR N'app) with (appBodyR M'app).
    right.
    apply term_eq.
    autorewrite with terms using trivial.
    apply conv_term_unique with (term (appBodyR Mapp)) Q.
    destruct (app_conv_app_right_aux Mapp M'app MM'); trivial.
    rewrite H1.
    destruct (app_conv_app_right_aux Napp N'app NN'); trivial.
    constructor; apply pair_mOrd_right; trivial.
    apply horpo_eq_compat'.
    apply horpo_RC.
    inversion left.
    left; apply L_L; trivial.
    replace (appBodyL N'app) with (appBodyL M'app).
    right.
    apply term_eq.
    autorewrite with terms using trivial.
    apply conv_term_unique with (term (appBodyL Mapp)) Q.
    destruct (app_conv_app_left_aux Mapp M'app MM'); trivial.
    rewrite H1.
    destruct (app_conv_app_left_aux Napp N'app NN'); trivial.
    apply R_R; trivial.

     (* HAbs *)
    assert (M'abs: isAbs M').
    assert (MeqM' : M ~ M') by (exists Q; trivial).
    rewrite <- MeqM'; trivial.
    assert (N'abs: isAbs N').
    assert (NeqN' : N ~ N') by (exists Q; trivial).
    rewrite <- NeqN'; trivial.
    constructor 6 with M'abs N'abs.
    apply IH with (absBody Mabs) (absBody Nabs) (envSubst_lift1 Q); trivial.
    left; apply absBody_subterm.
    apply abs_conv_absBody_aux; trivial.
    apply abs_conv_absBody_aux; trivial.
    apply absBody_eq_env; trivial.
    rewrite <- (terms_conv_eq_type (conv_by MM')),
      <- (terms_conv_eq_type (conv_by NN')).
    trivial.

     (* HBeta *)
    apply HBeta. 
    apply beta_conv_comp with M N Q; trivial.
  Qed.

  Lemma horpo_conv_comp : forall M N M' N' Q,
    M ~(Q) M' -> N ~(Q) N' -> M >> N -> env M' = env N' -> M' >> N'.

  Proof.
    intros M N.
    assert (Res: forall P M' N' Q,
      (fst P) ~(Q) M' ->
      (snd P) ~(Q) N' ->
      fst P >> snd P ->
      env M' = env N' ->
      M' >> N').
    intro P.
    apply well_founded_ind with
      (R := LexProd_Lt)
      (P := fun P =>
         forall M' N' Q,
	   (fst P) ~(Q) M' ->
	   (snd P) ~(Q) N' ->
	   fst P >> snd P ->
	   env M' = env N' ->
	   M' >> N').
    apply lexprod_wf.
    unfold ltL, gtR, subterm_gt.
    rewrite transp_invol.
    apply subterm_wf.
    unfold ltR, gtR, subterm_gt.
    rewrite transp_invol.
    apply subterm_wf.
    clear M N P.
    intros P IH M' N' Q MM' NN' MN M'N'.
    destruct P as [M N]; simpl in * .
    apply horpo_conv_comp_aux with M N Q; trivial.
    intros.
    apply IH with (L, R) Q0; trivial.
    destruct H.
    constructor; exact H.
    destruct H; rewrite H.
    constructor 2; trivial.
    auto with sets.
    intros.
    apply Res with (M, N) Q; trivial.
  Qed.

  Lemma horpo_args_subst : forall M Ms Ns G (MG: correct_subst M G),
    subst_list Ms Ns G ->
    (forall L R (CL: correct_subst L G) (CR: correct_subst R G),
      (subterm L M \/ (L = M /\ In R Ms)) ->  L >> R -> subst CL >> subst CR) ->
    M [>>] Ms -> subst MG [>>] Ns.

  Proof.
    induction Ms; intros Ns G MG MsNs IH MMs.
    inversion MsNs.
    constructor 1.
    inversion MsNs.
    assert (rest: subst MG [>>] ys).
    apply IHMs.
    inversion MMs; trivial.
    intros.
    apply IH; trivial.
    inversion H4.
    left; trivial.
    right; inversion H6; auto with datatypes.
    inversion MMs; trivial.

    inversion H1.
    inversion MMs.
    constructor 2; trivial.
    rewrite H4.
    apply IH; trivial.
    auto with datatypes.

    constructor 3; trivial.
    destruct H8 as [Marg Marg_arg Marg_a].
    destruct (subst_arg Marg MG Marg_arg) as [M'arg [M'arg_arg [MargG M'argG]]].
    exists M'arg; trivial.
    inversion Marg_a.
    constructor.
    rewrite M'argG, H4.
    apply IH; trivial.
    left; apply arg_subterm; trivial.
    replace M'arg with y.
    constructor 2.
    rewrite M'argG, H4.
    apply term_eq.
    autorewrite with terms; rewrite H10; trivial.
    autorewrite with terms; rewrite H10; trivial.
  Qed.

  Lemma horpo_subst_stable_aux : forall M N G (MG: correct_subst M G)
    (NG: correct_subst N G), algebraicSubstitution G ->
    (forall L R G (LG: correct_subst L G) (RG: correct_subst R G),
      algebraicSubstitution G -> (subterm L M \/ (L = M /\ subterm R N)) ->
      L >> R -> subst LG >> subst RG) ->
    M >> N -> subst MG >> subst NG.

  Proof.
    intros M N G MG NG Gnorm IH MN.
    destruct MN as [M N MNtype MNenv Mnorm Nnorm M_N].
    constructor; trivial.
    autorewrite with terms; trivial.
    autorewrite with terms; congruence.
    apply algebraic_subst; trivial.
    apply algebraic_subst; trivial.
    destruct M_N as 
      [ M N MFapp Cond 
      | M N f g Mf Ng f_g M_Nargs
      | M N f Mf Nf MNargs 
      | M N Ns Mfapp NsN MNs 
      | M N Mapp Napp Mnfapp Nnfapp LL 
      | M N Mabs Nabs MN 
      | M N MNbeta].

     (* case HSub *)
    destruct Cond as [Msub Msub_arg Cond].    
    constructor 1.
    apply funApp_subst_funApp; trivial.
    destruct (subst_arg Msub MG Msub_arg)
      as [M'sub [M'sub_arg [M'subG M'sub_def]]].
    exists M'sub; trivial.
    destruct Cond as [Msub N Msub_N | Msub].
    constructor.
    rewrite M'sub_def.
    apply IH; trivial.
    left; apply arg_subterm; trivial.
    replace (subst NG) with M'sub.
    constructor 2.
    rewrite M'sub_def.
    apply term_eq.
    autorewrite with terms; congruence.
    autorewrite with terms; trivial.

     (* case HFun *)
    constructor 2 with f g; trivial.
    apply funS_headS_subst; trivial.
    apply funS_headS_subst; trivial.
    apply horpo_args_subst with (appArgs N); trivial.
    apply subst_list_args.
    apply funS_is_funS with g; trivial.
    intros.
    apply IH; trivial.
    destruct H; auto.
    right; destruct H; split; trivial.
    apply arg_subterm; trivial.

     (* case HMul *)
    constructor 3 with f.
    apply funS_headS_subst; trivial.
    apply funS_headS_subst; trivial.
    constructor.
    set (P := fun L R => exists LG: correct_subst L G, R = subst LG).
    apply mord_list_sim with P (appArgs M) (appArgs N); auto.
    apply horpo_eq_compat'.
    unfold order_compatible; intros.
    inversion H1; inversion H4.
    rewrite H5, H6.
    split; intros.
    apply IH; trivial.
    left; apply arg_subterm; trivial.
    unfold eqA in H7; unfold TermsEqset.eqA in H7.
    apply term_eq; autorewrite with terms using try rewrite H7; trivial.
    unfold eq_compat; intros.
    destruct H2; rewrite H2.
    destruct H3; rewrite H3.
    apply term_eq; autorewrite with terms using trivial.
    unfold P; apply subst_list_args.
    apply funS_is_funS with f; trivial.
    unfold P; apply subst_list_args.
    apply funS_is_funS with f; trivial.
    inversion MNargs; trivial.

     (* case HAppFlat *)
    destruct (subst_list_partialFlattening Ns NG NsN) as [Ns' [Ns'N' NsNs']].
    constructor 4 with Ns'; trivial.
    apply funApp_subst_funApp; trivial.
    apply horpo_args_subst with Ns; trivial.
    intros.
    apply IH; trivial.
    destruct H; auto.
    right; destruct H; split; trivial.
    apply partialFlattening_subterm with Ns; trivial.

     (* HApp *)
    set (M'app := app_subst_app Mapp MG).
    set (N'app := app_subst_app Napp NG).
    destruct (app_subst Mapp MG) as [ML MR].
    destruct (app_subst Napp NG) as [NL NR].
    assert (L_L: appBodyL Mapp >> appBodyL Napp ->
      appBodyL M'app >> appBodyL N'app).
    intro MN.
    unfold M'app; rewrite ML.
    unfold N'app; rewrite NL.
    apply IH; trivial.
    left; apply appBodyL_subterm.
    assert (R_R: appBodyR Mapp >> appBodyR Napp ->
      appBodyR M'app >> appBodyR N'app).
    intro MN.
    unfold M'app; rewrite MR.
    unfold N'app; rewrite NR.
    apply IH; trivial.
    left; apply appBodyR_subterm.
    constructor 5 with M'app N'app.
    apply notFunApp_subst; trivial.
    apply notFunApp_subst; trivial.
    set (w := horpo_eq_compat).
    destruct (horpo_app M N Mapp Napp MNtype LL) as [LrL [RrR [Ls | Rs]]].
    constructor; apply pair_mOrd_left; trivial.
    apply horpo_eq_compat'.
    apply L_L; trivial.
    inversion RrR.
    left; trivial.
    apply R_R; trivial.
    right; apply term_eq.
    autorewrite with terms; rewrite MNenv; trivial.
    destruct (app_subst Mapp MG).
    rewrite (app_proof_irr (subst MG) M'app (app_subst_app Mapp MG)), H2.
    destruct (app_subst Napp NG).
    rewrite (app_proof_irr (subst NG) N'app (app_subst_app Napp NG)), H4.
    autorewrite with terms; rewrite H1; trivial.
    constructor; apply pair_mOrd_right; trivial.
    apply horpo_eq_compat'.
    inversion LrL.
    left; trivial.
    apply L_L; trivial.
    right; apply term_eq.
    autorewrite with terms; rewrite MNenv; trivial.
    destruct (app_subst Mapp MG).
    rewrite (app_proof_irr (subst MG) M'app (app_subst_app Mapp MG)), H0.
    destruct (app_subst Napp NG).
    rewrite (app_proof_irr (subst NG) N'app (app_subst_app Napp NG)), H3.
    autorewrite with terms; rewrite H1; trivial.
    apply R_R; trivial.

     (* HAbs *)
    constructor 6 with (abs_subst_abs Mabs MG) (abs_subst_abs Nabs NG).
    destruct (abs_subst Mabs MG) as [M'type M'body].
    destruct (abs_subst Nabs NG) as [N'type N'body].
    rewrite M'body, N'body.
    apply IH; trivial.
    apply algebraicSubstitution_cons_none.
    apply algebraicSubstitution_lifted; trivial.
    left; apply absBody_subterm.

     (* HBeta *)
    apply HBeta. apply beta_subst_stable. hyp.
  Qed.

  Lemma horpo_subst_stable : forall M N G (MS: correct_subst M G)
    (NS: correct_subst N G),
    algebraicSubstitution G -> M >> N -> subst MS >> subst NS.

  Proof.
    intros M N.
    assert (Res: forall P G (MS: correct_subst (fst P) G)
      (NS: correct_subst (snd P) G),
      algebraicSubstitution G ->
      fst P >> snd P ->
      subst MS >> subst NS).
    intro P.
    apply well_founded_ind with
      (R := LexProd_Lt)
      (P := fun P =>
         forall G (MS: correct_subst (fst P) G) (NS: correct_subst (snd P) G),
	   algebraicSubstitution G ->
	   fst P >> snd P ->
	   subst MS >> subst NS).
    apply lexprod_wf.
    unfold ltL, gtR, subterm_gt.
    rewrite transp_invol.
    apply subterm_wf.
    unfold ltR, gtR, subterm_gt.
    rewrite transp_invol.
    apply subterm_wf.
    clear M N P.
    intros P IH G MG NG Gnorm MN.
    destruct P as [M N]; simpl in * .
    apply horpo_subst_stable_aux; trivial.
    intros.
    apply (IH (L, R)); trivial.
    destruct H0.
    constructor; exact H0.
    destruct H0; rewrite H0.
    constructor 2; trivial.
    auto with sets.
    intros.
    apply (Res (M, N) G); trivial.
  Qed.

  Lemma horpo_args_var_consistent : forall M Ns,
    (forall L R, (subterm L M \/ (L = M /\ In R Ns)) -> L >> R ->
      envSubset (activeEnv R) (activeEnv L)) ->
    M [>>] Ns -> forall N', In N' Ns -> envSubset (activeEnv N') (activeEnv M).

  Proof.
    induction Ns; intros IH MNs N' N'Ns.    
    inversion N'Ns.
    inversion N'Ns.
    inversion MNs; rewrite <- H.
    apply IH; trivial.
    right; auto with datatypes.
    destruct H3.
    apply env_subset_trans with (activeEnv x).
    inversion H5.
    apply IH; trivial.
    left; apply arg_subterm; trivial.
    apply env_subset_refl.
    apply activeEnv_subset_arg; trivial.
    apply IHNs; trivial.
    intros; apply IH; trivial.
    destruct H0; auto.
    right; destruct H0; split; auto with datatypes.
    inversion MNs; trivial.
  Qed.

  Lemma horpo_var_consistent_aux : forall M N,
    (forall M' N', (subterm M' M \/ (M' = M /\ subterm N' N)) ->
      M' >> N' -> envSubset (activeEnv N') (activeEnv M')) ->
    M >> N -> envSubset (activeEnv N) (activeEnv M).

  Proof.
    intros M N IH MN.
    destruct MN as [M N MNtype MNenv Mnorm Nnorm M_N].
    destruct M_N as 
      [ M N MFapp Cond 
      | M N f g Mf Ng f_g M_Nargs
      | M N f Mf Nf MNargs 
      | M N Ns Mfapp NsN MNs 
      | M N Mapp Napp Mnfapp _ LL 
      | M N Mabs Nabs MN 
      | M N MNbeta].

     (* case HSub *)
    destruct Cond as [Msub Msub_arg Cond].
    destruct Cond.
    apply env_subset_trans with (activeEnv M0).
    apply IH; trivial.
    left; apply arg_subterm; trivial.
    apply activeEnv_subset_arg; trivial.
    apply activeEnv_subset_arg; trivial.

     (* case HFun *)
    apply activeEnv_subset_units; intros.
    destruct (appUnit_head_or_arg N N' H).
    rewrite (activeEnv_funS).
    apply env_subset_empty.
    apply funS_is_funS with g; rewrite H0; trivial.
    apply horpo_args_var_consistent with (appArgs N); trivial.
    intros.
    apply IH; trivial.
    destruct H1; auto.
    right; destruct H1; split; trivial.
    apply arg_subterm; trivial.
  
     (* case HMul *)
    apply activeEnv_subset_units; intros.
    destruct (appUnit_head_or_arg N N' H).
    rewrite (activeEnv_funS).
    apply env_subset_empty.
    apply funS_is_funS with f; rewrite H0; trivial.
    inversion MNargs.
    set (N'mul := member_list_multiset (appArgs N) N' H0).
    destruct (mOrd_elts_ge H1 N'mul).
    destruct H5.
    apply env_subset_trans with (activeEnv x).
    apply IH; trivial.
    destruct (member_multiset_list (appArgs M) H4).
    left; apply arg_subterm.
    unfold eqA in H7; unfold TermsEqset.eqA in H7; rewrite H7; trivial.
    apply activeEnv_subset_arg.
    destruct (member_multiset_list (appArgs M) H4).
    inversion H7; apply H6.    
    inversion H5; rewrite <- H6.
    apply activeEnv_subset_arg.
    destruct (member_multiset_list (appArgs M) H4).
    inversion H8; apply H7.

     (* case HAppFlat *)
    apply activeEnv_subset_partialFlattening with Ns; trivial; intros.
    apply horpo_args_var_consistent with Ns; trivial.
    intros.
    apply IH; trivial.
    destruct H0; auto.
    right; destruct H0; split; trivial.
    apply partialFlattening_subterm with Ns; trivial.

     (* HApp *)
    rewrite (activeEnv_app M Mapp), (activeEnv_app N Napp).
    destruct (horpo_app M N Mapp Napp MNtype LL) as [L_L [R_R str]].
    apply env_subset_sum.
    apply activeEnv_app_comp.
    inversion L_L.
    apply IH; trivial.
    left; apply appBodyL_subterm.
    rewrite H1; apply env_subset_refl.
    inversion R_R.
    apply IH; trivial.
    left; apply appBodyR_subterm.
    rewrite H1; apply env_subset_refl.

     (* HAbs *)
    rewrite activeEnv_abs with M Mabs, activeEnv_abs with N Nabs.
    apply env_subset_tail.
    apply IH; trivial.
    left; apply absBody_subterm.

     (* HBeta *)
    apply beta_var_consistent. hyp.
  Qed.

  Lemma horpo_var_consistent : forall M N,
    M >> N -> envSubset (activeEnv N) (activeEnv M).

  Proof.
    intros M N.
    assert (Res: forall P,
      fst P >> snd P ->
      envSubset (activeEnv (snd P)) (activeEnv (fst P))).
    intro P.
    apply well_founded_ind with
      (R := LexProd_Lt)
      (P := fun P =>
	fst P >> snd P ->
	envSubset (activeEnv (snd P)) (activeEnv (fst P))).
    apply lexprod_wf.
    unfold ltL, gtR, subterm_gt.
    rewrite transp_invol.
    apply subterm_wf.
    unfold ltR, gtR, subterm_gt.
    rewrite transp_invol.
    apply subterm_wf.
    clear M N P.
    intros P IH MN.
    destruct P as [M N]; simpl in * .
    apply horpo_var_consistent_aux; trivial.
    intros.
    apply (IH (M', N')).
    destruct H.
    constructor; exact H.
    destruct H; rewrite H.
    constructor 2; trivial.
    auto with sets.
    simpl; trivial.
    intros.
    apply (Res (M, N)); trivial.
  Qed.

  Lemma horpoArgs_dec : forall M Ns,
    (forall Marg N, subterm Marg M -> {Marg >>= N} + {~Marg >>= N}) ->
    (forall N, In N Ns -> {M >> N} + {~M >> N}) -> {M [>>] Ns} + {~M [>>] Ns}.

  Proof.
    induction Ns; intros.
    left; constructor.
    destruct IHNs; trivial.
    intros.
    destruct (X0 N); auto with datatypes.
    destruct (X0 a); auto with datatypes.
    left; constructor 2; trivial.
    destruct (many_one_dec horpoRC (appArgs M) a)
      as [[Marg [MMarg MargN]] | noSub].
    intros.
    destruct (X x a); try_solve.
    apply arg_subterm; trivial.
    left; constructor 3; trivial.
    exists Marg; trivial.
    right; intro MaNs; inversion MaNs; try_solve.
    destruct H2.
    apply (noSub x); trivial.
    right; intro MaNs; inversion MaNs; try_solve.
  Qed.

  Section ClausesDec.

    Variables M N : Term.
    Variable IH : forall L R,
      (subterm L M \/ (L = M /\ subterm R N)) -> {L >> R} + {~L >> R}.
    Variable Mfa : isFunApp M.

    Lemma IH_horpoRC : forall L R, (subterm L M \/ (L = M /\ subterm R N)) ->
      {L >>= R} + {~L >>= R}.

    Proof.
      intros.
      destruct (@IH L R); trivial.
      left; left; trivial.
      destruct (eq_Term_dec L R).
      left; rewrite e; right.
      right; intro LR; inversion LR; try_solve.
    Qed.

    Let Psub := exists2 M', isArg M' M & M' >>= N.
    Lemma HSub_dec : { Psub } + { ~Psub }.

    Proof.
      intros; unfold Psub.
      destruct (many_one_dec horpoRC (appArgs M) N)
        as [[Marg [MMarg MargN]] | noSub].
      intros.
      apply IH_horpoRC; left; apply arg_subterm; trivial.
      left; exists Marg; trivial.
      right; intro sub; destruct sub.
      absurd (x >>= N); trivial.
      apply noSub; trivial.
    Qed.

    Lemma HAppFlat_dec : {Ns : list Term | isPartialFlattening Ns N & M [>>] Ns}
      + {~exists2 Ns: list Term, isPartialFlattening Ns N & M [>>] Ns }.

    Proof.
      intros.
      destruct (isApp_dec N).
      destruct (allPartialFlattenings N) as [Npf Npf_ok]; trivial.
      destruct (many_one_dec (fun N M => M[>>]N) Npf M)
        as [[Np [NpNpf MNp]] | No_pf]; trivial.
      intros.
      apply horpoArgs_dec.
      intros; apply IH_horpoRC; left; trivial.
      intros; apply IH; right; split; trivial.
      apply (partialFlattening_subterm N x); trivial.
      apply (proj2 (Npf_ok x)); trivial.
      left; exists Np; trivial.
      apply (proj2 (Npf_ok Np)); trivial.
      right; intro flat; destruct flat.
      absurd (M [>>] x); trivial.
      apply No_pf; trivial.
      apply (proj1 (Npf_ok x)); trivial.
      right; intro Ns.
      destruct Ns.
      apply n.
      apply partialFlattening_app with x; trivial.
    Qed.

    Lemma HMul_dec : { f: FunctionSymbol | term (appHead M) = ^f
      /\ term (appHead N) = ^f /\
         list2multiset (appArgs M) {>>} list2multiset (appArgs N)} +
      { term (appHead M) <> term (appHead N) \/
        ~list2multiset (appArgs M) {>>} list2multiset (appArgs N) }.

    Proof.
      intros.
      destruct (funApp_head M Mfa).
      destruct (isFunApp_dec N) as [Nfa | Nnfa].
      destruct (funApp_head N Nfa).
      destruct (eq_FunctionSymbol_dec x x0).
      destruct (@mOrd_dec_aux horpo horpo_eq_compat'
                              (list2multiset (appArgs M)) 
	                      (list2multiset (appArgs N))); trivial.
      intros.
      apply IH.
      left; apply arg_subterm.
      destruct (member_multiset_list (appArgs M) H) as [w wM mw].
      unfold eqA in mw; unfold TermsEqset.eqA in mw; rewrite mw; trivial.
      left; exists x; repeat split; trivial.
      rewrite e1; trivial.
      right; right.
      intro MN; apply n.
      inversion MN; trivial.
      right; left; try_solve.
      unfold isFunApp in Nnfa.
      right; left.
      term_inv (appHead N).
    Qed.

    Lemma HFun_dec: { fg: FunctionSymbol * FunctionSymbol |
      term (appHead M) = ^(fst fg) /\ 
      term (appHead N) = ^(snd fg) /\ fst fg >#> snd fg /\ M [>>] (appArgs N)}
    + { ~isFunApp N \/ (forall f g, term (appHead M) = ^f ->
      term (appHead N) = ^g -> ~f >#> g) \/ ~M [>>] (appArgs N) }.

    Proof.
      intros.
      destruct (funApp_head M Mfa).
      destruct (isFunApp_dec N) as [Nfa | Nnfa].
      destruct (funApp_head N Nfa).
      destruct (Prec.Ord_dec x x0).
      destruct (@horpoArgs_dec M (appArgs N)).
      intros; apply IH_horpoRC; left; trivial.
      intros; apply IH; right; split; trivial.
      apply arg_subterm; trivial.
      left; exists (x, x0); repeat split; trivial.
      right; right; right; trivial.
      right; right; left; intros.
      rewrite e in H; rewrite e0 in H0.
      inversion H; inversion H0.
      rewrite <- H2; rewrite <- H3; trivial.
      right; left; trivial.
    Qed.

  End ClausesDec.

  Lemma prehorpo_dec : forall M N,
    (forall L R, (subterm L M \/ (L = M /\ subterm R N)) ->
      {L >> R} + {~L >> R}) -> env M = env N -> type M = type N ->
    algebraic M -> algebraic N -> {M >-> N} + {~ M >-> N}.

  Proof.
    intros M N IH MNenv MNtype Malg Nalg.
    assert (IHeq: forall L R,
      (subterm L M \/ (L = M /\ subterm R N)) ->
      {L >>= R} + {~L >>= R}
    ).
    intros.
    destruct (IH L R); trivial.
    left; constructor; trivial.
    destruct (eq_Term_dec L R).
    rewrite e; left; constructor 2.
    right; intro LR; destruct LR; auto.
    destruct (beta_dec M N). left. apply HBeta. hyp.
    destruct (isFunApp_dec M).
     (* fun. app *)
    destruct (@HSub_dec M N); trivial.
    left; apply HSub; trivial.
    destruct (@HAppFlat_dec M N); trivial.
    destruct s as [Ns NsN MNs].
    left; apply HAppFlat with Ns; trivial.
    destruct (@HMul_dec M N); trivial.
    destruct s as [f [Mf [Nf MNargs]]].
    left; apply HMul with f; trivial.
    destruct (@HFun_dec M N); trivial.
    destruct s as [[f g] [Mf [Ng [fg MNargs]]]].
    left; apply HFun with f g; trivial.
    right; intro MN; inversion MN; try_solve.
    destruct o0 as [Nnfa | [abs | MargsN]]; try_solve.
    absurd (isFunApp N); trivial.
    unfold isFunApp; apply funS_is_funS with g; trivial.
    absurd (f >#> g); auto.
    destruct o; try_solve.
    apply n1; exists Ns; trivial.
    term_inv M.
    destruct (term_case M) as [[[Mvar | Mfuns] | Mabs] | Mapp].
     (* variable *)
    right.
    apply prehorpo_var_normal; simpl; trivial.
     (* function symbol *)
    absurd (isFunApp M); trivial.
    term_inv M.
     (* abstraction *)
    destruct (isAbs_dec N) as [Nabs | Nnabs].
    destruct (IH (absBody Mabs) (absBody Nabs)).
    left; apply absBody_subterm.
    left; apply HAbs with Mabs Nabs; trivial.
    right; intro TrN.
    inversion TrN; term_inv M. 
    apply n1; trivial.
    rewrite (abs_proof_irr N Nabs NAbs); trivial.
    right; intro TrN.
    inversion TrN; term_inv M.
     (* application *)    
    assert (forall f, term (appHead M) = ^f -> False).
    intros; apply n0; unfold isFunApp.
    apply funS_is_funS with f; trivial.
    destruct (isApp_dec N) as [Napp | Nnapp].
    destruct (isFunApp_dec N) as [Nfapp | Nnfapp].
    right. intro MN.
    inversion MN; try solve [term_inv M; apply H with f; trivial].
    destruct (IHeq (appBodyL Mapp) (appBodyL Napp)).
    left; apply appBodyL_subterm.
    destruct (IHeq (appBodyR Mapp) (appBodyR Napp)).
    left; apply appBodyR_subterm.
    destruct (IH (appBodyL Mapp) (appBodyL Napp)).
    left; apply appBodyL_subterm.
    left; apply HApp with Mapp Napp; trivial.
    constructor; apply pair_mOrd_left; trivial.
    apply horpo_eq_compat'.
    destruct h0; [left | right]; auto with sets.
    destruct (IH (appBodyR Mapp) (appBodyR Napp)).
    left; apply appBodyR_subterm.
    left; apply HApp with Mapp Napp; trivial.
    constructor; apply pair_mOrd_right; trivial.
    apply horpo_eq_compat'.
    destruct h; [left | right]; auto with sets.
    right; intro TrN.
    inversion TrN; try solve [term_inv M; apply H with f; trivial].
    destruct (horpo_app M N MApp NApp MNtype) as [_ [_ [LL | RR]]]; trivial.
    apply n1; trivial.
    rewrite (app_proof_irr M Mapp MApp), (app_proof_irr N Napp NApp); trivial.
    apply n2; trivial.
    rewrite (app_proof_irr M Mapp MApp), (app_proof_irr N Napp NApp); trivial.
    right; intro TrN.
    inversion TrN; try solve [term_inv M; apply H with f; trivial].
    destruct (horpo_app M N MApp NApp MNtype) as [_ [RR _]]; trivial.
    apply n1.
    rewrite (app_proof_irr M Mapp MApp), (app_proof_irr N Napp NApp); trivial.
    right; intro TrN.
    inversion TrN; try solve [term_inv M; apply H with f; trivial].
    destruct (horpo_app M N MApp NApp MNtype) as [LL [_ _]]; trivial.
    apply n1.
    rewrite (app_proof_irr M Mapp MApp), (app_proof_irr N Napp NApp); trivial.
    right; intro TrN.
    inversion TrN; try solve [term_inv M; apply H with f; trivial].
  Qed.

  Lemma horpo_dec: forall M N, {M >> N} + {~ M >> N}.

  Proof.
    intros M N.
    assert (Res: forall P, {fst P >> snd P} + {~fst P >> snd P}).
    intro P.
    apply well_founded_induction_type with
      (R := LexProd_Lt)
      (P := fun P => {fst P >> snd P} + {~fst P >> snd P}).
    apply lexprod_wf.
    unfold ltL, gtR, subterm_gt.
    rewrite transp_invol.
    apply subterm_wf.
    unfold ltR, gtR, subterm_gt.
    rewrite transp_invol.
    apply subterm_wf.
    clear M N P.
    intros P. destruct P as [M N]; simpl; intro IH.
    destruct (eq_SimpleType_dec (type M) (type N)).
    destruct (eq_Env_dec (env M) (env N)).
    destruct (algebraic_dec M).
    destruct (algebraic_dec N).
    destruct (@prehorpo_dec M N); trivial.
    intros.
    destruct (IH (L, R)).
    destruct H.
    left; trivial.
    right; destruct H; simpl; trivial.
    rewrite H; auto with sets.
    left; trivial.
    right; trivial.
    left; constructor; trivial.
    right; intro MN; inversion MN; try_solve.
    right; intro MN; inversion MN; try_solve.
    right; intro MN; inversion MN; try_solve.
    right; intro MN; inversion MN; try_solve.
    right; intro MN; inversion MN; try_solve.
    destruct (Res (M, N)); auto.
  Qed.

  Lemma horpo_monotonous : algebraic_monotonicity horpo.

  Proof.
    apply algebraic_monotonicity_criterion; intros.
    unfold appMonCond; intros.
    destruct H1 as [P | [P | P]].

     (* not fun app. L *)
    destruct P as [Mnfa [M'nfa [L_red R_eq]]].
    constructor; trivial.
    apply app_type_eq with Mapp M'app; try_solve.
    apply horpo_type_preserving; trivial.
    rewrite <- (appBodyR_env M Mapp), <- (appBodyR_env M' M'app).
    try_solve.
    apply HApp with Mapp M'app; trivial.
    constructor; apply pair_mOrd_left; trivial.
    apply horpo_eq_compat'.
    right; trivial.

     (* not fun app. R *)
    destruct P as [Mnfa [M'nfa [L_eq R_red]]].
    constructor; trivial.
    apply app_type_eq with Mapp M'app; try_solve.
    apply horpo_type_preserving; trivial.
    rewrite <- (appBodyR_env M Mapp), <- (appBodyR_env M' M'app).
    apply horpo_env_preserving; trivial.
    apply HApp with Mapp M'app; trivial.
    constructor; apply pair_mOrd_right; trivial.
    apply horpo_eq_compat'.
    right; trivial.

     (* fun app. *)
    destruct P as [Mfa [MM'head [l [m [m' [Margs [M'args mm']]]]]]].
    constructor; trivial.
    apply eq_unitTypes_eq_types.
    rewrite (app_units_app M Mapp), (app_units_app M' M'app).
    simpl; rewrite Margs, M'args, !length_app; trivial.
    intros.
    rewrite (app_units_app M Mapp) in H1.
    rewrite (app_units_app M' M'app) in H2.
    destruct p.
    inversion H1; inversion H2.
    rewrite MM'head; trivial.
    simpl in H1; simpl in H2.
    rewrite Margs in H1.
    rewrite M'args in H2.
    destruct (Compare_dec.le_lt_dec (length (fst l)) p).
    rewrite nth_app_right in H1; trivial.
    rewrite nth_app_right in H2; trivial.
    destruct ((p - length (fst l))%nat).
    inversion H1; inversion H2.
    rewrite <- H4, <- H5.
    apply horpo_type_preserving; trivial.
    inversion H1; inversion H2; try_solve.
    rewrite nth_app_left in H1; trivial.
    rewrite nth_app_left in H2; trivial.
    inversion H1; inversion H2; try_solve.
    rewrite <- (@appUnit_env m M), <- (@appUnit_env m' M').
    apply horpo_env_preserving; trivial.
    apply appArg_is_appUnit.
    unfold isArg; rewrite M'args; auto with datatypes.
    apply appArg_is_appUnit.
    unfold isArg; rewrite Margs; auto with datatypes.
    destruct (funApp_head M Mfa).
    apply HMul with x; trivial.
    rewrite <- MM'head; trivial.
    rewrite Margs, M'args.
    constructor; apply mulOrd_oneElemDiff; trivial.
    apply horpo_eq_compat'.

     (* Abs *)
    unfold absMonCond; intros.
    constructor; trivial.
    apply abs_type_eq with Nabs N'abs; trivial.
    apply horpo_type_preserving; trivial.
    set (w := horpo_env_preserving H2).
    rewrite !absBody_env in w.
    inversion w; trivial.
    apply AlgAbs with Nabs; trivial.
    apply AlgAbs with N'abs; trivial.
    apply HAbs with Nabs N'abs; trivial.
  Qed.

  #[global] Hint Resolve horpo_prehorpo horpo_type_preserving horpo_eq_compat
    horpo_env_preserving horpo_algebraic_preserving horpo_var_normal 
    horpo_app_reduct horpo_abs_reduct horpo_monotonous horpo_conv_comp 
    horpo_subst_stable horpo_var_consistent : horpo.

End Horpo.
