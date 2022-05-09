(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Some computability results instantiated for horpo.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras Computability Horpo.
From Coq Require Import Setoid Morphisms.

Module HorpoComp (S : TermsSig.Signature)
  (Prec : Horpo.Precedence with Module S := S).

  Module Export Comp := Computability.Computability S Prec.

  Import List.

  Definition horpo_lt := transp horpo.
  Definition horpo_mul_lt := MultisetLT horpo.
  
  Notation "X << Y" := (horpo_lt X Y) (at level 55).
  Definition Htrans := clos_trans horpo.

  Definition Terms := list Term.
  Definition CompH := Computable horpo.
  Definition CompTerms (Ts: Terms) := AllComputable horpo Ts.
  Definition CompSubst (G: Subst) := forall Q, In (Some Q) G -> CompH Q.

  Definition WFterms := { Ts: Terms | CompTerms Ts }.
  Definition WFterms_to_mul (Ts: WFterms) := list2multiset (proj1_sig Ts).
  Coercion WFterms_to_mul: WFterms >-> Multiset.
  Definition H_WFterms_lt (M N: WFterms) := horpo_mul_lt M N.

  #[global] Hint Unfold horpo_lt horpo_mul_lt CompH CompTerms : horpo.

  Lemma horpo_comp_imp_acc M : CompH M -> AccR horpo M.

  Proof. intro Mcomp. apply comp_imp_acc; eauto with horpo. Qed.

  Lemma horpo_comp_step_comp M N : CompH M -> M >> N -> CompH N.

  Proof.
    intros Mcomp MN.
    unfold CompH; apply comp_step_comp with M; eauto with horpo.
  Qed.

  Lemma horpo_comp_manysteps_comp M N : CompH M -> M >>* N -> CompH N.

  Proof.
    intros Mcomp M_N.
    unfold CompH; apply comp_manysteps_comp with M; eauto with horpo.
  Qed.

  Lemma horpo_comp_pflat N Ns : isPartialFlattening Ns N -> algebraic N ->
    AllComputable horpo Ns -> CompH N.

  Proof.
    intros NsN Nnorm NsC; unfold CompH. apply comp_pflat with Ns; trivial.
  Qed.

  Lemma horpo_neutral_comp_step : forall M, algebraic M -> isNeutral M ->
    (CompH M <-> (forall N, M >> N -> CompH N)).

  Proof.
    intros M Mneutral; unfold CompH.
    apply neutral_comp_step; eauto with horpo.
  Qed.

  Lemma CompH_morph_aux : forall x1 x2 : Term, x1 ~ x2 -> CompH x1 -> CompH x2.

  Proof.
    intros t t' teqt' H_t.
    unfold CompH.
    apply Computable_morph_aux with t; eauto with horpo.
  Qed.

  #[global] Instance CompH_morph : Proper (terms_conv ==> iff) CompH.

  Proof.
    intros; split; apply CompH_morph_aux; auto using terms_conv_sym.
  Qed.

  Lemma horpo_comp_conv: forall M M', CompH M -> M ~ M' -> CompH M'.

  Proof. intros. rewrite <- H0; trivial. Qed.

  Lemma horpo_var_comp : forall M, isVar M -> CompH M.

  Proof.
    intros M Mvar; unfold CompH. apply var_comp; eauto with horpo.
  Qed.

  Lemma horpo_comp_abs : forall M (Mabs: isAbs M), algebraic M ->
    (forall G (cs: correct_subst (absBody Mabs) G) T, 
      isSingletonSubst T G -> CompH T ->
      CompH (subst cs)) -> CompH M.

  Proof.
    intros M Mnorm Mabs H; unfold CompH. eapply comp_abs; eauto with horpo.
  Qed.

  Lemma horpo_comp_lift : forall N, CompH N -> CompH (lift N 1).

  Proof.
    intros.
    setoid_replace (lift N 1) with N using relation terms_conv; trivial.
    apply terms_conv_sym; apply terms_lift_conv.
  Qed.

  Lemma horpo_comp_app : forall M (Mapp: isApp M), 
    CompH (appBodyL Mapp) -> CompH (appBodyR Mapp) -> CompH M.

  Proof.
    intros M Mapp Ml Mr; unfold CompH. apply comp_app with Mapp; trivial.
  Qed.

  Lemma horpo_comp_algebraic : forall M, CompH M -> algebraic M.

  Proof. intros. apply comp_algebraic with horpo; trivial. Qed.

  Lemma horpo_comp_units_comp M :
    (forall N, isAppUnit N M -> CompH N) -> CompH M.

  Proof. intro Munits; unfold CompH. apply comp_units_comp; trivial. Qed.

End HorpoComp.
