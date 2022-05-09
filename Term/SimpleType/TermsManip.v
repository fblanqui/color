(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

In this file some basic operations on terms of simply
typed lambda-calculus are defined.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras TermsTyping LogicUtil.
From Coq Require Import Lia.

Module TermsManip (Sig : TermsSig.Signature).

  Module Export TS := TermsTyping.TermsTyping Sig.

  Implicit Types M N : Term.

  Definition isVar M : Prop :=
  let (_, _, _, typ) := M in
  match typ with
  | TVar _ => True
  | _ => False
  end.

  Lemma var_is_var : forall M x, term M = %x -> isVar M.

  Proof.
    intro M; term_inv M.
  Qed.

  Definition isFunS M : Prop :=
  let (_, _, _, typ) := M in
  match typ with
  | TFun _ _ => True
  | _ => False
  end.

  Lemma funS_is_funS : forall M f, term M = ^f -> isFunS M.

  Proof. intro M; term_inv M. Qed.

  Lemma funS_fun : forall M, isFunS M -> exists f, term M = ^f.

  Proof. intro M; term_inv M. intro; exists f; trivial. Qed.

  Definition isAbs M : Prop :=
  let (_, _, _, typ) := M in
  match typ with
  | TAbs _ => True
  | _ => False
  end.

  #[global] Hint Unfold isVar isFunS isAbs : terms.

  Ltac assert_abs hypName M :=
     assert (hypName : isAbs M); 
     [try solve [eauto with terms | term_inv M] 
     | idtac
     ].

  Definition absBody M : isAbs M -> Term :=
  match M return (isAbs M -> Term) with
  | buildT typ =>
      match typ return (isAbs (buildT typ) -> Term) with
      | TAbs absT => fun _ : True => buildT absT
      | _ => fun notAbs: False => False_rect Term notAbs
      end
  end.
  Arguments absBody [M] _.

  Definition absType M : isAbs M -> SimpleType :=
  match M return (isAbs M -> SimpleType) with
  | buildT typ =>
      match typ return (isAbs (buildT typ) -> SimpleType) with
      | @TAbs _ A B _ _ => fun _ : True => A
      | _ => fun notAbs : False => False_rect SimpleType notAbs
      end
  end.
  Arguments absType [M] _.

  Lemma abs_isAbs : forall M A Pt, term M = \A => Pt -> isAbs M.

  Proof. intro M; term_inv M. Qed.

  Lemma absBody_eq_env : forall M N (MAbs: isAbs M) (NAbs: isAbs N),
    env M = env N -> type M = type N -> env (absBody MAbs) = env (absBody NAbs).

  Proof. intros M N; term_inv M; term_inv N. Qed.

  Lemma absBody_equiv_type : forall M N (MAbs: isAbs M) (NAbs: isAbs N),
    type M == type N -> type (absBody MAbs) == type (absBody NAbs).

  Proof. intros M N; term_inv M; term_inv N. Qed.

  Lemma absBody_eq_type : forall M N (MAbs: isAbs M) (NAbs: isAbs N),
    type M = type N -> type (absBody MAbs) = type (absBody NAbs).

  Proof. intros M N; term_inv M; term_inv N. Qed.

  Lemma absBody_term : forall M (Mabs: isAbs M) A Pt,
    term M = \A => Pt -> term (absBody Mabs) = Pt.

  Proof. intro M; term_inv M; congruence. Qed.

  Lemma absBody_env : forall M (Mabs: isAbs M),
    env (absBody Mabs) = decl (absType Mabs) (env M).

  Proof. intro M; term_inv M; congruence. Qed.

  Lemma abs_type : forall M (Mabs: isAbs M) A B,
    type M = A --> B -> absType Mabs = A.

  Proof. intro M; term_inv M; congruence. Qed.

  #[global] Hint Rewrite absBody_term absBody_env abs_type
    using solve [auto with terms] : terms.

  Lemma type_eq_absType_eq : forall M N (Mabs: isAbs M) (Nabs: isAbs N),
    type M = type N -> absType Mabs = absType Nabs.

  Proof. intros M N; term_inv M; term_inv N. Qed.

  Lemma absBody_type : forall M (Mabs: isAbs M) A B,
    type M = A --> B -> type (absBody Mabs) = B.

  Proof. intros M Mabs A B MAB. term_inv M; congruence. Qed.

  Lemma abs_type_eq : forall M N (Mabs: isAbs M) (Nabs: isAbs N),
    absType Mabs = absType Nabs ->
    type (absBody Mabs) = type (absBody Nabs) -> type M = type N.

  Proof.
    intros M N Mabs Nabs absTypeEq absBodyEq.
    term_inv M; term_inv N; congruence.
  Qed.

  Lemma abs_proof_irr : forall M (Mabs Mabs': isAbs M), Mabs = Mabs'.

  Proof.
    intro M; term_inv M.
    dependent inversion Mabs; dependent inversion Mabs'; trivial.
  Qed.

  Lemma absBody_eq : forall M N (Mabs: isAbs M) (Nabs: isAbs N),
    M = N -> absBody Mabs = absBody Nabs.

  Proof.
    intros; term_inv M; term_inv N.
    injection H; intros.
    apply term_eq; try_solve.
  Qed.

  Lemma abs_term : forall M (Mabs: isAbs M),
    term M = \ (absType Mabs) => (term (absBody Mabs)).

  Proof. intros; term_inv M. Qed.

  #[global] Hint Resolve absBody absType abs_isAbs absBody_eq_env funS_is_funS
    absBody_equiv_type absBody_eq_type : terms.
  #[global] Hint Rewrite absBody_env : terms.

  Definition isApp M : Prop :=
  let (_, _, _, typ) := M in
  match typ with
  | TApp _ _ => True
  | _ => False
  end.

  Ltac assert_app hypName M :=
     assert (hypName : isApp M); 
     [try solve [eauto with terms | term_inv M]
     | idtac
     ].

  Definition appBodyL M : isApp M -> Term :=
  match M return (isApp M -> Term) with
  | buildT typ =>
      match typ return (isApp (buildT typ) -> Term) with
      | TApp L R => fun _ : True => buildT L
      | _ => fun notApp: False => False_rect Term notApp
      end
  end.

  Arguments appBodyL [M] _.

  Definition appBodyR M : isApp M -> Term :=
  match M return (isApp M -> Term) with
  | buildT typ =>
      match typ return (isApp (buildT typ) -> Term) with
      | TApp L R => fun _ : True => buildT R
      | _ => fun notApp: False => False_rect Term notApp
      end
  end.

  Arguments appBodyR [M] _.

  Lemma app_isApp : forall M Pt0 Pt1, term M = Pt0 @@ Pt1 -> isApp M.

  Proof. intro M; term_inv M. Qed.

  Lemma app_eq : forall M N (Mapp: isApp M) (Napp: isApp N),
    appBodyL Mapp = appBodyL Napp -> appBodyR Mapp = appBodyR Napp -> M = N.

  Proof.
    intros M N; term_inv M; term_inv N.
    intros Mapp Napp Leq Req.
    inversion Leq; destruct H4.
    inversion Req; destruct H7.
    apply deriv_uniq; auto.
    simpl; congruence.
  Qed.

  Lemma app_Req_LtypeEq : forall M N (Mapp: isApp M) (Napp: isApp N),
    term (appBodyR Mapp) = term (appBodyR Napp) -> env M = env N ->
    type M = type N -> type (appBodyL Mapp) = type (appBodyL Napp).

  Proof.
    intros M N; term_inv M; term_inv N; intros; simpl in * |-.
    assert (Aeq: type (buildT T2) = type (buildT T4)).
    auto with terms.
    simpl in *; congruence.
  Qed.

  Lemma app_Leq_RtypeEq : forall M N (Mapp: isApp M) (Napp: isApp N),
    term (appBodyL Mapp) = term (appBodyL Napp) -> env M = env N ->
    type M = type N -> type (appBodyR Mapp) = type (appBodyR Napp).

  Proof.
    intros M N; term_inv M; term_inv N; intros; simpl in * |-.
    assert (ABeq: type (buildT T1) = type (buildT T3)).
    auto with terms.
    simpl in *; inversion ABeq; trivial.
  Qed.

  Lemma appBodyL_env : forall M (Mapp: isApp M), env (appBodyL Mapp) = env M.

  Proof. intro M; term_inv M. Qed.

  Lemma appBodyR_env : forall M (Mapp: isApp M), env (appBodyR Mapp) = env M.

  Proof. intro M; term_inv M. Qed.

  #[global] Hint Rewrite appBodyL_env appBodyR_env : terms.

  Lemma appBodyL_term : forall M PtL PtR (Mterm: term M = PtL @@ PtR)
    (Mapp: isApp M), term (appBodyL Mapp) = PtL.

  Proof. intros; term_inv M. Qed.

  Lemma appBodyR_term : forall M PtL PtR (Mterm: term M = PtL @@ PtR)
    (Mapp: isApp M), term (appBodyR Mapp) = PtR.

  Proof. intros; term_inv M. Qed.

  Lemma term_appBodyL_eq : forall M N (Mapp: isApp M) (Napp: isApp N),
    term M = term N -> term (appBodyL Mapp) = term (appBodyL Napp).

  Proof. intros M N; term_inv M; term_inv N. Qed.

  Lemma term_appBodyR_eq : forall M N (Mapp: isApp M) (Napp: isApp N),
    term M = term N -> term (appBodyR Mapp) = term (appBodyR Napp).

  Proof. intros M N; term_inv M; term_inv N. Qed.

  #[global] Hint Rewrite appBodyL_term appBodyR_term
    using solve [auto with terms] : terms.

  Lemma app_typeL_type : forall M A B (Mapp: isApp M),
    type (appBodyL Mapp) = A --> B -> type M = B.

  Proof. intros M A B Mapp Ml. term_inv M. Qed.

  Lemma app_typeR : forall M A B (Mapp: isApp M),
    type (appBodyL Mapp) = A --> B -> type (appBodyR Mapp) = A.

  Proof. intros. term_inv M. Qed.

  #[global] Hint Rewrite app_typeL_type app_typeR using solve [auto with terms] : terms.

  Lemma app_type_eq : forall M N (Mapp: isApp M) (Napp: isApp N),
    type (appBodyL Mapp) = type (appBodyL Napp) ->
    type (appBodyR Mapp) = type (appBodyR Napp) -> type M = type N.

  Proof. intros; term_inv M; term_inv N. Qed.

  Lemma app_proof_irr : forall M (Mapp Mapp': isApp M), Mapp = Mapp'.

  Proof.
    intro M; term_inv M.
    dependent inversion Mapp; dependent inversion Mapp'; trivial.
  Qed.

  Lemma app_term : forall M (Mapp: isApp M),
    term M = term (appBodyL Mapp) @@ term (appBodyR Mapp).

  Proof. intro M; term_inv M. Qed.

  #[global] Hint Resolve appBodyL appBodyR app_isApp app_proof_irr app_Req_LtypeEq
    app_Leq_RtypeEq : terms.
  #[global] Hint Unfold isApp : terms.
  #[global] Hint Rewrite appBodyL_env appBodyR_env : terms.

  Lemma isVar_dec : forall M, {isVar M} + {~isVar M}.

  Proof. intro M; term_inv M. Qed.

  Lemma isAbs_dec : forall M, {isAbs M} + {~isAbs M}.

  Proof. intro M; term_inv M. Qed.

  Lemma isFunS_dec : forall M, {isFunS M} + {~isFunS M}.

  Proof. intro M; term_inv M. Qed.

  Lemma isApp_dec : forall M, {isApp M} + {~isApp M}.

  Proof. intro M; term_inv M. Qed.

  Definition appUnits M : list Term :=
  let
    fix appUnits_rec M (Mt: TermTyping M) : list Term :=
    match Mt with
    | (TApp Ltyp Rtyp) => (buildT Rtyp) :: 
                                    (@appUnits_rec (buildT Ltyp) Ltyp)
    | _ => (buildT Mt)::nil
    end    
  in rev (appUnits_rec M M.(typing)).

  Lemma appUnits_not_nil : forall M, appUnits M <> nil.

  Proof.
    destruct M as [E Pt A TypM].
    induction TypM; 
       solve [unfold appUnits; simpl; auto with datatypes].
  Qed.

  Definition appHead M : Term := proj1_sig (head_notNil (appUnits_not_nil M)).
    
  Definition appArgs M := tail (appUnits M).

  Definition isArg M' M : Prop := In M' (appArgs M).

  Definition isAppUnit M' M : Prop := In M' (appUnits M).

  Definition isNeutral M : Prop := ~ isAbs M.

  Definition isFunApp M : Prop := isFunS (appHead M).

  Definition isPartialFlattening Args M : Prop :=
  match Args with
  | nil => False
  | hd::nil => False
  | hd::tl => appUnits hd ++ tl = appUnits M
  end.

  #[global] Hint Resolve appUnits appHead appArgs appUnits_not_nil : terms.
  #[global] Hint Unfold isPartialFlattening isFunApp isNeutral : terms.

  Lemma appUnits_notApp : forall M, ~isApp M -> appUnits M = M::nil.

  Proof. intro M; term_inv M. Qed.

  Lemma appUnit_notApp : forall M Mu, isAppUnit Mu M -> ~isApp M -> Mu = M.

  Proof.
    intros.
    unfold isAppUnit in H.
    rewrite appUnits_notApp in H; trivial.
    inversion H; try_solve.
  Qed.

  Lemma appUnit_head_or_arg : forall M M', In M' (appUnits M) ->
    M' = appHead M \/ In M' (appArgs M).

  Proof.
    intros.
    destruct (in_head_tail M' (appUnits M) H).
    left; sym.
    unfold appHead; apply head_of_notNil; auto.
    right; trivial.
  Qed.

  Lemma appUnits_app : forall M (Mapp: isApp M),
    appUnits M = appUnits (appBodyL Mapp) ++ (appBodyR Mapp)::nil.

  Proof. intro M; term_inv M. Qed.

  Lemma appUnit_app : forall Mu M (Mapp: isApp M), isAppUnit Mu M ->
    (Mu = appBodyR Mapp \/ isAppUnit Mu (appBodyL Mapp)).

  Proof.
    intros.
    unfold isAppUnit in H.
    rewrite (appUnits_app M Mapp) in H.
    destruct (in_app_or H).
    right; trivial.
    inversion H0; try_solve.
  Qed.

  Lemma appHead_notApp : forall M, ~isApp M -> appHead M = M.

  Proof. intro M; term_inv M. Qed.

  Lemma appHead_app_aux : forall M (Mapp: isApp M),
    head (appUnits M) = head (appUnits (appBodyL Mapp)).

  Proof.
    intro M; term_inv M.
    rewrite (appUnits_app Tr I).
    simpl.
    rewrite head_app.
    trivial.
    apply appUnits_not_nil.
  Qed.

  Lemma appHead_app : forall M (Mapp: isApp M),
    appHead M = appHead (appBodyL Mapp).

  Proof.
    intro M; term_inv M.
    unfold appHead.
    destruct (head_notNil (appUnits_not_nil Tr)).
    destruct (head_notNil (appUnits_not_nil (buildT T1))).
    simpl.
    assert (head (appUnits Tr) = head (appUnits (buildT T1))).
    change (buildT T1) with (@appBodyL Tr I).
    apply appHead_app_aux.
    congruence.
  Qed.

  Lemma appHead_app_explicit : forall E PtL PtR A B (L: E |- PtL := A --> B)
    (R: E |- PtR := A), appHead (buildT (TApp L R)) = appHead (buildT L).

  Proof. intros. rewrite (appHead_app (buildT (TApp L R)) I). trivial. Qed.

  Lemma appArgs_notApp : forall M, ~isApp M -> appArgs M = nil.

  Proof. intro M; term_inv M. Qed.

  Lemma appArgs_app : forall M (Mapp: isApp M),
    appArgs M = appArgs (appBodyL Mapp) ++ (appBodyR Mapp)::nil.

  Proof.
    intros M Mapp; unfold appArgs.
    rewrite (appUnits_app M Mapp).
    sym; auto with terms datatypes.
  Qed.

  Lemma app_units_app : forall M (Mapp: isApp M),
    appUnits M = appHead M :: nil ++ appArgs M.

  Proof.
    destruct M as [E Pt T M]; induction M; try_solve.
    simpl.
    rewrite (appUnits_app (buildT (TApp M1 M2)) I).
    rewrite (appArgs_app (buildT (TApp M1 M2)) I).
    rewrite (appHead_app (buildT (TApp M1 M2)) I).
    simpl.
    destruct (isApp_dec (buildT M1)).
    rewrite IHM1; trivial.
    rewrite (appUnits_notApp (buildT M1) n).
    rewrite (appArgs_notApp (buildT M1) n).
    rewrite (appHead_notApp (buildT M1) n).
    trivial.
  Qed.

  #[global] Hint Rewrite appUnits_notApp appUnits_app appHead_notApp appHead_app 
    appArgs_notApp appArgs_app : terms.

  Lemma appArg_inv : forall M N (Mapp: isApp M), isArg N M ->
    (isArg N (appBodyL Mapp) \/ N = (appBodyR Mapp)).

  Proof.
    destruct M as [E Pt A typM].
    induction typM; simpl; intros; try contr.
    unfold isArg in H.
    rewrite (appArgs_app (buildT (TApp typM1 typM2)) Mapp) in H.
    case (@in_app_or _ (appArgs (buildT typM1)) (buildT typM2::nil) N); auto.
    destruct 1; solve [auto | contr].
  Qed.

  Lemma appArg_is_appUnit : forall M N, isArg M N -> isAppUnit M N.

  Proof. unfold isArg, isAppUnit; auto with datatypes terms. Qed.

  Lemma appUnit_left : forall M N (Mapp: isApp M),
    isAppUnit N (appBodyL Mapp) -> isAppUnit N M.

  Proof.
    intro M; term_inv M.
    unfold isAppUnit.
    intros N Mapp.
    rewrite (appUnits_app Tr Mapp).
    simpl.
    auto with datatypes.
  Qed.

  Lemma appUnit_right : forall M N (Mapp: isApp M),
    N = appBodyR Mapp -> isAppUnit N M.

  Proof.
    intros.
    unfold isAppUnit.
    rewrite H.
    rewrite (appUnits_app M Mapp).
    auto with datatypes.
  Qed.

  Lemma appArg_left : forall M N (Mapp: isApp M),
    isArg N (appBodyL Mapp) -> isArg N M.

  Proof.
    intros M N Mapp Narg.
    unfold isArg in *.
    rewrite (appArgs_app M Mapp).
    auto with datatypes.
  Qed.

  Lemma appArg_right : forall M N (Mapp: isApp M),
    N = appBodyR Mapp -> isArg N M.

  Proof.
    intros M N Mapp Narg.
    unfold isArg in *.
    rewrite (appArgs_app M Mapp).
    rewrite Narg.
    auto with datatypes.
  Qed.

  Lemma appArg_app : forall M Marg, isArg Marg M -> isApp M.

  Proof.
    intro M.
    destruct (isApp_dec M); trivial.
    unfold isArg; rewrite appArgs_notApp; try_solve. 
  Qed.

  Lemma funS_neutral : forall M, isFunS M -> isNeutral M.

  Proof. intros; term_inv M. Qed.

  Lemma app_neutral : forall M, isApp M -> isNeutral M.

  Proof. intros; term_inv M. Qed.

  Lemma var_neutral : forall M, isVar M -> isNeutral M.

  Proof. intros; term_inv M. Qed.

  Lemma abs_not_neutral : forall M, isAbs M -> isNeutral M -> False.

  Proof. intros M; term_inv M. Qed.

  Lemma abs_isnot_app : forall M, isAbs M -> ~isApp M.

  Proof. intro M; term_inv M. Qed.

  Lemma app_isnot_abs : forall M, isApp M -> ~isAbs M.

  Proof. intro M; term_inv M. Qed.

  Lemma term_case : forall M, {isVar M} + {isFunS M} + {isAbs M} + {isApp M}.

  Proof. intro M; term_inv M. Qed.

  #[global] Hint Resolve appArg_inv appArg_is_appUnit abs_isnot_app app_isnot_abs 
               appUnits_notApp appHead_notApp appHead_app appArgs_notApp 
               appArgs_app appUnit_left: terms.

  Inductive subterm : relation Term :=
  | AppLsub: forall M N (Mapp: isApp M), 
      subterm_le N (appBodyL Mapp) -> 
      subterm N M
  | AppRsub: forall M N (Mapp: isApp M), 
      subterm_le N (appBodyR Mapp) -> 
      subterm N M
  | Abs_sub: forall M N (Mabs: isAbs M), 
      subterm_le N (absBody Mabs) -> 
      subterm N M
   with subterm_le: relation Term :=
  | subterm_lt: forall M N, 
      subterm N M -> 
      subterm_le N M
  | subterm_eq: forall M,
      subterm_le M M. 

  Definition subterm_gt := transp subterm.

  Module Subterm_Ord <: Ord.
    
    Module TermSet <: SetA.
      Definition A := Term.
    End TermSet.
    Module S := Eqset_def TermSet.

    Definition A := Term.
    Definition gtA := subterm_gt.
    Definition gtA_eqA_compat := Eqset_def_gtA_eqA_compat subterm_gt.

  End Subterm_Ord.

  Lemma subterm_wf : well_founded subterm.

  Proof.
    intros M; destruct M as [E Pt A TypM].
    induction TypM; constructor; inversion 1; simpl in *; 
      try contr.
     (* abstraction *)
    inversion H0; trivial.
    apply Acc_inv with (buildT TypM); trivial.
     (* application left *)
    inversion H0; trivial.
    apply Acc_inv with (buildT TypM1); trivial.
     (* application right *)
    inversion H0; trivial.
    apply Acc_inv with (buildT TypM2); trivial.
  Qed.

  Lemma appBodyL_subterm : forall M (Mapp: isApp M), subterm (appBodyL Mapp) M.

  Proof. intros. constructor 1 with Mapp; constructor 2. Qed.

  Lemma appBodyR_subterm : forall M (Mapp: isApp M), subterm (appBodyR Mapp) M.

  Proof. intros. constructor 2 with Mapp; constructor 2. Qed.

  Lemma absBody_subterm : forall M (Mabs: isAbs M), subterm (absBody Mabs) M.

  Proof. intros. constructor 3 with Mabs; constructor 2. Qed.

  Lemma appUnit_subterm : forall M N, isApp M -> isAppUnit N M -> subterm N M.

  Proof.
    destruct M as [E Pt A TypM].
    induction TypM; try contr.
    intros N M1M2app Narg.
     (* left argument application again *)
    case (isApp_dec (buildT TypM1)).
    intro M1app.
    unfold isAppUnit in Narg.
    rewrite (appUnits_app (buildT (TApp TypM1 TypM2)) M1M2app) in Narg.
    simpl in Narg.
    case (@in_app_or _ (appUnits (buildT TypM1)) (buildT TypM2::nil) N).
    trivial.
    constructor 1 with M1M2app; constructor.
    apply IHTypM1; trivial.
    intro N_M2.
    constructor 2 with M1M2app.
    inversion N_M2.
    rewrite <- H; constructor 2.
    contr.
     (* left argument is not application *)
    intro M1notApp.
    unfold isAppUnit, appUnits in Narg.
    simpl in Narg.
    change TypM1 at 2 with (typing (buildT TypM1)) in Narg.
    fold (appUnits (buildT TypM1)) in Narg.
    case (@in_app_or _ (appUnits (buildT TypM1)) (buildT TypM2::nil) N).
    trivial.
    intro N_M1; constructor 1 with M1M2app.
    rewrite appUnits_notApp in N_M1; trivial.
    destruct (in_inv N_M1) as [NM1 | Nnil].
    rewrite <- NM1; constructor 2.
    absurd (In N nil); auto with datatypes.
    intro N_M2; constructor 2 with M1M2app.
    destruct (in_inv N_M2) as [NM2 | Nnil].
    rewrite <- NM2; constructor 2.
    absurd (In N nil); auto with datatypes.
  Qed.

  Lemma arg_subterm : forall M Ma, isArg Ma M -> subterm Ma M.

  Proof.
    unfold isArg, appArgs.
    intros.
    destruct (isApp_dec M).
    apply appUnit_subterm; trivial.
    unfold isAppUnit; auto with datatypes.
    rewrite appUnits_notApp in H; try_solve.
  Qed.

  Lemma appUnits_notEmpty : forall M hd tl el,
    appUnits M ++ hd::tl = el::nil -> False.

  Proof.
    intros M hd tl el Eq.
    destruct (app_eq_unit (appUnits M) (hd::tl) Eq)
      as [[unitsL argR] | [unitsL argR]].
    absurd (appUnits M = nil); auto with terms.
    discr.
  Qed.

  Lemma partialFlattening_app : forall M Ms,
    isPartialFlattening Ms M -> isApp M.

  Proof.
    intros M Ms Ms_pflat_M.
    unfold isPartialFlattening in *.
    repeat (destruct Ms; [contr | idtac]).
    case (isApp_dec M).
    auto.
    intro Mnapp.
    rewrite (appUnits_notApp M) in Ms_pflat_M.
    exfalso.
    eapply appUnits_notEmpty; eexact Ms_pflat_M.
    trivial.
  Qed.

  Lemma app_notApp_diffUnits : forall M N,
    isApp M -> ~isApp N -> appUnits M = appUnits N -> False.

  Proof.
    intros M N Mapp Nnapp eqUnits.
    rewrite (appUnits_app M Mapp) in eqUnits.
    rewrite (appUnits_notApp N Nnapp) in eqUnits.
    eapply appUnits_notEmpty; eexact eqUnits.
  Qed.

  Lemma eq_unitTypes_eq_types : forall M N,
    length (appUnits M) = length (appUnits N) ->
    (forall p Ma Na, 
      nth_error (appUnits M) p = Some Ma -> 
      nth_error (appUnits N) p = Some Na ->
      type Ma = type Na) -> type M = type N.

  Proof.
    intro M.
    apply well_founded_ind with
      (R := subterm)
      (P := fun M =>
         forall N,
           length (appUnits M) = length (appUnits N) ->
           (forall p Ma Na, 
             nth_error (appUnits M) p = Some Ma ->
             nth_error (appUnits N) p = Some Na ->
             type Ma = type Na
           ) ->
           type M = type N).
    apply subterm_wf.
    clear M; intros M IH N MNunits H.
    destruct (isApp_dec M) as [Mapp | Mnapp].
    destruct (isApp_dec N) as [Napp | Nnapp].
    assert (type (appBodyL Mapp) = type (appBodyL Napp)).
    apply IH.
    apply appBodyL_subterm.
    rewrite (appUnits_app M Mapp) in MNunits.
    rewrite (appUnits_app N Napp) in MNunits.
    rewrite !length_app in MNunits.
    simpl in MNunits; lia.
    intros; apply (H p Ma Na).
    rewrite (appUnits_app M Mapp).
    rewrite nth_app_left; trivial.
    apply nth_some with Ma; trivial.
    rewrite (appUnits_app N Napp).
    rewrite nth_app_left; trivial.
    apply nth_some with Na; trivial.
    term_inv M; term_inv N.
    absurd (length (appUnits M) = length (appUnits N)); trivial.
    rewrite (appUnits_app M Mapp).
    rewrite (appUnits_notApp N Nnapp).
    rewrite length_app; try_solve.
    term_inv (appBodyL Mapp).
    rewrite (appUnits_app Tr I).
    rewrite length_app; simpl; lia.
    destruct (isApp_dec N) as [Napp | Nnapp].
    absurd (length (appUnits M) = length (appUnits N)); trivial.
    rewrite (appUnits_app N Napp).
    rewrite (appUnits_notApp M Mnapp).
    rewrite length_app; try_solve.
    term_inv (appBodyL Napp).
    rewrite (appUnits_app Tr I).
    rewrite length_app; simpl; lia.
    apply (H 0 M N).
    rewrite (appUnits_notApp M Mnapp); trivial.
    rewrite (appUnits_notApp N Nnapp); trivial.
  Qed.

  Lemma eq_units_eq_terms : forall M N, appUnits M = appUnits N -> M = N.

  Proof.
    intro M.
    apply well_founded_ind with
      (R := subterm)
      (P := fun M =>
         forall N,
           appUnits M = appUnits N ->
           M = N
      ).
    apply subterm_wf.
    clear M; intros M IH N unitsEq.
    case (isApp_dec M); case (isApp_dec N).
     (* M and N are applications *)
    intros Napp Mapp.
    rewrite (appUnits_app M Mapp) in unitsEq.
    rewrite (appUnits_app N Napp) in unitsEq.
    destruct (app_inj_tail (appUnits (appBodyL Mapp)) 
      (appUnits (appBodyL Napp)) (appBodyR Mapp) (appBodyR Napp)); 
      trivial.
    apply app_eq with Mapp Napp; simpl.
    apply IH; trivial.
    constructor 1 with Mapp; constructor 2.
    trivial.
     (* M application, N not *)
    intros; exfalso.
    apply app_notApp_diffUnits with M N; trivial.
     (* N application, M not *)
    intros; exfalso.
    apply app_notApp_diffUnits with N M; auto.
     (* M and N both not applications *)
    intros Nnapp Mnapp.
    do 2 rewrite appUnits_notApp in unitsEq; trivial.
    congruence.
  Qed.

  Lemma partialFlattening_subterm_aux : forall N L M,
    L <> nil -> appUnits M ++ L = appUnits N -> subterm M N.

  Proof.
    intro N. apply well_founded_ind with
      (R := subterm)
      (P := fun N =>
         forall L M,
           L <> nil ->
           appUnits M ++ L = appUnits N ->
           subterm M N
      ).
    apply subterm_wf.
    clear N; intros N IH L M L_neq_nil units.
    destruct L.
    tauto.
    case (isApp_dec N).
     (* -) N is application *)
    intro Napp.
    rewrite (appUnits_app N Napp) in units; trivial.
    constructor 1 with Napp.
    destruct L.
     (*   - M is equal to left applicant of N *)
    assert (Meq: M = appBodyL Napp).
    destruct (app_inj_tail (appUnits M) (appUnits (appBodyL Napp)) 
      t (appBodyR Napp)) as [unitsEq _]; trivial.
    apply eq_units_eq_terms; trivial.
    rewrite Meq; constructor 2.
     (*   - M is application (subterm of left applicant of N) *)
    rewrite <- list_app_first_last in units.
    destruct (@list_drop_last Term (appUnits M ++ t::nil) (t0::L)
      (appUnits (appBodyL Napp)) (appBodyR Napp)); auto with datatypes.
    constructor 1.
    apply IH with (t::x); auto with datatypes.
    constructor 1 with Napp; constructor 2.
    rewrite <- list_app_first_last; trivial.
     (* -) N not application *)
    intro Nnapp.
    rewrite (appUnits_notApp N) in units; trivial.
    exfalso; eapply appUnits_notEmpty; eexact units.
  Qed.

  Lemma partialFlattening_subterm : forall M Ms m,
    isPartialFlattening Ms M -> In m Ms -> subterm m M.

  Proof.
    intros M Ms m Ms_pflat m_Ms.
    assert (Mapp: isApp M).
    apply partialFlattening_app with Ms; trivial.
    unfold isPartialFlattening in *.
    repeat (destruct Ms; [contr | idtac]).
    destruct m_Ms as [m_t | [m_t0 | m_Ms]].
    apply partialFlattening_subterm_aux with (t0::Ms).
    auto with datatypes.
    rewrite <- m_t; trivial.
    apply appUnit_subterm; trivial.
    unfold isAppUnit; rewrite <- m_t0; rewrite <- Ms_pflat.
    auto with datatypes.
    apply appUnit_subterm; trivial.
    unfold isAppUnit; rewrite <- Ms_pflat; auto with datatypes.
  Qed.
 
  Lemma funApp_head : forall M, isFunApp M ->
    { f: FunctionSymbol | term (appHead M) = ^f }.

  Proof.
    unfold isFunApp; intros M MfunApp.
    term_inv (appHead M).
    exists f; trivial.
  Qed.

  Lemma funApp : forall M f, term (appHead M) = ^f -> isApp M -> isFunApp M.

  Proof. unfold isFunApp; intros M f Mhead Mapp. term_inv (appHead M). Qed.

  Lemma funS_funApp : forall M, isFunS M -> isFunApp M.

  Proof. intros. term_inv M. Qed.

  Lemma appHead_term : forall (M N: Term),
    term M = term N -> term (appHead M) = term (appHead N).

  Proof.
    intros M.
    apply well_founded_ind with
      (R := subterm)
      (P := fun (M: Term) =>
         forall (N: Term),
           term M = term N ->
           term (appHead M) = term (appHead N)
      ).
    apply subterm_wf.
    clear M; intros M IH N M_N.
    term_inv M; term_inv N.
    unfold Tr, Tr0.
    rewrite !appHead_app_explicit.
    apply IH.
    constructor 1 with I; constructor 2.
    simpl; congruence.
  Qed.

  Lemma appHead_left : forall M (Mapp: isApp M), isFunS (appHead M) ->
    isFunS (appHead (appBodyL Mapp)).

  Proof.
    intro M; term_inv M.
    rewrite (appHead_app Tr I); trivial.
  Qed.

  Lemma headFunS_dec : forall M, {isFunS (appHead M)} + {~isFunS (appHead M)}.

  Proof.
    destruct M as [E Pt A M]; induction M.
    fo.
    fo.
    fo.
    rewrite (appHead_app (buildT (TApp M1 M2)) I).
    destruct IHM1; fo.
  Qed.

  Lemma isFunApp_dec : forall M, {isFunApp M} + {~isFunApp M}.

  Proof.
    destruct M as [E Pt A M]; destruct M.
    fo.
    fo.
    fo.
    destruct (headFunS_dec (buildT (TApp M1 M2))) as [headF | headNF]; fo.
  Qed.

  Lemma isFunApp_left : forall M (Mapp: isApp M),
    isFunApp M -> isFunApp (appBodyL Mapp).

  Proof.
    unfold isFunApp; intros.
    rewrite (appHead_app M Mapp) in H; trivial.
  Qed.
    
  Lemma notFunApp_left: forall M (Mapp: isApp M),
    ~isFunApp (appBodyL Mapp) -> ~isFunApp M.

  Proof.
    intros.
    intro.
    absurd (isFunApp (appBodyL Mapp)); trivial.
    apply isFunApp_left; trivial.
  Qed.

  Lemma notFunApp_left_inv : forall M (Mapp: isApp M),
    ~isFunApp M -> ~isFunApp (appBodyL Mapp).

  Proof.
    unfold isFunApp; intros; intro MLfa.
    absurd (isFunApp M); trivial.
    term_inv M.
    unfold isFunApp; rewrite (appHead_app Tr I); trivial.
  Qed.

  Lemma notFunApp_left_eq : forall M (Mapp: isApp M) N (Napp: isApp N),
    ~isFunApp M -> appBodyL Mapp = appBodyL Napp -> ~isFunApp N.

  Proof.
    intro M; term_inv M.
    intros _ N; term_inv N.
    intros.
    apply notFunApp_left with I.
    simpl; rewrite <- H0.
    change (buildT T1) with (appBodyL (M:=buildT (TApp T1 T2)) I).
    apply notFunApp_left_inv; trivial.
  Qed.

  Lemma funAbs_notFunApp : forall M, isAbs (appHead M) -> ~isFunApp M.

  Proof.
    unfold isFunApp; intros.
    term_inv M.
    intro Tr_fa.
    term_inv (appHead Tr).
  Qed.

  Lemma notFunApp_notFunS : forall M, ~isFunApp M -> ~isFunS M.

  Proof. intro M; term_inv M. Qed. 

  Lemma appUnit_env : forall Mu M, isAppUnit Mu M -> env Mu = env M.

  Proof.
    destruct M as [E Pt T M].
    induction M; intros; 
      try solve [inversion H; try contr; rewrite <- H0; trivial].
    unfold isAppUnit in H.
    rewrite (appUnits_app (buildT (TApp M1 M2)) I) in H.
    simpl in H.
    destruct (in_app_or H).
    apply IHM1; trivial.
    inversion H0; try_solve.
    rewrite <- H1; trivial.
  Qed.

  Lemma partialFlattening_env : forall M Ms, isPartialFlattening Ms M ->
    forall Min, In Min Ms -> env Min = env M.

  Proof.
    intros.
    destruct Ms; try_solve.
    destruct Ms; try_solve.
    destruct H0.
    rewrite <- H0.
    destruct (head_notNil (appUnits_not_nil t)).
    destruct (head_notNil (appUnits_not_nil M)).
    rewrite <- (appUnit_env x t).
    rewrite <- (appUnit_env x0 M).
    rewrite (list_decompose_head (appUnits_not_nil t) e) in H.
    rewrite (list_decompose_head (appUnits_not_nil M) e0) in H.
    inversion H; trivial.
    unfold isAppUnit; destruct (appUnits M); inversion e0; try_solve.
    unfold isAppUnit; destruct (appUnits t); inversion e; try_solve.
    apply appUnit_env.
    unfold isAppUnit; rewrite <- H.
    destruct H0.
    rewrite <- H0; firstorder auto with datatypes.
    firstorder auto with datatypes.
  Qed.

  Lemma partialFlattening_inv : forall M (Mapp: isApp M) Ms,
    isPartialFlattening Ms M ->
    Ms = appBodyL Mapp :: appBodyR Mapp :: nil
    \/ exists Ns, isPartialFlattening Ns (appBodyL Mapp)
      /\ Ms = Ns ++ appBodyR Mapp :: nil.

  Proof.
    destruct M as [E Pt T M]; induction M; intros.
    set (w := partialFlattening_app (buildT (TVar v)) Ms H); try_solve.
    set (w := partialFlattening_app (buildT (TFun E f)) Ms H); try_solve.
    set (w := partialFlattening_app (buildT (TAbs M)) Ms H); try_solve.
    destruct Ms.
    inversion H.
    destruct Ms.
    inversion H.
    unfold isPartialFlattening in H.
    rewrite (appUnits_app (buildT (TApp M1 M2)) I) in H.
    destruct Ms.
    left.
    destruct (app_inj_tail (appUnits t) (appUnits (appBodyL Mapp)) 
      t0 (appBodyR Mapp)); trivial.
    rewrite H1.
    rewrite (eq_units_eq_terms t (appBodyL Mapp) H0); trivial.
    right.
    assert (MLapp: isApp (appBodyL Mapp)).
    destruct (isApp_dec (appBodyL Mapp)); trivial.
    rewrite (appUnits_notApp (appBodyL (M:=buildT (TApp M1 M2)) I)) in H;
      trivial.
    simpl in H.
    exfalso; cut (appUnits t <> nil).
    destruct (appUnits t); auto.
    inversion H.
    cut (length (l ++ t0 :: t1 :: Ms) = length (buildT M2 :: nil)).
    autorewrite with datatypes; simpl; lia.
    rewrite H2; trivial.
    apply appUnits_not_nil.
    exists (t :: t0 :: dropLast (t1 :: Ms)); split.
    set (w := dropLast_eq H).
    rewrite dropLast_last in w.
    set (ww := dropLast_app).
    rewrite dropLast_app in w.
    simpl in w; trivial.
    simpl; rewrite (appUnits_app (buildT M1) MLapp); auto with datatypes.
    set (w := last_eq H).
    simpl in w.
    rewrite last_app in w.
    rewrite last_app in w.
    change ((t :: t0 :: dropLast (t1 :: Ms)) ++ appBodyR Mapp :: nil) with
      (t :: t0 :: (dropLast (t1 :: Ms) ++ buildT M2 :: nil)).
    rewrite dropLast_plus_last; trivial.
  Qed.

  Lemma partialFlattening_desc : forall M (Mapp: isApp M) ML,
    isPartialFlattening ML (appBodyL Mapp) ->
    isPartialFlattening (ML ++ appBodyR Mapp :: nil) M.

  Proof.
    unfold isPartialFlattening.
    intros.
    destruct ML; try_solve.
    destruct ML; try_solve.
    rewrite (appUnits_app M Mapp).
    rewrite <- H.
    rewrite app_ass.
    auto with datatypes.
  Qed.

  Lemma allPartialFlattenings : forall M, isApp M ->
    { MF: list (list Term)
      | forall Mpf, isPartialFlattening Mpf M <-> In Mpf MF }.

  Proof.
    destruct M as [E Pt T M]; induction M; try_solve.
    intros _.
    destruct (isApp_dec (buildT M1)).
    destruct IHM1; trivial.
    set (F0 := buildT M1::buildT M2::nil).
    set (fp := (fun l => l ++ buildT M2::nil)).
    set (Fr := map fp x).
    exists (F0::Fr); split; intro.
    destruct (partialFlattening_inv (buildT (TApp M1 M2)) I Mpf H).
    rewrite H0; unfold F0; try_solve.
    destruct H0 as [Ns [NsL MpfNs]].
    rewrite MpfNs.
    right; unfold Fr.
    set (Nsx := proj1 (i0 Ns) NsL).
    destruct (list_In_nth x Ns Nsx) as [p xp].
    apply nth_some_in with p.
    simpl.
    change (Ns ++ buildT M2::nil) with (fp Ns).
    apply nth_map_some; trivial.
    inversion H.
    rewrite <- H0.
    unfold F0; simpl.
    rewrite (appUnits_app (buildT (TApp M1 M2)) I); trivial.
    destruct (list_In_nth Fr Mpf H0) as [p xp].
    unfold Fr in xp.
    destruct (nth_map_some_rev x p fp xp) as [w [xpw fpw]].
    rewrite <- fpw; unfold fp.
    change (buildT M2) with (appBodyR (M:=buildT (TApp M1 M2)) I).
    apply partialFlattening_desc.
    apply (proj2 (i0 w)).
    apply nth_some_in with p; trivial.
    exists ((buildT M1::buildT M2::nil)::nil).
    split; intros.
    destruct (partialFlattening_inv (buildT (TApp M1 M2)) I Mpf H).
    try_solve.
    destruct H0 as [Ns [NsL _]].
    absurd (isApp (buildT M1)); trivial.
    apply partialFlattening_app with Ns; trivial.
    unfold isPartialFlattening.
    inversion H; try_solve.
    rewrite <- H0; try_solve.
  Qed.

  Lemma term_neq_type : forall M N, type M <> type N -> M <> N.

  Proof.
    intros; intro MN.
    absurd (type M = type N); trivial.
    rewrite MN; trivial.
  Qed.

  #[global] Hint Resolve appUnit_subterm partialFlattening_app eq_units_eq_terms
               partialFlattening_subterm funApp_head funApp : terms.

  Module TermSet <: SetA.
     Definition A := Term.
  End TermSet.
  Module TermEqSet := Eqset_def TermSet.

End TermsManip.
