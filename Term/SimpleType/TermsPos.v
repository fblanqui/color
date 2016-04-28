(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Positions in terms, replacement of term at position,
monotonicity property.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras TermsBuilding.

Module TermsPos (Sig : TermsSig.Signature).

  Module Export TB := TermsBuilding.TermsBuilding Sig.

   (* Pos expresses position in preterm *)
  Inductive Pos : Term -> Type :=
  | PThis: forall M, Pos M
  | PAbs:  forall E A B Pt AbsB, 
              Pos (buildT AbsB) -> 
              Pos (buildT (@TAbs E A B Pt AbsB))
  | PAppL: forall E A B PtL PtR AppL AppR, 
              Pos (buildT AppL) -> 
              Pos (buildT (@TApp E A B PtL PtR AppL AppR))
  | PAppR: forall E A B PtL PtR AppL AppR, 
              Pos (buildT AppR) -> 
              Pos (buildT (@TApp E A B PtL PtR AppL AppR)).

   (* termAtPos computes a subterm at given position *)
  Fixpoint termAtPos M (pos: Pos M) : Term :=
  match pos with
  | PThis M => M
  | PAbs pos => termAtPos pos
  | PAppL _ pos => termAtPos pos
  | PAppR _ pos => termAtPos pos
  end.
  Notation "M // pos" := (@termAtPos M pos) (at level 40).

  Fixpoint swap_term M (pos: Pos M) (R: Term) : Preterm :=
    match pos with
    | PThis M => term R
    | @PAbs _ A _ _ _ pos => Abs A (swap_term pos R)
    | @PAppL _ _ _ PtL PtR _ _ pos => swap_term pos R @@ PtR
    | @PAppR _ _ _ PtL PtR _ _ pos => PtL @@ swap_term pos R
    end.

  Definition PlaceHolder M pos := 
    { T: Term | 
        env (M // pos) = env T &
	type (M // pos) = type T
    }.

  Definition swap_aux : forall M (pos: Pos M) (R: PlaceHolder pos),
    {N: Term | env N = env M /\ type N = type M
               /\ term N = swap_term pos (proj1_sig2 R)}.

  Proof.
    intros M pos N.
    destruct N as [N envN typeN termN].
    induction pos; simpl in * .
     (* PThis *)
    exists N; auto.
     (* PAbs *)
    destruct (IHpos envN typeN) as [R [R_env [R_type R_term]]].
    assert (Rt: E |- \A => term R := A --> B).
    constructor 3.
    destruct R as [E_r Pt_r A_r Typ_R].
    simpl in * .
    rewrite <- R_env.
    rewrite <- R_type.
    trivial.
    exists (buildT Rt); repeat split; try_solve.
     (* PAppL *)
    destruct (IHpos envN typeN) as [R [R_env [R_type R_term]]].
    assert (Rt: E |- term R @@ PtR := B).
    constructor 4 with A; trivial.
    destruct R as [E_r Pt_r A_r Typ_R].
    simpl in * .
    rewrite <- R_env.
    rewrite <- R_type.
    trivial.
    exists (buildT Rt); repeat split; try_solve.
     (* PAppR *)
    destruct (IHpos envN typeN) as [R [R_env [R_type R_term]]].
    assert (Rt: E |- PtL @@ term R := B).
    constructor 4 with A; trivial.
    destruct R as [E_r Pt_r A_r Typ_R].
    simpl in * .
    rewrite <- R_env.
    rewrite <- R_type.
    trivial.
    exists (buildT Rt); repeat split; try_solve.
  Defined.

  Definition swap M pos N : Term := proj1_sig (swap_aux (M := M) (pos := pos) N).

  Lemma swap_type_eq : forall M (pos: Pos M) (N: PlaceHolder pos), type (swap N) = type M.

  Proof.
    intros M pos N.
    unfold swap.
    destruct (swap_aux N) as [Np [Nenv [Ntype Nterm]]]; try_solve.
  Qed.

  Lemma swap_env_eq : forall M (pos: Pos M) (N: PlaceHolder pos), env (swap N) = env M.

  Proof.
    intros M pos N.
    unfold swap.
    destruct (swap_aux N) as [Np [Nenv [Ntype Nterm]]]; try_solve.
  Qed.

  Lemma swap_term_is : forall M (pos: Pos M) (N: PlaceHolder pos),
    term (swap N) = swap_term pos (proj1_sig2 N).

  Proof.
    intros M pos N.
    unfold swap.
    destruct (swap_aux N) as [Np [Nenv [Ntype Nterm]]]; try_solve.
  Qed.

  Lemma swap_this : forall T (Mpos: PlaceHolder (PThis T)) (M := proj1_sig2 Mpos), swap Mpos = M.

  Proof.
    intros; apply term_eq.
    rewrite swap_env_eq; trivial.
    destruct Mpos; unfold M; simpl.
    rewrite <- e; trivial.
    rewrite swap_term_is; trivial.
  Qed.

  Lemma posThis_dec : forall T (pos: Pos T), {pos = PThis T} + {pos <> PThis T}.

  Proof.
    intros; destruct pos; try solve [right; try_solve].
    left; trivial.
  Qed.

  Lemma swap_appL_eq : forall E PtL PtR A B (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Mr)) (Mpos: PlaceHolder (PAppR Ml pos)) (Npos: PlaceHolder (PAppR Ml pos))
      (Lapp: isApp (swap Mpos)) (Rapp: isApp (swap Npos)), appBodyL Lapp = appBodyL Rapp.

  Proof.
    intros E PtL PtR A B Ml Mr pos Mpos Npos Lapp Rapp.
    apply term_eq.
    do 2 rewrite appBodyL_env.
    do 2 rewrite swap_env_eq.
    trivial.
    assert (tL: term (swap Mpos) = PtL @@ swap_term pos (proj1_sig2 Mpos)).
    rewrite swap_term_is; try_solve.
    assert (tR: term (swap Npos) = PtL @@ swap_term pos (proj1_sig2 Npos)).
    rewrite swap_term_is; try_solve.
    rewrite (appBodyL_term (swap Mpos) tL).
    rewrite (appBodyL_term (swap Npos) tR).
    trivial.
  Qed.

  Lemma swap_appR_eq : forall E PtL PtR A B (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Ml)) (Mpos: PlaceHolder (PAppL Mr pos)) (Npos: PlaceHolder (PAppL Mr pos))
      (Lapp: isApp (swap Mpos)) (Rapp: isApp (swap Npos)), appBodyR Lapp = appBodyR Rapp.

  Proof.
    intros E PtL PtR A B Ml Mr pos Mpos Npos Lapp Rapp.
    apply term_eq.
    do 2 rewrite appBodyR_env.
    do 2 rewrite swap_env_eq.
    trivial.
    assert (tL: term (swap Mpos) = swap_term pos (proj1_sig2 Mpos) @@ PtR).
    rewrite swap_term_is; try_solve.
    assert (tR: term (swap Npos) = swap_term pos (proj1_sig2 Npos) @@ PtR).
    rewrite swap_term_is; try_solve.
    rewrite (appBodyR_term (swap Mpos) tL).
    rewrite (appBodyR_term (swap Npos) tR).
    trivial.
  Qed.

  Lemma appBodyR_swap_in_appL : forall E PtL PtR A B (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Ml)) (Mpos: PlaceHolder pos) (MLpos: PlaceHolder (PAppL Mr pos))
      (MLapp: isApp (swap MLpos)), proj1_sig2 Mpos = proj1_sig2 MLpos ->
      appBodyR (M:=swap MLpos) MLapp = buildT Mr.

  Proof.
    intros.
    apply term_eq.
    rewrite appBodyR_env.
    rewrite swap_env_eq; trivial.
    rewrite (@appBodyR_term (swap MLpos) (swap_term pos (proj1_sig2 MLpos)) PtR); trivial.
    rewrite swap_term_is; trivial.
  Qed.

  Lemma swap_in_appL : forall E PtL PtR A B (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Ml)) (Mpos: PlaceHolder pos) (MLpos: PlaceHolder (PAppL Mr pos))
      (MLapp: isApp (swap MLpos)), proj1_sig2 Mpos = proj1_sig2 MLpos ->
      swap Mpos = appBodyL (M := swap MLpos) MLapp.

  Proof.
    intros E PtL PtR A B Ml Mr pos Mpos MLpos MLapp M_MN.
    apply term_eq.
    rewrite appBodyL_env.
    do 2 rewrite swap_env_eq; try_solve.
    rewrite swap_term_is.
    rewrite appBodyL_term with (PtL := swap_term pos (proj1_sig2 Mpos)) (PtR := PtR); trivial.
    rewrite swap_term_is; try_solve.
  Qed.

  Lemma swap_in_appR : forall E PtL PtR A B  (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Mr)) (Mpos: PlaceHolder pos) (MLpos: PlaceHolder (PAppR Ml pos))
      (MLapp: isApp (swap MLpos)), proj1_sig2 Mpos = proj1_sig2 MLpos ->
      swap Mpos = appBodyR (M := swap MLpos) MLapp.

  Proof.
    intros E PtL PtR A B Ml Mr pos Mpos MLpos MLapp M_MN.
    apply term_eq.
    rewrite appBodyR_env.
    do 2 rewrite swap_env_eq; try_solve.
    rewrite swap_term_is.
    rewrite appBodyR_term with (PtL := PtL) (PtR := swap_term pos (proj1_sig2 Mpos)); trivial.
    rewrite swap_term_is; try_solve.
  Qed.

  Lemma appBodyL_swap_in_appR : forall E PtL PtR A B (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Mr)) (Mpos: PlaceHolder pos) (MLpos: PlaceHolder (PAppR Ml pos))
      (MLapp: isApp (swap MLpos)), proj1_sig2 Mpos = proj1_sig2 MLpos ->
      appBodyL (M := swap MLpos) MLapp = buildT Ml.

  Proof.
    intros.
    apply term_eq.
    rewrite appBodyL_env.
    rewrite swap_env_eq; trivial.
    rewrite (@appBodyL_term (swap MLpos) PtL (swap_term pos (proj1_sig2 MLpos))); trivial.
    rewrite swap_term_is; trivial.
  Qed.

  Lemma swap_in_abs : forall E Pt A B (M: E |- \A => Pt := A --> B) (Min: decl A E |- Pt := B)
      (pos: Pos (buildT Min)) (Mpos: PlaceHolder pos) (Min_pos: PlaceHolder (PAbs pos))
      (Min_abs: isAbs (swap Min_pos)), proj1_sig2 Mpos = proj1_sig2 Min_pos ->
      swap Mpos = absBody (M := swap Min_pos) Min_abs.

  Proof.
    intros E Pt A B M Min pos Mpos Min_pos Min_abs M_MN.
    apply term_eq.
    rewrite absBody_env.
    do 2 rewrite swap_env_eq; try_solve.
    rewrite abs_type with (A:=A) (B:=B); trivial.
    rewrite swap_type_eq; trivial.
    rewrite swap_term_is.
    rewrite absBody_term with (A:=A) (Pt:=swap_term pos (proj1_sig2 Mpos)); trivial.
    rewrite swap_term_is; try_solve.
  Qed.

  Lemma swap_left_app : forall E PtL PtR A B (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Ml)) (N: PlaceHolder (PAppL Mr pos)), isApp (swap N).

  Proof.
    intros E PtL PtR A B Ml Mr pos N.
    eapply app_isApp; rewrite swap_term_is; simpl; eauto.
  Qed.

  Lemma swap_right_app : forall E PtL PtR A B (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Mr)) (N: PlaceHolder (PAppR Ml pos)), isApp (swap N).

  Proof.
    intros E PtL PtR A B Ml Mr pos N.
    eapply app_isApp; rewrite swap_term_is; simpl; eauto.
  Qed.

  Lemma app_swap_app : forall M (pos: Pos M) (MP: PlaceHolder pos), pos <> PThis M ->
    isApp M -> isApp (swap MP).

  Proof.
    destruct pos; intros; try_solve.
    eapply app_isApp.
    rewrite swap_term_is; simpl; eauto.
    eapply app_isApp.
    rewrite swap_term_is; simpl; eauto.
  Qed.

  Lemma swap_abs : forall E Pt A B (Mb: decl A E |- Pt := B) (pos: Pos (buildT Mb))
      (N: PlaceHolder (PAbs pos)), isAbs (swap N).

  Proof.
    intros E Pt A B Mb pos N.
    eapply abs_isAbs; rewrite swap_term_is; simpl; eauto.
  Qed.

  Lemma placeHolder_appL : forall E PtL PtR A B (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Ml)) (N: PlaceHolder (PAppL Mr pos)),
      { W: PlaceHolder pos | proj1_sig2 W = proj1_sig2 N }.

  Proof.
    intros E PtL PtR A B Ml Mr pos N.
    exists N; trivial.
  Qed.

  Lemma placeHolder_appR : forall E PtL PtR A B (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
      (pos: Pos (buildT Mr)) (N: PlaceHolder (PAppR Ml pos)),
      { W: PlaceHolder pos | proj1_sig2 W = proj1_sig2 N }.

  Proof.
    intros E PtL PtR A B Ml Mr pos N.
    exists N; trivial.
  Qed.

  Lemma placeHolder_abs : forall E Pt A B (Mb: decl A E |- Pt := B) (pos: Pos (buildT Mb))
      (N: PlaceHolder (PAbs pos)), { W: PlaceHolder pos | proj1_sig2 W = proj1_sig2 N }.

  Proof.
    intros E Pt A B Mb pos N.
    exists N; trivial.
  Qed.

  Lemma swap_isFunApp : forall T (pos: Pos T) (Mpos: PlaceHolder pos) (M := proj1_sig2 Mpos),
      isFunApp T -> ~isFunApp (T // pos) -> isFunApp (swap Mpos).

  Proof.
    induction pos; try_solve; intros.

    set (MPapp := swap_left_app Mpos).
    unfold isFunApp in * .
    rewrite (appHead_app (swap Mpos) MPapp).
    destruct (placeHolder_appL Mpos).
    replace (appBodyL MPapp) with (swap x).
    apply IHpos; trivial.
    rewrite (@appHead_app (buildT (TApp AppL AppR)) I) in H; trivial.
    apply term_eq.
    rewrite appBodyL_env, !swap_env_eq; trivial.
    rewrite (@appBodyL_term (swap Mpos) (swap_term pos (proj1_sig2 Mpos)) PtR);
      trivial.
    rewrite swap_term_is, e; trivial.
    rewrite swap_term_is; trivial.

    set (MPapp := swap_right_app Mpos).
    unfold isFunApp in * .
    rewrite (appHead_app (swap Mpos) MPapp).
    destruct (placeHolder_appR Mpos).
    rewrite (@appBodyL_swap_in_appR E PtL PtR A B AppL AppR pos Mpos Mpos);
      trivial.
    rewrite (@appHead_app (buildT (TApp AppL AppR)) I) in H; trivial.
  Qed. 

  Lemma swap_not_funApp : forall T (pos: Pos T) (Mpos: PlaceHolder pos) (M := proj1_sig2 Mpos),
    pos <> PThis T -> ~isFunApp T -> (isFunApp M -> isBaseType (type M)) -> ~isFunApp (swap Mpos).

  Proof.
    induction pos; intros; try_solve.

    assert (isAbs (swap Mpos)).
    apply swap_abs.
    unfold isFunApp; rewrite appHead_notApp; term_inv (swap Mpos).

    assert (MPapp: isApp (swap Mpos)).
    apply app_swap_app; simpl; trivial.
    apply notFunApp_left with MPapp.
    destruct (placeHolder_appL Mpos) as [MPin MPeq].
    rewrite <- (swap_in_appL MPin Mpos); trivial.
    destruct (posThis_dec pos).
    replace (swap MPin) with M.
    intro Mfa.
    absurd (isBaseType (type M)).
    unfold M; destruct Mpos; simpl in * .
    rewrite <- e1; rewrite e; auto.
    apply H1; trivial.
    apply term_eq.
    rewrite swap_env_eq; trivial.
    unfold M; destruct MPin; simpl in * .
    rewrite <- MPeq; rewrite <- e0; rewrite e; trivial.
    rewrite swap_term_is; trivial. 
    rewrite MPeq.
    unfold M; destruct Mpos; simpl in * .
    rewrite e; trivial.
    apply IHpos; try_solve.
    change (buildT AppL) with (appBodyL (M:=buildT (TApp AppL AppR)) I).
    apply notFunApp_left_inv; trivial.
    rewrite MPeq; trivial.
  
    assert (MPapp: isApp (swap Mpos)).
    apply app_swap_app; simpl; trivial.
    apply notFunApp_left with MPapp.  
    destruct (placeHolder_appR Mpos).
    rewrite (appBodyL_swap_in_appR x Mpos MPapp); trivial.
    change (buildT AppL) with (appBodyL (M:=buildT (TApp AppL AppR)) I).
    apply notFunApp_left_inv; trivial.
  Qed.

  Section Monotonicity.

    Variable R : relation Term.

    Notation "X -R-> Y" := (R X Y) (at level 50).

    Definition monotonous :=
      forall T (pos: Pos T) (Mpos: PlaceHolder pos) (Npos: PlaceHolder pos),
	proj1_sig2 Mpos -R-> proj1_sig2 Npos ->
	swap Mpos -R-> swap Npos.

    Lemma monotonicity_criterion : 
	(forall M M' (Mapp: isApp M) (M'app: isApp M'),
	  appBodyL Mapp -R-> appBodyL M'app ->
	  appBodyR Mapp = appBodyR M'app ->
	  M -R-> M'
	) ->
	(forall M M' (Mapp: isApp M) (M'app: isApp M'),
	  appBodyL Mapp = appBodyL M'app ->
	  appBodyR Mapp -R-> appBodyR M'app ->
	  M -R-> M'
	) ->
	(forall N N' (Nabs: isAbs N) (N'abs: isAbs N'),
	  absType Nabs = absType N'abs ->
	  absBody Nabs -R-> absBody N'abs ->
	  N -R-> N'
	) ->
	monotonous.

    Proof.
      unfold monotonous; intros M_AppL M_AppR M_Abs.
      induction pos; simpl; intros Mpos Npos MN.

       (* PThis *)
      replace (swap Mpos) with (proj1_sig2 Mpos).
      replace (swap Npos) with (proj1_sig2 Npos).
      trivial.
      apply term_eq.
      rewrite swap_env_eq; destruct Npos; try_solve.
      rewrite swap_term_is; try_solve.
      apply term_eq.
      rewrite swap_env_eq; destruct Mpos; try_solve.
      rewrite swap_term_is; try_solve.

       (* PAbs *)
      set (Labs := swap_abs Mpos).
      set (Rabs := swap_abs Npos).
      apply M_Abs with Labs Rabs.
      apply type_eq_absType_eq.
      do 2 rewrite swap_type_eq; trivial.
      destruct (placeHolder_abs Mpos) as [MLpos ML].
      destruct (placeHolder_abs Npos) as [NLpos NL].
      replace (absBody Labs) with (swap MLpos).
      replace (absBody Rabs) with (swap NLpos).
      apply IHpos.
      rewrite ML; rewrite NL; trivial.
      apply swap_in_abs; trivial.
      apply TAbs; trivial.
      apply swap_in_abs; trivial.
      apply TAbs; trivial.

       (* PAppL *)
      set (Lapp := swap_left_app Mpos).
      set (Rapp := swap_left_app Npos).
      apply M_AppL with Lapp Rapp.
      destruct (placeHolder_appL Mpos) as [MLpos ML].
      destruct (placeHolder_appL Npos) as [NLpos NL].
      replace (appBodyL Lapp) with (swap MLpos).
      replace (appBodyL Rapp) with (swap NLpos).
      apply IHpos.
      rewrite ML; rewrite NL; trivial.
      apply swap_in_appL; trivial.
      apply swap_in_appL; trivial.
      apply swap_appR_eq.

       (* PAppR *)
      set (Lapp := swap_right_app Mpos).
      set (Rapp := swap_right_app Npos).
      apply M_AppR with Lapp Rapp.
      apply swap_appL_eq.
      destruct (placeHolder_appR Mpos) as [MLpos ML].
      destruct (placeHolder_appR Npos) as [NLpos NL].
      replace (appBodyR Lapp) with (swap MLpos).
      replace (appBodyR Rapp) with (swap NLpos).
      apply IHpos.
      rewrite ML; rewrite NL; trivial.
      apply swap_in_appR; trivial.
      apply swap_in_appR; trivial.
    Qed.

    Variable R_monotonous : monotonous.

    Variable R_type_preserving : forall M N, M -R-> N -> type M = type N.

    Variable R_env_preserving: forall M N, M -R-> N -> env M = env N.

    Definition posAppLeft : forall M (Mapp: isApp M), Pos M.

    Proof.
      intros; term_inv M; unfold Tr.
      apply PAppL; apply PThis.
    Defined.
    
    Lemma monotonous_appL : forall M N (Mapp: isApp M) (Napp: isApp N),
	appBodyL Mapp -R-> appBodyL Napp -> appBodyR Mapp = appBodyR Napp -> M -R-> N.

    Proof.
      intros M N Mapp Napp MNl MNr.
      set (pos := posAppLeft M Mapp).
      assert (envOkL: env (M // pos) = env (appBodyL Mapp)).
      term_inv M.
      assert (typeOkL: type (M // pos) = type (appBodyL Mapp)).
      term_inv M.
      set (Tl := exist2 (fun L => env (M // pos) = env L) 
	(fun L => type (M // pos) = type L) (appBodyL Mapp) envOkL typeOkL).
      assert (envOkR: env (M // pos) = env (appBodyL Napp)).
      apply R_env_preserving; term_inv M.
      assert (typeOkR: type (M // pos) = type (appBodyL Napp)).
      apply R_type_preserving; term_inv M.
      set (Tr := exist2 (fun R => env (M // pos) = env R) 
	(fun R => type (M // pos) = type R) (appBodyL Napp) envOkR typeOkR).
      replace M with (swap Tl).
      replace N with (swap Tr).
      apply R_monotonous; trivial.
      apply term_eq.
      rewrite swap_env_eq; term_inv M; term_inv N.
      rewrite swap_term_is; term_inv M; term_inv N.
      change PtR with (term (buildT T2)). rewrite MNr; trivial.
      apply term_eq.
      rewrite swap_env_eq; term_inv M; term_inv N.
      rewrite swap_term_is; term_inv M; term_inv N.
    Qed.

  End Monotonicity.

End TermsPos.
