(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Convertibility of substituted terms.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras TermsSubst.
From Stdlib Require Import Arith Lia.

Module TermsSubstConv (Sig : TermsSig.Signature).

  Module Export TS := TermsSubst.TermsSubst Sig.

  Record subst_conv_with (G1: Subst) (G2: Subst) (Q: EnvSubst) : Prop := {
    sc_lr: forall x y T, Q.(envSub) x y -> G1 |-> x/T  ->
      exists T', G2 |-> y/T' /\ T ~(Q) T';
    sc_rl: forall x y T',Q.(envSub) x y -> G2 |-> y/T' ->
      exists T,  G1 |-> x/T /\ T ~(Q) T';
    sc_inj_l: forall x T, G1 |-> x/T -> exists y, Q.(envSub) x y;
    sc_inj_r: forall y T, G2 |-> y/T -> exists x, Q.(envSub) x y }.

  Notation "G ~~ ( S ) H" := (subst_conv_with G H S) (at level 70).

  Definition subst_conv G1 G2 := exists S, G1 ~~(S) G2.

  Infix "~~" := subst_conv (at level 70).

  Lemma subst_empty_conv : forall S, nil ~~(S) nil.

  Proof.
    intros; constructor; solve [destruct x; try_solve | destruct y; try_solve].
  Qed.

  Lemma conv_subst_udecl G G' Q x y :
    G ~~(Q) G' -> Q.(envSub) x y -> G |-> x/- -> G' |-> y/- .

  Proof.
    intros.
    destruct (nth_error_In G' y) as [[T GT] | Gn]; auto.
    destruct T.
    destruct (sc_rl H x H0 GT) as [W [GW _]].
    inversion H1; inversion GW; try_solve.
    constructor 2; trivial.
    constructor; trivial.
  Qed.

 Lemma singletonSubst_conv T T' G G' Q :
   isSingletonSubst T G -> isSingletonSubst T' G' -> G ~~(Q) G' -> T ~(Q) T'.

  Proof.
    intros.
    destruct H; destruct H0; destruct H1.
    assert (Q00: envSub Q 0 0).
    destruct (sc_inj_l0 0 T H).
    destruct x; trivial.
    destruct (sc_lr0 0 (S x) T H1 H) as [W [G'W _]].
    destruct (H3 x); inversion G'W; try_solve.
    destruct (sc_lr0 0 0 T Q00 H) as [T'' [G'T'' TT'']].
    assert (T'T'': T' = T'').
    inversion H0; inversion G'T''; destruct G'; try_solve.
    rewrite T'T''; trivial.
  Qed.

  Lemma singletonSubst_conv_rev T T' G G' Q : isSingletonSubst T G ->
    isSingletonSubst T' G' -> envSub Q 0 0 -> T ~(Q) T' -> G ~~(Q) G'.

  Proof.
    intros.
    destruct H; destruct H0.
    constructor; intros.

    destruct x; destruct y.
    exists T'; split; trivial.
    assert (T = T0).
    inversion H; inversion H6; try_solve.
    rewrite <- H7; trivial.
    absurd (S y = 0); [lia | apply envSub_Lok with Q 0; trivial].
    absurd (S x = 0); [lia | apply envSub_Rok with Q 0; trivial].
    destruct (H3 x); inversion H6; try_solve.

    destruct x; destruct y.
    exists T; split; trivial.
    assert (T'0 = T').
    inversion H0; inversion H6; try_solve.
    rewrite H7; trivial.
    absurd (S y = 0); [lia | apply envSub_Lok with Q 0; trivial].
    absurd (S x = 0); [lia | apply envSub_Rok with Q 0; trivial].
    destruct (H4 y); inversion H6; try_solve.

    destruct x.
    exists 0; trivial.
    destruct (H3 x); inversion H5; try_solve.

    destruct y.
    exists 0; trivial.
    destruct (H4 y); inversion H5; try_solve.
  Qed.

  Lemma uneffective_singleton_subst_conv M G T (MG: correct_subst M G) :
    isSingletonSubst T G -> (activeEnv M |= 0 :!) -> terms_conv M (subst MG).

  Proof.
    intros. apply terms_conv_criterion_strong.
    apply singleton_subst_activeEnv_noSubst with T; trivial.
    apply singleton_subst_term_noSubst with T; trivial.
  Qed.

  Lemma subst_conv_singleton M G G' Q :
    Q.(envSub) 0 0 -> isSingletonSubst M G -> G ~~(Q) G' ->
    exists M', isSingletonSubst M' G' /\ M ~(Q) M'.

  Proof.
    intros.
    destruct H0.
    destruct (sc_lr H1 0 H H0) as [W [NW MW]].
    exists W; split; trivial.
    constructor; trivial.
    intro i.
    destruct (nth_error_In G' (S i)) as [[T GT] | Gn]; auto.
    destruct T.
    destruct (sc_inj_r H1 GT).
    destruct x.
    absurd (0 = S i).
    lia.
    apply envSub_Lok with Q 0; trivial.
    apply conv_subst_udecl with G Q (S x); trivial.
    constructor 2; trivial.
    constructor; trivial.
  Qed.

  Lemma subst_conv_sym G1 G2 S : G1 ~~(S) G2 -> G2 ~~(envSubst_transp S) G1.

  Proof.
    intro G1G2. constructor; intros.
    destruct (@sc_rl G1 G2 S G1G2 y x T) as [T' [G1T' TT']]; trivial.
    destruct S; trivial.
    exists T'; split; auto.
    apply terms_conv_sym_aux; trivial.
    destruct (@sc_lr G1 G2 S G1G2 y x T') as [T [G2T' TT']]; trivial.
    destruct S; trivial.
    exists T; split; auto.
    apply terms_conv_sym_aux; trivial.
    destruct (sc_inj_r G1G2 H).
    exists x0; destruct S; trivial.
    destruct (sc_inj_l G1G2 H).
    exists x; destruct S; trivial.
  Qed.  

  Lemma subst_conv_cons G G' Q : G ~~(Q) G' ->
    None :: (lift_subst G 1) ~~(envSubst_lift1 Q) None :: (lift_subst G' 1).

  Proof.
    intros.
    constructor; intros.

    destruct x; destruct y; try_solve.
    destruct Q; try_solve.
    inversion H1.
    destruct (var_subst_lift_rev G 1 H3) as [W [GxW TW]].
    assert (envSub Q x y).
    destruct Q; try_solve.
    destruct (sc_lr H y H2 GxW) as [W' [G'yW' WW']].
    exists (lift W' 1); split.
    apply var_subst_cons.
    apply var_subst_lift; trivial.
    rewrite TW.
    apply terms_conv_conv_lift; trivial.
    
    destruct x; destruct y; try_solve.
    destruct Q; try_solve.
    inversion H1.
    destruct (var_subst_lift_rev G' 1 H3) as [W [GxW TW]].
    assert (envSub Q x y).
    destruct Q; try_solve.
    destruct (sc_rl H x H2 GxW) as [W' [G'yW' WW']].
    exists (lift W' 1); split.
    apply var_subst_cons.
    apply var_subst_lift; trivial.
    rewrite TW.
    apply terms_conv_conv_lift; trivial.

    destruct x; try_solve.
    inversion H0.
    destruct (var_subst_lift_rev G 1 H2) as [W [GxW _]].
    destruct (sc_inj_l H GxW).
    exists (S x0).
    destruct Q; try_solve.

    destruct y; try_solve.
    inversion H0.
    destruct (var_subst_lift_rev G' 1 H2) as [W [GxW _]].
    destruct (sc_inj_r H GxW).
    exists (S x).
    destruct Q; try_solve.
  Qed.

  Lemma conv_subst_conv_term_aux :
    forall M M' G G' Q, conv_term M M' Q -> G ~~(Q) G' ->
                        conv_term (presubst M G) (presubst M' G') Q.

  Proof.
    induction M; intros; inversion H.

     (* variable *)
    unfold presubst; simpl.
    destruct (varSubst_dec G x) as [[T GxT] | GxN].
    rewrite GxT.
    destruct (sc_lr H0 y H2 GxT) as [T' [G'yT' TT']].
    rewrite G'yT'.
    rewrite !lift_0.
    destruct TT'; trivial.
    inversion GxN; rewrite H5;
      destruct (conv_subst_udecl y H0 H2 GxN); rewrite H6; constructor; trivial.

     (* function symbol *)
    unfold presubst; simpl; constructor.

     (* abstraction *)
    unfold presubst; simpl; constructor.
    set (w := subst_lift_subst_aux M (None::G) 0 1).
    simpl in w; rewrite w.
    set (w' := subst_lift_subst_aux R (None::G') 0 1).
    simpl in w'; rewrite w'.
    fold (presubst M (None::lift_subst G 1)).
    fold (presubst R (None::lift_subst G' 1)).
    apply IHM; trivial.
    apply subst_conv_cons; trivial.

     (* application *)
    unfold presubst; simpl; constructor.
    fold (presubst M1 G); fold (presubst RL G').
    apply IHM1; trivial.
    fold (presubst M2 G); fold (presubst RR G').
    apply IHM2; trivial.
  Qed.

  Definition subst_envMinimal G := forall x T, G |-> x/T -> envMinimal T.

  Lemma subst_ran_decl_conv G G' S x y A :
    G ~~(S) G' -> envSub S x y -> subst_envs_comp G -> subst_envMinimal G' ->
    subst_ran G' |= y := A -> subst_ran G |= x := A.

  Proof.
    intros GG' Sxy G'comp G'min G'x.
    destruct (subst_ran_decl G' G'x) as [W [p [Gp Wx]]].
    destruct (sc_inj_r GG' Gp) as [q pq].
    destruct (sc_rl GG' q pq Gp) as [W' [G'W' WW']].
    apply subst_ran_component_comp with q W'; trivial.
    apply activeEnv_subset.
    apply (proj2 (proj2 WW' x y Sxy A)); trivial. 
    rewrite <- G'min with p W; trivial.
  Qed.

  Lemma conv_subst_correct M M' G G' S :
    M ~(S) M' -> envMinimal M' -> G ~~(S) G' -> subst_envs_comp G' ->
    subst_envMinimal G' -> correct_subst M G -> correct_subst M' G'.

  Proof.
    intros MM' M'min GG' G'comp G'min MG. constructor; trivial.

    intros p A B pG' pM'.
    destruct (subst_dom_varSubst_rev G' pG') as [W [G'W WA]].
    destruct GG'.
    destruct (sc_inj_r0 p W G'W) as [q qp].
    destruct MG as [envsMG domMG ranMG].
    apply (domMG q A B).
    destruct (sc_rl0 q p W qp G'W) as [W' [GW' WW']].
    rewrite <- WA.
    assert (W_W': W' ~ W).
    exists S; trivial.
    rewrite <- (terms_conv_eq_type W_W').
    apply subst_dom_varSubst; trivial.
    destruct MM'.
    apply activeEnv_subset.
    apply (proj2 (H0 q p qp B)).
    rewrite <- M'min; trivial.

    intros p A B pG'G' pM'.
    set (pG' := env_sub_suby_ly (subst_ran G') (subst_dom G') pG'G').
    destruct (subst_ran_decl G' pG') as [W [i [G'i Wp]]].
    destruct (sc_inj_r GG' G'i) as [m ml].
    destruct (sc_rl GG' m ml G'i) as [W' [GmW' WW']].
    destruct MG as [envsMG domMG ranMG].
    set (Wmin := G'min i W G'i).
    rewrite Wmin in Wp.
    destruct (terms_conv_activeEnv_rev WW' Wp) as [q qp].
    apply (ranMG q A B).
    apply env_sub_ly_rn.
    apply (subst_ran_decl_conv) with G' S p; trivial.
    apply subst_dom_varNotSubst.
    apply conv_subst_udecl with G' (envSubst_transp S) p.
    apply subst_conv_sym; destruct GG'; constructor; trivial.
    destruct S; trivial.
    apply subst_dom_varNotSubst_rev.
    apply env_sub_suby_rn with (subst_ran G') A; trivial.
    destruct MM'.
    apply activeEnv_subset.
    apply (proj2 (H0 q p qp B)).
    rewrite <- M'min; trivial.
  Qed.

  Lemma conv_subst_singleton_build M M' T G Q : envSub Q 0 0 -> M ~(Q) M' ->
    envSub_minimal Q M -> isSingletonSubst T G -> correct_subst M G ->
    exists Q' G' T',
      correct_subst M' G' /\ isSingletonSubst T' G' /\ Q' |=> Q /\ G ~~(Q') G'.

  Proof.
    intros.
    destruct (@term_build_conv T Q (None :: tail (env M'))) 
      as [Q' [Q'Q [T' [TT' [T'env T'min]]]]].
    intros.
    destruct x; destruct y.
    inversion H6.
    absurd (0 = S y); [lia | apply envSub_Lok with Q 0; trivial].
    absurd (S x = 0); [lia | apply envSub_Rok with Q 0; trivial].
    destruct (envSub_minimal_rev (S x) (S y) H1 H0 H4).
    replace B with x0.
    set (MM'comp := proj2 H0 (S x) (S y) H4).
    set (w := proj2 (MM'comp x0) H7).
    set (Tx := activeEnv_subset T H5).
    set (Mx := activeEnv_subset M w).
    apply (@ran_c M G H3 (S x)); trivial.
    rewrite (subst_ran_singleton H2).
    apply env_sub_ly_rn; trivial.
    destruct (subst_dom_singleton H2) as [E [Gdom Eempty]].
    rewrite Gdom; unfold VarUD; simpl.
    destruct (Eempty x); auto.
    assert (M'y := activeEnv_subset M' H7); clear H7.
    inversion H6; inversion M'y; destruct (env M'); try_solve.
    exists Q'; exists (Some T'::nil); exists T'; split.
    constructor.
    apply subst_envs_comp_single.
    intros p A B T'p M'p.
    destruct p.
    inversion T'p.
    rewrite <- (terms_conv_eq_type (conv_by TT')).
    apply (@dom_c M G H3 0).
    destruct (subst_dom_singleton H2) as [E [DomG Eempty]].
    rewrite DomG; constructor.
    apply activeEnv_subset.
    destruct (envSub_minimal_rev 0 0 H1 H0 H).
    inversion H0.
    set (M'0 := proj2 (H7 0 0 H x) H4).
    set (w := activeEnv_subset M' H4).
    assert (x = B).
    inversion w; inversion M'p; try_solve.
    rewrite <- H8; trivial.
    inversion T'p; destruct p; try_solve.
    rewrite subst_ran_single.
    intros p A B T'ps M'p.
    destruct p.
    destruct (env T'); try destruct o; try_solve.
    apply (T'env (S p)).
    apply (env_sub_suby_ly (env T') (subst_dom {x/T'})); trivial.
    inversion M'p; destruct (env M'); try_solve.
    split.
    apply singletonSubst_cond.
    split; trivial.
    apply singletonSubst_conv_rev with T T'; trivial.
    apply singletonSubst_cond.
    apply Q'Q; trivial.
  Qed.

  Lemma conv_subst_conv :
    forall M M' G G' Q (MG: correct_subst M G) (M'G': correct_subst M' G'),
      M ~(Q) M' -> G ~~(Q) G' -> (subst MG) ~(Q) (subst M'G').

  Proof.
    destruct M as [E Pt T M]; induction M; intros.
     (* variable *)
    inversion H; inversion H1.
    destruct (varSubst_dec G x) as [[T Gx] | Gxn].
    destruct (sc_lr H0 y H5 Gx) as [T' [G'y TT']].
    assert (MG_term: term (subst MG) = term T).
    autorewrite with terms using unfold presubst; simpl.
    rewrite Gx; rewrite lift_0; trivial.
    assert (M'G'_term: term (subst M'G') = term T').
    autorewrite with terms using unfold presubst; rewrite <- H4; simpl.
    rewrite G'y; rewrite lift_0; trivial.
    apply terms_conv_diff_env with T'; trivial.
    apply terms_conv_diff_env_rev with T; trivial.
    apply equiv_term_activeEnv; trivial.
    apply subst_env_compat with x; trivial.
    apply equiv_term_activeEnv; trivial.
    apply subst_env_compat with y; trivial.
    term_inv M'.
    assert (MG_term: term (subst MG) = %x).
    autorewrite with terms using unfold presubst; simpl.
    destruct Gxn; rewrite H7; trivial.
    assert (M'G'_term: term (subst M'G') = %x1).
    autorewrite with terms using unfold presubst; simpl.
    inversion H4; rewrite <- H8.
    destruct (conv_subst_udecl y H0 H5 Gxn); rewrite H7; trivial.
    apply terms_conv_diff_env with (buildT (TVar T)); trivial.
    apply terms_conv_diff_env_rev with (buildT (TVar v)); trivial.
    assert (type (subst MG) = A).
    autorewrite with terms using trivial.
    term_inv (subst MG).
    assert (type (subst M'G') = A0).
    autorewrite with terms using trivial.
    term_inv (subst M'G').
     (* function symbol *)
    inversion H.
    inversion H1.
    constructor.
    rewrite funS_presubst; simpl; trivial.
    rewrite funS_presubst; trivial.
    apply funS_is_funS with f; auto.
    intros x y xy A.
    rewrite activeEnv_funS.
    rewrite activeEnv_funS.
    destruct x; destruct y; try_solve.
    apply funS_subst_funS.
    apply funS_is_funS with f; auto.
    apply funS_is_funS with f.
    rewrite funS_presubst; simpl; trivial.
     (* abstraction *)
    destruct (abs_subst (M := buildT (TAbs M)) I MG).
    assert (M'abs: isAbs M').
    assert (H': (buildT (TAbs M)) ~ M') by (exists Q; trivial).
    rewrite <- H'; simpl; trivial.
    destruct (abs_subst M'abs M'G').
    apply abs_conv with (abs_subst_abs (M:=buildT (TAbs M)) I MG) 
      (abs_subst_abs M'abs M'G'); term_inv M'.
    inversion H; inversion H5; try_solve.
    rewrite H2; rewrite H4.
    apply IHM; trivial.
    constructor; simpl.
    inversion H; inversion H5; trivial.
    change (buildT M) with (absBody (M:=buildT (TAbs M)) I).
    change (buildT T) with (absBody (M:=buildT (TAbs T)) I).
    apply conv_env_absBody; trivial.
    inversion H; inversion H5; trivial.
    inversion H; trivial.
    apply subst_conv_cons; trivial.
     (* application *)
    destruct (app_subst (M := buildT (TApp M1 M2)) I MG).
    assert (M'app: isApp M').
    assert (H' : (buildT (TApp M1 M2)) ~ M') by (exists Q; trivial).
    rewrite <- H'; simpl; trivial.
    destruct (app_subst M'app M'G').
    apply app_conv with (app_subst_app (M:=buildT (TApp M1 M2)) I MG)
      (app_subst_app M'app M'G').
    rewrite H1; rewrite H3.
    apply IHM1; trivial.
    change (buildT M1) with (appBodyL (M:=buildT (TApp M1 M2)) I).
    apply app_conv_app_left_aux; trivial.
    rewrite H2; rewrite H4.
    apply IHM2; trivial.
    change (buildT M2) with (appBodyR (M:=buildT (TApp M1 M2)) I).
    apply app_conv_app_right_aux; trivial.
  Qed.
  
  Lemma presubst_singleton_conv_sim_aux : forall M M' T T' Q R R' i,
    (forall j, j <= i -> envSub Q j j) -> conv_term M M' Q ->
    (lift T i) ~(Q) (lift T' i) ->
    conv_term R R' Q -> presubst_aux M i (copy i None ++ {x/T}) = R ->
    presubst_aux M' i (copy i None ++ {x/T'}) = R'.

  Proof.
    induction M; unfold presubst; simpl; intros; inversion H0;
      rewrite <- H3 in H2.
     (* variable *)
    destruct (lt_eq_lt_dec i x) as [[i_x | i_x] | i_x].
    rewrite nth_beyond in H2.
    inversion H2.
    simpl; rewrite nth_beyond.
    cut (y = y0); auto.
    apply envSub_Lok with Q x; trivial.
    autorewrite with datatypes using simpl.
    destruct (le_gt_dec y i).
    absurd (x = y).
    lia.
    apply envSub_Rok with Q y; trivial.
    apply H; trivial.
    lia.
    autorewrite with datatypes using simpl; try lia.
    rewrite nth_app_right in H2; autorewrite with datatypes using try lia.
    replace (x - length (copy i (None (A:=Term)))) with 0 in H2.
    simpl in H2.
    destruct H1.
    assert (x = y).
    apply envSub_Lok with Q x; trivial.
    apply H; lia.
    rewrite  <- H9; simpl.
    rewrite nth_app_right; autorewrite with datatypes.
    replace (x - i) with 0; simpl.
    apply conv_term_unique with (term (lift T i)) Q; trivial.
    lia.
    lia.
    autorewrite with datatypes using lia.
    rewrite nth_app_left in H2; autorewrite with datatypes using trivial.
    rewrite nth_copy_in in H2; trivial.
    assert (x = y).
    apply envSub_Lok with Q x; trivial.
    apply H; lia.
    rewrite <- H8; simpl.
    rewrite nth_app_left; autorewrite with datatypes using trivial.
    inversion H2.
    cut (x = y0); auto.
    rewrite <- H8 in H5.
    apply envSub_Lok with Q x; trivial.
     (* function symbol *)
    inversion H2; trivial.
     (* abstraction *)
    inversion H2.
    change (None :: copy i None ++ {x/T'}) with 
      (copy (Datatypes.S i) None ++ {x/T'}).
    assert (presubst_aux R0 (Datatypes.S i) (copy (Datatypes.S i) None
                                                  ++ {x/T'}) = R1).
    apply (@IHM R0 T T' (envSubst_lift1 Q) L0 R1 (Datatypes.S i)); auto.
    intros j j_i; destruct j; destruct Q; simpl; trivial.
    apply H; lia.
    rewrite <- (lift_fold_1out T).
    rewrite <- (lift_fold_1out T').
    apply terms_conv_conv_lift; trivial.
    rewrite H11; trivial.
    try_solve.
     (* application *)
    inversion H2.
    simpl.
    rewrite (IHM1 RL T T' Q LL0 RL0); auto.
    rewrite (IHM2 RR T T' Q LR0 RR0); auto.
    rewrite H11; trivial.
    rewrite H10; trivial.
  Qed.

  Lemma presubst_singleton_conv_sim M M' T T' Q R R' :
    envSub Q 0 0 -> conv_term M M' Q -> T ~(Q) T' -> conv_term R R' Q ->
    presubst M {x/T} = R -> presubst M' {x/T'} = R'.

  Proof.
    intros.
    unfold presubst.
    change {x/T'} with (copy 0 None ++ {x/T'}).
    apply presubst_singleton_conv_sim_aux with M T Q R; trivial.
    intros; destruct j; trivial.
    lia.
    rewrite !lift_0; trivial.
  Qed.

End TermsSubstConv.
