(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Definition and properties of active environments: subset of term
environments with declarations that are really used in a term.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras TermsEnv LogicUtil.
From Coq Require Import Arith Lia.

Module TermsActiveEnv (Sig : TermsSig.Signature).

  Module Export TE := TermsEnv.TermsEnv Sig.

  Definition activeEnv (M: Term) : Env :=
    match M with
    | @buildT E Pt T M0 =>
      Typing_rect
      (fun E0 Pt0 T0 _ => Env)
      (fun _ x A _ => copy x None ++ A [#] EmptyEnv)
      (fun _ _ => EmptyEnv)
      (fun _ _ _ _ _ Ein => tail Ein)
      (fun _ _ _ _ _ _ El _ Er => El [+] Er)
      M0
    end.

  Definition envMinimal M := env M = activeEnv M.

  Lemma activeEnv_length : forall M, length (activeEnv M) <= length (env M).

  Proof.
    destruct M as [E Pt T M]; induction M.
    simpl; autorewrite with datatypes using simpl.
    assert (x < length E); [idtac | lia].
    apply (proj1 (nth_in E x)).
    inversion v; try_solve.
    simpl; lia.
    simpl; fold (activeEnv (buildT M)).
    destruct (activeEnv (buildT M)).
    simpl; lia.
    simpl in *; lia.
    simpl; fold (activeEnv (buildT M1)); fold (activeEnv (buildT M2)).
    rewrite env_sum_length.
    apply Nat.max_case; trivial.
  Qed.

  Lemma activeEnv_abs : forall M (Mabs: isAbs M),
    activeEnv M = tail (activeEnv (absBody Mabs)).

  Proof.
    intros M; term_inv M.
  Qed.

  Lemma activeEnv_app : forall M (Mapp: isApp M),
    activeEnv M = activeEnv (appBodyL Mapp) [+] activeEnv (appBodyR Mapp).

  Proof.
    intros M; term_inv M.
  Qed.

  Lemma activeEnv_funS : forall M (Mfs: isFunS M), activeEnv M = EmptyEnv.

  Proof.
    intro M; term_inv M.
  Qed.

  Lemma activeEnv_var_det : forall M x i A,
    term M = %x -> activeEnv M |= i := A -> i = x /\ A = type M.

  Proof.
    unfold VarD; intros.
    term_inv M.
    destruct (lt_eq_lt_dec x0 i) as [[x_lt_i | x_eq_i] | x_gt_i].
    rewrite nth_app_right in H0.
    destruct (O_or_S (i - length (copy x0 (None (A:=SimpleType)))))
      as [[m sm] | z].
    rewrite <- sm in H0; simpl in H0; destruct m; try_solve.
    absurd (0 = i - length (copy x0 (None (A:=SimpleType)))); trivial.
    autorewrite with datatypes using lia.
    autorewrite with datatypes; lia.
    rewrite x_eq_i in H0.
    rewrite nth_app_right in H0.
    replace (i - length (copy i (None (A:=SimpleType)))) with 0 in H0.
    rewrite <- x_eq_i.
    replace A0 with A.
    split; trivial.
    inversion H; trivial.
    inversion H0; trivial.
    autorewrite with datatypes using lia.
    autorewrite with datatypes using lia.
    rewrite nth_app_left in H0.
    rewrite nth_copy_in in H0; try_solve.
    autorewrite with datatypes using lia.
  Qed.

  Lemma activeEnv_var_single : forall M x y A,
    term M = %x -> activeEnv M |= y := A -> x = y.

  Proof.
    intros.
    destruct (activeEnv_var_det M H H0); auto.
  Qed.

  Lemma activeEnv_var_type : forall M x y A,
    term M = %x -> activeEnv M |= y := A -> A = type M.

  Proof.
    intros.
    destruct (activeEnv_var_det M H H0); trivial.
  Qed.

  Lemma activeEnv_subset : forall M, envSubset (activeEnv M) (env M).

  Proof.
    destruct M as [E Pt T M]; induction M; simpl; intros; intros x0 A0 H.
    inversion H.
    destruct (@activeEnv_var_det (buildT (TVar v)) x x0 A0); trivial.
    rewrite H2; rewrite H0; trivial.
    destruct x0; try_solve.
    fold (activeEnv (buildT M)) in H.
    assert (activeEnv (buildT M) |= S x0 := A0).
    destruct (activeEnv (buildT M)); try_solve.
    destruct x0; try_solve.
    set (w := IHM (S x0) A0 H0).
    inversion w; trivial.
    fold (activeEnv (buildT M1)) in H.
    fold (activeEnv (buildT M2)) in H.
    destruct (env_sum_varDecl (activeEnv (buildT M1)) (activeEnv (buildT M2)) H)
      as [[DL _] | DR].
    apply IHM1; trivial.
    apply IHM2; trivial.
  Qed.

  Lemma activeEnv_abs0 : forall M (Mabs: isAbs M) A,
    activeEnv (absBody Mabs) |= 0 := A -> A = absType Mabs.

  Proof.
    intros.
    term_inv M.
    fold (activeEnv (buildT T)) in H.
    set (w := activeEnv_subset (buildT T) H).
    inversion w; trivial.
  Qed.

  Lemma activeEnv_app_comp : forall M (Mapp: isApp M),
    activeEnv (appBodyL Mapp) [<->] activeEnv (appBodyR Mapp).

  Proof.
    intros M Mapp p A B LA RB.
    set (l := activeEnv_subset (appBodyL Mapp) LA).
    rewrite appBodyL_env in l.
    set (r := activeEnv_subset (appBodyR Mapp) RB).
    rewrite appBodyR_env in r.
    inversion l; inversion r; try_solve.
  Qed.

  Lemma activeEnv_appBodyL_varD : forall M (Mapp: isApp M),
    envSubset (activeEnv (appBodyL Mapp)) (activeEnv M).

  Proof.
    intro M; term_inv M.
    fold (activeEnv (buildT T1)); fold (activeEnv (buildT T2)); intros;
      intros x A0.
    apply env_sum_ly; trivial.
    apply (activeEnv_app_comp (buildT (TApp T1 T2)) I).
  Qed.

  Lemma activeEnv_appBodyR_varD : forall M (Mapp: isApp M),
    envSubset (activeEnv (appBodyR Mapp)) (activeEnv M).

  Proof.
    intro M; term_inv M.
    fold (activeEnv (buildT T1)); fold (activeEnv (buildT T2)); intros;
      intros x A0.
    apply env_sum_ry; trivial.
  Qed.

  Lemma typing_activeEnv : forall M, activeEnv M |- term M := type M.

  Proof.
    destruct M as [E Pt T M].
    induction M; simpl.
    constructor 1.
    unfold VarD; rewrite nth_app_right; autorewrite with datatypes.
    replace (x - x) with 0; trivial.
    lia.
    lia.
    constructor.
    constructor.
    fold (activeEnv (buildT M)).
    apply typing_ext_env with (activeEnv (buildT M)); trivial.
    intros x C MAx.
    assert (forall C, activeEnv (buildT M) |= 0 := C -> A = C).
    intros; set (w := activeEnv_subset (buildT M) H).
    inversion w; trivial.
    destruct (activeEnv (buildT M)).
    inversion MAx; destruct x; try_solve.
    destruct x; try_solve.
    rewrite (H C); trivial.
    constructor.
    constructor 4 with A.
    apply typing_ext_env_r; trivial.
    apply (activeEnv_app_comp (buildT (TApp M1 M2)) I).
    apply typing_ext_env_l; trivial.
  Qed.

  Lemma term_env_activeEnv : forall M, env M = env M [+] activeEnv M.

  Proof.
    intros.
    apply env_subset_as_sum_r.
    apply activeEnv_length.
    apply activeEnv_subset.
  Qed.

  Lemma equiv_term_activeEnv : forall M N,
    term M = term N -> env M [<->] env N -> activeEnv M = activeEnv N.

  Proof.
    intro M; destruct M as [E Pt T M]; induction M; intro N; term_inv N; intros.
     (* variable *)
    inversion H.
    rewrite (H0 x A A0); trivial.
    rewrite H2; trivial.
     (* abstraction *)
    fold (activeEnv (buildT T)).
    rewrite <- (IHM (buildT T)); trivial.
    inversion H; trivial.
    simpl; unfold decl.
    apply env_comp_cons; trivial.
    left; inversion H; trivial.
     (* application *)
    fold (activeEnv (buildT T1)).
    fold (activeEnv (buildT T2)).
    rewrite <- IHM1.
    rewrite <- IHM2; trivial. 
    inversion H; trivial.
    inversion H; trivial.
    trivial.
  Qed.

  Lemma activeEnv_var : forall M x,
    term M = %x -> activeEnv M = copy x None ++ type M [#] EmptyEnv.

  Proof.
    intro M; term_inv M.
  Qed.

  Lemma activeEnv_var_decl : forall M x A,
    term M = %x -> env M |= x := A -> activeEnv M |= x := A.

  Proof.
    intro M; term_inv M; intros.
    inversion H.
    replace A with A0.
    unfold VarD, EmptyEnv, decl; apply nth_after_copy.
    rewrite <- H2 in H0.
    inversion T; inversion H0; try_solve.
  Qed.

  Lemma activeEnv_lift_aux : forall M n k,
    activeEnv (proj1_sig (lift_aux n M k)) [=] liftedEnv n (activeEnv M) k.

  Proof.
    destruct M as [E Pt T M]; induction M; intros.
     (* variable *)
    unfold liftedEnv; simpl.
    destruct (le_gt_dec k x); simpl.
    rewrite initialSeg_app; autorewrite with datatypes using trivial.
    rewrite initialSeg_copy.
    rewrite Nat.min_r; trivial.
    rewrite finalSeg_copy; trivial.
    rewrite <- copy_split.
    repeat (rewrite <- app_ass; rewrite <- copy_split).
    replace (x + n) with (k + n + (x - k)); [apply env_eq_refl | lia].
    rewrite initialSeg_full; autorewrite with datatypes using simpl; try lia.
    rewrite finalSeg_empty; autorewrite with datatypes using simpl; try lia.
    rewrite <- app_nil_end.
    apply env_eq_empty_tail.
     (* function symbol *)
    simpl; unfold liftedEnv.
    destruct k; unfold finalSeg; simpl; rewrite <- app_nil_end;
      change (copy n (None (A:=SimpleType))) with (EmptyEnv ++ copy n None);
	apply env_eq_empty_tail.
     (* abstraction *)
    rewrite activeEnv_abs with (buildT (TAbs M)) I.
    set (l := proj1_sig (lift_aux n (buildT (TAbs M)) k)).
    assert (labs: isAbs l).
    apply abs_isAbs with A (prelift_aux n Pt (S k)).
    unfold l; destruct (lift_aux n (buildT (TAbs M)) k) as [W [WE [WPt WT]]].
    simpl; rewrite WPt; trivial.
    rewrite (activeEnv_abs l labs).
    rewrite (lift_tail (activeEnv (absBody (M:=buildT (TAbs M)) I)) n k).
    apply env_eq_tail.
    simpl; fold (activeEnv (buildT M)).
    rewrite <- (IHM n (S k)).
    unfold l; rewrite (lift_absBody M).
    apply env_eq_refl.
     (* application *)
    rewrite activeEnv_app with (buildT (TApp M1 M2)) I.
    rewrite (liftedEnv_distr_sum
      (activeEnv (appBodyL (M:=buildT (TApp M1 M2)) I))
      (activeEnv (appBodyR (M:=buildT (TApp M1 M2)) I)) n k).
    set (l := proj1_sig (lift_aux n (buildT (TApp M1 M2)) k)).
    assert (lapp: isApp l).
    apply app_isApp with (prelift_aux n PtL k) (prelift_aux n PtR k).
    unfold l; destruct (lift_aux n (buildT (TApp M1 M2)) k) as [W [WE [WPt WT]]].
    simpl; rewrite WPt; trivial.
    rewrite (activeEnv_app l lapp).
    unfold l.
    rewrite (lift_appBodyL n k M1 M2 lapp).
    rewrite (lift_appBodyR n k M1 M2 lapp).
    rewrite (IHM1 n k).
    rewrite (IHM2 n k).
    apply env_eq_sum; apply env_eq_refl.
  Qed.

  Lemma activeEnv_lift : forall M n,
    activeEnv (lift M n) [=] liftedEnv n (activeEnv M) 0.

  Proof.
    intros; unfold lift.
    apply activeEnv_lift_aux.
  Qed.

  Lemma activeEnv_lower_aux : forall M n (Menv: env M |= n :!),
    activeEnv (proj1_sig (lower_aux M Menv)) = loweredEnv (activeEnv M) n.

  Proof.
    destruct M as [E Pt T M]; induction M; intros.
     (* variable *)
    unfold loweredEnv; simpl.
    destruct (le_gt_dec n x); simpl.
    destruct (le_gt_dec x n).
    exfalso; apply varD_UD_absurd with E x A; trivial.
    replace x with n; [trivial | lia].
    rewrite initialSeg_app; autorewrite with datatypes using trivial.
    rewrite initialSeg_copy.
    rewrite Nat.min_r; trivial.
    rewrite finalSeg_copy; [idtac | lia].
    rewrite <- app_ass.
    rewrite <- copy_split.
    replace (pred x) with (n + (x - S n)); trivial.
    lia.
    rewrite initialSeg_full; autorewrite with datatypes using simpl; try lia.
    rewrite finalSeg_empty; autorewrite with datatypes using simpl; try lia.
    rewrite <- app_nil_end; trivial.
     (* function symbol *)
    destruct n; try_solve.
     (* abstraction *)
    rewrite activeEnv_abs with (buildT (TAbs M)) I.
    set (l := proj1_sig (lower_aux (buildT (TAbs M)) Menv)).
    assert (labs: isAbs l).
    apply abs_isAbs with A (prelower_aux Pt (S n)).
    unfold l; destruct (lower_aux (buildT (TAbs M)) Menv) as [W [WE [WPt WT]]].
    simpl; rewrite WPt; trivial.
    rewrite (activeEnv_abs l labs).
    rewrite (lower_tail (activeEnv (absBody (M:=buildT (TAbs M)) I)) n).
    replace (activeEnv (absBody labs)) with 
      (loweredEnv (activeEnv (absBody (M:=buildT (TAbs M)) I)) (S n)); trivial.
    change (absBody (M:=buildT (TAbs M)) I) with (buildT M).
    rewrite <- (IHM (S n) Menv).
    rewrite (@lower_absBody E Pt A B M n Menv Menv); trivial.
     (* application *)
    rewrite activeEnv_app with (buildT (TApp M1 M2)) I.
    rewrite loweredEnv_distr_sum.
    set (l := proj1_sig (lower_aux (buildT (TApp M1 M2)) Menv)).
    assert (lapp: isApp l).
    apply app_isApp with (prelower_aux PtL n) (prelower_aux PtR n).
    unfold l; destruct (lower_aux (buildT (TApp M1 M2)) Menv)
      as [W [WE [WPt WT]]].
    simpl; rewrite WPt; trivial.
    rewrite (activeEnv_app l lapp).
    unfold l.
    set (wL := lower_appBodyL Menv M1 M2 lapp); simpl in *; rewrite wL.
    set (wR := lower_appBodyR Menv M1 M2 lapp); simpl in *; rewrite wR.
    rewrite (IHM1 n).
    rewrite (IHM2 n); trivial.
  Qed.

  Lemma activeEnv_lower : forall M Menv,
    activeEnv (lower M Menv) = loweredEnv (activeEnv M) 0.

  Proof.
    intros.
    unfold lower.
    apply activeEnv_lower_aux.
  Qed.

  Lemma activeEnv_minimal_len : forall M M', env M [<->] env M' ->
    term M = term M' -> length (activeEnv M) = length (activeEnv M').

  Proof.
    destruct M as [E Pt T M]; induction M; intros; term_inv M'.
     (* variable *)
    inversion H0.
    autorewrite with datatypes using simpl; trivial.
     (* abstraction *)
    fold (activeEnv (buildT M)) in *; fold (activeEnv (buildT T)).
    rewrite !length_tail_minus.
    inversion H0.
    rewrite (IHM (buildT T)); simpl; trivial.
    unfold decl; apply env_comp_cons; trivial.
    left; try_solve.
     (* application *)
    fold (activeEnv (buildT M1)) in *; fold (activeEnv (buildT T1)).
    fold (activeEnv (buildT M2)) in *; fold (activeEnv (buildT T2)).
    rewrite !env_sum_length.
    inversion H0.
    rewrite (IHM1 (buildT T1)); trivial.
    rewrite (IHM2 (buildT T2)); trivial.
  Qed.

  Lemma activeEnv_minimal_aux : forall M M', env M [<->] env M' ->
    term M = term M' -> envSubset (activeEnv M) (activeEnv M').

  Proof.
    destruct M as [E Pt T M]; induction M; intros; term_inv M'.
     (* variable *)
    inversion H0.
    apply env_subset_single.
    rewrite (H x A A0); trivial.
    unfold VarD, decl, EmptyEnv; apply nth_after_copy.
    rewrite H2; trivial.
     (* function symbol *)
    (*apply env_subset_empty.*)
     (* abstraction *)
    fold (activeEnv (buildT M)); fold (activeEnv (buildT T)); 
      fold (activeEnv (buildT M)) in IHM.
    apply env_subset_tail.
    inversion H0.
    apply IHM; simpl; trivial.
    unfold decl; apply env_comp_cons; trivial.
    left; try_solve.
     (* application *)
    fold (activeEnv (buildT M1)) in *; fold (activeEnv (buildT T1)).
    fold (activeEnv (buildT M2)) in *; fold (activeEnv (buildT T2)).
    inversion H0.
    apply env_subset_sum.
    change (buildT T1) with (appBodyL (M:=buildT (TApp T1 T2)) I).
    change (buildT T2) with (appBodyR (M:=buildT (TApp T1 T2)) I).
    apply activeEnv_app_comp.
    apply IHM1; simpl; trivial.
    apply IHM2; simpl; trivial.
  Qed.

  Lemma activeEnv_minimal : forall M M',
    env M [<->] env M' -> term M = term M' -> activeEnv M = activeEnv M'.

  Proof.
    intros.
    apply env_equiv_eq.
    split.
    apply activeEnv_minimal_aux; trivial.
    apply activeEnv_minimal_aux; auto.
    apply env_comp_sym; trivial.
    apply activeEnv_minimal_len; trivial.
  Qed.

  Lemma envMinimal_app : forall M Ml Mr (Mapp: isApp M),
    envMinimal Ml -> envMinimal Mr -> env Ml [<->] env Mr ->
    env M = env Ml [+] env Mr -> term M = term Ml @@ term Mr -> envMinimal M.

  Proof.
    unfold envMinimal; intros.
    rewrite activeEnv_app with M Mapp.
    rewrite H2.
    rewrite (@activeEnv_minimal (appBodyL Mapp) Ml); trivial.
    rewrite (@activeEnv_minimal (appBodyR Mapp) Mr); trivial.
    rewrite H; rewrite H0; trivial.
    rewrite appBodyR_env.
    rewrite H2.
    apply env_comp_ext_l.
    rewrite (appBodyR_term M H3); trivial.
    rewrite appBodyL_env.    
    rewrite H2.
    apply env_comp_sym.
    apply env_comp_sum; auto with terms.
    rewrite (appBodyL_term M H3); trivial.
  Qed.

  Lemma envMinimal_abs : forall M N (Mabs: isAbs M),
    term (absBody Mabs) = term N ->
    tail (env (absBody Mabs)) = tail (env N) ->
    (env N |= 0 :! \/ env N |= 0 := absType Mabs) ->
    envMinimal N -> envMinimal M.

  Proof.
    unfold envMinimal; intros.
    rewrite (activeEnv_abs M Mabs).
    rewrite (@activeEnv_minimal (absBody Mabs) N); trivial.
    rewrite <- H2.
    rewrite <- H0.
    rewrite absBody_env; trivial.
    rewrite absBody_env.
    destruct (env N).
    apply env_comp_empty.
    unfold decl; apply env_comp_cons.
    rewrite absBody_env in H0.
    simpl in H0; rewrite H0; auto with terms.
    destruct o; auto.
    destruct H1; inversion H1; try_solve.
  Qed.

  Lemma activeEnv_subset_unit : forall Mu M,
    isAppUnit Mu M -> envSubset (activeEnv Mu) (activeEnv M).

  Proof.
    destruct M as [E Pt T M]; induction M.
    intros; rewrite (appUnit_notApp (buildT (TVar v)) Mu); auto with terms.
    apply env_subset_refl.
    intros; rewrite (appUnit_notApp (buildT (TFun E f)) Mu); auto with terms.
    apply env_subset_refl.
    intros; rewrite (appUnit_notApp (buildT (TAbs M)) Mu); auto with terms.
    apply env_subset_refl.
    intros.
    rewrite (@activeEnv_app (buildT (TApp M1 M2)) I).
    destruct (appUnit_app Mu (buildT (TApp M1 M2)) I); trivial.
    rewrite H0.
    apply env_subset_sum_r; apply env_subset_refl.
    apply env_subset_sum_l.
    apply activeEnv_app_comp.
    apply IHM1; trivial.
  Qed.

  Lemma activeEnv_subset_arg : forall Marg M, isArg Marg M ->
    envSubset (activeEnv Marg) (activeEnv M).

  Proof.
    intros.
    apply activeEnv_subset_unit.
    apply appArg_is_appUnit; trivial.
  Qed.

  Lemma activeEnv_subset_units : forall M N,
    (forall N', In N' (appUnits N) -> envSubset (activeEnv N') (activeEnv M)) ->
    envSubset (activeEnv N) (activeEnv M).

  Proof.
    intros M N; gen M; clear M.
    apply well_founded_ind with (R := subterm)
      (P := fun N =>
	forall M,
	  (forall N', 
	    In N' (appUnits N) -> 
	    envSubset (activeEnv N') (activeEnv M)
	  ) ->
	  envSubset (activeEnv N) (activeEnv M)).
    apply subterm_wf.
    clear N; intros N IH M H.
    destruct (isApp_dec N) as [Napp | Nnapp].
    rewrite (activeEnv_app N Napp).
    apply env_subset_lsum.
    apply IH.
    apply appBodyL_subterm.
    intros.
    apply H.
    fold (isAppUnit N' N).
    apply appUnit_left with Napp; trivial.    
    apply H.
    apply appArg_is_appUnit.
    apply appArg_right with Napp; trivial.
    apply H.
    rewrite appUnits_notApp; auto with datatypes.
  Qed.

  Lemma activeEnv_subset_partialFlattening : forall M N Ns,
    isPartialFlattening Ns N ->
    (forall N', In N' Ns -> envSubset (activeEnv N') (activeEnv M)) ->
    envSubset (activeEnv N) (activeEnv M).

  Proof.
    intros M N; gen M; clear M.
    apply well_founded_ind with (R := subterm)
      (P := fun N =>
	forall M Ns,
	  isPartialFlattening Ns N ->
	  (forall N', 
	    In N' Ns ->
	    envSubset (activeEnv N') (activeEnv M)
	  ) ->
	  envSubset (activeEnv N) (activeEnv M)).
    apply subterm_wf.
    clear N; intros N IH M Ns NsN H.    
    set (Napp := partialFlattening_app N Ns NsN).
    rewrite (activeEnv_app N Napp).
    destruct (partialFlattening_inv N Napp Ns NsN) 
      as [Ns_def | [Ns' [Ns'flat Ns_def]]].
    apply env_subset_lsum.
    apply H.
    rewrite Ns_def; auto with datatypes.
    apply H.
    rewrite Ns_def; auto with datatypes.
    apply env_subset_lsum.
    apply IH with Ns'; trivial.
    apply appBodyL_subterm.
    intros.
    apply H.
    rewrite Ns_def; auto with datatypes.
    apply H.
    rewrite Ns_def; auto with datatypes.
  Qed.

End TermsActiveEnv.
