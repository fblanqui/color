(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Operation of lifting (increasing indexes of variables) 
and lowering (decreasing them) on terms of simply typed
lambda-calculus (which is an equivalent of renaming
of variables for the representation of terms using
de Bruijn indices) is defined in this file.
*)

Set Implicit Arguments.

From Coq Require Import Compare_dec Arith Lia.
From CoLoR Require Import RelExtras ListExtras LogicUtil.
From CoLoR Require TermsManip.

Module TermsLifting (Sig : TermsSig.Signature).

  Module Export TB := TermsManip.TermsManip Sig.

  Fixpoint prelift_aux (n: nat) (P: Preterm) (k: nat) : Preterm :=
    match P with
    | Fun _ => P
    | Var i => 
        match (le_gt_dec k i) with
	| left _ =>  (* i >= k *) Var (i + n)
	| right _ => (* i < k *)  Var i
	end
    | App M N => App (prelift_aux n M k) (prelift_aux n N k)
    | Abs A M => Abs A (prelift_aux n M (S k))
    end.
  Definition prelift P n := prelift_aux n P 0.

  Definition liftedEnv (n: nat) (E: Env) (k: nat) : Env :=
    initialSeg E k ++ copy n None ++ finalSeg E k.

  Lemma liftedEnv_next : forall A E n k,
    liftedEnv n (decl A E) (S k) = decl A (liftedEnv n E k).

  Proof.
    intros A E n k.
    unfold liftedEnv; simpl.
    destruct k.
    simpl.
    rewrite finalSeg_full.
    unfold decl; rewrite finalSeg_cons; trivial.
    destruct E; trivial.
  Qed.

  #[global] Hint Rewrite liftedEnv_next : terms.

  Lemma liftedEnv_var_lifted : forall E x A k n, E |= x := A -> x >= k ->
    liftedEnv n E k |= x + n := A.

  Proof.
    intros E x A k n.
    unfold VarD, liftedEnv.
    intros E_x x_k.
    assert (x_E: x < length E).
    rewrite_lr (nth_in E x).
    destruct (nth_error E x); discr.
    assert (k_E: Min.min k (length E) = k).
    apply Min.min_l.
    lia.
    rewrite nth_app_right; autorewrite with datatypes.
    rewrite k_E.
    rewrite nth_app_right; autorewrite with datatypes.
    replace (k + (x + n - k - n)) with x; trivial.
    lia.
    lia.
    lia.
  Qed.

  Lemma liftedEnv_var_notLifted : forall E x A k n,
    E |= x := A -> x < k -> liftedEnv n E k |= x := A.

  Proof.
    unfold VarD, liftedEnv.
    intros E x A k n Ex x_k.
    rewrite nth_app_left.
    rewrite initialSeg_nth; trivial.
    autorewrite with datatypes.
    apply (Min.min_case2 k (length E)); trivial.
    rewrite_lr (nth_in E x).
    destruct (nth_error E x); discr.    
  Qed.

  Lemma var_liftedEnv_var_lifted : forall E x A k n,
    liftedEnv n E k |= x + n := A -> x >= k -> E |= x := A.

  Proof.
    unfold VarD, liftedEnv.
    intros E x A k n Ex x_k.
    assert (x < length E).
    set (q := initialSeg E k ++ copy n None ++ finalSeg E k).
    assert (nth_error q (x + n) <> None).
    unfold q; try_solve.
    set (w := proj1 (nth_in q (x + n)) H).
    assert (length q = length E + n).
    unfold q.
    do 2 rewrite length_app.
    rewrite plus_comm.
    rewrite <- plus_assoc.
    rewrite (plus_comm (length (finalSeg E k)) (length (initialSeg E k))).
    rewrite initialFinalSeg_length.
    autorewrite with datatypes using lia.
    rewrite H0 in w; lia.
    rewrite nth_app_right in Ex.
    rewrite initialSeg_length in Ex.
    destruct (le_lt_dec k (length E)).
    rewrite nth_app_right in Ex.
    rewrite copy_length in Ex.
    rewrite Min.min_l in Ex; trivial.
    rewrite (finalSeg_nth_nth E x_k).
    replace (x - k) with (x + n - k - n); trivial.
    lia.
    autorewrite with datatypes.
    rewrite Min.min_l; trivial.
    lia.
    lia.
    autorewrite with datatypes.
    destruct (le_gt_dec k (length E)).
    rewrite Min.min_l; solve [trivial | lia].
    lia.
  Qed.

  Lemma var_liftedEnv_var_notLifted : forall E x A k n,
    liftedEnv n E k |= x := A -> x < k -> E |= x := A.

  Proof.
    unfold VarD, liftedEnv.
    intros E x A k n Ex x_k.
    destruct (le_gt_dec k (length E)).
    rewrite nth_app_left in Ex.
    rewrite <- (initialSeg_nth E x_k); trivial.
    autorewrite with datatypes.
    rewrite Min.min_l; trivial.
    destruct (le_gt_dec (length E) x).
    rewrite nth_app_right in Ex.
    rewrite initialSeg_length in Ex.
    rewrite Min.min_r in Ex; [trivial | lia].
    rewrite finalSeg_empty in Ex; trivial.
    rewrite <- app_nil_end in Ex.
    destruct (le_gt_dec (length (copy n (A := option SimpleType) None)) 
      (x - length E)).
    set (w := nth_beyond (copy n None) l0); try_solve.
    assert (x - length E < n).
    rewrite copy_length in g0.
    trivial.
    set (w := nth_copy_in (A:=option SimpleType) (n:=n) None H); try_solve.
    lia.    
    autorewrite with datatypes.
    rewrite Min.min_r; trivial.
    lia.
    rewrite nth_app_left in Ex.
    rewrite <- (initialSeg_nth E x_k); trivial.
    autorewrite with datatypes.
    rewrite Min.min_r; lia.
  Qed.

  #[global] Hint Rewrite liftedEnv_var_lifted liftedEnv_var_notLifted
    var_liftedEnv_var_lifted var_liftedEnv_var_notLifted
    using solve [lia | auto] : terms.

  Definition lift_aux : forall (n: nat) (M: Term) (k: nat),
   {N: Term | env N = liftedEnv n (env M) k
              /\ term N = prelift_aux n (term M) k /\ type N = type M }.

  Proof.
    intros n M; gen n; clear n.
    destruct M as [E Pt T TypM].
    induction TypM; intros n k.
     (* variable *)
    simpl.
    case (le_gt_dec k x); intro xk.
    assert (TT: (liftedEnv n E k) |- %(x + n) := A).
    constructor.
    apply liftedEnv_var_lifted; trivial.
    exists (buildT TT); repeat split; auto.
    assert (TT: (liftedEnv n E k) |- %x := A).
    constructor.
    apply liftedEnv_var_notLifted; trivial.
    exists (buildT TT); repeat split; auto.
    simpl.
     (* function symbol *)
    assert (TT: (liftedEnv n E k) |- ^f := f_type f).
    constructor.
    exists (buildT TT); auto.
     (* abstraction *)
    destruct (IHTypM n (S k)) as [W [envW [termW typeW]]].
    destruct W as [EW PtW TW TypW].
    simpl in *.
    assert (TT: (liftedEnv n E k) |- \A => PtW := A --> B).
    constructor.
    rewrite <- liftedEnv_next.
    rewrite <- envW.
    rewrite <- typeW.
    trivial.
    exists (buildT TT); repeat split; auto.
    simpl; rewrite termW; auto.
     (* application *)
    destruct (IHTypM1 n k) as [L [envL [termL typeL]]].
    destruct (IHTypM2 n k) as [R [envR [termR typeR]]].
    destruct L as [EL PtL' TL TypL].
    destruct R as [ER PtR' TR TypR].
    simpl in * .  
    rewrite typeL in TypL.
    rewrite typeR in TypR.
    rewrite envL in TypL.
    rewrite envR in TypR.
    exists (buildT (TApp TypL TypR)); repeat split; auto.
    simpl; congruence.
  Defined.

  Definition lift (M: Term)(n: nat) : Term := 
    proj1_sig (lift_aux n M 0).

  Definition Subst := list (option Term).

  Definition lift_subst_comp P l :=
    match P with
    | None => None
    | Some P => Some (lift P l)
    end.

  Definition lift_subst (G: Subst)(l: nat) : Subst := map (fun T => lift_subst_comp T l) G.

  #[global] Hint Resolve prelift_aux : terms.
  #[global] Hint Unfold lift : terms.

  Lemma lift_env : forall M n, env (lift M n) = liftedEnv n (env M) 0.

  Proof.
    intros; unfold lift.
    destruct (lift_aux n M 0) as [M' [env_M' [term_M' type_M']]].
    trivial.
  Qed.

  Lemma lift_term : forall M n, term (lift M n) = prelift (term M) n.

  Proof.
    intros; unfold lift.
    destruct (lift_aux n M 0) as [M' [env_M' [term_M' type_M']]].
    trivial.
  Qed.

  Lemma lift_type : forall M n, type (lift M n) = type M.

  Proof.
    intros; unfold lift.
    destruct (lift_aux n M 0) as [M' [env_M' [term_M' type_M']]].
    trivial.
  Qed.

  #[global] Hint Rewrite lift_env lift_term lift_type : terms.

  Lemma in_lift_subst : forall Q G i, In (Some Q) (lift_subst G i) ->
    (exists2 W, In (Some W) G  &  Q = lift W i).

  Proof.
    induction G.
    simpl; tauto.
    intros i Q_G.
    unfold lift_subst_comp in Q_G; simpl in Q_G.
    destruct Q_G.
    destruct a; try discr.
    exists t.
    auto with datatypes.
    unfold lift_subst_comp in H; simpl in H.
    congruence.
    destruct (IHG i); trivial.
    exists x; auto with datatypes.
  Qed.

  Lemma lift_subst_distr : forall G H i,
    lift_subst (G ++ H) i = lift_subst G i ++ lift_subst H i.

  Proof.
    induction G; trivial.
    intros H i; simpl.
    rewrite (IHG H i); trivial.
  Qed.

  Lemma prelift_aux_0 : forall Pt i, prelift_aux 0 Pt i = Pt.

  Proof.
    induction Pt; intro i.
     (* variable *)
    unfold prelift_aux.
    case (le_gt_dec i x); auto.
     (* function symbol *)
    auto.
     (* abstraction *)
    simpl.
    rewrite (IHPt (S i)); trivial.
     (* application *)
    simpl.
    rewrite (IHPt1 i); rewrite (IHPt2 i); trivial.
  Qed.

  Lemma prelift_0 : forall Pt, prelift Pt 0 = Pt.

  Proof.
    unfold prelift; intros.
    apply prelift_aux_0.
  Qed.

  Lemma lift_0 : forall (M: Term), lift M 0 = M.

  Proof.
    intro M.
    unfold lift.
    destruct (lift_aux 0 M 0) as [W [envW [termW typeW]]].
    simpl.
    apply term_eq.
    rewrite envW.
    unfold liftedEnv.
    simpl.
    rewrite finalSeg_full; trivial.
    rewrite termW.
    rewrite (prelift_aux_0 (term M) 0); trivial.
  Qed.
 
  Lemma lift_subst_0 : forall (G: Subst), lift_subst G 0 = G.

  Proof.
    induction G; trivial.
    simpl; unfold lift_subst_comp.
    destruct a; try rewrite lift_0; rewrite IHG; trivial.
  Qed.

  #[global] Hint Rewrite prelift_aux_0 prelift_0 lift_0 lift_subst_0 : terms.

  Lemma prelift_aux_fold_aux : forall Pt m n i j, j >= i -> j <= n + i ->
    prelift_aux m (prelift_aux n Pt i) j = prelift_aux (m + n) Pt i.

  Proof.
    induction Pt; unfold prelift; intros m n i j j_ge j_le; simpl.
    destruct (le_gt_dec i x); simpl.
    destruct (le_gt_dec j (x + n)); simpl.
    assert (x + (m + n) = x + n + m).
    lia.
    try_solve.
    lia.
    destruct (le_gt_dec j x); simpl.
    lia.
    try_solve.
    trivial.
    rewrite <- (IHPt m n (S i) (S j)); trivial.
    lia.
    lia.
    rewrite IHPt1; try_solve.
    rewrite IHPt2; try_solve.
  Qed.

  Lemma prelift_aux_fold : forall Pt m n i,
    prelift_aux (m + n) Pt i = prelift_aux m (prelift_aux n Pt i) i.

  Proof.
    intros.
    rewrite prelift_aux_fold_aux; try_solve.
    lia.
  Qed.

  Lemma prelift_fold : forall Pt m n,
    prelift Pt (m + n) = prelift (prelift Pt n) m.

  Proof.
    intros Pt m n.
    unfold prelift.
    apply prelift_aux_fold.
  Qed.

  Lemma lift_fold : forall Pt m n, lift Pt (m + n) = lift (lift Pt m) n.

  Proof.
    intros Pt m n.
    unfold lift.
    destruct (lift_aux (m+n) Pt 0) as [L [envL [termL typeL]]].
    destruct (lift_aux m Pt 0) as [Rm [envRm [termRm typeRm]]].
    simpl.
    destruct (lift_aux n Rm 0) as [Rn [envRn [termRn typeRn]]].
    apply term_eq; simpl in * .

     (* equality of environments *)
    rewrite envL, envRn, envRm. unfold liftedEnv; simpl.    
    rewrite !finalSeg_full, plus_comm, copy_split, app_ass; trivial.

     (* equality of preterms *)
    rewrite termL, termRn, termRm, plus_comm. fold (prelift (term Pt) (n+m)).
    rewrite prelift_fold. trivial.
  Qed.

  Lemma lift_fold_1out : forall M n, lift (lift M n) 1 = lift M (S n).

  Proof.
    intros.
    replace (S n) with (n + 1).
    rewrite lift_fold; trivial.
    lia.
  Qed.

  Lemma lift_fold_1in : forall M n, lift (lift M 1) n = lift M (S n).

  Proof.
    intros.
    replace (S n) with (1 + n).
    rewrite lift_fold; trivial.
    lia.
  Qed.

  Lemma lift_subst_fold : forall G m n,
    lift_subst G (m+n) = lift_subst (lift_subst G m) n.

  Proof.
    induction G.
    trivial.
    intros m n; simpl.
    rewrite (IHG m n).
    destruct a; simpl.
    rewrite lift_fold; trivial.
    trivial.
  Qed.

  #[global] Hint Rewrite lift_fold lift_subst_fold : terms.

  Lemma lift_empty_subst : forall m i,
    lift_subst (copy m None) i = copy m None.

  Proof.
    induction m; intro i.
    trivial.
    simpl.
    rewrite (IHm i); trivial.
  Qed.

  Lemma length_lift_subst : forall G i, length (lift_subst G i) = length G.

  Proof.
    induction G.
    trivial.
    intro i; simpl.
    rewrite (IHG i); trivial.
  Qed.

  #[global] Hint Rewrite lift_empty_subst length_lift_subst : terms.

  Lemma nth_lift_subst_n : forall (G: Subst) i x, nth_error G x = None ->
    nth_error (lift_subst G i) x = None.

  Proof.
    unfold lift_subst; intros.
    rewrite nth_map_none; trivial.
  Qed.

  Lemma nth_lift_subst_n_rev : forall (G: Subst) i x,
    nth_error (lift_subst G i) x = None -> nth_error G x = None.

  Proof.
    unfold lift_subst; intros.
    rewrite (nth_map_none_rev G x (fun T => lift_subst_comp T i) H); trivial.
  Qed.

  Lemma nth_lift_subst_sn : forall G i x, nth_error G x = Some None ->
    nth_error (lift_subst G i) x = Some None.

  Proof.
    unfold lift_subst; intros.
    rewrite (nth_map_some G x (fun T => lift_subst_comp T i) H).
    simpl; trivial.
  Qed.

  Lemma nth_lift_subst_sn_rev : forall G i x,
    nth_error (lift_subst G i) x = Some None -> nth_error G x = Some None.

  Proof.
    unfold lift_subst; intros.
    destruct (nth_map_some_rev G x (fun T => lift_subst_comp T i) H)
      as [T [GT LT]].
    destruct T; trivial.
    try_solve.
  Qed.

  Lemma nth_lift_subst_s : forall G i x T, nth_error G x = Some (Some T) ->
    nth_error (lift_subst G i) x = Some (Some (lift T i)).

  Proof.
    unfold lift_subst; intros.
    rewrite (nth_map_some G x (fun T => lift_subst_comp T i) H).
    simpl; trivial.
  Qed.

  #[global] Hint Rewrite nth_lift_subst_n nth_lift_subst_n_rev nth_lift_subst_sn
    nth_lift_subst_sn_rev 
    using solve [auto with terms] : terms.

  Lemma nth_lift_subst_s_rev : forall G i x T,
    nth_error (lift_subst G i) x = Some (Some T) ->
    exists T', nth_error G x = Some (Some T') /\ T = lift T' i.

  Proof.
    unfold lift_subst; intros.
    destruct (nth_map_some_rev G x (fun T => lift_subst_comp T i) H)
      as [W [GW LW]].
    destruct W.
    exists t; split; try_solve.
    try_solve.
  Qed.

  Lemma nth_lift_normal : forall G i x T,
    nth_error (lift_subst G i) x = Some (Some T) ->
    exists2 Tg, T = lift Tg i & nth_error G x = Some (Some Tg).

  Proof.
    induction G; destruct x; try_solve.
    destruct a; try_solve.
    exists t; try_solve.
  Qed.

  Lemma app_lift_app_aux : forall M (Mapp: isApp M) n k,
    isApp (proj1_sig (lift_aux n M k)).

  Proof.
    intros.
    destruct M as [E Pt T M]; destruct M; try contr.
    destruct (lift_aux n (buildT (TApp M1 M2))) as [W [WE [WPt WT]]].
    apply app_isApp with (prelift_aux n PtL k) (prelift_aux n PtR k); trivial.
  Qed.

  Lemma app_lift_app : forall M (Mapp: isApp M) n, isApp (lift M n).

  Proof.
    intros; unfold lift.
    apply app_lift_app_aux; trivial.
  Qed.

  Lemma lift_absBody : forall E Pt A B (M: decl A E |- Pt := B) n k
    (MLabs: isAbs (proj1_sig (lift_aux n (buildT (TAbs M)) k))),
    absBody MLabs = proj1_sig (lift_aux n (buildT M) (S k)).

  Proof.
    intros.
    destruct (lift_aux n (buildT M) (S k)) as [P [Penv [Pterm Ptype]]].
    destruct (lift_aux n (buildT (TAbs M)) k) as [Q [Qenv [Qterm Qtype]]].
    apply term_eq.
     (* equal environment *)
    rewrite absBody_env.
    simpl; rewrite Penv; rewrite Qenv.
    unfold liftedEnv, decl; simpl.
    replace A with (absType MLabs).
    unfold finalSeg; trivial.
    apply abs_type with B; trivial.

     (* equal preterm *)
    apply absBody_term with A.
    simpl; rewrite Qterm; rewrite Pterm; trivial.
  Qed.

  Lemma lift_appBodyL : forall E PtL PtR A B n k (Ml: E |- PtL := A --> B)
    (Mr: E |- PtR := A)
    (MLapp: isApp (proj1_sig (lift_aux n (buildT (TApp Ml Mr)) k))),
    appBodyL MLapp = proj1_sig (lift_aux n (buildT Ml) k).

  Proof.
    intros.
    destruct (lift_aux n (buildT (TApp Ml Mr)) k) as [P [PE [PPt PA]]].
    destruct (lift_aux n (buildT Ml) k) as [Q [QE [QPt QA]]].
    apply term_eq.
     (* environment equal *)
    rewrite appBodyL_env.
    simpl; rewrite QE; rewrite PE; trivial.
     (* preterms equal *)
    simpl; rewrite QPt; simpl.
    apply appBodyL_term with (prelift_aux n PtR k).
    rewrite PPt; trivial.
  Qed.

  Lemma lift_appBodyR : forall E PtL PtR A B n k (Ml: E |- PtL := A --> B)
    (Mr: E |- PtR := A)
    (MLapp: isApp (proj1_sig (lift_aux n (buildT (TApp Ml Mr)) k))),
    appBodyR MLapp = proj1_sig (lift_aux n (buildT Mr) k).

  Proof.
    intros.
    destruct (lift_aux n (buildT (TApp Ml Mr)) k) as [P [PE [PPt PA]]].
    destruct (lift_aux n (buildT Mr) k) as [Q [QE [QPt QA]]].
    apply term_eq.
     (* environment equal *)
    rewrite appBodyR_env.
    simpl; rewrite QE; rewrite PE; trivial.
     (* preterms equal *)
    simpl; rewrite QPt; simpl.
    apply appBodyR_term with (prelift_aux n PtL k).
    rewrite PPt; trivial.
  Qed.

  Lemma term_prelift_eq : forall M N i j,
    prelift_aux i M j = prelift_aux i N j -> M = N .

  Proof.
    induction M; destruct N; intros; try_solve; try solve
      [destruct (le_gt_dec j x); try_solve].
    destruct (le_gt_dec j x); destruct (le_gt_dec j x0); try_solve.
    inversion H.
    cut (x = x0); [auto | lia].
    inversion H; lia.
    inversion H; lia.
    rewrite (IHM N i (S j)); inversion H; trivial.
    rewrite (IHM1 N1 i j).
    rewrite (IHM2 N2 i j).
    trivial.
    inversion H; trivial.
    inversion H; trivial.
  Qed.

  Lemma terms_lift_eq : forall M N, lift M 1 = lift N 1 -> M = N.

  Proof.
    intros.
    apply term_eq.
    cut (env (lift M 1) = env (lift N 1)).
    autorewrite with terms datatypes using unfold liftedEnv; try_solve.
    rewrite H; trivial.
    apply term_prelift_eq with 1 0.
    cut (term (lift M 1) = term (lift N 1)).
    autorewrite with terms using trivial.
    rewrite H; trivial.
  Qed.

  Fixpoint prelower_aux (P: Preterm) (k: nat) : Preterm :=
    match P with
    | Fun _ => P
    | Var i => 
        match (le_gt_dec k i) with
	| left _ =>  (* i >= k *) Var (pred i)
	| right _ => (* i < k *)  Var i
	end
    | App M N => App (prelower_aux M k) (prelower_aux N k)
    | Abs A M => Abs A (prelower_aux M (S k))
    end.
  Definition prelower P := prelower_aux P 0.

  Definition loweredEnv (E: Env) (k: nat) : Env :=
    initialSeg E k ++ finalSeg E (S k).

  Lemma loweredEnv_var_lowered : forall E x A k,
    E |= k :! -> E |= x := A -> k <= x -> loweredEnv E k |= pred x := A.

  Proof.
    intros E x A k Ek0 Ex k_x.
    assert (x_E: x < length E).
    rewrite_lr (nth_in E x); unfold VarD in Ex; try_solve.
    destruct (le_lt_or_eq k_x) as [k_lt_x | k_eq_x].
    destruct x.
    lia.
    unfold VarD, loweredEnv.
    rewrite nth_app_right.
    unfold finalSeg; simpl.
    destruct E; try_solve.
    assert (k_E: Min.min k (S (length E)) = k).
    rewrite Min.min_l; lia.
    rewrite seg_nth.
    rewrite initialSeg_length; simpl.
    rewrite k_E.
    replace (k + (x - k)) with x; solve [trivial | lia].
    rewrite initialSeg_length; simpl.
    rewrite k_E; lia.
    rewrite initialSeg_length.
    rewrite Min.min_l; lia.
    rewrite k_eq_x in Ek0.
    unfold VarD in Ex; destruct Ek0; try_solve.
  Qed.

  Lemma loweredEnv_var_notLowered : forall E x A k,
    E |= k :! -> E |= x := A -> k > x -> loweredEnv E k |= x := A.

  Proof.
    intros E x A k Ek0 Ex kx.
    unfold VarD, loweredEnv.
    rewrite nth_app_left.
    rewrite initialSeg_nth; trivial.
    rewrite initialSeg_length; trivial.
    apply Min.min_case2; trivial.
    rewrite_lr (nth_in E x); unfold VarD in Ex; try_solve.
  Qed.

  Lemma var_loweredEnv_var_lowered : forall E x A k,
    E |= k :! -> loweredEnv E k |= x := A -> k <= x -> E |= S x := A.

  Proof.
    unfold VarD, loweredEnv.
    intros E x A k Ek0 Ex kx.
    rewrite nth_app_right in Ex.
    rewrite initialSeg_length in Ex.
    destruct (le_gt_dec (length E) k).
    rewrite finalSeg_empty in Ex.
    destruct (x - Min.min k (length E)); try_solve.
    lia.
    rewrite Min.min_l in Ex.
    destruct (le_gt_dec (length E) (S x)).
    rewrite nth_beyond in Ex; try_solve.
    rewrite finalSeg_length.
    lia.
    rewrite (@finalSeg_nth_nth (option SimpleType) E (S k) (S x)).
    replace (S x - S k) with (x - k); trivial.
    lia.
    lia.
    rewrite initialSeg_length.
    set (w := Min.le_min_l k (length E)).
    lia.
  Qed.

  Lemma var_loweredEnv_var_notLowered : forall E x A k,
    E |= k :! -> loweredEnv E k |= x := A -> k > x -> E |= x := A.

  Proof.
    unfold VarD, loweredEnv.
    intros E x A k Ek0 Ex kx.
    destruct (le_gt_dec (length E) x).
    destruct (le_gt_dec k (length E)).
    rewrite nth_app_left in Ex; trivial.
    rewrite <- (initialSeg_nth E kx); trivial.
    autorewrite with datatypes.
    apply Min.min_case2; lia.
    rewrite nth_app_right in Ex.
    rewrite finalSeg_empty in Ex.
    destruct (x - length (initialSeg E k)); try_solve.
    lia.
    autorewrite with datatypes.
    rewrite Min.min_r; trivial.
    lia.
    rewrite nth_app_left in Ex.
    rewrite initialSeg_nth in Ex; trivial.
    autorewrite with datatypes.
    apply Min.min_case2; lia.
  Qed.

  Lemma prelower_prelift_aux : forall Pt i j k, k >= j -> k <= i + j + 1 ->
    prelift_aux i Pt j = prelower_aux (prelift_aux (i + 1) Pt j) k.

  Proof.
    induction Pt; intros; simpl.
    destruct (le_gt_dec j x); simpl.
    destruct (le_gt_dec k (x + (i + 1))); simpl.
    assert (x + i = pred (x + (i + 1))).
    lia.
    try_solve.
    lia.
    destruct (le_gt_dec k x); trivial.
    lia.
    trivial.
    rewrite (IHPt i (S j) (S k)); solve [trivial | lia].
    rewrite (IHPt1 i j k); try lia.
    rewrite (IHPt2 i j k); try lia.
    trivial.
  Qed.

  Lemma prelower_prelift : forall Pt i,
    prelift Pt i = prelower_aux (prelift Pt (i + 1)) i.

  Proof.
    intros; unfold prelift.
    apply prelower_prelift_aux.
    lia.
    lia.
  Qed.

  Definition lower_aux : forall (M: Term) (k: nat), env M |= k :! ->
    {N: Term | env N = loweredEnv (env M) k
               /\ term N = prelower_aux (term M) k /\ type N = type M }.

  Proof.
    destruct M as [E Pt T TypM].
    induction TypM; intros k env0.

     (* variable *)
    simpl.
    case (le_gt_dec k x); intro k_x.
     (*   - variable lowered *)
    set (res := loweredEnv_var_lowered env0 v k_x).
    exists (buildT (TVar res)); repeat split; try_solve.
     (*  - variable untouched *)
    set (res := loweredEnv_var_notLowered env0 v k_x).
    exists (buildT (TVar res)); repeat split; try_solve.

     (* function symbols *)
    exists (buildT (TFun (loweredEnv E k) f)); split; try_solve.

     (* abstraction *)
    simpl in * .
    assert (res: loweredEnv E k |- \A => prelower_aux Pt (S k) := A --> B).
    constructor.
    destruct (IHTypM (S k)) as [W [WE [WPt WB]]]; try_solve.
    rewrite <- WPt.
    rewrite <- WB.
    replace (decl A (loweredEnv E k)) with (loweredEnv (decl A E) (S k)).
    rewrite <- WE.
    exact (typing W).
    unfold loweredEnv, finalSeg; try_solve.
    exists (buildT res); repeat split; try_solve.

     (* application *)
    simpl in * .
    destruct (IHTypM1 k) as [L [LE [LPt LT]]]; trivial.
    destruct (IHTypM2 k) as [R [RE [RPt RT]]]; trivial.
    assert
      (res: loweredEnv E k |- prelower_aux PtL k [prelower_aux PtR k] := B).
    constructor 4 with A.
    rewrite <- LE.
    rewrite <- LPt.
    rewrite <- LT.
    exact (typing L).
    rewrite <- RE.
    rewrite <- RPt.
    rewrite <- RT.
    exact (typing R).
    exists (buildT res); repeat split; try_solve.
  Defined.

  Definition lower (M: Term) (ME: env M |= 0 :!) : Term :=
    proj1_sig (lower_aux M ME).

  Lemma lower_env : forall M ME, env (lower M ME) = loweredEnv (env M) 0.

  Proof.
    intros; unfold lower.
    destruct (lower_aux M ME); try_solve.
  Qed.

  Lemma lower_term : forall M ME, term (lower M ME) = prelower (term M).

  Proof.
    intros; unfold lower.
    destruct (lower_aux M ME); try_solve.
  Qed.

  Lemma lower_type : forall M ME, type (lower M ME) = type M.

  Proof.
    intros; unfold lower.
    destruct (lower_aux M ME); try_solve.
  Qed.

  #[global] Hint Rewrite lower_env lower_term lower_type : terms.

  Lemma prelift_prelower_aux : forall M i, env M |= i :! ->
    prelift_aux 1 (prelower_aux (term M) i) i = (term M).

  Proof.
    destruct M as [E Pt T M].
    induction M; simpl; intros.
    destruct (le_gt_dec i x); simpl.
    destruct (le_gt_dec i (pred x)); simpl.
    destruct x.
    assert (i = 0).
    lia.
    rewrite H0 in H.
    inversion v; destruct E; inversion H; try_solve.
    assert (pred (S x) + 1 = S x); [lia | auto].
    assert (i = x).
    lia.
    inversion v; destruct E; inversion H; try_solve.
    destruct (le_gt_dec i x); simpl; trivial.
    assert (i = x).
    lia.
    inversion v; destruct E; inversion H; try_solve.
    trivial.
    set (w := IHM (S i)); simpl in w.
    rewrite w; trivial.
    set (w := IHM1 i); simpl in w; rewrite w; trivial.
    set (t := IHM2 i); simpl in t; rewrite t; trivial.
  Qed.

  Lemma prelift_prelower : forall M M0, term (lift (lower M M0) 1) = term M.

  Proof.
    intros.
    autorewrite with terms; unfold prelift, prelower.
    rewrite (prelift_prelower_aux M M0); trivial.
  Qed.

  Lemma lower_absBody : forall E Pt A B (M: decl A E |- Pt := B) n
    (Menv: E |= n :!) (M'env: decl A E |= S n :!)
    (MLabs: isAbs (proj1_sig (lower_aux (buildT (TAbs M)) Menv))),
    absBody MLabs = proj1_sig (lower_aux (buildT M) M'env).

  Proof.
    intros.
    destruct (lower_aux (buildT M) M'env) as [P [Penv [Pterm Ptype]]].
    destruct (lower_aux (buildT (TAbs M)) Menv) as [Q [Qenv [Qterm Qtype]]].
    apply term_eq.
     (* equal environment *)
    rewrite absBody_env.
    simpl; rewrite Penv; rewrite Qenv.
    unfold loweredEnv, decl; simpl.
    replace A with (absType MLabs); simpl; trivial.
    rewrite (@abs_type Q MLabs A B); trivial.

     (* equal preterm *)
    apply absBody_term with A.
    simpl; rewrite Qterm; rewrite Pterm; trivial.
  Qed.

  Lemma lower_appBodyL : forall E PtL PtR A B n (Menv: E |= n :!)
    (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
    (MLapp: isApp (proj1_sig (lower_aux (buildT (TApp Ml Mr)) Menv))),
    appBodyL MLapp = proj1_sig (lower_aux (buildT Ml) Menv).

  Proof.
    intros.
    destruct (lower_aux (buildT (TApp Ml Mr)) Menv) as [P [PE [PPt PA]]].
    destruct (lower_aux (buildT Ml) Menv) as [Q [QE [QPt QA]]].
    apply term_eq.
     (* environment equal *)
    rewrite appBodyL_env.
    simpl; rewrite QE; rewrite PE; trivial.
     (* preterms equal *)
    simpl; rewrite QPt; simpl.
    apply appBodyL_term with (prelower_aux PtR n).
    rewrite PPt; trivial.
  Qed.

  Lemma lower_appBodyR : forall E PtL PtR A B n (Menv: E |= n :!)
    (Ml: E |- PtL := A --> B) (Mr: E |- PtR := A)
    (MLapp: isApp (proj1_sig (lower_aux (buildT (TApp Ml Mr)) Menv))),
    appBodyR MLapp = proj1_sig (lower_aux (buildT Mr) Menv).
  Proof.
    intros.
    destruct (lower_aux (buildT (TApp Ml Mr)) Menv) as [P [PE [PPt PA]]].
    destruct (lower_aux (buildT Mr) Menv) as [Q [QE [QPt QA]]].
    apply term_eq.
     (* environment equal *)
    rewrite appBodyR_env.
    simpl; rewrite QE; rewrite PE; trivial.
     (* preterms equal *)
    simpl; rewrite QPt; simpl.
    apply appBodyR_term with (prelower_aux PtL n).
    rewrite PPt; trivial.
  Qed.

End TermsLifting.
