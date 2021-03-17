(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Operation of substitution for simple typed
lambda-calculus is defined in this file.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListPermutation TermsConv ListUtil
     ListExtras LogicUtil.
From Coq Require Import Arith Lia.

Module TermsSubst (Sig : TermsSig.Signature).

  Module Export TC := TermsConv.TermsConv Sig.

  Notation "{x/ N }" := (Some N::nil).
  Notation "{x/ N ,y/ M }" := (Some N::Some M::nil).

  Definition varSubstTo (G: Subst) x T : Prop := nth_error G x = Some (Some T).
  Notation "G |-> x / T" := (varSubstTo G x T) (at level 50, x at level 0).

  Definition varIsSubst (G: Subst) x : Type := {T: Term | G |-> x/T}.
  Notation "G |-> x /*" := (varIsSubst G x) (at level 50, x at level 0).

  Definition varIsNotSubst (G: Subst) x : Prop :=
    nth_error G x = None \/ nth_error G x = Some None.
  Notation "G |-> x /-" := (varIsNotSubst G x) (at level 50, x at level 0).
 
  Definition isEmptySubst G : Prop := forall x, G |-> x/- .

  Definition isSingletonSubst M G : Prop :=
    G |-> 0 / M /\ forall i, G |-> (S i)/- .

  Lemma singletonSubst_cond M : isSingletonSubst M {x/M}.

  Proof. constructor; constructor. destruct i; trivial. Qed.

  #[global] Hint Unfold varSubstTo varIsSubst varIsNotSubst : terms.

  Lemma varSubst_dec G x : {T: Term | G |-> x/T} + { G |-> x/- }.

  Proof.
    destruct (nth_error_In G x) as [[T Gx] | Gnx].
    destruct T as [T |].
    left; exists T; auto.
    right; auto with terms.
    right; auto with terms.
  Qed.

  Lemma var_notSubst_lift G x i : G |-> x/- -> (lift_subst G i) |-> x/-.

  Proof.
    destruct 1.
    left; apply (nth_lift_subst_n G i x H).
    right; apply (nth_lift_subst_sn G i x H).
  Qed.

  Lemma var_notSubst_lift_rev G x i : (lift_subst G i) |-> x/- -> G |-> x/- .

  Proof.
    intros Gxn. destruct Gxn.
    left; apply nth_lift_subst_n_rev with i; trivial.
    right; apply nth_lift_subst_sn_rev with i; trivial.
  Qed.

  Lemma var_subst_lift G x i T :
    G |-> x/T  -> (lift_subst G i) |-> x/(lift T i).

  Proof. intros Gx_T. unfold varSubstTo; apply nth_lift_subst_s; trivial. Qed.

  Lemma var_subst_lift_rev G x i T :
    (lift_subst G i) |-> x/T -> exists T', G |-> x/T' /\ T = lift T' i.

  Proof.
    intros Gx_T. unfold varSubstTo.
    destruct (nth_lift_subst_s_rev G i x Gx_T) as [W [GW LW]].
    exists W; split; try_solve.
  Qed.

  Lemma var_notSubst_cons G x : G |-> x/- -> (None::G) |-> (S x)/- .

  Proof. destruct 1. constructor; trivial. constructor 2; trivial. Qed.

  Lemma var_cons_notSubst G x : (None::G) |-> (S x)/- -> G |-> x/- .

  Proof. destruct 1. constructor; trivial. constructor 2; trivial. Qed.

  Lemma var_subst_cons G x T : G |-> x / T -> (None :: G) |-> (S x) / T.

  Proof. intro GxT. unfold varSubstTo in *; trivial. Qed.

  Lemma lift_subst_app : forall G1 G2 i,
      lift_subst (G1 ++ G2) i = lift_subst G1 i ++ lift_subst G2 i.

  Proof. induction G1; trivial. intros; simpl. rewrite IHG1; trivial. Qed.

  Definition subst_dom (G: Subst) : Env :=
    map (fun T => 
      match T with
      | None => None
      | Some T => Some (type T)
      end) G.

  Definition subst_ran (G: Subst) : Env :=
    fold_left (fun E S => 
      match S with
      | None => E
      | Some T => E [+] env T
      end
    ) G EmptyEnv. 

  Definition subst_envs_comp (G: Subst) : Prop :=
    forall i j Ti Tj,
      G |-> i/Ti ->
      G |-> j/Tj ->
      env Ti [<->] env Tj.

  Lemma subst_ran_single T : subst_ran {x/T} = env T.

  Proof. unfold subst_ran; simpl. destruct (env T); trivial. Qed.

  Lemma subst_ran_single_after_empty T :
    forall i, subst_ran (copy i None ++ {x/T}) = env T.

  Proof.
    induction i. simpl; apply subst_ran_single. unfold subst_ran; trivial.
  Qed.

  Lemma subst_envs_comp_single : forall T, subst_envs_comp {x/T}.

  Proof.
    unfold subst_envs_comp; intros.
    destruct i; destruct j; try solve [
      inversion H; destruct i; simpl in *; discr |
      inversion H0; destruct j; simpl in *; discr
    ].
    inversion H; inversion H0; rewrite <- H2; rewrite <- H3;
      apply env_comp_refl.
  Qed.

  Lemma subst_envs_comp_singleton :
    forall G T, isSingletonSubst T G -> subst_envs_comp G.

  Proof.
    intros; intros i j Ti Tj Gi Gj.
    inversion H.
    destruct i; destruct j; try solve
    [ inversion Gj; destruct (H1 j); destruct G; try_solve
    | inversion Gi; destruct (H1 i); destruct G; try_solve
    ].
    assert (Ti = Tj).
    inversion Gi; inversion Gj; destruct G; try_solve.
    rewrite H2; apply env_comp_refl. 
  Qed.

  Record correct_subst (M: Term) (G: Subst) : Prop := {
    envs_c: subst_envs_comp G;
    dom_c: subst_dom G [<->] env M;
    ran_c: subst_ran G [-] subst_dom G [<->] env M
  }.

  Lemma one_var_subst_correct M N :
    (forall A, env M |= 0 := A -> A = type N) ->
    env M [<->] env N -> correct_subst M {x/N}.

  Proof.
    intros M_x MN_comp; split.
    apply subst_envs_comp_single.
    simpl; intro p; destruct p; intros A B.
    intros Nx Mx.
    unfold VarD in Nx.
    inversion Nx.
    sym; apply M_x; trivial.
    unfold VarD; destruct p; simpl; intros; discr.
    rewrite subst_ran_single.
    apply env_comp_sub.
    apply env_comp_sym; trivial.
  Qed.

  Lemma subst_dom_varNotSubst : forall G x, G |-> x/- -> subst_dom G |= x :!.

  Proof.
    induction G.
    destruct x; unfold VarUD; auto with datatypes.
    intros x xUD.
    destruct x.
    unfold varIsNotSubst in xUD; simpl in *.
    destruct a.
    destruct xUD; discr.
    unfold VarUD; auto.
    unfold VarUD; simpl.
    apply IHG; trivial.
  Qed.

  Lemma subst_dom_varNotSubst_rev :
    forall G x, subst_dom G |= x :! -> G |-> x/- .

  Proof.
    induction G.
    destruct x; try_solve.
    intros x xUD.
    destruct x.
    unfold varIsNotSubst in xUD; simpl in * .
    destruct a.
    destruct xUD; discr.
    compute; auto.
    unfold VarUD in xUD; simpl in xUD.
    unfold varIsNotSubst; simpl.
    apply IHG; trivial.
  Qed.

  Lemma subst_dom_varSubst :
    forall G x T, G |-> x/T -> subst_dom G |= x := type T.

  Proof.
    induction G.
    destruct x; try_solve.
    intros x T Gx.
    destruct x.
    destruct a.
    inversion Gx; try_solve.
    try_solve.
    unfold VarD; simpl.
    apply IHG; trivial.
  Qed.

  Lemma subst_dom_varSubst_rev : forall G x A,
      subst_dom G |= x := A -> exists T, G |-> x/T /\ type T = A.

  Proof.
    induction G.
    destruct x; try_solve.
    intros x A Gx.
    destruct x.
    destruct a.
    inversion Gx.
    exists t; fo.
    try_solve.
    inversion Gx.
    destruct (IHG x A H0).
    exists x0; fo.
  Qed.

  Lemma subst_dom_lifted :
    forall G n, subst_dom (lift_subst G n) = subst_dom G.

  Proof.
    induction G.
    auto.
    intros n; simpl; unfold lift_subst_comp.
    rewrite IHG.
    destruct a; trivial.
    rewrite lift_type; trivial.
  Qed.

  Lemma lifted_subst_envs_comp G n :
    subst_envs_comp G -> subst_envs_comp (lift_subst G n).

  Proof.
    unfold subst_envs_comp.
    intros G_comp i j Ti Tj Gi Gj p.
    destruct (nth_lift_normal G n i Gi) as [T_i TiL TiG].
    destruct (nth_lift_normal G n j Gj) as [T_j TjL TjG].
    rewrite TiL.
    rewrite TjL.
    do 2 rewrite lift_env.
    unfold liftedEnv, env_comp_on, VarD; simpl.
    case (le_lt_dec n p).
    intro n_le_p.
    rewrite !nth_app_right; autorewrite with datatypes using trivial.
    unfold finalSeg; simpl.
    repeat rewrite initialSeg_full; try solve [auto with datatypes | lia].
    exact (G_comp i j T_i T_j TiG TjG (p-n)).
    intro p_lt_n.
    rewrite !nth_app_left; autorewrite with datatypes using try_solve.
  Qed.

  Lemma subst_ran_cons_none G : subst_ran (None::G) = subst_ran G.

  Proof. unfold subst_ran; trivial. Qed.

  Lemma fold_subst_ran : forall G l 
    (f :=  fun E S => match S with Some T => E[+]env T | None => E end),
    fold_left f G l = l [+] fold_left f G nil.

  Proof.
    induction G.
    intros; simpl.
    rewrite env_sum_empty_r; trivial.
    intros l f.
    destruct a.
    simpl; destruct (env t).
    rewrite env_sum_empty_r.
    apply IHG.
    rewrite IHG; fold f.
    unfold f; rewrite (IHG (o::e)); fold f.
    rewrite env_sum_assoc; trivial.
    simpl; apply IHG.
  Qed.

  Lemma subst_ran_cons_some t G :
    subst_ran (Some t::G) = env t [+] subst_ran G.

  Proof.
    unfold subst_ran.
    simpl.
    destruct (env t).
    rewrite env_sum_empty_l; trivial.
    simpl.
    rewrite fold_subst_ran.
    set (f := fun E S => match S with Some T => E[+]env T 
                                    | None => E end).
    fold EmptyEnv.
    destruct (fold_left f G EmptyEnv).
    rewrite env_sum_empty_r; trivial.
    destruct o0; trivial.
  Qed.

  Lemma subst_ran_decl : forall G x A,
      subst_ran G |= x := A -> exists T p, G |-> p/T /\ env T |= x := A.

  Proof.
    induction G.
    destruct x; try_solve.
    intros.
    destruct a.
    rewrite subst_ran_cons_some in H.
    destruct (env_sum_varDecl (env t) (subst_ran G) H) as [[Tx Gx] | Gx].
    exists t; exists 0; split; compute; trivial.
    destruct (IHG x A Gx) as [T [p [Gp Tx]]].
    exists T; exists (S p); split; trivial.
    rewrite subst_ran_cons_none in H.
    destruct (IHG x A H) as [T [p [Gp Tx]]].
    exists T; exists (S p); split; trivial.
  Qed.

  Hint Rewrite subst_ran_single subst_ran_cons_none subst_ran_cons_some : terms.

  Lemma subst_cons_empty G : isEmptySubst G -> isEmptySubst (None::G).

  Proof.
    intros Ge x; destruct x; unfold varIsNotSubst. auto. apply (Ge x).
  Qed.

  Lemma subst_tail_empty G : isEmptySubst (None::G) -> isEmptySubst G.

  Proof. intros NGe x. apply (NGe (S x)). Qed.

  #[global] Hint Resolve subst_cons_empty subst_tail_empty : terms.

  Lemma subst_nil_empty : isEmptySubst nil.

  Proof. unfold isEmptySubst, varIsNotSubst. destruct x; auto. Qed.

  Lemma subst_lift_empty G i : isEmptySubst G -> isEmptySubst (lift_subst G i).

  Proof.
    intros Ge x. destruct (Ge x); unfold varIsNotSubst.
    left; apply nth_lift_subst_n; trivial.
    right; apply nth_lift_subst_sn; trivial.
  Qed.

  Lemma subst_lift_empty_rev G i :
    isEmptySubst (lift_subst G i) -> isEmptySubst G.

  Proof.
    intros Ge x. destruct (Ge x); unfold varIsNotSubst.
    left; apply nth_lift_subst_n_rev with i; trivial.
    right; apply nth_lift_subst_sn_rev with i; trivial.
  Qed.

  #[global] Hint Resolve subst_lift_empty subst_lift_empty_rev : terms.

  Lemma subst_empty_dec : forall G, {isEmptySubst G} + {~isEmptySubst G}.

  Proof.
    induction G.
    left; apply subst_nil_empty.
    destruct a.
    right; unfold isEmptySubst; intro f.
    absurd ((Some t::G) |-> 0/-); auto.
    compute; intro f'; destruct f'; discr.
    destruct IHG.
    left; apply subst_cons_empty; trivial.
    right.
    intro f.
    absurd (isEmptySubst G); trivial.
    unfold isEmptySubst; intro x; apply (f (S x)).
  Qed.

  Ltac prove_correct_subst :=
    match goal with 
    | |- correct_subst ?M ?G =>
      (
        constructor; [
	  auto with terms |
	  autorewrite with terms datatypes using unfold decl, liftedEnv; try_solve |
	  destruct (subst_empty_dec G); 
	    autorewrite with terms datatypes using unfold decl, liftedEnv; try_solve
	]
      )
    | _ => fail "Goal is not of required shape"
    end.

  Lemma subst_ran_empty : forall G, isEmptySubst G -> subst_ran G = EmptyEnv.

  Proof.
    induction G; auto.
    destruct a.
    intro f; destruct (f 0); discr.
    intro Ge.
    rewrite subst_ran_cons_none.
    apply IHG.
    apply subst_tail_empty; trivial.
  Qed.

  Lemma subst_dom_Empty : forall G, isEmptySubst G -> emptyEnv (subst_dom G).

  Proof.
    induction G.
    simpl; intro; apply emptyEnv_empty.
    intro aG_empty.
    destruct a.
    absurd ((Some t :: G) |-> 0 /- ); trivial.
    intro w; destruct w; try_solve.
    intro p; destruct p.
    right; try_solve.
    unfold VarUD; simpl.
    apply IHG.
    apply subst_tail_empty; trivial.
  Qed.

  Lemma subst_ran_singleton G T : isSingletonSubst T G -> subst_ran G = env T.

  Proof.
    intro.
    inversion H.
    destruct G; try_solve.
    destruct o; try_solve.
    rewrite subst_ran_cons_some.
    rewrite subst_ran_empty.
    autorewrite with terms.
    inversion H0; try_solve.    
    intro p; apply (H1 p).
  Qed.

  Lemma subst_dom_singleton G T : isSingletonSubst T G ->
    exists E, subst_dom G = Some (type T) :: E /\ emptyEnv E.

  Proof.
    intro.
    inversion H.
    destruct G; try_solve.
    destruct o; try_solve.
    exists (subst_dom G); split.
    inversion H0; trivial.
    apply subst_dom_Empty.
    intro p; apply (H1 p).
  Qed.

  Lemma subst_dom_singleton_after_none_decl : forall i T,
    subst_dom (copy i None ++ {x/T}) |= i := type T.

  Proof. induction i. simpl; constructor. trivial. Qed.

  Lemma subst_dom_singleton_after_none_nodecl : forall i j T, i <> j ->
    subst_dom (copy i None ++ {x/T}) |= j :! .

  Proof.
    induction i; intros.
    destruct j; simpl.
    lia.
    constructor; destruct j; trivial.
    destruct j.
    constructor 2; trivial.
    simpl; trivial.
    destruct (IHi j T); try_solve.
  Qed.

  Lemma subst_ran_lifted_empty : forall G,
      isEmptySubst G -> subst_ran (lift_subst G 1) = EmptyEnv.

  Proof.
    induction G; auto.
    intro aG_empty.
    destruct a.
    absurd ((Some t::G) |-> 0/-); auto.
    compute; intro f; destruct f; discr.
    unfold subst_ran; simpl.
    apply IHG.
    apply subst_tail_empty; trivial.
  Qed.

  Lemma subst_dom_lifted_Empty G :
    isEmptySubst G -> emptyEnv (subst_dom (lift_subst G 1)).

  Proof. intro. apply subst_dom_Empty. apply subst_lift_empty; trivial. Qed.

  Lemma subst_ran_lifted_ne : forall G, ~isEmptySubst G ->
    subst_ran (lift_subst G 1) = None :: subst_ran G.

  Proof.
    induction G; intro GR_nn.
    absurd (isEmptySubst nil); trivial.
    apply subst_nil_empty.
    simpl; unfold lift_subst_comp.
    destruct a.
     (* -) hd G = Some t *)
    rewrite !subst_ran_cons_some, lift_env.
    destruct (subst_empty_dec G) as [Ge | G_ne].
    rewrite subst_ran_lifted_empty; trivial.
    rewrite subst_ran_empty; trivial.
    rewrite !env_sum_empty_r.
    unfold liftedEnv; simpl.
    unfold finalSeg; simpl.
    rewrite initialSeg_full; solve [auto with datatypes | lia].
    rewrite IHG; trivial.
    simpl.
    unfold finalSeg; simpl.
    rewrite initialSeg_full; solve [auto with datatypes | lia].
     (* -) hd G = None *)
    rewrite !subst_ran_cons_none.
    apply IHG.
    intro Ge.
    absurd (isEmptySubst (None::G)); trivial.
    apply subst_cons_empty; trivial.
  Qed.

  Hint Rewrite subst_ran_empty subst_ran_lifted_empty subst_ran_lifted_ne 
    using solve [auto with terms] : terms.

  Lemma subst_ran_lifted_noDecl G : subst_ran (lift_subst G 1) |= 0 :! .

  Proof.
    destruct (subst_empty_dec G).
    rewrite subst_ran_lifted_empty; auto with terms.
    rewrite subst_ran_lifted_ne; auto with terms.
  Qed.

  Hint Rewrite subst_ran_single subst_dom_lifted subst_ran_cons_none
       subst_ran_cons_some : terms.

  Fixpoint presubst_aux (P: Preterm) (l: nat) (G: Subst) : Preterm :=
    match P with
    | Fun _ => P
    | Var i =>
        match (nth_error G i) with
        | Some (Some Q) => term (lift Q l)
        | _ => Var i
        end
    | App M N => App (presubst_aux M l G) (presubst_aux N l G)
    | Abs A M => Abs A (presubst_aux M (S l) (None::G) )
    end.

  Definition presubst P G := presubst_aux P 0 G.

  Lemma subst_lift_subst_aux: forall Pt G m n,
    presubst_aux Pt (m + n) G = presubst_aux Pt m (lift_subst G n).

  Proof.
    induction Pt.
     (* variable *)
    intros G m n.
    unfold presubst_aux.
    destruct (varSubst_dec G x) as [[T GxT] | Gxn].
    rewrite GxT.
    rewrite (nth_lift_subst_s G n x GxT).
    rewrite plus_comm.
    rewrite lift_fold; trivial.
    destruct (var_notSubst_lift n Gxn) as [Nglx | Nglx];
      destruct Gxn as [Ngx | Ngx];
      rewrite Ngx; rewrite Nglx; trivial.
     (* function symbol *)
    simpl; trivial.
     (* abstraction *)
    intros G m n; simpl.
    assert (Splus: forall m n, S (m + n) = S m + n).
    intros; auto with arith.
    rewrite Splus.
    rewrite (IHPt (None::G) (S m) n).
    simpl; trivial.
     (* application *)
    intros G m n; simpl.
    rewrite (IHPt1 G m n).
    rewrite (IHPt2 G m n).
    trivial.
  Qed.

  Lemma subst_lift_subst Pt G i :
    presubst_aux Pt i G = presubst Pt (lift_subst G i).

  Proof.
    replace i with (0 + i). rewrite (subst_lift_subst_aux Pt G 0 i).
    unfold presubst; trivial. auto.
  Qed.

  Lemma subst_type_comp M G x T :
    correct_subst M G -> G |-> x/T -> env M |= x := type T \/ env M |= x :!.

  Proof.
    intros MG Gx.
    destruct MG.
    inversion Gx.
    destruct (isVarDecl_dec (env M) x) as [[A MxA] | MxN].
    left.
    rewrite (dom_c0 x (type T) A); trivial.
    apply subst_dom_varSubst; trivial.
    auto.
  Qed.

  Lemma subst_envs_comp_tail a G : subst_envs_comp (a::G) -> subst_envs_comp G.

  Proof.
    intros envc_aG p q Ti Tj p_neq_q Gp Gq.
    apply (envc_aG (S p) (S q)); trivial.
  Qed.

  Lemma subst_envs_comp_head a :
    forall G, subst_envs_comp (Some a::G) -> env a [<->] subst_ran G.

  Proof.
    induction G.
    intros; apply env_comp_empty.
    intros envsc.
    assert (se: subst_envs_comp (Some a :: G)).
    intros p q Ti Tj A B.
    destruct p.
    destruct q; try tauto.
    inversion A; inversion B; rewrite <- H0; rewrite <- H1; apply env_comp_refl.
    apply (envsc 0 (S (S q))); try_solve.
    destruct q.
    apply (envsc (S (S p)) 0); try_solve.
    apply (envsc (S (S p)) (S (S q))); try_solve.
    destruct a0.
    rewrite subst_ran_cons_some.
    apply env_comp_sum.
    apply (envsc 0 1); try_solve.
    apply IHG; trivial.
    rewrite subst_ran_cons_none.
    apply IHG; trivial.
  Qed.

  Lemma subst_ran_component_comp : forall G x T,
      G |-> x/T -> subst_envs_comp G ->
      forall p A, env T |= p := A -> subst_ran G |= p := A.

  Proof.
    induction G.
    destruct x; try_solve.
    destruct a.
     (* head G = Some t *)
    rewrite subst_ran_cons_some.
    destruct x; intros T Gx envsc p A Tp.
     (*   - x = 0 *)
    inversion Gx.
    destruct (isVarDecl_dec (subst_ran G) p) as [[B Gp] | Gpn].
    apply env_sum_ry.
    rewrite <- H0 in Tp.
    rewrite (subst_envs_comp_head envsc Tp Gp); trivial.
    apply env_sum_ly_rn; trivial.
     (*   - x > 0 *)
    apply env_sum_ry.
    apply IHG with x T; try_solve.
    apply subst_envs_comp_tail with (Some t); trivial.
     (* head G = None *)
    rewrite subst_ran_cons_none.
    destruct x; try_solve.
    intros T Gx envc_G.
    apply (IHG x T); trivial.
    eapply subst_envs_comp_tail; eauto.
  Qed.

  Lemma subst_comp_comp_ran G x T :
    G |-> x/T -> subst_envs_comp G -> env T [<->] subst_ran G.

  Proof.
    intros GxT Gc p A B Tp Gp. set (w := subst_ran_component_comp GxT Gc Tp).
    unfold VarD in *; congruence.
  Qed.

  Lemma subst_comp_env : forall G x T,
      G |-> x/T -> subst_envs_comp G -> subst_ran G = subst_ran G [+] env T.

  Proof.
    induction G.
    destruct x; try_solve.
    intros x T aG_xT envsc_aG.
    destruct a.
     (* a = Some t *)
    rewrite subst_ran_cons_some.
    destruct x.
    assert (Tt: t = T).
    unfold varSubstTo in *; simpl in *.
    inversion aG_xT; trivial.
    rewrite Tt.
    rewrite env_comp_sum_comm.
    rewrite env_sum_assoc.
    rewrite env_sum_double; trivial.
    apply env_comp_sum_comp_right with (env t).
    rewrite <- subst_ran_cons_some.
    apply subst_comp_comp_ran with 0; trivial.
    rewrite env_sum_assoc.
    assert (G_GT: subst_ran G = subst_ran G [+] env T).
    apply (IHG x T); auto.
    apply subst_envs_comp_tail with (Some t); trivial.
    congruence.
     (* a = None *)
    rewrite subst_ran_cons_none.
    destruct x.
    try_solve.
    apply (IHG x T); try_solve.
    eapply subst_envs_comp_tail; eauto.
  Qed.

  Lemma typing_in_subst_env M G (C: correct_subst M G) x T :
    G |-> x/T -> subst_ran G |- term T := type T.

  Proof.
    intros. destruct C. rewrite (subst_comp_env H envs_c0).
    apply typing_ext_env_l. exact (typing T).
  Qed.

  Lemma presubst_beyond_aux : forall Pt i j k G,
      j + k >= length G -> (forall p, p < k -> G |-> p/-) ->
      presubst_aux (prelift_aux j Pt k) i G = prelift_aux j Pt k.

  Proof.
    induction Pt; unfold prelift; intros; simpl.
    destruct (le_gt_dec k x); simpl.
    rewrite nth_beyond; trivial.
    lia.
    destruct (H0 x).
    lia.
    rewrite H1; trivial.
    rewrite H1; trivial.
    trivial.
    assert (presubst_aux (prelift_aux j Pt (S k)) (S i) (None :: G)
            = prelift_aux j Pt (S k)).
    apply IHPt.
    simpl; lia.
    intros.
    destruct p.
    constructor 2; trivial.
    apply (H0 p); lia.
    congruence.
    rewrite IHPt1; trivial.
    rewrite IHPt2; trivial.
  Qed.

  Lemma presubst_beyond Pt i j G :
    j >= length G -> presubst_aux (prelift Pt j) i G = prelift Pt j.

  Proof.
    intro. unfold prelift. apply presubst_beyond_aux. lia.
    intros; lia.
  Qed.

  Lemma presubst_prelift_aux : forall M G i j,
    presubst_aux (prelift_aux j M i) i (copy (i + j) None ++ lift_subst G j)
    = prelift_aux j (presubst_aux M i (copy i None ++ G)) i.

  Proof.
    induction M; simpl; intros.
    destruct (Compare_dec.le_gt_dec i x); simpl.
    rewrite !nth_app_right; autorewrite with datatypes using trivial; try lia.
    replace (x + j - (i + j)) with (x - i); [idtac | lia].
    destruct (varSubst_dec G (x-i)) as [[W GW] | Gn].
    rewrite GW.
    rewrite (var_subst_lift j GW).
    autorewrite with terms.
    rewrite <- prelift_fold.
    unfold prelift; rewrite prelift_aux_fold_aux; try_solve; try lia.
    rewrite plus_comm; trivial.
    destruct (var_notSubst_lift j Gn); destruct Gn;
      rewrite H; rewrite H0; simpl; destruct (Compare_dec.le_gt_dec i x); solve
	[ lia
	| assert (S x = (x + 1)%nat); [lia | try_solve]
        ].
    rewrite !nth_app_left; autorewrite with datatypes using trivial; try lia.
    simpl.
    destruct (Compare_dec.le_gt_dec i x).
    lia.
    rewrite nth_app_left; autorewrite with datatypes using trivial; try lia.
    trivial.
    replace (None :: copy (i + j) None ++ lift_subst G 1) with 
      (copy (S i + j) None ++ lift_subst G 1); trivial.
    rewrite <- (IHM G (S i)); trivial.
    rewrite <- IHM1.
    rewrite <- IHM2.
    trivial.
  Qed.

  Lemma presubst_prelift_comm Pt i G :
    presubst (prelift Pt i) (copy i None ++ lift_subst G i)
    = prelift (presubst Pt G) i.

  Proof.
    unfold presubst, prelift. replace i with (0 + i); trivial.
    rewrite presubst_prelift_aux; trivial.
  Qed.

  Definition subst_aux : forall (M: Term) (G: Subst) (C: correct_subst M G),
    {Q: Term | env Q  = env M [-] subst_dom G [+] subst_ran G
               /\ term Q = presubst (term M) G
               /\ type Q = type M }.

  Proof.
    destruct M as [EM PtM TM TypM].
    induction TypM; intros G C; unfold presubst; simpl.

     (* -) variable *)
    destruct (varSubst_dec G x) as [[T G_xT] | x_uc].
     (*   - variable is substituted *)
    rewrite G_xT.
    assert (Vc: subst_ran G |- term T := A).
    assert (TA: type T = A).
    destruct (subst_type_comp C G_xT).
    unfold VarD in *; simpl in *; congruence.
    unfold VarD, VarUD in *; destruct H; 
      exfalso; simpl in *; congruence.
    rewrite <- TA.
    apply typing_in_subst_env with (buildT (TVar v)) x; trivial.
    exists (buildT (typing_ext_env_l (E [-] subst_dom G) Vc));
      repeat split; auto.
    simpl; rewrite lift_0; trivial.
     (*   - variable is not substituted *)
    assert (Vnc: (E [-] subst_dom G) [+] subst_ran G |- %x := A).
    constructor.
    destruct C; simpl in * .
    destruct (isVarDecl_dec (subst_ran G) x) as [[B GxB] | Gxn].
    assert (eAB: A = B).
    sym; apply (ran_c0 x B A); trivial.
    apply env_sub_ly_rn; trivial.
    apply subst_dom_varNotSubst; trivial.
    rewrite eAB; apply env_sum_ry; trivial.
    apply env_sum_ly_rn; trivial.
    apply env_sub_ly_rn; trivial.
    apply subst_dom_varNotSubst; trivial.
    exists (buildT Vnc); repeat split; auto.
    destruct x_uc as [G_xn | G_xn]; rewrite G_xn; trivial.

     (* -) function symbol *)
    assert (t: (E [-] subst_dom G) [+] subst_ran G |- ^f := f_type f).
    constructor.
    exists (buildT t); auto.

     (* -) abstraction *)
    destruct (IHTypM (None::(lift_subst G 1))) 
      as [AB [AB_env [AB_term AB_type]]];
      clear IHTypM.
    split; intros; destruct C.
     (*    - environments in substitution are ok *)
    unfold subst_envs_comp; intros.
    destruct i; simpl in *; try discr.
    destruct j; simpl in *; try discr.
    set (lc := lifted_subst_envs_comp 1 envs_c0).
    apply (lc i j); trivial.
     (*    - substitution domain compatibile with term *)
    simpl; unfold decl.
    apply env_comp_cons; auto.
    rewrite subst_dom_lifted; trivial.
     (*    - substitution range compatibile with term *)
    change (None :: lift_subst G 1) with (lift_subst (None::G) 1).
    rewrite subst_dom_lifted.
    simpl.
    rewrite subst_ran_cons_none.
    destruct (subst_empty_dec G) as [Ge | Gne].
    rewrite subst_ran_lifted_empty; trivial.
    apply env_comp_sub.
    apply env_comp_sym.
    apply env_comp_empty.
    rewrite subst_ran_lifted_ne; trivial.
    simpl; unfold decl.
    apply env_comp_cons; auto.
     (*  - substitution on abstraction *)
    assert (t: (E [-] subst_dom G) [+] subst_ran (None::G)
            |- \A => term AB := A --> B).
    constructor.
    change (None :: lift_subst G 1) with 
      (lift_subst (None::G) 1) in AB_env.
    assert (ABenv: decl A ((E [-] subst_dom G) [+] subst_ran (None::G))
                   = env AB).
    rewrite AB_env.
    destruct (subst_empty_dec G) as [Ge | Gne].
     (*  - G empty *)
    assert (ES: isEmptySubst (lift_subst (None :: G) 1)).
    simpl.
    apply subst_cons_empty.
    apply subst_lift_empty; trivial.
    rewrite !subst_ran_empty; trivial.
    rewrite !env_sub_Empty, !env_sum_empty_r; trivial.
    apply subst_dom_Empty; trivial.
    apply subst_dom_Empty; trivial.
    apply subst_cons_empty; trivial.
     (*  - G non-empty *)
    rewrite subst_ran_lifted_ne; trivial.
    rewrite subst_dom_lifted; trivial.
    intro f.
    absurd (isEmptySubst G); trivial.
    apply subst_tail_empty; trivial.
    rewrite ABenv.
    simpl in AB_type; rewrite <- AB_type.
    exact (typing AB).
    exists (buildT t); repeat split; simpl.
    rewrite subst_lift_subst.
    simpl in *; congruence.

     (* -) application *)
    destruct C.
    destruct (IHTypM1 G) as [L [L_env [L_term L_type]]].
    split; trivial.
    destruct (IHTypM2 G) as [R [R_env [R_term R_type]]].
    split; trivial.
    simpl in * .
    assert (t: (E [-] subst_dom G) [+] subst_ran G |- term L @@ term R := B).
    constructor 4 with A.
    rewrite <- L_env; rewrite <- L_type; exact (typing L).
    rewrite <- R_env; rewrite <- R_type; exact (typing R).
    exists (buildT t); repeat split; simpl.
    unfold presubst in *; congruence.
  Qed.

  Definition subst (M: Term) (G: Subst) (C: correct_subst M G) : Term :=
    proj1_sig (subst_aux C).

  Lemma subst_env M G (C: correct_subst M G) :
    env (subst C) = env M [-] subst_dom G [+] subst_ran G.

  Proof. unfold subst; intros. destruct (subst_aux C); simpl; tauto. Qed.

  Lemma subst_term M G (C: correct_subst M G) :
    term (subst C) = presubst (term M) G.

  Proof. unfold subst; intros. destruct (subst_aux C); simpl; tauto. Qed.

  Lemma subst_type M G (C: correct_subst M G) : type (subst C) = type M.

  Proof. unfold subst. destruct (subst_aux C); simpl; tauto. Qed.

  Hint Rewrite subst_env subst_term subst_type : terms.

  Lemma subst_env_cont_subst_comp M G x (MG: correct_subst M G) T :
    G |-> x/T -> env (subst MG) = env (subst MG) [+] env T.

  Proof.
    intro GT. rewrite subst_env. destruct MG.
    set (q := subst_comp_env GT envs_c0). rewrite env_sum_assoc. congruence.
  Qed.

  Lemma subst_proof_irr M G (C1 C2: correct_subst M G) : subst C1 = subst C2.

  Proof.
    apply term_eq. rewrite !subst_env; trivial. rewrite !subst_term; trivial.
  Qed.

  Lemma subst_eq M M' G (MG: correct_subst M G) (MG': correct_subst M' G) :
    M = M' -> subst MG = subst MG'.

  Proof.
    intro M_M'. apply term_eq.
    rewrite !subst_env, M_M'; trivial.
    rewrite !subst_term, M_M'; trivial.
  Qed.

  Lemma subst_env_compat M G x T (MG: correct_subst M G) :
    G |-> x / T -> env (subst MG) [<->] env T.

  Proof.
    intro GxT. inversion MG.
    assert (TG: env T [<->] subst_ran G).
    apply subst_comp_comp_ran with x; trivial.

    rewrite subst_env.
    intros p A B LA RB.
    
    set (w := subst_ran_component_comp GxT envs_c0 RB).
    set (w' := env_sum_ry (env M [-] subst_dom G) w).
    unfold VarD in *; congruence.
  Qed.

  #[global] Hint Resolve presubst_aux : terms.
  #[global] Hint Unfold subst presubst : terms.

  Definition emptySubst : Subst := nil.

  Lemma emptySubst_correct : forall M, correct_subst M emptySubst.

  Proof.
    split.
    intros i j; destruct i; try_solve.
    simpl; apply env_comp_sym; apply env_comp_empty.
    simpl; apply env_comp_sym; apply env_comp_empty.
  Qed.

  Lemma emptySubst_empty : isEmptySubst (emptySubst).

  Proof. exact subst_nil_empty. Qed.

  Lemma empty_presubst_neutral_aux : forall Pt i G,
      (forall x, In x G -> x = None) -> Pt = presubst_aux Pt i G.

  Proof.
    induction Pt.
     (* variable *)
    unfold presubst, presubst_aux.
    intros.
    destruct (nth_error_In G x) as [[Gx Gx_nth] | Gxn].
    rewrite Gx_nth.
    rewrite (H Gx (nth_some_in G x Gx_nth)); trivial.
    rewrite Gxn; trivial.
     (* function symbol *)
    auto.
     (* abstraction *)
    intros i G Gempty; simpl.
    assert (Pt = presubst_aux Pt (S i) (None::G)).
    apply IHPt; trivial.
    intros x xIn.
    destruct xIn.
    congruence.
    apply Gempty; trivial.
    congruence.
     (* application *)
    intros i G Gempty; simpl.
    assert (Pt1 = presubst_aux Pt1 i G).
    apply (IHPt1 i G); trivial.
    assert (Pt2 = presubst_aux Pt2 i G).
    apply (IHPt2 i); trivial.
    congruence.
  Qed.

  Lemma empty_presubst_neutral : forall Pt G,
    (forall x, In x G -> x = None) -> presubst Pt G = Pt. 

  Proof.
    intro Pt; unfold presubst. sym; apply empty_presubst_neutral_aux; trivial.
  Qed.

  Lemma emptySubst_neutral : forall M S (CS: correct_subst M S),
    isEmptySubst S -> subst CS = M.

  Proof.
    intros; apply term_eq.
    rewrite subst_env; simpl.
    rewrite subst_ran_empty; trivial.
    rewrite env_sum_empty_r.
    rewrite env_sub_Empty; trivial.
    apply subst_dom_Empty; trivial.
    rewrite subst_term.
    apply empty_presubst_neutral.
    intros p pS.
    destruct p; trivial.
    destruct (list_In_nth S (Some t) pS).
    destruct (H x); try_solve.
  Qed.

  Definition idSubst : forall M : Term, Subst.

  Proof.
    intros M; destruct M.
    destruct (isVarDecl_dec env0 0) as [[A EA] | EE].
    set (var := TVar EA).
    exact ({x/buildT var}).
    assert (var: decl (#baseTypesNotEmpty) EmptyEnv |= 0 := #baseTypesNotEmpty).
    constructor.
    exact ({x/buildT (TVar var)}).
  Defined.

  Lemma idSubst_decl0 M A (M0: env M |= 0 := A) :
    idSubst M = {x/buildT (TVar M0)}.

  Proof.
    destruct M; simpl.
    destruct (isVarDecl_dec env0 0) as [[B EB] | En].
    replace (buildT (TVar EB)) with (buildT (TVar M0)); trivial.
    apply term_eq; trivial.
    exfalso; apply varD_UD_absurd with env0 0 A; trivial.
  Qed.

  Lemma idSubst_correct M : correct_subst M (idSubst M).

  Proof.
    destruct M.
    unfold idSubst; simpl.
    destruct (isVarDecl_dec env0 0) as [[A EA] | En].
    simpl; apply one_var_subst_correct; simpl.
    intros; inversion EA; inversion H; try_solve.
    apply env_comp_refl.
    simpl; apply one_var_subst_correct; simpl.
    intros A E0; inversion E0; inversion En; destruct env0; try_solve.
    destruct env0.
    apply env_comp_sym; apply env_comp_empty.
    destruct o.
    inversion En; try_solve.
    unfold decl; apply env_comp_cons; auto.
    apply env_comp_empty.
  Qed.

  Lemma idSubst_neutral_aux :
    forall M n, presubst_aux (term M) n (copy n None ++ idSubst M) = term M.

  Proof.
    destruct M as [E Pt A M].
    simpl; gen E.
    induction M; intros E0 n; try_solve.
     (* variable *)
    destruct (lt_eq_lt_dec x n) as [[x_lt_n | x_eq_n] | x_gt_n].
    rewrite nth_app_left.
    rewrite nth_copy_in; trivial.
    autorewrite with datatypes using trivial.
    rewrite nth_app_right; autorewrite with datatypes.
    rewrite x_eq_n.
    rewrite <- (minus_n_n n); simpl.
    destruct (isVarDecl_dec E0 0) as [[B EB] | En]; trivial.
    lia.
    rewrite nth_beyond; trivial.
    rewrite length_app.
    autorewrite with datatypes.
    destruct (isVarDecl_dec E0 0) as [[B EB] | En]; simpl; lia.
     (* abstraction *)
    set (hint := IHM E0 (S n)).
     (* x-man, replace... at would be useful *)
    set (Pt2 := Pt) in |- * at 1.
    rewrite <- hint.
    unfold Pt2; clear hint.
    destruct (isVarDecl_dec E0 0) as [[C EC] | En]; trivial.
    (* application *)
    set (PtL' := PtL) in |- * at 1.
    set (PtR' := PtR) in |- * at 1.
    rewrite <- (IHM1 E0 n).
    rewrite <- (IHM2 E0 n).
    destruct (isVarDecl_dec E n) as [[C EC] | en]; trivial.
  Qed.

  Lemma idSubst_neutral M : (subst (idSubst_correct M)) ~ M.

  Proof.
    apply terms_conv_criterion.
     (* env *)
    rewrite subst_env.
    destruct M; unfold idSubst; simpl.
    destruct (isVarDecl_dec env0 0) as [[A EA] | En]; simpl.
    destruct env0; try destruct o; try_solve.
    rewrite env_sub_empty.
    rewrite env_sum_double.
    apply env_comp_refl.
    unfold subst_ran; simpl.
    destruct env0; try_solve.
    destruct o.
    inversion En; try_solve.
    simpl; rewrite env_sub_empty; rewrite env_sum_empty_r.
    apply env_comp_cons; auto.
    apply env_comp_refl.
     (* preterm *)
    rewrite subst_term.
    unfold presubst.
    change (idSubst M) with (copy 0 None ++ idSubst M).
    apply idSubst_neutral_aux.
  Qed.

  Lemma presubst_lift_beyond : forall Pt G m n i (W := prelift_aux n Pt m),
      m <= i -> m + n >= i + length G -> presubst W (copy i None ++ G) = W.

  Proof.
    induction Pt; intros G m n i W m_c mn_c; unfold W, presubst; simpl.
     (* variable *)
    destruct (le_gt_dec m x); simpl.
    rewrite nth_beyond; trivial.
    rewrite length_app.
    rewrite copy_length.
    lia.
    rewrite nth_app_left.
    destruct (nth_error_In (copy i (@None Term)) x) as [ [ss ss_nth] 
                                                       | sn].
    rewrite ss_nth.
    rewrite (copy_in i None ss (nth_some_in _ _ ss_nth)); trivial.
    rewrite sn; trivial.
    autorewrite with datatypes using lia.
     (* function symbol *)
    trivial.
     (* abstraction *)
    rewrite subst_lift_subst; simpl.
    rewrite lift_subst_distr.
    rewrite lift_empty_subst.
    rewrite app_comm_cons.
    rewrite copy_cons.
    rewrite (IHPt (lift_subst G 1) (S m) n (S i)); trivial.
    lia.
    rewrite (length_lift_subst G 1).
    lia.
     (* application *)
    fold (presubst (prelift_aux n Pt1 m) (copy i None ++ G)).
    rewrite IHPt1; trivial.
    fold (presubst (prelift_aux n Pt2 m) (copy i None ++ G)).
    rewrite IHPt2; trivial.
  Qed.

  Lemma presubst_var_beyond G i x :
    x >= length G -> presubst_aux (%x) i G = %x.

  Proof.
    intro x_G. rewrite subst_lift_subst.
    change (%x) at 1 with (prelift_aux x (%0) 0).
    change (lift_subst G i) with (copy 0 None ++ lift_subst G i).
    rewrite presubst_lift_beyond; trivial.
    rewrite length_lift_subst; trivial.
  Qed.

  Lemma presubst_aux_disjoint :
    forall Pt Pt_x G i k (shift := fun k G => copy k None ++ G)
           (EL := shift k (lift_subst (None::G) (S k))) (ER := shift k {x/Pt_x})
           (EC := shift k (Some Pt_x :: lift_subst G (S k))),
      presubst_aux (presubst_aux Pt i EL) i ER = presubst_aux Pt i EC.

  Proof.
    induction Pt; intros.
     (* variable *)
    unfold EL, ER, EC, shift; simpl.
    destruct (gt_eq_gt_dec k x) as [[x_gt_k | x_eq_k] | k_eq_x].
     (*   - x > k *)
    do 2 (rewrite nth_app_right; 
      autorewrite with datatypes using auto with arith).
    assert (w_xk: exists w, x - k = S w).
    assert (x_k_0: x - k > 0).
    lia.
    destruct (x - k).
    absurd (0 > 0); auto with arith.
    exists n; trivial.
    destruct w_xk as [w w_eq].
    rewrite w_eq; simpl.
    destruct (nth_error_In (lift_subst G (S k)) w) as [[ps ps_nth] | pn].
     (*     - x within G *)
    rewrite ps_nth.
    destruct ps.
     (*        - x is substituted *)
    destruct (in_lift_subst t G (S k)) as [q q_in q_lift].
    eapply nth_some_in; eauto.
    rewrite q_lift.
    rewrite <- lift_fold.
    unfold lift.
    destruct (lift_aux ((S k)+i) q 0) as [Q [Q_env [Q_term Q_type]]]; 
      simpl.
    rewrite Q_term.
    rewrite subst_lift_subst.
    rewrite lift_subst_distr.
    rewrite lift_empty_subst.
    rewrite presubst_lift_beyond; trivial.
    lia.
    rewrite length_lift_subst; simpl.
    lia.
     (*        - x not substituted *)
    rewrite presubst_var_beyond; trivial.
    autorewrite with datatypes using simpl.
    lia.
     (*     - x beyond G *)
    rewrite pn.
    rewrite presubst_var_beyond; trivial.
    autorewrite with datatypes using simpl.
    lia.
     (*   - x = k *)
    rewrite x_eq_k.
    do 2 (rewrite nth_app_right; autorewrite with datatypes using auto).
    rewrite <- minus_n_n; simpl.
    rewrite nth_app_right; autorewrite with datatypes using auto.
    rewrite <- minus_n_n; trivial.
     (*   - x < k *)
    do 2 (rewrite nth_app_left; autorewrite with datatypes using trivial).
    simpl.
    rewrite nth_app_left; autorewrite with datatypes using trivial.
     (* function symbol *)
    auto.
     (* abstraction *)
    unfold EL, ER, EC, shift; simpl.
    replace (S i) with (i + 1); [idtac | lia].
    rewrite !subst_lift_subst_aux; simpl.
    rewrite !lift_subst_distr; simpl.
    rewrite <- lift_subst_fold.
    rewrite lift_empty_subst, !app_comm_cons, copy_cons.
    replace (S k + 1) with (S (S k)); [idtac | lia].
    rewrite <- (IHPt (lift Pt_x 1) G i (S k)); auto.
    simpl; trivial.
     (* application *)
    simpl.
    unfold EL, ER, EC, shift.
    rewrite (IHPt1 Pt_x G i k).
    rewrite (IHPt2 Pt_x G i k).
    trivial.
  Qed.

  Lemma presubst_disjoint : forall Pt Pt_x G,
    presubst (presubst Pt (lift_subst (None::G) 1)) {x/Pt_x} =
    presubst Pt (Some Pt_x :: lift_subst G 1).

  Proof.
    intros; unfold presubst.
    replace (Some Pt_x :: lift_subst G 1) 
       with (copy 0 None ++ Some Pt_x :: lift_subst G 1).
    rewrite <- (presubst_aux_disjoint Pt Pt_x G 0 0).
    trivial.
    simpl; trivial.
  Qed.

  Lemma subst_disjoint_c M G P
        (S: correct_subst M (lift_subst (None::G) 1))
        (S': correct_subst (subst S) {x/P}) :
    correct_subst M (Some P::lift_subst G 1).

  Proof.
    inversion S; inversion S'.
    simpl in * .
    rewrite subst_env in dom_c1.
    rewrite subst_env in ran_c1.
    rewrite subst_ran_cons_none in dom_c1.
    rewrite subst_ran_cons_none in ran_c0.
    rewrite subst_ran_cons_none in ran_c1.
    split.
     (* subst envs correct *)
    assert (P_comp_MR: forall Ti Tj q,
      (Some P :: lift_subst G 1) |-> 0 / Ti ->
      (Some P :: lift_subst G 1) |-> (Datatypes.S q) / Tj ->
      env Ti [<->] env Tj).
    intros Ti Tj q Gp Gq p A B PA MB; destruct p.
    destruct (nth_lift_normal G 1 q Gq) as [T_j Tj_lift Tj_nth].
    rewrite Tj_lift in MB.
    rewrite lift_env in MB; try_solve.
    inversion Gp.
    rewrite <- H0 in PA.
    apply (ran_c1 (Datatypes.S p)).
    rewrite subst_ran_single.
    destruct (env P); try_solve.
    replace (e [-] nil) with e.
    destruct o; try_solve.
    destruct e; try destruct o0; try_solve.
    apply env_sum_ry.
    assert (Gq_Tj: lift_subst G 1 |-> q / Tj).
    try_solve.
    rewrite (subst_comp_env Gq_Tj).
    apply env_sum_ry; trivial.
    eapply subst_envs_comp_tail; eauto.

    intros p q Ti Tj Gp Gq.
    destruct p.
    destruct q; try_solve.
    inversion Gp; inversion Gq.
    apply P_comp_MR with q; trivial.
    destruct q.
    apply env_comp_sym.
    apply P_comp_MR with p; trivial.
    apply (envs_c0 (Datatypes.S p) (Datatypes.S q)); try_solve.

     (* subst_dom compatible *)
    simpl; intros p A B.
    destruct p.
    intros A_typeP MB.
    apply (dom_c1 0); try_solve.
    apply env_sum_ly_rn; trivial.
    apply env_sub_ly_rn; auto with terms.
    apply subst_ran_lifted_noDecl.
    intros Gp Mp.
    apply (dom_c0 (Datatypes.S p)); try_solve.

     (* subst_ran compatible *)
    simpl in * .
    intros p A B RA MB.
    destruct p.
    destruct (subst_ran (Some P :: lift_subst G 1)); try_solve.
    destruct o; try_solve.
    destruct (env_sub_varDecl _ _ RA) as [PGr_p Gd_p].
    rewrite subst_ran_cons_some in PGr_p.
    destruct (env_sum_varDecl _ _ PGr_p) as [[P_p Gr_p] | Gr_p].
    apply (ran_c1 (Datatypes.S p)).
    apply env_sub_ly_rn; try_solve.
    rewrite subst_ran_single; trivial.
    destruct p; try_solve.
    apply env_sum_ly_rn; trivial.
    apply env_sub_ly_rn; trivial.
    apply (ran_c0 (Datatypes.S p)); trivial.
    apply env_sub_ly_rn; trivial.
  Qed.

  Lemma fold_progress : forall (A B: Type) (conv: B -> A) g l (a init: A)
    (f := fun r el => match el with None => r | Some e => g r (conv e) end),
  (forall a b c, g (g a b) c = g a (g b c)) -> 
  (forall a, g a init = g init a) ->
  g a (fold_left f l init) = fold_left f l (g init a).

  Proof.
    induction l.
    simpl; auto.
    intros a' init f g_assoc g_init_comm; destruct a.
    simpl.
    rewrite g_assoc.
    unfold f.
    rewrite <- (IHl (conv b) init); trivial.
    rewrite <- (IHl (g a' (conv b)) init); trivial.
    fold f.
    rewrite g_assoc; trivial.
    apply (IHl a' init); trivial.
  Qed.

  Lemma subst_disjoint M G P
        (S: correct_subst M (None :: lift_subst G 1))
        (S': correct_subst (subst S) {x/P})
        (Sj: correct_subst M (Some P :: lift_subst G 1)) : subst S' = subst Sj.

  Proof.
    apply term_eq.
     (* environments equal *)
    rewrite !subst_env, subst_ran_cons_none, subst_ran_single. simpl.
    rewrite env_sum_sub, env_sub_sub_sum. simpl.
    rewrite env_sum_empty_r, env_sum_assoc,
      (@env_comp_sum_comm (subst_ran (lift_subst G 1)) (env P)),
      subst_ran_cons_some; trivial.
    apply env_comp_sym.
    apply env_comp_sum_comp_right with (env P).
    rewrite <- subst_ran_cons_some.
    apply subst_comp_comp_ran with 0.
    unfold varSubstTo; trivial.
    destruct Sj; trivial.
    intro p; destruct p.
    destruct (subst_empty_dec G) as [Ge | Gne].
    rewrite subst_ran_lifted_empty; trivial.
    left; left; trivial.
    rewrite subst_ran_lifted_ne; trivial.
    left; right; trivial.
    right; left; destruct p; trivial.

     (* preterms equal *)
    rewrite !subst_term.
    change (None :: lift_subst G 1) with (lift_subst (None::G) 1).
    apply presubst_disjoint.
  Qed.

  Lemma singleton_correct_single M P G :
    correct_subst M G -> isSingletonSubst P G -> correct_subst M {x/P}.

  Proof.
    intros.
    destruct H.
    constructor.
    apply subst_envs_comp_single.
    simpl; intros p A B pA.
    destruct p.
    intro M0.
    replace A with (type P); trivial.
    apply (dom_c0 0 (type P) B); trivial.
    destruct (subst_dom_singleton H0) as [E [GE _]].
    rewrite GE; constructor.
    inversion pA; trivial.
    inversion pA; destruct p; try_solve.
    simpl.
    rewrite (subst_ran_singleton H0) in ran_c0.
    rewrite subst_ran_single.
    destruct (subst_dom_singleton H0) as [E [GE Eempty]].
    rewrite GE in ran_c0.
    intros p A B Pp.
    destruct p.
    exfalso.
    apply (varD_UD_absurd Pp).
    apply env_sub_ry with (type P); constructor.
    intros Mp.
    apply (ran_c0 (S p)); trivial.
    apply env_sub_ly_rn.
    apply env_sub_suby_ly with {x/type P}; trivial.
    unfold VarUD; simpl.
    apply Eempty.
  Qed.

  Lemma singleton_presubst : forall M P G i j, isSingletonSubst P G ->
    presubst_aux (term M) j (copy i None ++ {x/P})
    = presubst_aux (term M) j (copy i None ++ G).

  Proof.
    destruct M as [E Pt T M]; induction M; intros; unfold presubst; simpl in * .
    destruct (lt_eq_lt_dec x i) as [[x_i | x_i] | x_i].
    rewrite !nth_app_left; autorewrite with datatypes; solve [lia | trivial].
    rewrite x_i.
    rewrite !nth_app_right; autorewrite with datatypes; try lia.
    replace (i - i) with 0; [simpl | lia].
    destruct G.
    inversion H; inversion H0.
    destruct o; inversion H; inversion H0.
    rewrite <- H3; trivial.
    rewrite !nth_app_right; autorewrite with datatypes; try lia.
    assert (x - i > 0); [lia | destruct (x - i)].
    lia.
    destruct G.
    inversion H; inversion H1.
    destruct o; simpl.
    replace (nth_error (A:=option Term) nil n) with (None (A:=option Term)).
    inversion H.
    destruct (H2 n); simpl in H3; rewrite H3; trivial.
    destruct n; trivial.
    inversion H; inversion H1.
    trivial.
    rewrite !app_comm_cons.
    change ((None (A:=Term)) :: copy i None) with 
      (copy (S i) (None (A:=Term))).
    rewrite (IHM P G (S i) (S j)); trivial.
    rewrite (IHM1 P G i j); trivial.
    rewrite (IHM2 P G i j); trivial.
  Qed.

  Lemma singleton_subst M P G
        (CS: correct_subst M {x/P}) (CS': correct_subst M G) :
    isSingletonSubst P G -> subst CS = subst CS'.

  Proof.
    intro. apply term_eq.
    autorewrite with terms using simpl.
    rewrite (subst_ran_singleton H).
    destruct (subst_dom_singleton H) as [E [DomG Eempty]].
    rewrite DomG.
    destruct (env M); destruct (env P); try destruct o; try destruct o0;
      try_solve;
      autorewrite with terms using simpl; try rewrite (env_sub_Empty e Eempty); 
	try_solve.
    autorewrite with terms.
    unfold presubst.
    apply (singleton_presubst M 0 0 H).
  Qed.

  Lemma app_subst_app (M: Term) (Mapp: isApp M) G (CS: correct_subst M G) :
    isApp (subst CS).

  Proof.
    term_inv M.
    unfold subst; destruct (subst_aux CS) as [T [Tenv [Tterm Ttype]]].
    unfold presubst in Tterm; simpl in *.
    eapply app_isApp; eauto.
  Qed.

  Lemma abs_subst_abs M (Mabs: isAbs M) G (CS: correct_subst M G) :
    isAbs (subst CS).

  Proof.
    term_inv M.
    apply abs_isAbs with A (presubst_aux Pt 1 (None::G)).
    rewrite subst_term; auto.
  Qed.

  Lemma subst_appL_c : forall (M: Term) (Mapp: isApp M) G,
      correct_subst M G -> correct_subst (appBodyL Mapp) G.

  Proof. intro M; term_inv M. fo. Qed.

  Lemma subst_appR_c M (Mapp: isApp M) G :
      correct_subst M G -> correct_subst (appBodyR Mapp) G.

  Proof. term_inv M. fo. Qed.

  Lemma subst_abs_c M (Mabs: isAbs M) G :
    correct_subst M G -> correct_subst (absBody Mabs) (None :: lift_subst G 1).

  Proof.
    intro MG.
    term_inv M.
    destruct MG.
    split.
     (* environments in G compatible *)
    intros i j Ti Tj.
    destruct i; unfold varSubstTo; try_solve.
    destruct j; try_solve.
    intros Gi Gj.
    destruct (nth_lift_normal G 1 i Gi) as [T_i Til Tin].
    destruct (nth_lift_normal G 1 j Gj) as [T_j Tjl Tjn].
    rewrite Til.
    rewrite Tjl.
    rewrite !lift_env.
    unfold liftedEnv, finalSeg; simpl.
    rewrite !initialSeg_full; try solve [auto | lia].
    apply env_comp_cons; auto.
    apply (envs_c0 i j); trivial.
     (* domain of G ok *)
    simpl.
    unfold decl; apply env_comp_cons; auto.
    rewrite subst_dom_lifted; trivial.
     (* range of G ok *)
    simpl.
    rewrite subst_ran_cons_none.
    rewrite subst_dom_lifted.
    destruct (subst_empty_dec G) as [Ge | Gne].
    rewrite subst_ran_lifted_empty; trivial.
    apply env_comp_sub.
    apply env_comp_sym.
    apply env_comp_empty.
    rewrite subst_ran_lifted_ne; trivial.
    simpl; unfold decl; apply env_comp_cons; try_solve.
  Qed.

  Lemma var_subst M G (MG: correct_subst M G) : isVar M ->
    { T:Term & { x:nat | G |-> x/T & term (subst MG) = term T }}
    + { term (subst MG) = term M }.

  Proof.
    intro.
    term_inv M.
    autorewrite with terms.
    unfold presubst; simpl.
    destruct (varSubst_dec G x) as [[W Gx] | Gxn].
    left; exists W; exists x; trivial.
    rewrite Gx; rewrite lift_0; trivial.
    right.
    destruct Gxn; rewrite H0; trivial.
  Qed.

  Lemma funS_presubst M G (MG: correct_subst M G) :
    isFunS M -> term (subst MG) = term M.

  Proof. intros. term_inv M. rewrite subst_term. compute; trivial. Qed.

  Lemma funS_subst M G (MG: correct_subst M G) : isFunS M -> (subst MG) ~ M.

  Proof.
    intro.
    exists emptyEnvSubst.
    constructor.
    term_inv M.
    rewrite funS_presubst; trivial.
    simpl; constructor.
    apply conv_env_empty.
  Qed.

  Lemma funS_subst_funS M G (MG: correct_subst M G) :
    isFunS M -> isFunS (subst MG).

  Proof.
    intro.
    term_inv M.
    apply funS_is_funS with f.
    change (^f) with (term Tr).
    apply funS_presubst; trivial.
  Qed.

  Lemma app_subst M (Mapp: isApp M) G (S: correct_subst M G)
    (SL : correct_subst (appBodyL Mapp) G := subst_appL_c Mapp S)
    (SR : correct_subst (appBodyR Mapp) G := subst_appR_c Mapp S)
    (Sapp : isApp (subst S) := app_subst_app Mapp S) :
    appBodyL Sapp = subst SL /\ appBodyR Sapp = subst SR.

  Proof.
    split; apply term_eq.
    autorewrite with terms; trivial.
    term_inv M.
    rewrite subst_term; simpl.
    assert (Mterm: term (subst S) = presubst PtL G @@ presubst PtR G).
    rewrite subst_term; trivial.
    rewrite (appBodyL_term (subst S) Mterm); trivial.
    autorewrite with terms; trivial.
    term_inv M.
    rewrite subst_term; simpl.
    assert (Mterm: term (subst S) = presubst PtL G @@ presubst PtR G).
    rewrite subst_term; trivial.
    rewrite (appBodyR_term (subst S) Mterm); trivial.    
  Qed.

  Lemma type_appBodyL_subst M G (MG: correct_subst M G) (Mapp: isApp M) 
    (MGapp: isApp (subst MG) := app_subst_app Mapp MG) :
    type (appBodyL Mapp) = type (appBodyL MGapp).

  Proof.
    destruct (app_subst Mapp MG). unfold MGapp; rewrite H.
    autorewrite with terms; trivial.
  Qed.

  Lemma abs_subst M (Mabs: isAbs M) G (S: correct_subst M G)
        (Sabs : isAbs (subst S) := abs_subst_abs Mabs S)
        (S' : correct_subst (absBody Mabs) (None :: lift_subst G 1)
         := subst_abs_c Mabs S) :
    absType Sabs = absType Mabs /\ absBody Sabs = subst S'.

  Proof.
    split.
     (* absType *)
    term_inv M.
    apply abs_type with B.
    autorewrite with terms; trivial.
     (* absBody *)
    apply term_eq.
     (* - environments equal *)
    assert (absTypeEq: absType Sabs = absType Mabs).
    term_inv M.
    apply abs_type with B.
    rewrite subst_type; trivial.
    rewrite absBody_env, !subst_env, subst_ran_cons_none, absBody_env.
    destruct (subst_empty_dec G) as [Ge | Gne].
    rewrite subst_ran_lifted_empty; trivial.
    rewrite subst_ran_empty; simpl; trivial.
    rewrite !env_sub_Empty, !env_sum_empty_r; trivial.
    unfold decl; congruence.
    apply subst_dom_lifted_Empty; trivial.
    apply subst_dom_Empty; trivial.
    rewrite subst_ran_lifted_ne; trivial.
    unfold decl; simpl.
    rewrite subst_dom_lifted.
    congruence.
     (* - terms equal *)
    term_inv M.
    rewrite subst_term.
    assert (Sterm: term (subst S) = \A => presubst_aux Pt 1 (None::G)).
    rewrite subst_term; trivial.
    rewrite (absBody_term (subst S) Sabs Sterm).
    rewrite subst_lift_subst; trivial.
  Qed.

  Lemma funS_headS_subst : forall M f G (MG: correct_subst M G),
      term (appHead M) = ^f -> term (appHead (subst MG)) = ^f.

  Proof.
    destruct M as [E Pt A TypM].
    induction TypM; try_solve; intros.
    autorewrite with terms using unfold presubst; trivial.
    assert (isFunS (subst MG)).
    apply funS_is_funS with f.
    rewrite funS_presubst; simpl; trivial.
    term_inv (subst MG).
    destruct (app_subst (M:=buildT (TApp TypM1 TypM2)) I MG).
    set (MG_app := app_subst_app (M:=buildT (TApp TypM1 TypM2)) I MG).
    rewrite (appHead_app (subst MG) MG_app).
    unfold MG_app; rewrite H0.
    apply IHTypM1; trivial.
    rewrite (appHead_app (buildT (TApp TypM1 TypM2)) I) in H; trivial.
  Qed.

  Lemma funS_head_subst : forall M G (MG: correct_subst M G),
      isFunS (appHead M) -> isFunS (appHead (subst MG)).

  Proof.
    destruct M as [E Pt A TypM].
    simpl; induction TypM; try contr.
     (* function symbol *)
    intros; apply funS_is_funS with f.
    unfold subst; destruct (subst_aux MG) as [N [Nenv [Nterm Ntype]]].
    term_inv N.
     (* application *)
    intros.
    assert_app M_app (buildT (TApp TypM1 TypM2)).
    destruct (app_subst M_app MG) as [ML MR].
    rewrite (appHead_app (subst MG) (app_subst_app M_app MG)).
    rewrite ML.
    apply IHTypM1.
    rewrite (appHead_app (buildT (TApp TypM1 TypM2)) M_app) in H; 
      trivial.
  Qed.

  Lemma funApp_subst_funApp :
    forall M G (MG: correct_subst M G), isFunApp M -> isFunApp (subst MG).

  Proof. apply funS_head_subst; trivial. Qed.

  Lemma appUnits_subst_c M G W i (MG: correct_subst M G) :
    nth_error (appUnits M) i = Some W -> correct_subst W G.

  Proof.
    intro.
    destruct MG.
    assert (isAppUnit W M).
    unfold isAppUnit.
    apply nth_some_in with i; trivial.
    constructor; trivial.
    rewrite (appUnit_env W M H0); trivial.
    rewrite (appUnit_env W M H0); trivial.
  Qed.

  Lemma appUnits_subst_length : forall M G (MG: correct_subst M G),
      isFunS (appHead M) -> length (appUnits (subst MG)) = length (appUnits M).

  Proof.
    intro M; destruct M as [E Pt T M]; induction M; try_solve; intros.
    rewrite appUnits_notApp; trivial.
    intro MGapp.
    assert (forall M, isApp M -> isFunS M -> False).
    intro M; term_inv M.
    apply H0 with (subst MG); trivial.
    apply funS_subst_funS; trivial.
    rewrite (appUnits_app (buildT (TApp M1 M2)) I).
    rewrite (appUnits_app (subst MG)
                          (app_subst_app (M:=buildT (TApp M1 M2)) I MG)).
    autorewrite with datatypes using simpl.
    destruct (app_subst (M:=buildT (TApp M1 M2)) I MG).
    rewrite H0.
    rewrite <- (IHM1 G (subst_appL_c (M:=buildT (TApp M1 M2)) I MG)); trivial.
    set (w := @appHead_left (buildT (TApp M1 M2)) I); auto.
  Qed.

  Lemma appUnits_subst_rev : forall M G i W' (MG: correct_subst M G),
      isFunS (appHead M) -> nth_error (appUnits (subst MG)) i = Some W' ->
      exists W, exists Mi: nth_error (appUnits M) i = Some W,
          W' = subst (appUnits_subst_c i MG Mi).

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm)
      (P := fun M =>
	forall G i W' (MG: correct_subst M G),
	  isFunS (appHead M) ->
	  nth_error (appUnits (subst MG)) i = Some W' ->
	  exists W,
	    exists Mi: nth_error (appUnits M) i = Some W,
	      W' = subst (appUnits_subst_c i MG Mi)).
    apply subterm_wf.
    clear M; intros M IH G i W' MG M_fapp W'arg.
    destruct (isApp_dec M) as [Mapp | Mnapp].
    set (MG_app := app_subst_app Mapp MG).
    set (W''arg := W'arg).
    rewrite (appUnits_app (subst MG) MG_app) in W''arg.
    destruct (app_subst Mapp MG).
    set (MGl := subst (subst_appL_c Mapp MG)) in * .
    set (MGr := subst (subst_appR_c Mapp MG)) in * .
    replace (appBodyL MG_app) with MGl in W''arg.
    replace (appBodyR MG_app) with MGr in W''arg.
    assert (ML_head: isFunS (appHead (appBodyL Mapp))).
    rewrite (appHead_app M Mapp) in M_fapp; trivial.
    destruct (nth_app (appUnits MGl) (MGr::nil) i W''arg) 
      as [[MGl_i i_l] | [MGr_i i_r]].
    destruct (IH (appBodyL Mapp) (appBodyL_subterm M Mapp) G i W' 
      (subst_appL_c Mapp MG)) as [W [Mi W'def]]; trivial.
    exists W.
    assert (M_i: nth_error (appUnits M) i = Some W).
    rewrite (appUnits_app M Mapp).
    rewrite nth_app_left; trivial.
    rewrite <- (appUnits_subst_length (subst_appL_c Mapp MG)); trivial.
    exists M_i.
    rewrite W'def; trivial.
    apply term_eq; autorewrite with datatypes terms using trivial.
    exists (appBodyR Mapp).
    destruct (nth_error_singleton_in MGr (i - length (appUnits MGl)) MGr_i).
    assert (i = length (appUnits MGl)).
    lia.
    assert (Mi: nth_error (appUnits M) i = Some (appBodyR Mapp)).
    rewrite (appUnits_app M Mapp).
    rewrite nth_app_right.
    rewrite H3.
    rewrite <- (appUnits_subst_length (subst_appL_c Mapp MG)); trivial.
    fold MGl; rewrite <- minus_n_n; trivial.
    rewrite H3.
    rewrite <- (appUnits_subst_length (subst_appL_c Mapp MG)); trivial.
    fold MGl; auto.
    exists Mi.
    destruct (nth_error_singleton_in MGr (i - length (appUnits MGl)) MGr_i).
    rewrite <- H4.
    unfold MGr; apply subst_proof_irr.
    term_inv M.
    exists Tr.
    rewrite appUnits_notApp in W'arg.
    destruct i.
    inversion W'arg.
    simpl.
    assert (Some (buildT (TFun E f)) = Some Tr); trivial.
    exists H.
    apply term_eq; autorewrite with terms using trivial. 
    simpl in W'arg.
    destruct i; try_solve.
    assert (forall M, isFunS M -> isApp M -> False).
    intro M; term_inv M.
    intro MG_app; apply H with (subst MG); trivial.
    apply funS_subst_funS; trivial.
  Qed.

  Lemma subst_arg : forall M Marg G (MG: correct_subst M G), isArg Marg M ->
    exists MGarg, isArg MGarg (subst MG)
                  /\ exists MargG: correct_subst Marg G, MGarg = subst MargG.

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm)
      (P := fun M =>
	forall Marg G  (MG: correct_subst M G),
	  isArg Marg M ->
	  exists MGarg,
	    isArg MGarg (subst MG) /\
	    exists MargG: correct_subst Marg G,
	      MGarg = subst MargG).
    apply subterm_wf.
    clear M; intros M IH Marg G MG MargM.
    destruct (isApp_dec M) as [Mapp | Mnapp].
    set (MG_app := app_subst_app Mapp MG).
    destruct (app_subst Mapp MG) as [MGl MGr].
    destruct (appArg_inv M Marg Mapp MargM) as [argL | argR].
    destruct (IH (appBodyL Mapp) (appBodyL_subterm M Mapp) Marg G
      (subst_appL_c Mapp MG) argL) as [W [WL [MargG WMargG]]].
    exists W; split.
    apply appArg_left with MG_app.
    unfold MG_app; rewrite MGl; trivial.
    exists MargG; trivial.
    exists (appBodyR MG_app); split.
    apply appArg_right with MG_app; trivial.
    rewrite argR.
    exists (subst_appR_c Mapp MG); trivial.
    absurd (isArg Marg M); trivial.
    unfold isArg; rewrite appArgs_notApp; try_solve.
  Qed.

  Ltac term_ind X := 
    intro X;
    match goal with
    | |- ?G => 
      apply well_founded_ind with (R := subterm)(P := fun M: Term => G)
    end; 
    [apply subterm_wf | idtac | trivial].

  Lemma eq_term_arg_aux : forall M Marg M', isArg Marg M -> term M = term M' ->
    exists M'arg, isArg M'arg M' /\ term M'arg = term Marg.

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm)
      (P := fun M =>
	forall Marg M',
	  isArg Marg M ->
	  term M = term M' ->
	  exists M'arg,
	    isArg M'arg M' /\
	    term M'arg = term Marg).
    apply subterm_wf.
    clear M; intros M IH Marg M' MargM MM'term.
    set (Mapp := appArg_app M Marg MargM).
    assert (M'app: isApp M').
    term_inv M; term_inv M'.
    destruct (appArg_inv M Marg Mapp); trivial.
    destruct (IH (appBodyL Mapp) (appBodyL_subterm M Mapp) Marg 
      (appBodyL M'app) H) as [M'Larg [M'LargM' M'Larg_term]].
    term_inv M; term_inv M'.
    exists M'Larg; split.
    apply appArg_left with M'app; trivial.
    term_inv M; term_inv M'.
    exists (appBodyR M'app); split.
    apply appArg_right with M'app; trivial.
    rewrite H; trivial.
    term_inv M; term_inv M'.
  Qed.

  Lemma subst_arg_rev : forall M G MGarg (MG: correct_subst M G),
    isArg MGarg (subst MG) ->
    (exists Marg, isArg Marg M
                  /\ exists MGin: correct_subst Marg G, MGarg = subst MGin)
    \/ (exists p T Targ, isArg Targ T /\ G |-> p / T /\ term MGarg = term Targ).

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm)
      (P := fun M =>
	forall G MGarg (MG: correct_subst M G),
	  isArg MGarg (subst MG) ->
	  (exists Marg,
	    isArg Marg M /\ 
	    exists MGin: correct_subst Marg G, MGarg = subst MGin
	  )
	  \/
	  (exists p, exists T, exists Targ,
	    isArg Targ T /\
	    G |-> p / T /\
	    term MGarg = term Targ
	  )).
    apply subterm_wf.
    clear M; intros M IH G MGarg MG MGargMG.
    destruct (term_case M) as [[[Mvar | Mfun] | Mabs] | Mapp].
     (* variable *)
    destruct (var_subst MG Mvar) as [[T [p GpT MGterm]] | MGvar].
    right; exists p; exists T.
    destruct (eq_term_arg_aux (subst MG) MGarg T)
     as [Targ [TargT TargMGarg]]; trivial.
    exists Targ; split; trivial.
    split; auto.
    assert (forall W, isVar W -> isApp W -> False).
    intro W; term_inv W.
    exfalso.
    apply H with (subst MG).
    term_inv M.
    apply var_is_var with x; rewrite MGvar; trivial.
    apply appArg_app with MGarg; trivial.
     (* function symbol *)
    assert (forall W, isFunS W -> isApp W -> False).
    intro W; term_inv W.
    exfalso.
    apply H with (subst MG); trivial.
    apply funS_subst_funS; trivial.
    apply appArg_app with MGarg; trivial.
     (* abstraction *)
    assert (forall W, isApp W -> isAbs W -> False).
    intro W; term_inv W.
    exfalso.
    apply H with (subst MG); trivial.
    apply appArg_app with MGarg; trivial.
    apply abs_subst_abs; trivial.
     (* application *)
    destruct (app_subst Mapp MG).
    destruct (appArg_inv (subst MG) MGarg (app_subst_app Mapp MG)); trivial.
    destruct (IH (appBodyL Mapp) (appBodyL_subterm M Mapp) G MGarg
      (subst_appL_c Mapp MG)) as 
      [[Marg [MargML [MGin MGargMGin]]] | 
       [p [T [Targ [TargT [GpT MGarg_term]]]]]].
    rewrite <- H; trivial.
    left; exists Marg; split.
    apply appArg_left with Mapp; trivial.
    exists MGin; trivial.
    right; exists p; exists T; exists Targ; split; trivial.
    split; trivial.
    left; exists (appBodyR Mapp); split.
    apply appArg_right with Mapp; trivial.
    exists (subst_appR_c Mapp MG).
    rewrite <- H0; trivial.
  Qed.

  Lemma singleton_subst_activeEnv_noSubst_aux : forall M T i
    (MG: correct_subst M (copy i None ++ Some T :: nil)),  
    activeEnv M |= i :! -> activeEnv M = activeEnv (subst MG).

  Proof.
    destruct M as [E Pt T M]; induction M; intros.
     (* variable *)
    simpl.
    assert (MGterm: term (subst MG) = %x).
    autorewrite with terms using unfold presubst; simpl.
    destruct (lt_eq_lt_dec x i) as [[x_i | x_i] | x_i].
    rewrite nth_app_left; autorewrite with datatypes using trivial.
    exfalso; apply (@varD_UD_absurd (copy i None ++ A [#] EmptyEnv) x A).
    unfold VarD, EmptyEnv, decl.
    rewrite x_i; apply nth_after_copy.
    simpl in H.
    rewrite x_i; rewrite x_i in H; trivial.
    rewrite nth_app_right; autorewrite with datatypes using (try lia).
    cut (x - i > 0).
    destruct (x - i).
    intros; lia.
    destruct n; trivial.
    lia.
    rewrite (activeEnv_var (subst MG) MGterm).
    autorewrite with terms; trivial.
     (* function symbol *)
    rewrite activeEnv_funS; simpl; trivial.
    rewrite activeEnv_funS; trivial.
    apply funS_is_funS with f.
    change (^f) with (term (buildT (TFun E f))).
    apply funS_presubst; simpl; trivial.
     (* abstraction *)
    set (MG_abs := abs_subst_abs (M := buildT (TAbs M)) I MG).
    assert (eqin: activeEnv (buildT M) = activeEnv (absBody MG_abs)).
    destruct (abs_subst (M:=buildT (TAbs M)) I MG).
    unfold MG_abs; rewrite H1.
    assert (MG': correct_subst (buildT M) (copy (S i) None ++ {x/lift T 1})).
    set (w := subst_abs_c (M:=buildT (TAbs M)) I MG).
    simpl in w.
    rewrite lift_subst_app in w.
    rewrite lift_empty_subst in w; trivial.
    replace (subst (subst_abs_c (M:=buildT (TAbs M)) I MG)) with (subst MG').
    apply IHM.
    apply varUD_tail_rev; trivial.
    apply term_eq.
    rewrite !subst_env, !lift_subst_app, !lift_empty_subst.
    autorewrite with terms datatypes using simpl; trivial.
    autorewrite with datatypes terms.
    rewrite lift_subst_app.
    autorewrite with datatypes terms using simpl; trivial.
    rewrite (activeEnv_abs (buildT (TAbs M)) I).
    rewrite (activeEnv_abs (subst MG) MG_abs).
    rewrite <- eqin; trivial.
     (* application *)
    rewrite (activeEnv_app (buildT (TApp M1 M2)) I).
    rewrite (activeEnv_app (subst MG)
                           (app_subst_app (M:=buildT (TApp M1 M2)) I MG)).
    destruct (app_subst (M := buildT (TApp M1 M2)) I MG).
    rewrite H0; rewrite H1.
    unfold appBodyL; cbv beta.
    unfold appBodyR; cbv beta.    
    rewrite (@activeEnv_app (buildT (TApp M1 M2)) I) in H.
    rewrite (IHM1 T i (subst_appL_c (M:=buildT (TApp M1 M2)) I MG)).
    rewrite (IHM2 T i (subst_appR_c (M:=buildT (TApp M1 M2)) I MG)); trivial.
    apply env_sumn_rn with (activeEnv (buildT M1)); trivial.
    apply env_sumn_ln with (activeEnv (buildT M2)); trivial.
  Qed.

  Lemma singleton_subst_activeEnv_noSubst M G T (MG: correct_subst M G) :  
    activeEnv M |= 0 :! -> isSingletonSubst T G ->
    activeEnv M = activeEnv (subst MG).

  Proof.
    intros.
    set (MT := singleton_correct_single MG H0).
    rewrite <- (singleton_subst MT MG H0).
    change {x/T} with (copy 0 None ++ {x/T}) in MT.
    apply (singleton_subst_activeEnv_noSubst_aux T MT); trivial.
  Qed.

  Lemma singleton_subst_term_noSubst_aux :
    forall M T i (MG: correct_subst M (copy i None ++ {x/T})),
      activeEnv M |= i :! -> term M = term (subst MG).

  Proof.
    destruct M as [E Pt T M]; induction M; intros;
      autorewrite with terms using unfold presubst; simpl.
     (* variable *)
    destruct (lt_eq_lt_dec i x) as [[i_x | i_x] | i_x].
    rewrite nth_app_right; autorewrite with datatypes using trivial; try lia.
    assert (x - i > 0).
    lia.
    destruct (x - i).
    lia.
    destruct n; simpl; trivial.
    exfalso; apply varD_UD_absurd with 
      (activeEnv (buildT (TVar v))) x A.
    apply activeEnv_var_decl; trivial.
    rewrite <- i_x; trivial.
    rewrite nth_app_left; autorewrite with datatypes using trivial.
     (* function symbol *)
    trivial.
     (* abstraction *)
    set (sc := subst_abs_c (M:=buildT (TAbs M)) I MG).
    simpl in sc.
    replace (None :: lift_subst (copy i None ++ {x/T}) 1) with
      (copy (S i) None ++ {x/lift T 1}) in sc.
    rewrite subst_lift_subst.
    replace (lift_subst (None :: copy i None ++ {x/T}) 1) with
      (copy (S i) None ++ {x/lift T 1}).
    set (w := IHM (lift T 1) (S i) sc).
    rewrite subst_term in w.
    change Pt with (term (buildT M)).
    rewrite <- w; clear w; trivial.
    rewrite (@activeEnv_abs (buildT (TAbs M)) I) in H.
    change (absBody (M:=buildT (TAbs M)) I) with (buildT M) in H.
    destruct (activeEnv (buildT M)); try_solve.
    simpl; rewrite lift_subst_app; rewrite lift_empty_subst; trivial.
    simpl; rewrite lift_subst_app; rewrite lift_empty_subst; trivial.
     (* application *)
    change PtL with (term (buildT M1)).
    change PtR with (term (buildT M2)).
    set (w := IHM1 T i (subst_appL_c (M:=buildT (TApp M1 M2)) I MG)).
    rewrite subst_term in w; unfold presubst in w; rewrite <- w; clear w.
    set (w := IHM2 T i (subst_appR_c (M:=buildT (TApp M1 M2)) I MG)).
    rewrite subst_term in w; unfold presubst in w; rewrite <- w; trivial.
    rewrite (activeEnv_app (buildT (TApp M1 M2)) I) in H.
    change (buildT M2) with (appBodyR (M:=buildT (TApp M1 M2)) I).
    eapply env_sumn_rn; eexact H.
    rewrite (activeEnv_app (buildT (TApp M1 M2)) I) in H.
    change (buildT M1) with (appBodyL (M:=buildT (TApp M1 M2)) I).
    eapply env_sumn_ln; eexact H.
  Qed.

  Lemma singleton_subst_term_noSubst : forall M G T (MG: correct_subst M G),
    isSingletonSubst T G -> activeEnv M |= 0 :! -> term M = term (subst MG).

  Proof.
    intros.
    set (MT := singleton_correct_single MG H).
    rewrite <- (singleton_subst MT MG); trivial.
    apply (@singleton_subst_term_noSubst_aux M T 0); trivial.
  Qed.

  Lemma singleton_subst_active_aux : forall El Er El' Er' E i,
    (forall j, j <> i -> env_comp_on E El j) ->
    (forall j, j <> i -> env_comp_on E Er j) ->
    (forall j A, j <> i -> (El |= j := A <-> El' |= j := A)) ->
    (forall j A, j <> i -> (Er |= j := A <-> Er' |= j := A)) ->
    El' [<->] Er' -> El |= i :! -> Er |= i :! -> 
    El [+] E [+] Er
       [=] (initialSeg (El' [+] Er') i ++ None :: finalSeg (El' [+] Er') (S i))
           [+] E.

  Proof.
    intros.
    apply env_eq_def; intros j A.
    destruct (eq_nat_dec i j).
    rewrite <- e.
    split; intro D.
    destruct (env_sum_varDecl (El[+]E) Er D) as [[D' _] | D'].
    destruct (env_sum_varDecl El E D') as [[D'' _] | D''].
    exfalso; apply varD_UD_absurd with El i A; trivial.
    apply env_sum_ry; trivial.
    exfalso; apply varD_UD_absurd with Er i A; trivial.
    apply env_sum_ly_rn; trivial.
    apply env_sum_ry.    
    destruct (env_sum_varDecl (initialSeg (El'[+]Er') i ++ None :: 
      finalSeg (El'[+]Er') (S i)) E D) as [[D' _] | D']; trivial.
    exfalso; apply (varD_UD_absurd D').
    apply varUD_hole.

    assert (j <> i); [lia | idtac].
    split; intro D.
    destruct (env_sum_varDecl (El[+]E) Er D) as [[D' Dn] | D'].
    destruct (env_sum_varDecl El E D') as [[D'' Dn'] | D''].
    apply env_sum_ly_rn; trivial.
    apply varD_hole; trivial.
    apply env_sum_ly; trivial.
    apply (proj1 (H1 j A H6)); trivial.
    apply env_sum_ry; trivial.
    destruct (isVarDecl_dec E j) as [[B Ej] | En].
    apply env_sum_ry.
    rewrite <- (H0 j H6 B); trivial.    
    apply env_sum_ly.
    intros B C D1 D2.
    exfalso; apply varD_UD_absurd with E j C; trivial.
    apply varD_hole; trivial.
    apply env_sum_ry.
    apply (proj1 (H2 j A H6)); trivial.
    destruct (env_sum_varDecl (initialSeg (El'[+]Er') i ++ None :: 
      finalSeg (El'[+]Er') (S i)) E D) as [[D' _] | D'].
    set (El'Er' := env_hole_subset (El'[+]Er') i D').
    destruct (env_sum_varDecl El' Er' El'Er') as [[D'' Dn] | D''].
    apply env_sum_ly.
    intros B C D1 D2.
    destruct (env_sum_varDecl El E D1) as [[D1l _] | D1r].
    apply (H3 j B C). apply H1; hyp. apply H2; hyp.
    apply (H0 j H6); trivial.
    apply env_sum_ly.
    apply env_comp_on_sym.
    apply H; trivial.    
    apply (proj2 (H1 j A H6)); trivial.
    apply env_sum_ry.
    apply (proj2 (H2 j A H6)); trivial.    
    destruct (isVarDecl_dec Er j) as [[B D''] | Ern].
    rewrite (H0 j H6 A B D' D'').
    apply env_sum_ry; trivial.
    apply env_sum_ly_rn; trivial.
    apply env_sum_ry; trivial.
  Qed.

  Opaque activeEnv.

  Lemma singleton_subst_activeEnv_subst_aux :
    forall M T i A (MG: correct_subst M (copy i None ++ Some T :: nil)),
      (activeEnv M |= i := A) -> 
      activeEnv (subst MG)
      [=] (initialSeg (activeEnv M) i ++ None :: finalSeg (activeEnv M) (S i))
          [+] activeEnv T.

  Proof.
    destruct M as [E Pt T M]; induction M; intros.

     (* variable *)
    simpl in H.
    destruct (lt_eq_lt_dec x i) as [[x_i | xi] | i_x].
    exfalso;
      apply varD_UD_absurd with (copy x None ++ A[#]EmptyEnv) i A0; trivial.
    constructor; apply nth_beyond.
    autorewrite with datatypes using simpl; try lia.
    rewrite (@activeEnv_var (buildT (TVar v)) x); trivial.
    rewrite (equiv_term_activeEnv (subst MG) T).
    simpl.
    assert (ES: envSubset (initialSeg (copy x None ++ A[#]EmptyEnv) i ++
      None :: finalSeg (copy x None ++ A[#]EmptyEnv) (S i)) (activeEnv T)).
    rewrite xi.
    apply env_eq_empty_subset.
    rewrite
      (@initialSeg_app (option SimpleType) (copy i None) (A[#]EmptyEnv) i).
    rewrite finalSeg_app_right; autorewrite with datatypes using auto.
    replace (S i - i) with 1; [idtac | lia].
    unfold finalSeg; simpl.
    rewrite initialSeg_full.
    change ((None (A:=SimpleType)) :: nil) with (copy 1 (None (A:=SimpleType))).
    rewrite <- copy_split.
    apply env_eq_empty.
    intro w.
    destruct (le_gt_dec (i + 1) w).
    left; apply nth_beyond; autorewrite with datatypes using trivial.
    right; apply nth_copy_in; trivial.
    autorewrite with datatypes using auto.
    autorewrite with datatypes using auto.
    rewrite <- (env_eq_subset_sum_l ES); auto with terms.
    autorewrite with terms.
    unfold presubst; simpl.
    rewrite xi.
    rewrite nth_app_right; autorewrite with datatypes; auto.
    replace (i - i) with 0; [idtac | lia].
    simpl; rewrite lift_0; trivial.
    apply subst_env_compat with i.
    unfold varSubstTo; apply nth_after_copy.
    exfalso;
      apply varD_UD_absurd with (copy x None ++ A[#]EmptyEnv) i A0; trivial.
    unfold VarUD; rewrite nth_app_left; autorewrite with datatypes using auto.

     (* function symbol *)
    rewrite activeEnv_funS in H; simpl; trivial.
    destruct i; try_solve.

     (* abstraction *)
    rewrite (activeEnv_abs (buildT (TAbs M)) I).
    rewrite (activeEnv_abs (subst MG) (abs_subst_abs (M:=buildT (TAbs M))I MG)).
    destruct (abs_subst (M:=buildT (TAbs M)) I MG).
    rewrite H1.
    set (IHyp := IHM (lift T 1) (S i) A0).
    replace (copy (S i) None ++ {x/lift T 1}) with 
      (None :: lift_subst (copy i None ++ {x/T}) 1) in IHyp.
    simpl.
    set (w := IHyp (subst_abs_c (M:=buildT (TAbs M)) I MG)).
    apply env_eq_trans with (tail ((initialSeg (activeEnv (buildT M)) (S i) ++
      None :: finalSeg (activeEnv (buildT M)) (S (S i)))
                                     [+] activeEnv (lift T 1))).
    apply env_eq_tail.
    apply IHyp.
    apply varD_tail_rev; trivial.
    apply env_eq_trans
      with (tail ((initialSeg (activeEnv (buildT M)) (S i) ++ None :: 
                              finalSeg (activeEnv (buildT M)) (S (S i)))
                    [+] liftedEnv 1 (activeEnv T) 0)).
    apply env_eq_tail.
    rewrite (activeEnv_lift T 1); apply env_eq_refl.
    set (envM := activeEnv (buildT M)).
    set (envT := activeEnv T).
    rewrite tail_distr_sum.
    simpl; autorewrite with datatypes using simpl.
    destruct envM; simpl.
    destruct envT; destruct i; simpl; autorewrite with datatypes;
      unfold finalSeg; simpl.
    apply env_eq_empty_none_empty.
    apply env_eq_empty_none_empty.
    destruct o; destruct envT; auto with terms.
    destruct o; destruct envT; auto with terms.
    auto with terms.
    rewrite lift_subst_app.
    rewrite lift_empty_subst; trivial.

     (* application *)
    rewrite (activeEnv_app (buildT (TApp M1 M2)) I).
    rewrite (activeEnv_app
               (subst MG) (app_subst_app (M:=buildT (TApp M1 M2)) I MG)).
    destruct (app_subst (M := buildT (TApp M1 M2)) I MG).
    simpl; rewrite (@activeEnv_app (buildT (TApp M1 M2)) I) in H.
    unfold appBodyL, appBodyR in H; cbv beta in H.
    set (AE1 := activeEnv (buildT M1)) in * .
    set (AE2 := activeEnv (buildT M2)) in * .
     (*   - assertion useful for all 3 cases *)
    assert (forall j, j <> i -> env_comp_on (env T) E j).
    clear H0; clear H1; destruct MG.
    rewrite subst_ran_single_after_empty in ran_c0.
    simpl in ran_c0.
    intros; intros C D Tj Ej.
    apply (ran_c0 j); trivial.
    apply env_sub_ly_rn; trivial.
    apply subst_dom_singleton_after_none_nodecl; lia.
    assert (forall j, j <> i -> env_comp_on (activeEnv T) AE1 j).
    intros.
    apply env_comp_on_subset with (env T) E.
    apply H2; trivial.
    apply activeEnv_subset.
    unfold AE1; change E with (env (appBodyL (M:=buildT (TApp M1 M2)) I)).
    apply activeEnv_subset.
    assert (forall j, j <> i -> env_comp_on (activeEnv T) AE2 j).
    intros.
    apply env_comp_on_subset with (env T) E.
    apply H2; trivial.
    apply activeEnv_subset.
    unfold AE2; change E with (env (appBodyR (M:=buildT (TApp M1 M2)) I)).
    apply activeEnv_subset.
    assert (activeEnv T [<->] initialSeg AE1 i ++ None :: finalSeg AE1 (S i)).
    intro p.
    destruct (eq_nat_dec p i).
    intros C D _ F.
    exfalso; apply varD_UD_absurd
        with (initialSeg AE1 i ++ None :: finalSeg AE1 (S i)) p D; trivial.
    rewrite e; apply varUD_hole.
    apply env_comp_on_subset with (activeEnv T) AE1.
    apply H3; trivial.
    apply env_subset_refl.
    apply env_hole_subset.
    assert (activeEnv T [<->] initialSeg AE2 i ++ None :: finalSeg AE2 (S i)).
    intro p.
    destruct (eq_nat_dec p i).
    intros C D _ F.
    exfalso; apply varD_UD_absurd
         with (initialSeg AE2 i ++ None :: finalSeg AE2 (S i)) p D; trivial.
    rewrite e; apply varUD_hole.
    apply env_comp_on_subset with (activeEnv T) AE2.
    apply H4; trivial.
    apply env_subset_refl.
    apply env_hole_subset.
    assert (AE1 [<->] AE2).
    unfold AE1, AE2.
    change (buildT M1) with (appBodyL (M:=buildT (TApp M1 M2)) I).
    change (buildT M2) with (appBodyR (M:=buildT (TApp M1 M2)) I).
    apply activeEnv_app_comp.
    assert (forall (j : nat) (A : SimpleType), j <> i ->
      ((initialSeg AE1 i ++ None :: finalSeg AE1 (S i)) |= j := A
      <-> AE1 |= j := A)).
    intros; split; intro.
    apply varD_hole_rev with i; [lia | trivial].
    apply varD_hole; [lia | trivial].
    assert (forall (j : nat) (A : SimpleType), j <> i ->
      ((initialSeg AE2 i ++ None :: finalSeg AE2 (S i)) |= j := A
      <-> AE2 |= j := A)).
    intros; split; intro.
    apply varD_hole_rev with i; [lia | trivial].
    apply varD_hole; [lia | trivial].

     (*   - case 1 *)
    destruct (env_sum_varDecl AE1 AE2 H) as [[MLi MRi] | MRi]. 
    rewrite H0.
    simpl;
      rewrite (IHM1 T i A0 (subst_appL_c (M:=buildT (TApp M1 M2)) I MG) MLi).
    rewrite H1.
    rewrite <- (singleton_subst_activeEnv_noSubst_aux T
      (subst_appR_c (M:=buildT (TApp M1 M2)) I MG) MRi).
    apply singleton_subst_active_aux; trivial.
    simpl; unfold AE2; split; auto.
    apply varUD_hole.

     (*   - case 2 *)
    rewrite H1.
    simpl;
      rewrite (IHM2 T i A0 (subst_appR_c (M:=buildT (TApp M1 M2)) I MG) MRi).
    rewrite H0.
    destruct (isVarDecl_dec AE1 i) as [[A1 MLi] | MLn].
    assert (A01: A1 = A0).
    apply (@activeEnv_app_comp (buildT (TApp M1 M2)) I i); trivial.
    rewrite A01 in MLi.
    simpl;
      rewrite (IHM1 T i A0 (subst_appL_c (M:=buildT (TApp M1 M2)) I MG) MLi).
    rewrite env_comp_sum_comm
      with (initialSeg AE2 i ++ None :: finalSeg AE2 (S i)) (activeEnv T).
    rewrite env_sum_assoc.
    rewrite <- env_sum_assoc with (activeEnv T) (activeEnv T) 
      (initialSeg AE2 i ++ None :: finalSeg AE2 (S i)).
    rewrite env_sum_double.
    rewrite <- env_sum_assoc.
    apply singleton_subst_active_aux; trivial.
    apply varUD_hole.
    apply varUD_hole.
    apply env_comp_sym; trivial.

     (*   - case 3 *)
    rewrite <- (singleton_subst_activeEnv_noSubst_aux T
      (subst_appL_c (M:=buildT (TApp M1 M2)) I MG) MLn).
    rewrite env_comp_sum_comm
      with (initialSeg AE2 i ++ None :: finalSeg AE2 (S i)) (activeEnv T).
    rewrite <- env_sum_assoc.
    apply singleton_subst_active_aux; trivial.
    simpl; unfold AE1; split; auto.
    apply varUD_hole.
    apply env_comp_sym; trivial.
  Qed.

  Lemma singleton_subst_activeEnv_subst : forall M G T (MG: correct_subst M G),
    isSingletonSubst T G -> (exists A, activeEnv M |= 0 := A) ->
    activeEnv (subst MG) [=] (None :: tail (activeEnv M)) [+] activeEnv T.

  Proof.
    intros.
    destruct H0 as [A M0A].
    set (MT := singleton_correct_single MG H).
    rewrite <- (singleton_subst MT MG H).
    set (w := @singleton_subst_activeEnv_subst_aux M T 0 A MT).
    change (copy 0 None ++ {x/T}) with {x/T} in w.
    apply env_eq_trans with ((initialSeg (activeEnv M) 0 ++ 
      None :: finalSeg (activeEnv M) 1) [+] activeEnv T).
    apply w; trivial.
    clear w.
    simpl; destruct (activeEnv T); rewrite finalSeg1_tail; apply env_eq_refl.
  Qed.

  Definition subst_list Ms Ns G := list_sim 
    (fun M N => exists MG: correct_subst M G, N = subst MG) Ms Ns.

  Lemma subst_list_units : forall M G (MG: correct_subst M G),
    isFunS (appHead M) -> subst_list (appUnits M) (appUnits (subst MG)) G.

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm)
      (P := fun M =>
	forall G (MG: correct_subst M G),
	  isFunS (appHead M) ->
	  subst_list (appUnits M) (appUnits (subst MG)) G).
    apply subterm_wf.
    clear M; intros M IH G MG Mhead.
    destruct (isApp_dec M) as [Mapp | Mnapp].
     (* application *)
    destruct (app_subst Mapp MG); trivial.
    rewrite (appUnits_app M Mapp).
    rewrite (appUnits_app (subst MG) (app_subst_app Mapp MG)).
    unfold subst_list; apply list_sim_app.
    rewrite H.
    apply (IH (appBodyL Mapp)).
    apply appBodyL_subterm.
    apply appHead_left; trivial.
    constructor.
    exists (subst_appR_c Mapp MG).
    destruct (app_subst Mapp MG); trivial.
    constructor.
      (* function symbol *)
    rewrite appUnits_notApp; try_solve.
    rewrite appUnits_notApp.
    constructor.
    exists MG; trivial.
    constructor.
    term_inv M.
    assert (isFunS (subst MG)).
    apply funS_subst_funS; trivial.
    term_inv (subst MG).
  Qed.

  Lemma subst_list_args : forall M G (MG: correct_subst M G),
    isFunS (appHead M) -> subst_list (appArgs M) (appArgs (subst MG)) G.

  Proof.
    intros. unfold appArgs, subst_list. apply list_sim_tail.
    apply subst_list_units; trivial.
  Qed.

  Lemma subst_list_partialFlattening : forall M Ms G (MG: correct_subst M G),
    isPartialFlattening Ms M ->
    exists Ns, isPartialFlattening Ns (subst MG) /\ subst_list Ms Ns G.

  Proof.
    intro M.
    apply well_founded_ind with (R := subterm)
      (P := fun M =>
	forall Ms G (MG: correct_subst M G),
	  isPartialFlattening Ms M ->
	  exists Ns,
	    isPartialFlattening Ns (subst MG) /\
	    subst_list Ms Ns G).
    apply subterm_wf.
    clear M; intros M IH Ms G MG MsM.
    set (Mapp := partialFlattening_app M Ms MsM).
    set (MGapp := app_subst_app Mapp MG).
    destruct (app_subst Mapp MG).
    destruct (partialFlattening_inv M Mapp Ms MsM).
     (* trivial flattening *)
    exists (appBodyL MGapp :: appBodyR MGapp :: nil).
    split.
    unfold isPartialFlattening;
      rewrite (appUnits_app (subst MG) MGapp); trivial.
    rewrite H1; constructor.
    exists (subst_appL_c Mapp MG); trivial.
    constructor.
    exists (subst_appR_c Mapp MG); trivial.
    constructor.
     (* true flattening *)
    destruct H1 as [MsL [MsLflat Ms_def]].
    destruct (IH (appBodyL Mapp) (appBodyL_subterm M Mapp) MsL G
      (subst_appL_c Mapp MG)) as [NsL [NsL_flat MsLNsL]]; trivial.
    exists (NsL ++ appBodyR MGapp :: nil).
    constructor.
    apply (partialFlattening_desc (subst MG) MGapp); trivial.
    unfold MGapp; rewrite H; trivial.
    rewrite Ms_def.
    unfold subst_list; apply list_sim_app; trivial.
    constructor.
    exists (subst_appR_c Mapp MG); trivial.
    constructor.
  Qed.

End TermsSubst.
