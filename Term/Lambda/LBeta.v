(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05


* Beta-reduction
*)

Set Implicit Arguments.

Require Import Wf_nat Relations Basics Morphisms LogicUtil.
Require LTerm LAlpha.

Module Make (Export L : LTerm.L_Struct).

  Module Export A := LAlpha.Make L.

  Inductive beta_top : relation Te :=
  | beta_top_intro : forall x u v,
    beta_top (App (Lam x u) v) (subs (single x v) u).

  Infix "->bh" := beta_top (at level 70).

  Notation beta := (clos_mon beta_top).

  Infix "->b" := (clos_mon beta_top) (at level 70).

  (** Note that, because [subs] may rename some bound variables, [->b]
  cannot be stable by substitution, syntactically. We therefore define
  beta-reduction [=>b] as the closure by alpha-equivalence of
  [->b]. *)

  Notation beta_aeq := (clos_aeq beta).

  Infix "=>b" := (clos_aeq beta) (at level 70).

  (*REMOVE? attempt to prove the commutation of [beta] and [aeq]:
  if it works, then we could simplify [clos_aeq R] to [aeq @ R].

  Lemma rename_beta : forall x y u v, rename x y u ->b v ->
    exists v', u ->b v' /\ rename y x v' ~~ v.

  Proof.
    cut (forall t v, t ->b v -> forall x y u, t = rename x y u ->
      exists v', u ->b v' /\ rename y x v' ~~ v).
    intros h x y u v r. eapply h. apply r. refl.
    induction 1; intros y z w e.
    (* top *)
    inversion H; subst.
    unfold rename in H0; destruct w; simpl in H0; try discr.
    unfold single, update, id in H0. destruct (eq_dec x0 y); discr.
    inversion H0. destruct w1; simpl in H2; try discr.
    unfold single, update, id in H2. destruct (eq_dec x0 y); discr.
    inversion H2. exists (subs (single x0 w2) w1). split.
    apply m_step. apply beta_top_intro. unfold rename. rewrite 2!subs_comp.
    apply subs_saeq. intros a ha. rewrite <- H4 in *.
    unfold comp. unfold single at 2. unfold update, id.
    destruct (eq_dec a x0); simpl.
    rewrite single_eq.
    Focus 2.
    unfold single at 1. unfold single at 3. unfold update, id.
    destruct (eq_dec a z); destruct (eq_dec a y); simpl.
    unfold single at 1. unfold update, id. destruct (eq_dec z x).

    change (App (Lam x u0) v0 = App (rename y z w1) (rename y z w2)) in H0.
    inversion H0.
  Qed.

  Lemma aeq_beta : aeq @ beta << beta @ aeq.

  Proof.
    intros t v [u [tu uv]]. revert u v uv t tu. induction 1; intros t tu.
    (* top *)
    inversion H; subst. inv_aeq tu; subst. inv_aeq i0; subst.
    exists (subs (single x0 u1) u2). split. apply m_step. apply beta_top_intro.
    rewrite j0. rewrite single_rename. 2: hyp.
    (*COQ does not accept: rewrite i1.*) apply single_aeq; auto. refl.
    (* app_l *)
    inv_aeq tu; subst. destruct (IHuv _ i0) as [u0' [h1 h2]].
    exists (App u0' u1). split. mon. rewrite h2, i1. refl.
    (* app_r *)
    inv_aeq tu; subst. destruct (IHuv _ i1) as [u1' [h1 h2]].
    exists (App u0 u1'). split. mon. rewrite h2, i0. refl.
    (* lam *)
    inv_aeq tu; subst.
    assert (k : rename x0 x u0 ~~ u).
    rewrite j0, rename2, rename_id. refl. hyp.
    destruct (IHuv _ k) as [t [h1 h2]].


    (* induction on the size of [u] *)
    intros t v [u [tu uv]]. revert u v uv t tu.
    ind_size1 u; intros a ua t tu.
    (* var *)
    inversion ua; subst. inversion H.
    (* fun *)
    inversion ua; subst. inversion H.
    (* app *)
    inv_aeq tu; subst. inversion ua; subst.
    (* top *)
    inversion H; subst. inv_aeq i0; subst. exists (subs (single x0 u1) u0).
    split. apply m_step. apply beta_top_intro.
    rewrite j0. rewrite single_rename. 2: hyp.
    (*COQ does not accept: rewrite i1.*) apply single_aeq; auto. refl.
    (* app_l *)
    destruct (hu _ H2 _ i0) as [u0' [h1 h2]].
    exists (App u0' u1). split. mon. rewrite h2, i1. refl.
    (* app_r *)
    destruct (hv _ H2 _ i1) as [u1' [h1 h2]].
    exists (App u u1'). split. mon. rewrite h2, i0. refl.
    (* lam *)
    inv_aeq tu; subst. inversion ua; subst. inversion H.
    assert (k : size u0 <= size u). rewrite j0. rewrite size_rename. refl.
    destruct (hu _ (le_refl _) _ H2 (rename x0 x u0)) as [t [h1 h2]].
    rewrite j0, rename2, rename_id. refl. hyp.

    assert (k : rename x0 x u0 ~~ u).
    destruct (IHuv _ k) as [t [h1 h2]].

  Qed.*)

(****************************************************************************)
(** Beta-reduction is stable by substitution. *)

  Lemma subs_beta_aeq : Proper (Logic.eq ==> beta_aeq ==> beta_aeq) subs.

  Proof.
    intros s s' ss' u v uv. subst s'. revert u v uv s.
    (* We proceed by induction on the size of [u]. *)
    intro u; pattern u; apply (induction_ltof1 _ size); clear u.
    intros u IH v uv s. inversion uv; subst. rewrite H, H0.
    (* We now proceed by case on [->b]. *)
    inversion H1; subst.
    (* top *)
    inversion H2; subst; simpl. set (x':=var x u0 s).
    eapply clos_aeq_intro with
      (v':=subs (single x' (subs s v0)) (subs (update x (Var x') s) u0)).
    refl. do 2 rewrite subs_comp. apply subs_saeq. intros z hz. unfold comp.
    unfold single at 1. unfold update. eq_dec z x; simpl.
    rewrite single_eq. refl.
    unfold x'. rewrite single_var. refl. hyp. auto.
    apply m_step. apply beta_top_intro.
    (* app_l *)
    simpl. mon. apply IH. unfold ltof. rewrite H. max. apply incl_clos_aeq. hyp.
    (* app_r *)
    simpl. mon. apply IH. unfold ltof. rewrite H. max. apply incl_clos_aeq. hyp.
    (* lam *)
    (* We rename [x] into some variable [k] not in [xs] so that [subs s]
       makes no alpha-conversion. *)
    set (xs := union (union (fv u0) (fvcodom (remove x (fv u0)) s))
                     (union (fv u'0) (fvcodom (remove x (fv u'0)) s))).
    set (k := var_notin xs).
    gen (var_notin_ok xs). fold k. unfold xs. set_iff. intro hk.
    rewrite (aeq_alpha k). 2: tauto. rewrite (@aeq_alpha x _ k). 2: tauto.
    rewrite subs_lam_no_alpha. 2: rewrite remove_fv_rename; tauto.
    rewrite subs_lam_no_alpha. 2: rewrite remove_fv_rename; tauto.
    mon. apply IH. unfold ltof. rewrite size_rename, H. simpl. omega.
    apply IH. unfold ltof. rewrite H. simpl. omega.
    apply incl_clos_aeq. hyp.
  Qed.

  Instance rename_beta_aeq :
    Proper (Logic.eq ==> Logic.eq ==> beta_aeq ==> beta_aeq) rename.

  Proof.
    intros x x' xx' y y' yy' u u' uu'. subst x' y'. apply subs_beta_aeq; auto.
  Qed.

(****************************************************************************)
(** Inversion lemmas for beta-reduction. *)

  Lemma var_beta_aeq_l : forall x u, ~Var x =>b u.

  Proof.
    intros x u b. inversion b; subst. inv_aeq H; subst. inversion H1; subst.
    inversion H.
  Qed.

  Lemma fun_beta_aeq_l : forall f u, ~Fun f =>b u.

  Proof.
    intros x u b. inversion b; subst. inv_aeq H; subst. inversion H1; subst.
    inversion H.
  Qed.

  Lemma lam_beta_aeq_l : forall x u v,
    Lam x u =>b v -> exists y, exists w, v = Lam y w /\ u =>b rename y x w.

  Proof.
    intros x u v b. inversion b; subst.
    destruct (lam_aeq_l H) as [y [w [i1 [i2 i3]]]]; subst.
    inversion H1; subst. inversion H2; subst.
    destruct (lam_aeq_r H0) as [z [a [j1 [j2 j3]]]]; subst.
    exists z. exists a. split. refl. rewrite j2, rename2. 2: hyp.
    assert (h : u ~~ rename y x w). rewrite i2, rename2, rename_id. refl. hyp.
    rewrite h. apply rename_beta_aeq. refl. refl. apply incl_clos_aeq. hyp.
  Qed.

  Lemma app_beta_aeq_l : forall u v w, App u v =>b w ->
    (exists u', w ~~ App u' v /\ u =>b u')
    \/ (exists v', w ~~ App u v' /\ v =>b v')
    \/ (exists x, exists a, u = Lam x a /\ w ~~ subs (single x v) a).

  Proof.
    intros u v w b. inversion b; subst.
    destruct (app_aeq_l H) as [u'1 [v'1 [e [uu'1 vv'1]]]]; subst.
    inversion H1; subst.
    (* top *)
    inversion H2; subst.
    right. right. destruct (lam_aeq_l uu'1) as [y [u0' [i1 [i2 i3]]]]; subst.
    exists y. exists u0'. split. refl. rewrite H0, i2. unfold rename.
    rewrite subs_comp. apply subs_saeq. intros z hz.
    unfold comp, single, update at -2. eq_dec z x; simpl.
    rewrite update_eq. hyp.
    unfold update. eq_dec z y. destruct i3; subst; tauto. refl.
    (* app_l *)
    left. destruct (app_aeq_r H0) as [c [d [i1 [i2 i3]]]]. subst.
    exists u'. split. rewrite <- vv'1. hyp.
    rewrite <- uu'1. apply incl_clos_aeq. hyp.
    (* app_r *)
    right. left. destruct (app_aeq_r H0) as [c [d [i1 [i2 i3]]]]. subst.
    exists v'0. split. rewrite <- uu'1. hyp.
    rewrite <- vv'1. apply incl_clos_aeq. hyp.
  Qed.

(****************************************************************************)
(** Inversion tactic for beta-reduction. *)

  Ltac inv_beta_aeq h :=
    match type of h with
      | Var _ =>b _ => apply var_beta_aeq_l in h; tauto
      | Fun _ =>b _ => apply fun_beta_aeq_l in h; tauto
      | App _ _ =>b _ => let x := fresh "x" in let u := fresh "u" in
        let h1 := fresh "h" in let h2 := fresh "h" in
          destruct (app_beta_aeq_l h)
            as [[u [h1 h2]]|[[u [h1 h2]]|[x [u [h1 h2]]]]]
      | Lam _ _ =>b _ => let x := fresh "x" in let u := fresh "u" in
        let h1 := fresh "h" in let h2 := fresh "h" in
          destruct (lam_beta_aeq_l h) as [x [u [h1 h2]]]
      | _ =>b _ => let u := fresh "u" in let v := fresh "v" in
        let h1 := fresh "h" in let h2 := fresh "h" in let h3 := fresh "h" in
          destruct h as [u [h1 [v [h2 h3]]]]
    end.

(****************************************************************************)
(** Beta-reduction do not create free variables. *)

  Instance fv_beta_top : Proper (beta_top --> Subset) fv.

  Proof.
    intros u u' u'u. unfold flip in u'u. inversion u'u; subst.
    rewrite fv_single. case_eq (mem x (fv u0)); intro hx. refl.
    intros y hy. simpl. set_iff. rewrite <- not_mem_iff in hx.
    eq_dec x y. subst. tauto. left. auto.
  Qed.

  Instance fv_beta : Proper (beta --> Subset) fv.

  Proof.
    induction 1; simpl; try (intro y; set_iff; intuition; fail).
    apply fv_beta_top. hyp.
  Qed.

  Instance fv_beta_aeq : Proper (beta_aeq --> Subset) fv.

  Proof.
    intros u v b. inversion b; subst. rewrite H, H0. apply fv_beta. hyp.
  Qed.

  Lemma beta_aeq_notin_fv_lam : forall x y u v,
    Lam x u =>b Lam y v -> y=x \/ ~In x (fv v).

  Proof.
    intros x y u v r. eq_dec y x. auto. right. intro i.
    absurd (In x (fv (Lam x u))). simpl. set_iff. tauto.
    rewrite r. simpl. set_iff. auto.
  Qed.

(****************************************************************************)
(** If [apps u us] beta-reduces to [t] and [u] is not an abstraction,
then [t] is of the form [apps v vs] with [Vcons u us ==>b Vcons v vs]. *)

  Require Import VecUtil VecOrd.

  Infix "-->b" := (Vgt_prod beta) (at level 70).
  Infix "==>b" := (vaeq_prod beta) (at level 70).

  Lemma beta_apps_no_lam : forall n (us : Tes n) u t,
    not_lam u -> apps u us ->b t ->
    exists v vs, t = apps v vs /\ Vcons u us -->b Vcons v vs.

  Proof.
    induction us; simpl; intros u t hu b.
    (* nil *)
    exists t. exists Vnil. intuition. apply left_sym. hyp.
    (* cons *)
    assert (k : not_lam (App u h)). discr.
    destruct (IHus _ _ k b) as [v [vs [h1 h2]]]. inversion h2; subst.
    inversion H0; subst.
    inversion H; subst. exfalso. eapply hu. refl.
    exists u'. exists (Vcons h vs). intuition. apply left_sym. hyp.
    exists u. exists (Vcons v' vs). intuition. apply right_sym. apply left_sym.
    hyp.
    exists u. exists (Vcons h vs). intuition. do 2 apply right_sym. hyp.
  Qed.

  Arguments beta_apps_no_lam [n us u t] _ _.

  Lemma beta_aeq_apps_no_lam : forall n (us : Tes n) u t,
    not_lam u -> apps u us =>b t ->
    exists v vs, t = apps v vs /\ vaeq_prod beta (Vcons u us) (Vcons v vs).

  Proof.
    intros n us u t hu b. inversion b; subst.
    destruct (apps_aeq_l H) as [v [vs [h1 [h2 h3]]]]; subst.
    rewrite <- h2 in hu.
    destruct (beta_apps_no_lam hu H1) as [w [ws [i1 i2]]]; subst.
    destruct (apps_aeq_r H0) as [c [cs [j1 [j2 j3]]]]; subst.
    exists c. exists cs. intuition. symmetry in h2, h3, j2, j3.
    exists (Vcons v vs). split. fo. exists (Vcons w ws). intuition. fo.
  Qed.

  Arguments beta_aeq_apps_no_lam [n us u t] _ _.

(****************************************************************************)
(** [apps (Fun f) us] is strongly normalizing wrt beta-reduction if
every element of [us] is strongly normalizing wrt beta-reduction. *)

  Require Import SN.

  Lemma sn_beta_apps_fun : forall f n (us : Tes n),
    Vforall (SN beta_aeq) us -> SN beta_aeq (apps (Fun f) us).

  Proof.
    intros f n us h. cut (SN (@vaeq_prod beta n) us).
    2: apply sn_vaeq_prod; hyp.
    clear h. revert us. induction 1. apply SN_intro. intros v r.
    assert (k : not_lam (Fun f)). discr.
    destruct (beta_aeq_apps_no_lam k r) as [u [y [h1 h2]]]; subst.
    rewrite vaeq_prod_cons in h2. destruct h2 as [[i1 i2]|[i1 i2]].
    inversion i1; subst. inv_aeq H1; subst. inversion H3; subst. inversion H1.
    inv_aeq i1; subst. apply H0. hyp.
  Qed.

End Make.
