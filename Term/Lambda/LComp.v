(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05


* Tait and Girard computability
*)

Set Implicit Arguments.

Require Import Morphisms Basics RelUtil VecUtil VecOrd LogicUtil SN SetUtil.
Require Export LBeta.

(****************************************************************************)
(** ** Computability predicates. *)

Section cp.

  Variables F X : Type.

  Notation Te := (@Te F X).

  Variables (aeq R_aeq : relation Te) (neutral : set Te).

  Infix "=>R" := R_aeq (at level 70).

  (** A computability predicate must be compatible with alpha-equivalence. *)

  Notation cp_aeq := (Proper (aeq ==> impl)) (only parsing).

  (** A computability predicate contains strongly normalizing terms. *)

  Definition cp_sn (P : set Te) := forall u, P u -> SN R_aeq u.

  (** A computability predicate is stable by reduction. *)

  Definition cp_red (P : set Te) := Proper (R_aeq ==> impl) P.

  (** A computability predicate containing all the reducts of a
    neutral term [u] contains [u] too. *)

  Definition cp_neutral (P : set Te) :=
    forall u, neutral u -> (forall v, u =>R v -> P v) -> P u.

  (** A computability predicate is a predicate satisfying the four
     conditions above. *)

  Class cp P := {
    cp1 : cp_aeq P;
    cp2 : cp_sn P;
    cp3 : cp_red P;
    cp4 : cp_neutral P }.

  (** Interpretation of arrow types. *)

  Definition arr (P Q : set Te) : set Te :=
    fun u => forall v, P v -> Q (App u v).

End cp.

(****************************************************************************)
(** * Structure on which we will define computability predicates. *)

Module Type CP_Struct.

  Declare Module Export L : L_Struct.

  Notation subs := (@subs F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation aeq := (@aeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation clos_aeq := (@clos_aeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation vaeq := (@vaeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation vaeq_prod :=
    (@vaeq_prod F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation beta_top := (@beta_top F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).

  Infix "->bh" := beta_top (at level 70).

  (** We assume given a relation [->Rh] and a predicate [neutral]. *)

  Parameter Rh : relation Te.
  Infix "->Rh" := Rh (at level 70).

  Parameter neutral : set Te.

  (** We then denote by [->R] the monotone closure of [->Rh] and by
     [=>R] the closure by alpha-equivalence of [->R]. *)

  Notation R := (clos_mon Rh).
  Infix "->R" := (clos_mon Rh) (at level 70).

  Notation R_aeq := (clos_aeq R).
  Infix "=>R" := (clos_aeq R) (at level 70).

  Infix "==>R" := (vaeq_prod R) (at level 70).

  (** Properties not involving reduction. *)

  Declare Instance neutral_aeq : Proper (aeq ==> impl) neutral.
  Parameter neutral_var : forall x, neutral (Var x).
  Parameter neutral_app : forall u v, neutral u -> neutral (App u v).
  Parameter not_neutral_lam : forall x u, ~neutral (Lam x u).
  Parameter neutral_beta : forall x u v, neutral (App (Lam x u) v).

  (** Properties involving reduction. *)

  Declare Instance subs_R_aeq : Proper (Logic.eq ==> R_aeq ==> R_aeq) subs.
  Declare Instance fv_Rh : Proper (Rh --> Subset) fv.
  Parameter not_Rh_var : forall x u, ~ Var x ->Rh u.
  Parameter not_Rh_lam : forall x u w, ~ Lam x u ->Rh w.
    (* FIXME: We exclude eta-reduction here. *)
  Parameter Rh_bh : forall x u v w,
    App (Lam x u) v ->Rh w -> App (Lam x u) v ->bh w.
  Parameter not_Rh_app_neutral : forall u v w, neutral u -> ~ App u v ->Rh w.

  (** Some notations. *)

  Notation cp_aeq := (Proper (aeq ==> impl)) (only parsing).
  Notation cp_sn := (@cp_sn F X R_aeq).
  Notation cp_red := (@cp_red F X R_aeq).
  Notation cp_neutral := (@cp_neutral F X R_aeq neutral).
  Notation cp := (@cp F X aeq R_aeq neutral).

End CP_Struct.

(****************************************************************************)
(** * CP structure for beta-reduction alone. *)

Module CP_beta (Import L : L_Struct) <: CP_Struct.

  Module L := L.

  Module Import B := LBeta.Make L.

  Definition Rh := beta_top.
  Infix "->Rh" := Rh (at level 70).

  Notation R := (clos_mon Rh).
  Infix "->R" := (clos_mon Rh) (at level 70).

  Notation R_aeq := (clos_aeq R).
  Infix "=>R" := (clos_aeq R) (at level 70).

  (** A term is neutral if it is not a [Lam]. *)

  Definition neutral (u : Te) :=
    match u with
      | Def.Lam _ _ => False
      | _ => True
    end.

  (** CP structure properties not involving reduction. *)

  Instance neutral_aeq : Proper (aeq ==> impl) neutral.

  Proof. intros u u' uu' hu. destruct u; inv_aeq uu'; subst; simpl; auto. Qed.

  Lemma neutral_var : forall x, neutral (Var x).

  Proof. fo. Qed.

  Lemma neutral_app : forall u v, neutral u -> neutral (App u v).

  Proof. fo. Qed.

  Lemma not_neutral_lam : forall x u, ~neutral (Lam x u).

  Proof. fo. Qed.

  Lemma neutral_beta : forall x u v, neutral (App (Lam x u) v).

  Proof. fo. Qed.

  (** CP structure properties involving reduction. *)

  Instance subs_R_aeq : Proper (Logic.eq ==> R_aeq ==> R_aeq) subs.

  Proof. exact subs_beta_aeq. Qed.

  Lemma not_Rh_var : forall x u, ~ Var x ->Rh u.

  Proof. intros x u b. inversion b. Qed.

  Lemma not_Rh_lam : forall x u w, ~ Lam x u ->Rh w.

  Proof. intros x u w b. inversion b. Qed.

  Lemma Rh_bh : forall x u v w,
    App (Lam x u) v ->Rh w -> App (Lam x u) v ->bh w.

  Proof. fo. Qed.

  Lemma not_Rh_app_neutral : forall u v w, neutral u -> ~ App u v ->Rh w.

  Proof. intros u v w h r. destruct u; inversion r; auto. Qed.

  Instance fv_Rh : Proper (Rh --> Subset) fv.

  Proof. exact fv_beta_top. Qed.

  (** Some notations. *)
  (*COQ: can we avoid to repeat these notations already declared in CP_Struct?*)

  Notation cp_aeq := (Proper (aeq ==> impl)) (only parsing).
  Notation cp_sn := (@cp_sn F X R_aeq).
  Notation cp_red := (@cp_red F X R_aeq).
  Notation cp_neutral := (@cp_neutral F X R_aeq neutral).
  Notation cp := (@cp F X aeq R_aeq neutral).

End CP_beta.

(****************************************************************************)
(** * Properties of CP structures. *)

Module Make (Export CP : CP_Struct).

  Module Export B := LBeta.Make L.

  (** Variables are irreducible. *)

  Lemma not_R_var : forall x u, ~ Var x ->R u.

  Proof. intros x u r. inversion r; subst. eapply not_Rh_var. apply H. Qed.

  Lemma not_R_aeq_var : forall x u, ~ Var x =>R u.

  Proof.
    intros x u r. inversion r; subst. simpl_aeq; subst.
    eapply not_R_var. apply H1.
  Qed.

  (** [App u v] is not head-reducible if [u] is neutral. *)

  Lemma R_app_neutral : forall u v w, neutral u -> App u v ->R w ->
      (exists u', w = App u' v /\ u ->R u')
      \/ (exists v', w = App u v' /\ v ->R v').

  Proof.
    intros u v w n r. inversion r; subst.
    exfalso. eapply not_Rh_app_neutral. apply n. apply H.
    left. exists u'. auto. right. exists v'. auto.
  Qed.

  Lemma R_aeq_app_neutral : forall u v w, neutral u -> App u v =>R w ->
      (exists u', w ~~ App u' v /\ u =>R u')
      \/ (exists v', w ~~ App u v' /\ v =>R v').

  Proof.
    intros u v w n r. inversion r; subst. inv_aeq H; clear H; subst.
    rewrite <- i0 in n.
    destruct (R_app_neutral n H1) as [h|h]; destruct h as [t [a s]]; subst.
    left. exists t. rewrite <- i1, <- i0. intuition.
    apply incl_clos_aeq. hyp.
    right. exists t. rewrite <- i1, <- i0. intuition.
    apply incl_clos_aeq. hyp.
  Qed.

  (** No reduction can occur at the top of an abstraction. *)

  Lemma R_lam : forall x u w, Lam x u ->R w ->
    exists v, w = Lam x v /\ u ->R v.

  Proof.
    intros x u w r. inversion r; subst.
    apply not_Rh_lam in H. tauto. exists u'. auto.
  Qed.

  Lemma R_aeq_lam : forall x u w, Lam x u =>R w ->
    exists y v, w = Lam y v /\ u =>R rename y x v.

  Proof.
    intros x u w r. inversion r; subst. inv_aeq H; clear H; subst.
    inversion H1; subst.
    exfalso. eapply not_Rh_lam. apply H.
    inv_aeq H0; clear H0; subst. exists x1. exists u1. split. refl.
    rewrite i2, rename2. 2: hyp.
    assert (a : u ~~ rename x0 x u0).
    rewrite i0, rename2, rename_id. refl. hyp.
    rewrite a. apply subs_R_aeq. refl. apply incl_clos_aeq. hyp.
  Qed.

  (** Extension of properties from [App] to [apps]. *)

  Lemma neutral_apps : forall n (us : Tes n) u,
    neutral u -> neutral (apps u us).

  Proof.
    induction us; simpl. auto.
    intros u nu. apply IHus. apply neutral_app. hyp.
  Qed.

  Lemma neutral_apps_var : forall x n (us : Tes n), neutral (apps (Var x) us).

  Proof. intros x n us. apply neutral_apps. apply neutral_var. Qed.

  Lemma R_aeq_apps_neutral : forall n (us : Tes n) u v, neutral u ->
    apps u us =>R v -> (exists u', v ~~ apps u' us /\ u =>R u')
    \/ (exists us', v ~~ apps u us' /\ Vgt_prod R_aeq us us').

  Proof.
    induction us as [|a n us IHus]; simpl; intros u v nu r.
    left. exists v. split. refl. hyp.
    destruct (IHus _ _ (neutral_app a nu) r).
    destruct H as [w [h1 h2]].
    destruct (R_aeq_app_neutral nu h2).
    destruct H as [u' [i1 i2]]. left. exists u'.
    split. rewrite h1, i1. refl. hyp.
    destruct H as [a' [i1 i2]]. right. exists (Vcons a' us).
    split. rewrite h1, i1. refl. apply left_sym. hyp.
    destruct H as [us' [h1 h2]]. right. exists (Vcons a us'). 
    split. rewrite h1. refl. apply right_sym. hyp.
  Qed.

  (** Alpha-transitive closure of [=>R]. *)

  Infix "=>R*" := (R_aeq*) (at level 70).

  (** Extension of [R_aeq_lam] to [=>R*]. *)

  Lemma atc_lam : forall x u w, Lam x u =>R* w ->
    exists y v, w = Lam y v /\ u =>R* rename y x v.

  Proof.
    cut (forall t w, t =>R* w -> forall x u, t = Lam x u ->
      exists y v, w = Lam y v /\ u =>R* rename y x v).
    intros h x u w i.
    destruct (h _ _ i _ _ (refl_equal _)) as [y [v [h1 h2]]].
    exists y. exists v. auto.
    (* We proceed by induction on [=>R*]. *)
    induction 1; intros x' u' e; subst.
    (* step *)
    destruct (R_aeq_lam H) as [y0 [v0 [h1 h2]]].
    exists y0. exists v0. intuition. apply at_step. hyp.
    (* refl *)
    inv_aeq H; clear H; subst. exists x. exists u.
    (*COQ does not accept: rewrite j0.*)
    split. refl. rewrite i0, rename2, rename_id. refl. hyp.
    (* trans *)
    destruct (IHclos_aeq_trans1 x' u' (refl_equal _)) as [y0 [v0 [h1 h2]]].
    subst v.
    destruct (IHclos_aeq_trans2 y0 v0 (refl_equal _)) as [y1 [v1 [i1 i2]]].
    subst w.
    exists y1. exists v1. intuition. trans (rename y0 x' v0). hyp.
    eapply rename_atc in i2; auto. 2: apply subs_R_aeq.
    rewrite rename2 in i2. apply i2.
    rewrite notin_fv_lam, <- H0. simpl. set_iff. fo.
  Qed.

  (** Extension of [=>R*] to substitutions. *)

  Definition satc s s' := forall x : X, s x =>R* s' x.

  Instance satc_preorder : PreOrder satc.

  Proof.
    split.
    intros s x. refl.
    intros a b c ab bc x. trans (b x). apply ab. apply bc.
  Qed.

  Lemma subs_satc_aux : Proper (satc ==> Logic.eq ==> R_aeq*) subs.

  Proof.
    intros s s' ss' u u' uu'. subst u'. revert u s s' ss'.
    induction u; intros s s' ss'.
    apply ss'.
    refl.
    simpl. rewrite IHu1, IHu2. refl. hyp. hyp.
    set (xs := union (fv u) (union (fvcodom (remove x (fv u)) s)
      (fvcodom (remove x (fv u)) s'))).
    gen (var_notin_ok xs). set (z := var_notin xs). unfold xs. set_iff.
    intro hz. rewrite (aeq_alpha z). 2: tauto.
    do 2 (rewrite subs_lam_no_alpha; [idtac|rewrite remove_fv_rename; tauto]).
    apply Lam_atc. class. refl.
    unfold_rename. rewrite !subs_comp. apply IHu.
    intro y. unfold comp. unfold_single. unfold Def.update at 2.
    unfold Def.update at 3. eq_dec y x; simpl.
    rewrite !update_eq. refl.
    unfold_update. eq_dec y z. refl. apply ss'.
  Qed.

  Instance subs_satc : Proper (satc ==> R_aeq* ==> R_aeq*) subs.

  Proof.
    intros s s' ss' u u' uu'. revert u u' uu'. induction 1.
    (* step *)
    trans (subs s v). apply at_step. apply subs_R_aeq. refl. hyp.
    apply subs_satc_aux. hyp. refl.
    (* aeq *)
    rewrite H. apply subs_satc_aux. hyp. refl.
    (* trans *)
    trans (subs s v). rewrite uu'1. refl. hyp.
  Qed.

  (** [SN R_aeq] is compatible with [aeq]. *)

  Instance SN_R_aeq_impl : Proper (aeq ==> impl) (SN R_aeq).

  Proof.
    intros t u tu h. apply SN_intro. intros u' uu'. rewrite <- tu in uu'.
    eapply SN_inv. apply h. hyp.
  Qed.

  (** [SN R_aeq] is stable by [=>R*]. *)

  Instance SN_atc : Proper (R_aeq* ==> impl) (SN R_aeq).

  Proof.
    intros t u tu ht. revert t u tu ht. induction 1; intro ht.
    inversion ht; fo. rewrite <- H. hyp. fo.
  Qed.

  (** Restriction of [=>R] to the reducts of some term [t]. *)

  Definition R_aeq_red t u v := t =>R* u /\ u =>R v.

  Lemma WF_R_aeq_red : forall t, SN R_aeq t -> WF (R_aeq_red t).

  Proof.
    (*FIXME: We prove this lemma by using the axiom of
      dependent choice (DepChoice) and classical logic. We should try
      to find an intuitionistic proof. *)
    Require NotSN_IS.
    intros t ht. rewrite NotSN_IS.WF_notIS_eq. intros f hf.
    absurd (SN R_aeq (f 0)).
    rewrite NotSN_IS.SN_notNT_eq. intro h. apply h. exists f. intuition.
    intro i. destruct (hf i). hyp.
    destruct (hf 0). rewrite H in ht. hyp.
  Qed.

  (** The subterms of a strongly normalizing term are strongly
     normalizing. *)

  Lemma sn_app_l : forall u v, SN R_aeq (App u v) -> SN R_aeq u.

  Proof.
    cut (forall w, SN R_aeq w -> forall u v, w = App u v -> SN R_aeq u).
    intros h u v i. eapply h. apply i. refl.
    induction 1. intros u v e. subst. apply SN_intro. intros u' uu'.
    eapply H0. apply mon_app_l. class. apply uu'.
    refl. refl.
  Qed.

  Lemma sn_lam : forall x u, SN R_aeq u -> SN R_aeq (Lam x u).

  Proof.
    intro x. induction 1. rename x0 into u. apply SN_intro. intros t r.
    destruct (R_aeq_lam r) as [y [v [h1 h2]]]; subst.
    destruct (fv_R_notin_fv_lam _ r).
    subst. apply H0. rewrite rename_id in h2. hyp.
    rewrite (@aeq_alpha y v x). 2: hyp. apply H0. hyp.
  Qed.

(****************************************************************************)
(** ** Properties of computability predicates. *)

  (** We check that computability properties are invariant wrt [=]. *)

  Instance cp_aeq_equiv : Proper (equiv ==> impl) cp_aeq.

  Proof. intros P Q PQ hP t u tu Qt. rewrite <- PQ in *. fo. Qed.

  Instance cp_sn_equiv : Proper (equiv ==> impl) cp_sn.

  Proof. fo. Qed.

  Instance cp_red_equiv : Proper (equiv ==> impl) cp_red.

  Proof. intros P Q PQ hP t u tu Qt. rewrite <- PQ in *. fo. Qed.

  Instance cp_neutral_equiv : Proper (equiv ==> impl) cp_neutral.

  Proof. fo. Qed.

  Instance cp_equiv : Proper (equiv ==> impl) cp.

  Proof. intros P Q PQ [P1 P2 P3 P4]. rewrite PQ in *. fo. Qed.

  (** A computability predicate is stable by [=>R*] if it satisfies
     [cp_aeq] and [cp_red]. *)

  Instance cp_atc : forall P, cp_aeq P -> cp_red P ->
    Proper (R_aeq* ==> impl) P.

  Proof.
    intros P P1 P3 u u' uu' hu. revert u u' uu' hu. induction 1.
    fo. rewrite H. auto. fo.
  Qed.

  (** Computability of a beta-redex. *)

  Lemma cp_beta : forall P, cp_aeq P -> cp_red P -> cp_neutral P ->
    forall x u v, SN R_aeq (Lam x u) -> SN R_aeq v ->
      P (subs (single x v) u) -> P (App (Lam x u) v).

  Proof.
    intros P P1 P3 P4 x0 u0 v0 h0 h1 h.
    set (gt_red x0 u0 v0 :=
      Rof (symprod (R_aeq_red (Lam x0 u0)) (R_aeq_red v0))
      (fun a => match a with ((x,u),v) => (Lam x u, v) end)).
    (* We proceed by well-founded induction on [((x,u),v)] with
       [gt_red] as well-founded relation ([Lam x0 u0] and [v0] are [SN]). *)
    set (Q := fun a => match a with ((x,u),v) =>
      Lam x0 u0 =>R* Lam x u -> v0 =>R* v -> P (App (Lam x u) v) end).
    cut (Q ((x0,u0),v0)). intro q. apply q; refl.
    cut (SN (gt_red x0 u0 v0) (x0,u0,v0)).
    Focus 2. apply WF_inverse. apply WF_symprod; apply WF_R_aeq_red; hyp.
    apply SN_ind with (R:=gt_red x0 u0 v0). intros [[x u] v] i IH i1 i2.
    destruct (atc_lam i1) as [x1 [u1 [j1 j2]]]. inversion j1; subst x1 u1.
    clear j1. apply P4. apply neutral_beta. intros c r. inversion r; subst.
    inv_aeq H; clear H; subst. inv_aeq i3; subst. inversion H1; subst.
    (* top *)
    apply Rh_bh in H. inversion H; subst. rewrite H0, i5, single_rename.
    2: hyp. eapply cp_atc; auto. 2: apply h.
    trans (subs (single x0 u2) (rename x x0 u)). apply subs_satc. 2: hyp.
    intro z. unfold_single_update. eq_dec z x0.
    rewrite i4. hyp. refl.
    rewrite single_rename. refl.
    rewrite notin_fv_lam, <- i1. simpl. set_iff. fo.
    (* app_l *)
    destruct (R_lam H4) as [t [k1 k2]]; subst. rewrite H0, i4.
    assert (a : Lam x u =>R Lam x1 t).
    apply (incl_clos_aeq R) in k2. destruct i6.
    subst. rewrite rename_id in i5. rewrite <- i5. mon.
    rewrite (aeq_alpha x1), <- i5. 2: hyp. mon.
    cut (Q ((x1,t),v)). intro q. apply q. 2: hyp.
    trans (Lam x u). hyp. apply at_step. hyp.
    apply IH. unfold gt_red, Rof. apply left_sym. split; hyp.
    (* app_r *)
    rewrite H0, i3.
    assert (a : v =>R v'0). rewrite <- i4. apply incl_clos_aeq. hyp.
    cut (Q ((x,u),v'0)). intro q. apply q. hyp.
    trans v. hyp. rewrite <- i4. apply at_step. apply incl_clos_aeq. hyp.
    apply IH. unfold gt_red, Rof. apply right_sym. split; hyp.
  Qed.

  (** [SN R_aeq] is a computability predicate. *)

  Lemma cp_sn_SN : cp_sn (SN R_aeq).

  Proof. fo. Qed.

  Lemma cp_red_SN : cp_red (SN R_aeq).

  Proof. intros u u' b h. inversion h. apply H. hyp. Qed.

  Lemma cp_neutral_SN : cp_neutral (SN R_aeq).

  Proof. intros u n h. apply SN_intro. hyp. Qed.

  Lemma cp_SN : cp (SN R_aeq).

  Proof.
    constructor. apply SN_R_aeq_impl. apply cp_sn_SN. apply cp_red_SN.
    apply cp_neutral_SN.
  Qed.

  (** A computability predicate contains every strongly normalizing term
     of the form [x t1 .. tn]. *)

  Lemma cp_var_app_sn : forall P, cp_aeq P -> cp_neutral P ->
    forall x n (us : Tes n), Vforall (SN R_aeq) us -> P (apps (Var x) us).

  Proof.
    intros P p1 p4 x n us h.
    cut (SN (Vgt_prod R_aeq) us). clear h. revert us. induction 1.
    rename x0 into us. apply p4. apply neutral_apps_var. intros v r.
    destruct (R_aeq_apps_neutral _ (neutral_var x) r).
    destruct H1 as [x' [h1 h2]]. apply not_R_aeq_var in h2. tauto.
    destruct H1 as [us' [h1 h2]]. rewrite h1. apply H0. hyp.
    apply Vforall_SN_gt_prod. hyp.
  Qed.

  Lemma cp_var : forall P, cp_aeq P -> cp_neutral P -> forall x, P (Var x).

  Proof.
    intros P p1 p4 x. change (P (apps (Var x) Vnil)). apply cp_var_app_sn; fo.
  Qed.

(****************************************************************************)
(** ** Properties of the interpretation of arrow types. *)

  Notation arr := (@arr F X).

  (** [arr] preserves [cp_aeq]. *)

  Instance cp_aeq_arr : forall P Q, cp_aeq Q -> cp_aeq (arr P Q).

  Proof. intros P Q q t u tu h v hv. rewrite <- tu. fo. Qed.

  (** [arr] preserves [cp_sn]. *)

  Lemma cp_sn_arr : forall P Q, cp_aeq P -> cp_sn P -> cp_neutral P ->
    cp_sn Q -> cp_sn (arr P Q).

  Proof.
    intros P Q p1 p2 p4 q2 t ht.
    apply sn_app_l with (v:=Var(var_notin XSet.empty)).
    apply q2. apply ht. apply cp_var; hyp.
  Qed.

  (** [arr] preserves [cp_red]. *)

  Lemma cp_red_arr : forall P Q, cp_red Q -> cp_red (arr P Q).

  Proof.
    intros P Q q3 v v' vv' hv u hu. eapply q3. apply mon_app_l.
    class. apply vv'. refl. apply hv. hyp.
  Qed.

  (** [arr] preserves [cp_neutral]. *)

  Lemma cp_neutral_arr : forall P Q, cp_sn P -> cp_red P ->
    cp_aeq Q -> cp_neutral Q -> cp_neutral (arr P Q).

  Proof.
    intros P Q p2 p3 q1 q4 v nv hv u. revert u.
    cut (forall u, SN R_aeq u -> P u -> Q (App v u)).
    intros h u hu. apply h. apply p2. hyp. hyp.
    induction 1. rename x into u. intro hu.
    apply q4. apply neutral_app. hyp. intros w r.
    destruct (R_aeq_app_neutral nv r).
    destruct H1 as [v' [h1 h2]]. rewrite h1. apply hv; hyp.
    destruct H1 as [u' [h1 h2]]. rewrite h1. apply H0. hyp.
    eapply p3. apply h2. hyp.
  Qed.

  (** [arr] preserves [cp]. *)

  Lemma cp_arr : forall P Q, cp P -> cp Q -> cp (arr P Q).

  Proof.
    intros P Q [p1 p2 p3 p4] [q1 q2 q3 q4]. constructor.
    apply cp_aeq_arr; fo. apply cp_sn_arr; fo.
    apply cp_red_arr; fo. apply cp_neutral_arr; fo.
  Qed.

  (** Monotony properties of [arr]. *)

  Instance arr_incl : Proper (incl --> incl ==> incl) arr.

  Proof. fo. Qed.

  Instance arr_equiv : Proper (equiv ==> equiv ==> equiv) arr.

  Proof. fo. Qed.

End Make.