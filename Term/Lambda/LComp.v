(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05

* Tait and Girard computability
*)

Set Implicit Arguments.

From Stdlib Require Import Morphisms Basics.
From CoLoR Require Import RelUtil VecUtil VecOrd LogicUtil SN SetUtil.
From CoLoR Require Export LBeta LEta.

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
  Notation clos_vaeq :=
    (@clos_vaeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation beta_top := (@beta_top F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation eta_top := (@eta_top F X ens_X).

  Infix "->bh" := beta_top (at level 70).
  Infix "->eh" := eta_top (at level 70).

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

  Infix "==>R" := (clos_vaeq R) (at level 70).

  (** Properties not involving reduction. *)

  Global Declare Instance neutral_aeq : Proper (aeq ==> impl) neutral.
  Parameter neutral_var : forall x, neutral (Var x).
  Parameter neutral_app : forall u v, neutral u -> neutral (App u v).
  Parameter not_neutral_lam : forall x u, ~neutral (Lam x u).
  Parameter neutral_beta : forall x u v, neutral (App (Lam x u) v).

  (** Properties involving reduction. *)

  Global Declare Instance subs_R_aeq : Proper (Logic.eq ==> R_aeq ==> R_aeq) subs.
  Global Declare Instance fv_Rh : Proper (Rh --> Subset) fv.
  Parameter not_Rh_var : forall x u, ~ Var x ->Rh u.
  Parameter Rh_eh : forall x u w, Lam x u ->Rh w -> Lam x u ->eh w.
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

Module CP_beta_eta (Import L : L_Struct) <: CP_Struct.

  Module L := L.

  Module Import B := LBeta.Make L.
  Module Import E := LEta.Make L.

  Definition Rh := beta_top U eta_top.
  Infix "->Rh" := Rh (at level 70).

  Notation R := (clos_mon Rh).
  Infix "->R" := (clos_mon Rh) (at level 70).

  Notation R_aeq := (clos_aeq R).
  Infix "=>R" := (clos_aeq R) (at level 70).

  Lemma R_aeq_alt : R_aeq == beta_aeq U eta_aeq.

  Proof. unfold Rh. rewrite clos_mon_union, clos_aeq_union. refl. Qed.

  (** A term is neutral if it is not a [Lam]. *)

  Definition neutral (u : Te) :=
    match u with
      | Def.Lam _ _ => False
      | _ => True
    end.

  (** CP structure properties not involving reduction. *)

  Global Instance neutral_aeq : Proper (aeq ==> impl) neutral.

  Proof. intros u u' uu' hu. destruct u; inv_aeq uu'; subst; simpl; auto. Qed.

  Lemma neutral_var x : neutral (Var x).

  Proof. fo. Qed.

  Lemma neutral_app u v : neutral u -> neutral (App u v).

  Proof. fo. Qed.

  Lemma not_neutral_lam x u : ~neutral (Lam x u).

  Proof. fo. Qed.

  Lemma neutral_beta x u v : neutral (App (Lam x u) v).

  Proof. fo. Qed.

  (** CP structure properties involving reduction. *)

  Global Instance subs_R_aeq : Proper (Logic.eq ==> R_aeq ==> R_aeq) subs.

  Proof.
    eapply stable_same_iff. apply R_aeq_alt. apply stable_union.
    apply subs_beta_aeq. apply subs_eta_aeq.
  Qed.

  Lemma not_Rh_var x u : ~ Var x ->Rh u.

  Proof. intro r; inversion r; clear r; inversion H. Qed.

  Lemma Rh_eh x u w : Lam x u ->Rh w -> Lam x u ->eh w.

  Proof. intro r; inversion r; clear r. inversion H. hyp. Qed.

  Lemma Rh_bh x u v w : App (Lam x u) v ->Rh w -> App (Lam x u) v ->bh w.

  Proof. intro r; inversion r; clear r. hyp. inversion H. Qed.

  Lemma not_Rh_app_neutral u v w : neutral u -> ~ App u v ->Rh w.

  Proof.
    intros h r. inversion r; clear r; inversion H; clear H; subst. auto.
  Qed.

  Global Instance fv_Rh : Proper (Rh --> Subset) fv.

  Proof. apply fv_union. apply fv_beta_top. apply fv_eta_top. Qed.

  (** Some notations. *)
  (*COQ: can we avoid to repeat these notations already declared in CP_Struct?*)

  Notation cp_aeq := (Proper (aeq ==> impl)) (only parsing).
  Notation cp_sn := (@cp_sn F X R_aeq).
  Notation cp_red := (@cp_red F X R_aeq).
  Notation cp_neutral := (@cp_neutral F X R_aeq neutral).
  Notation cp := (@cp F X aeq R_aeq neutral).

  (** Extra properties. *)

  Lemma R_aeq_apps_fun f n (us : Tes n) t : apps (Fun f) us =>R t ->
    exists vs, t = apps (Fun f) vs /\ clos_vaeq R us vs.

  Proof.
    intro r. apply R_aeq_alt in r. destruct r as [r|r].
    destruct (beta_aeq_apps_fun r) as [vs [h1 h2]].
    ex vs. split_all. (*COQ:rewrite clos_mon does not work*)
    unfold Rh. eapply clos_vaeq_same. rewrite clos_mon_union. refl.
    eapply clos_vaeq_incl. apply incl_union_l. refl. hyp.

    destruct (eta_aeq_apps_fun r) as [vs [h1 h2]].
    ex vs. split_all. (*COQ:rewrite clos_mon does not work*)
    unfold Rh. eapply clos_vaeq_same. rewrite clos_mon_union. refl.
    eapply clos_vaeq_incl. apply incl_union_r. refl. hyp.
  Qed.

  Arguments R_aeq_apps_fun [f n us t] _ : rename.

End CP_beta_eta.

(****************************************************************************)
(** * Properties of CP structures. *)

Module Make (Export CP : CP_Struct).

  Notation arr := (@arr F X).

  Module Export B := LBeta.Make L.
  Module Export E := LEta.Make L.

(****************************************************************************)
(** ** Properties of [R_aeq]. *)

  (** Variables are irreducible. *)

  Lemma not_R_var x u : ~ Var x ->R u.

  Proof. intro r; inversion r; subst. eapply not_Rh_var. apply H. Qed.

  Lemma not_R_aeq_var x u : ~ Var x =>R u.

  Proof.
    intro r; inversion r; subst. simpl_aeq; subst. eapply not_R_var. apply H1.
  Qed.

  (** A reduct of an abstraction is either a top-eta-reduct or an
  non-top-reduct. *)

  Lemma lam_R_aeq_l x u v : Lam x u =>R v ->
    (exists v', u = App v' (Var x) /\ ~In x (fv v') /\ v' ~~ v)
    \/ (exists y w, v = Lam y w /\ u =>R rename y x w).

  Proof.
    intro r; inversion r; clear r; subst. inv_aeq H; clear H; subst.
    permut_rename i0; clear i1. inversion H1; clear H1; subst.
    (* top reduction = top eta *)
    left. apply Rh_eh in H; inversion H; clear H; subst.
    rewrite rename_app in i. inv_aeq i; clear i; subst. ex u0. split.
    rewrite rename_var, eqb_refl in i3. inv_aeq i3. subst. refl.
    (*COQ: inv_aeq i3; subst does not give the same result*)
    rewrite rename_notin_fv in i1. 2: hyp. rewrite i1. split. 2: hyp.
    revert i2. simpl. set_iff. split_all. subst. contr.
    (* non top reduction *)
    right. inv_aeq H0; clear H0; subst. ex x1 u1. split. refl.
    (*VERY SLOW*)rewrite i, i1, rename2. 2: hyp. 
    apply subs_R_aeq. refl. apply clos_aeq_intro_refl. hyp.
  Qed.

  (** [App u v] is not head-reducible if [u] is neutral. *)

  Lemma R_app_neutral u v w : neutral u -> App u v ->R w ->
      (exists u', w = App u' v /\ u ->R u')
      \/ (exists v', w = App u v' /\ v ->R v').

  Proof.
    intros n r; inversion r; subst.
    exfalso. eapply not_Rh_app_neutral. apply n. apply H.
    left. exists u'. auto. right. exists v'. auto.
  Qed.

  Lemma R_aeq_app_neutral u v w : neutral u -> App u v =>R w ->
      (exists u', w ~~ App u' v /\ u =>R u')
      \/ (exists v', w ~~ App u v' /\ v =>R v').

  Proof.
    intros n r; inversion r; subst. inv_aeq H; clear H; subst.
    rewrite <- i0 in n.
    destruct (R_app_neutral n H1) as [h|h]; destruct h as [t [a s]]; subst.
    left. exists t. rewrite <- i1, <- i0. intuition.
    apply incl_clos_aeq. hyp.
    right. exists t. rewrite <- i1, <- i0. intuition.
    apply incl_clos_aeq. hyp.
  Qed.

  (** Extension of properties from [App] to [apps]. *)

  Lemma neutral_apps : forall n (us : Tes n) u,
      neutral u -> neutral (apps u us).

  Proof.
    induction us; simpl. auto.
    intros u nu. apply IHus. apply neutral_app. hyp.
  Qed.

  Lemma neutral_apps_var x n (us : Tes n) : neutral (apps (Var x) us).

  Proof. apply neutral_apps. apply neutral_var. Qed.

  Lemma R_aeq_apps_neutral : forall n (us : Tes n) u v, neutral u ->
    apps u us =>R v -> (exists u', v ~~ apps u' us /\ u =>R u')
    \/ (exists us', v ~~ apps u us' /\ Vrel1 R_aeq us us').

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

  Arguments R_aeq_apps_neutral [n us u v] _ _.

  (** Alpha-transitive closure of [=>R]. *)

  Infix "=>R*" := (R_aeq*) (at level 70).

  Notation satc := (subs_rel (R_aeq*)).

  Lemma subs_satc u s s' : satc (fv u) s s' -> subs s u =>R* subs s' u.

  Proof. intro ss'. apply subs_rel_mon_preorder_aeq; class. Qed.

(****************************************************************************)
(** ** Properties of [SN R_aeq]. *)

  (** [SN R_aeq] is a computability predicate. *)

  Lemma cp_sn_SN : cp_sn (SN R_aeq).

  Proof. fo. Qed.

  Lemma cp_red_SN : cp_red (SN R_aeq).

  Proof. intros u u' b h. inversion h. apply H. hyp. Qed.

  Lemma cp_neutral_SN : cp_neutral (SN R_aeq).

  Proof. intros u n h. apply SN_intro. hyp. Qed.

  Lemma cp_SN : cp (SN R_aeq).

  Proof.
    constructor. class. apply cp_sn_SN. apply cp_red_SN. apply cp_neutral_SN.
  Qed.

  (** If [u] is SN , then [Lam x u] is SN too. *)

  Lemma sn_lam x u : SN R_aeq u -> SN R_aeq (Lam x u).

  Proof.
    intro h'.
    (* [u] is SN wrt [supterm! U R_aeq] since [R_aeq] is monotone. *)
    assert (h : SN (supterm! U R_aeq) u). apply SN_supterm_R_mon. class. hyp.
    (* We proceed by induction on [u] with [supterm! U R_aeq] as
    well-founded relation. *)
    clear h'. revert h; induction 1; rename x0 into u.
    (* We prove that every reduct [t] of [Lam x u] is SN. *)
    apply SN_intro; intros t r.
    inversion r; clear r; subst. inv_aeq H1; clear H1; subst.
    permut_rename i0; clear i1. inversion H3; clear H3; subst.
    (* reduction at the top (eta) *)
    apply Rh_eh in H1. inversion H1; clear H1; subst.
    rewrite rename_app, rename_var, eqb_refl in i. inv_aeq i; clear i; subst.
    rewrite rename_notin_fv in i1. 2: hyp. rewrite H2, <- i1.
    apply (SN_incl (supterm! U R_aeq)). apply incl_union_r. refl.
    apply H. left. apply t_step. apply st_app_l.
    (* reduction in [u]. *)
    assert (e : t ~~ Lam x (rename x0 x u')). 
    trans (Lam x0 u'). hyp. apply aeq_alpha'. destruct i2. auto.
    right. intro h. apply fv_clos_mon in H6; class.
    rewrite e. apply H0. right. rewrite i. apply subs_R_aeq. refl.
    apply clos_aeq_intro_refl. hyp.
  Qed.

(****************************************************************************)
(** ** Computability properties are invariant wrt [=]. *)

  Global Instance cp_aeq_equiv : Proper (equiv ==> impl) cp_aeq.

  Proof. intros P Q PQ hP t u tu Qt. apply PQ. rewrite <- tu. fo. Qed.

  Global Instance cp_sn_equiv : Proper (equiv ==> impl) cp_sn.

  Proof. fo. Qed.

  Global Instance cp_red_equiv : Proper (equiv ==> impl) cp_red.

  Proof.
    intros P Q PQ hP t u tu Qt. apply PQ. apply PQ in Qt. clear PQ; fo.
  Qed.

  Global Instance cp_neutral_equiv : Proper (equiv ==> impl) cp_neutral.

  Proof. fo. Qed.

  Global Instance cp_equiv : Proper (equiv ==> impl) cp.

  Proof. intros P Q PQ [P1 P2 P3 P4]. rewrite PQ in *. fo. Qed.

(****************************************************************************)
(** ** Properties of computability predicates wrt variables. *)

  (** A computability predicate contains every strongly normalizing term
     of the form [x t1 .. tn]. *)

  Lemma cp_var_app_sn : forall P, cp_aeq P -> cp_neutral P ->
    forall x n (us : Tes n), Vforall (SN R_aeq) us -> P (apps (Var x) us).

  Proof.
    intros P p1 p4 x n us h.
    cut (SN (Vrel1 R_aeq) us). clear h. revert us. induction 1.
    rename x0 into us. apply p4. apply neutral_apps_var. intros v r.
    destruct (R_aeq_apps_neutral (neutral_var x) r).
    destruct H1 as [x' [h1 h2]]. apply not_R_aeq_var in h2. tauto.
    destruct H1 as [us' [h1 h2]]. rewrite h1. apply H0. hyp.
    apply Vforall_SN_rel1. hyp.
  Qed.

  Lemma cp_var : forall P, cp_aeq P -> cp_neutral P -> forall x, P (Var x).

  Proof.
    intros P p1 p4 x. change (P (apps (Var x) Vnil)). apply cp_var_app_sn; fo.
  Qed.

(****************************************************************************)
(** ** Properties of [arr]. *)

  (** Monotony properties of [arr]. *)

  Global Instance arr_incl :
    Proper (SetUtil.subset --> SetUtil.subset ==> SetUtil.subset) arr.

  Proof. fo. Qed.

  Global Instance arr_equiv : Proper (equiv ==> equiv ==> equiv) arr.

  Proof. fo. Qed.

  (** [arr] preserves [cp_aeq]. *)

  Global Instance cp_aeq_arr : forall P Q, cp_aeq Q -> cp_aeq (arr P Q).

  Proof. intros P Q q t u tu h v hv. rewrite <- tu. fo. Qed.

  (** [arr] preserves [cp_sn]. *)

  Lemma cp_sn_arr : forall P Q, cp_aeq P -> cp_sn P -> cp_neutral P ->
    cp_sn Q -> cp_sn (arr P Q).

  Proof.
    intros P Q p1 p2 p4 q2 t ht.
    apply SN_st_app_l with (v:=Var(var_notin XSet.empty)). class.
    apply q2. apply ht. apply cp_var; hyp.
  Qed.

  (** [arr] preserves [cp_red]. *)

  Lemma cp_red_arr : forall P Q, cp_red Q -> cp_red (arr P Q).

  Proof.
    intros P Q q3 v v' vv' hv u hu. eapply q3. eapply mon_app_l.
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

(****************************************************************************)
(** ** Computability of an application. *)

  Lemma cp_app P Q : cp_aeq P -> cp_red P -> cp_sn P ->
                     cp_aeq Q -> cp_red Q -> cp_neutral Q ->
    forall t, (neutral t \/ exists x u, t = Lam x u) ->
              (forall t', t =>R t' -> arr P Q t') ->
              forall v, P v ->
                        (forall x u, t = Lam x u -> Q (subs (single x v) u)) ->
                        Q (App t v).

  Proof.
    intros P_aeq P_red P_sn Q_aeq Q_red Q_neu
           t t_neu_or_abs t_red_comp v0 v0_sn tv0_beta_comp.
    (* We prove the more general property that [App t v] is
    computable for every reduct of [v] of [v0]. *)
    set (B := fun v => v0 =>R* v -> Q (App t v)).
    cut (B v0). intro h. apply h. refl.
    (* Since [P] satisfies [cp_sn], [v0] is SN wrt [R_aeq] and thus
    wrt the restriction of [R_aeq] of the reducts of [v0]. *)
    set (S := RelUtil.restrict (R_aeq* v0) R_aeq). cut (SN S v0).
    2:{ apply wf_restrict_sn. intros v hv. eapply proper_atc. class.
    2: apply hv. class. apply P_sn. hyp. }
    (* We prove that every reduct of [v0] is computable by
       well-founded induction on [v0] with [S] as well-founded relation. *)
    apply SN_ind; intros v i IH v0v.
    (* Since [App t v] is neutral, it suffices to prove that its
    reducts are computable. *)
    apply Q_neu. destruct t_neu_or_abs as [t_neu|[x [u e]]].
    apply neutral_app. hyp. rewrite e. apply neutral_beta.
    intros w tv_w. inversion tv_w as [? a ? w' tv_a ww' aw']; clear tv_w; subst.
    inv_aeq tv_a; clear tv_a; subst; rename u into t'; rename u0 into v'.
    inversion aw'; clear aw'; subst.
    (* top *)
    destruct t_neu_or_abs as [t_neu|[x [u e]]].
    exfalso. eapply not_Rh_app_neutral. 2: apply H. rewrite i1. hyp.
    rewrite e in i1. inv_aeq i1; clear i1. rewrite i0 in H. apply Rh_bh in H.
    inversion H; clear H; subst x1 u1 v1 w'. rewrite ww', i3, single_rename.
    rewrite fold_subs_single, i2. (*COQ: rewrite <- v0v does not work*)
    eapply proper_atc. hyp. apply Q_red.
    eapply subs_single_mon_preorder_aeq; class. apply v0v. refl.
    apply tv0_beta_comp. hyp. tauto.
    (* app_l *)
    rewrite ww'. apply t_red_comp.
    rewrite <- i1. apply clos_aeq_intro_refl. hyp.
    rewrite i2. (*COQ: rewrite <- v0v does not work*)
    gen (proper_atc P_aeq P_red); intro P_reds.
    assert (h : Proper (Logic.eq ==> R_aeq* ==> aeq ==> R_aeq*) subs_single).
    apply subs_single_mon_preorder_aeq; class. rewrite <- v0v. hyp.
    (* app_r *)
    rewrite ww', i1. apply IH.
    split. hyp. rewrite <- i2. apply clos_aeq_intro_refl. hyp.
    trans v. hyp. rewrite <- i2. apply at_step. apply clos_aeq_intro_refl. hyp.
  Qed.

(****************************************************************************)
(** ** Computability of an abstraction. *)

  Lemma cp_lam P Q : cp_aeq P -> cp_red P -> cp_sn P -> cp_neutral P ->
                     cp_aeq Q -> cp_red Q -> cp_sn Q -> cp_neutral Q ->
    forall x u, (forall v, P v -> Q (subs (single x v) u)) ->
                arr P Q (Lam x u).

  Proof.
    intros P_aeq P_red P_sn P_neu Q_aeq Q_red Q_sn Q_neu x u hu.
    (* [u] is SN. *)
    cut (SN R_aeq u).
    2:{ apply Q_sn. rewrite <- (single_id x). apply hu. apply cp_var; hyp. }
    (* We prove that [Lam x u] is computable by wellfounded induction on [u].*)
    intro u_sn. revert u u_sn hu. induction 1; rename x0 into u; intros hu v hv.
    (* We apply the lemma [cp_app]. *)
    apply cp_app with (P:=P); auto.
    right. ex x u. refl.
    2:{ intros x' u' e; inversion e; clear e; subst. fo. }
    (* We prove that every reduct of [Lam x u] is computable. *)
    intros t r. gen r; intro r'. apply lam_R_aeq_l in r'.
    destruct r' as [[t' [h1 [h2 h3]]]|[y [w [h1 h2]]]]; subst.
    (* top eta reduction *)
    intros a ha.
    assert (e : App t a ~~ subs (single x a) (App t' (Var x))).
    simpl. rewrite single_eq, single_notin_fv, h3. refl. hyp.
    rewrite e; clear e. apply hu. hyp.
    (* non top reduction *)
    assert (h : y=x \/ ~In x (fv w)). eq_dec x y. auto.
    right. intro hx. apply fv_clos_aeq in r. 2: class. simpl in r.
    assert (i : In x (remove y (fv w))). set_iff. fo.
    apply r in i. revert i. set_iff. fo.
    (* [Lam y w] is alpha-equivalent to [Lam x (rename y x w)]. *)
    rewrite aeq_alpha' with (y:=x). 2: hyp. apply H0. hyp. intros a ha.
    eapply proper_atc. class. apply Q_red. eapply subs_atc. class. refl.
    apply at_step. apply h2. fo.
  Qed.

End Make.
