(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2015-04-10

* Eta-reduction
*)

Set Implicit Arguments.

From Coq Require Import Morphisms Basics.
From CoLoR Require Import LogicUtil RelUtil VecOrd VecUtil.
From CoLoR Require Export LAlpha.

(****************************************************************************)
(** Definition of eta-top-reduction. *)

Section eta_top.

  Variables F X : Type.

  Notation Te := (@Te F X).

  Variable ens_X : Ens X.

  Notation In := (@Ens_In X ens_X).
  Notation fv := (@fv F X ens_X).
  Notation Var := (@Var F X).

  Inductive eta_top : relation Te :=
  | eta_top_intro : forall x u,
      ~In x (fv u) -> eta_top (Lam x (App u (Var x))) u.

End eta_top.

(****************************************************************************)
(** * Properties of eta-reduction. *)

Module Make (Export L : L_Struct).

  Module Export A := LAlpha.Make L.

  Notation In := (@Ens_In X ens_X).

  Notation eta_top := (@eta_top F X ens_X).
  Infix "->eh" := eta_top (at level 70).

  Notation eta := (clos_mon eta_top).
  Infix "->e" := (clos_mon eta_top) (at level 70).

  Notation eta_aeq := (clos_aeq eta).
  Infix "=>e" := (clos_aeq eta) (at level 70).

(****************************************************************************)
(** Eta-reduction do not create free variables. *)

  #[global] Instance fv_eta_top_Equal : Proper (eta_top ==> Equal) fv.

  Proof.
    intros u u' u'u; unfold flip in u'u. inversion u'u; clear u'u; subst.
    simpl. intro y. set_iff. split_all. contr. subst. contr.
  Qed.

  #[global] Instance fv_eta_top : Proper (eta_top --> Subset) fv.

  Proof. intros u u' u'u; unfold flip in u'u. rewrite u'u. refl. Qed.

(****************************************************************************)
(** Eta-reduction is stable by substitution. *)

  #[global] Instance subs_eta_top : Proper (Logic.eq ==> eta_top ==> eta_top) subs.

  Proof.
    intros s s' ss' u v uv. subst s'. inversion uv; clear uv; subst. simpl.
    set (x':= var x (App v (Var x)) s).
    rewrite update_eq, subs_seq with (s':=s).
    2:{ intros y hy. unfold Def.update. eq_dec y x. subst. contr. refl. }
    apply eta_top_intro.
    case_eq (mem x (fvcodom (fv v) s)); intro e; subst x';
      unfold Def.var; ens; simpl; Equal; rewrite !remove_equal; auto; rewrite e.
    set (xs := union (fv v) (add x (fvcodom (fv v) s))).
    gen (var_notin_ok xs). set (x' := var_notin xs). unfold xs.
    rewrite fv_subs; simpl. set_iff. split_all.
    rewrite fv_subs; simpl. set_iff. rewrite <- not_mem_iff in e. split_all.
  Qed.

  (*COQ: should follow from a general meta-theorem
    since [R] is a subrelation of [clos_aeq R]. *)
  #[global] Instance subs_clos_aeq_eta_top :
    Proper (Logic.eq ==> eta_top ==> clos_aeq eta_top) subs.

  Proof.
    intros s s' ss' u u' uu'. subst s'. apply clos_aeq_intro_refl.
    apply subs_eta_top. refl. hyp.
  Qed.

  #[global] Instance subs_eta_aeq : Proper (Logic.eq ==> eta_aeq ==> eta_aeq) subs.

  Proof. class. Qed.

(****************************************************************************)
(** Inversion lemmas for beta-reduction. *)

  Lemma var_eta_aeq_l x u : ~Var x =>e u.

  Proof.
    intro e; inversion e; subst. simpl_aeq; subst. inversion H1; subst.
    inversion H.
  Qed.

  Lemma fun_eta_aeq_l f u : ~Fun f =>e u.

  Proof.
    intro e; inversion e; subst. simpl_aeq; subst. inversion H1; subst.
    inversion H.
  Qed.

  Lemma lam_eta_aeq_l x u v : Lam x u =>e v ->
    (exists v', u = App v' (Var x) /\ ~In x (fv v') /\ v' ~~ v)
    \/ (exists y w, v = Lam y w /\ (x=y \/ ~In y (fv u)) /\ u =>e rename y x w).

  Proof.
    rename x into x0. rename u into u0. rename v into v0.
    intro e; inversion e; clear e; subst; rename v' into v1.
    inv_aeq H; clear H; subst. permut_rename i0; clear i1.
    rename x into x1. rename u into u1. inversion H1; clear H1; subst.
    (* top reduction *)
    left. inversion H; clear H; subst.
    rewrite rename_app, rename_var, eqb_refl, rename_notin_fv in i. 2: hyp.
    inv_aeq i; clear i; subst; rename u into v2. ex v2. split. refl. split.
    2: trans v1; hyp.
    revert i2. simpl. set_iff. rewrite i1. split_all. subst. contr.
    (* non top reduction *)
    right. inv_aeq H0; clear H0; subst.
    rename x into x2; rename u into u2'; rename u' into u1'.
    ex x2 u2'. split. refl. split.
    2:{ (*VERY SLOW*)rewrite i, i1, rename2. apply subs_eta_aeq. refl.
    apply clos_aeq_intro_refl. hyp. hyp. }
    (* condition on variables *)
    permut_rename i1; clear i3.
    split_all; subst; try rewrite rename_id in *. auto.
    rewrite i, fv_rename. apply notin_replace.
    rewrite i, H4, i0, fv_rename. apply notin_replace.
    rewrite i, fv_rename, H4, i0, fv_rename, replace2.
    apply notin_replace. auto.
  Qed.

  Lemma app_eta_aeq_l u v w : App u v =>e w -> exists u' v',
    w = App u' v' /\ ((u =>e u' /\ v ~~ v') \/ (u ~~ u' /\ v =>e v')).

  Proof.
    intro e; inversion e; clear e; subst. inv_aeq H; clear H; subst.
    inversion H1; clear H1; subst. inversion H.
    inv_aeq H0; clear H0; subst. ex u2 u3. split. refl.
    left. split. 2: trans u1; hyp.
    eapply clos_aeq_intro. 3: apply H4. hyp. hyp.
    inv_aeq H0; clear H0; subst. ex u2 u3. split. refl.
    right. split. trans u0; hyp.
    eapply clos_aeq_intro. 3: apply H4. hyp. hyp.
  Qed.

(****************************************************************************)
(** Inversion tactic for eta-reduction. *)

  Ltac inv_eta_aeq h :=
    match type of h with
      | Var _ =>e _ => apply var_eta_aeq_l in h; tauto
      | Fun _ =>e _ => apply fun_eta_aeq_l in h; tauto
      | App _ _ =>e _ =>
        let u := fresh "u" in let v := fresh "v" in let e := fresh "e" in
        let h1 := fresh "h" in let h2 := fresh "h" in
          destruct (app_eta_aeq_l h) as [u [v [e [[h1 h2]|[h1 h2]]]]]
      | Lam _ _ =>e _ =>
        let y := fresh "x" in let v := fresh "v" in
        let h1 := fresh "h" in let h2 := fresh "h" in let h3 := fresh "h" in
          destruct (lam_eta_aeq_l h)
          as [[v [h1 [h2 h3]]]|[[y [v [h1 [h2 h3]]]]]]
      | _ =>e _ => let u := fresh "u" in let v := fresh "v" in
        let h1 := fresh "h" in let h2 := fresh "h" in let h3 := fresh "h" in
          destruct h as [u [h1 [v [h2 h3]]]]
    end.

(****************************************************************************)
(** If [apps u us] eta-reduces to [t],
then [t] is of the form [apps v vs] with [Vcons u us ==>b Vcons v vs]. *)

  Infix "-->e" := (Vrel1 eta) (at level 70).
  Infix "==>e" := (clos_vaeq eta) (at level 70).

  Lemma eta_apps : forall n (us : Tes n) u t, apps u us ->e t
    -> exists v vs, t = apps v vs /\ Vcons u us -->e Vcons v vs.

  Proof.
    induction us; simpl; intros u t e.
    (* nil *)
    exists t. exists Vnil. split_all. apply left_sym. hyp.
    (* cons *)
    destruct (IHus _ _ e) as [v [vs [h1 h2]]]. inversion h2; subst.
    inversion H0; subst. inversion H.
    ex u' (Vcons h vs). split_all. apply left_sym. hyp.
    ex u (Vcons v' vs). split_all. apply right_sym. apply left_sym. hyp.
    ex u (Vcons h vs). split_all. do 2 apply right_sym. hyp.
  Qed.

  Arguments eta_apps [n us u t0] _ : rename.

  Lemma eta_aeq_apps : forall n (us : Tes n) u t, apps u us =>e t ->
    exists v vs, t = apps v vs /\ Vcons u us ==>e Vcons v vs.

  Proof.
    intros n us u t e. inversion e; subst.
    destruct (apps_aeq_l H) as [v [vs [h1 [h2 h3]]]]; subst.
    destruct (eta_apps H1) as [w [ws [i1 i2]]]; subst.
    destruct (apps_aeq_r H0) as [c [cs [j1 [j2 j3]]]]; subst.
    ex c cs. split_all. symmetry in h2, h3, j2, j3.
    ex (Vcons v vs). split. fo. ex (Vcons w ws). split_all. fo.
  Qed.

  Arguments eta_aeq_apps [n us u t0] _ : rename.

  Lemma eta_aeq_apps_fun f n (us : Tes n) t : apps (Fun f) us =>e t ->
    exists vs, t = apps (Fun f) vs /\ us ==>e vs.

  Proof.
    intro r.
    destruct (eta_aeq_apps r) as [v [vs [h1 h2]]]; clear r; subst.
    ex vs. rewrite clos_vaeq_cons in h2. destruct h2 as [[h1 h2]|[h1 h2]].
    inv_eta_aeq h1. simpl_aeq. subst. auto.
  Qed.

  Arguments eta_aeq_apps_fun [f n us t0] _ : rename.

End Make.
