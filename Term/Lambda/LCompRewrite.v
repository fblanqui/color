(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-05-06

* Higher-order rewriting and its associated CP structure
*)

Set Implicit Arguments.

From Stdlib Require Import Morphisms Basics Lia.
From CoLoR Require Import LogicUtil RelUtil VecOrd VecUtil LAlpha.

(****************************************************************************)
(** * Rewrite system structure. *)

Module Type RS_Struct.

  Declare Module Export L : L_Struct.

  (** We assume given a set of rules preserving free variables and
  whose left-hand sides are of the form [apps (Fun f) ls]. *)

  Parameter rule : relation Te.

  Global Declare Instance fv_rule : Proper (rule --> Subset) fv.

  Parameter lhs_fun : forall l r, rule l r -> F.
  Parameter lhs_nb_args : forall l r, rule l r -> nat.
  Parameter lhs_args : forall l r (h : rule l r), Tes (lhs_nb_args h).
  Parameter lhs_ok : forall l r (h : rule l r),
    l = apps (Fun (lhs_fun h)) (lhs_args h).

End RS_Struct.

(****************************************************************************)
(** * Rewrite relation associated to a rewrite system and some of its properties. *)

Module Make (Export RS : RS_Struct).

  Module Export A := LAlpha.Make L.

  Lemma rule_ok : forall l r, rule l r ->
    exists f n (ls : Tes n), l = apps (Fun f) ls.

  Proof.
    intros l r h. ex (lhs_fun h) (lhs_nb_args h) (lhs_args h). apply lhs_ok.
  Qed.

  (** Equations satisfied by [lhs_fun], [lhs_nb_args] and [lhs_args]. *)

  Lemma lhs_fun_eq : forall f n (ts : Tes n) r
    (h : rule (apps (Fun f) ts) r), lhs_fun h = f.

  Proof.
    intros f n ts r h. eapply eq_apps_fun_head with (F:=F) (X:=X).
    sym. apply lhs_ok.
  Qed.

  Arguments lhs_fun_eq [f n ts r] _.

  Lemma lhs_nb_args_eq : forall f n (ts : Tes n) r
    (h : rule (apps (Fun f) ts) r), lhs_nb_args h = n.

  Proof.
    intros f n ts r h. sym. eapply eq_apps_fun_nb_args with (F:=F) (X:=X).
    apply lhs_ok.
  Qed.

  Arguments lhs_nb_args_eq [f n ts r] _.

  Lemma lhs_nb_args_eq_sym : forall f n (ts : Tes n) r
    (h : rule (apps (Fun f) ts) r), n = lhs_nb_args h.

  Proof. intros f n ts r h. sym. apply lhs_nb_args_eq. Qed.

  Arguments lhs_nb_args_eq_sym [f n ts r] _.

  Lemma lhs_args_eq : forall f n (ts : Tes n) r (h : rule (apps (Fun f) ts) r),
    lhs_args h = Vcast ts (lhs_nb_args_eq_sym h).

  Proof.
    intros f n ts r h. gen (lhs_ok h); intro e. symmetry in e.
    gen (eq_apps_fun_args e); intro i. rewrite i. apply Vcast_pi.
  Qed.

  Arguments lhs_args_eq [f n ts r] _.

  (** Rewriting is defined as the alpha-closure of the monotone
  closure of the substitution closure of the set of rules. *)

  Notation Sh := (clos_subs rule).
  Infix "->Sh" := (clos_subs rule) (at level 70).

  Notation succ := Datatypes.S.
  Notation S := (clos_mon Sh).
  Infix "->S" := (clos_mon Sh) (at level 70).

  Notation S_aeq := (clos_aeq S).
  Infix "=>S" := (clos_aeq S) (at level 70).

  (** Rewriting is stable by substitution. *)

  Global Instance subs_S_aeq : Proper (Logic.eq ==> S_aeq ==> S_aeq) subs.

  Proof.
    intros s s' ss' t u tu. subst s'. inversion tu; subst; clear tu.
    revert u' v' H1 t H u H0 s.
    (* We proceed by induction on [u' ->S v']. *)
    induction 1; intros a ha b hb s; rewrite ha, hb.
    (* m_step *)
    inversion H; subst. rewrite 2!subs_comp.
    apply clos_aeq_intro_refl. apply m_step. apply subs_step. hyp.
    (* m_app_l *)
    simpl. apply mon_app_l. class. eapply IHclos_mon. refl. refl. refl.
    (* m_app_r *)
    simpl. apply mon_app_r. class. refl. eapply IHclos_mon. refl. refl.
    (* m_lam *)
    simpl. set (x1 := var x u s). set (s1 := S.update x (Var x1) s).
    set (x2 := var x u' s). set (s2 := S.update x (Var x2) s).
    set (xs := XSet.union (fv (subs s1 u)) (fv (subs s2 u'))).
    (* We rename [x1] and [x2] by [z]. *)
    set (z := var_notin xs).
    gen (var_notin_ok xs); fold z; unfold xs; set_iff; intuition.
    rewrite aeq_alpha with (x:=x1). 2: unfold not; apply H0.
    rewrite aeq_alpha with (x:=x2). 2: unfold not; apply H2.
    (* We can now apply [mon_lam]. *)
    unfold Def.rename. rewrite 2!subs_comp. apply mon_lam. class. refl.
    (* First remark that [fv u' [<=] fv u]. *)
    assert (h : fv u' [<=] fv u). rewrite <- H1. refl.
    (* We prove that the substitutions applied to [u] and [u'] are
    identical on [fv u']. *)
    assert (i : seq (fv u') (comp (single x2 (Var z)) s2)
                    (comp (single x1 (Var z)) s1)).
    intros y hy. unfold Def.comp, s1, s2, Def.update. eq_dec y x.
    subst. simpl. rewrite 2!single_eq. refl.
    rewrite 2!subs_notin_fv. refl.
    rewrite domain_single_empty.
    left. apply var_notin_fv_subs. 2: hyp. rewrite <- h. hyp.
    rewrite domain_single_empty.
    left. apply var_notin_fv_subs. 2: hyp. hyp.
    (* We can now apply the induction hypothesis. *)
    rewrite (subs_seq i). eapply IHclos_mon. refl. refl.
  Qed.

  (** Term vector rewriting modulo alpha-equivalence. *)

  Infix "-->S" := (Vrel1 S) (at level 70).
  Infix "==>S" := (clos_vaeq S) (at level 70).

  (** Inversion lemma when rewriting a term of the form [apps (Fun f) us]. *)

  Lemma rewrite_apps_fun : forall f n (us : Tes n) t,
    apps (Fun f) us ->S t ->
    (exists vs, t = apps (Fun f) vs /\ us -->S vs)
    \/ (exists p (ls : Tes p) r s q (vs : Tes q) (h : p+q=n),
      rule (apps (Fun f) ls) r
      /\ us = Vcast (Vapp (Vmap (subs s) ls) vs) h
      /\ t = apps (subs s r) vs).

  Proof.
    intro f. induction n; intros us t ht.
    (* 0 *)
    right. VOtac. simpl in ht. inversion ht; subst; clear ht.
    inversion H; subst; clear H.
    destruct (rule_ok H1) as [g [n [ls e]]]; subst.
    rewrite subs_apps in H0. simpl in H0. destruct ls; simpl in *.
    2: rewrite apps_app in H0; discr.
    inversion H0. subst g. clear H0.
    ex 0 (@Vnil Te) y s 0 (@Vnil Te).
    assert (a : 0+0=0). refl. ex a. simpl. rewrite Vcast_refl. intuition.
    (* S *)
    inversion ht; subst; clear ht.
    (* m_step *)
    right. inversion H; subst. destruct (rule_ok H1) as [g [m [ls e]]]; subst.
    rewrite subs_apps in H0. simpl in H0.
    gen (eq_apps_fun_head H0); intro e; subst g.
    gen (eq_apps_fun_nb_args H0); intro e; subst m.
    gen (eq_apps_nb_args_args H0); intro e.
    ex (succ n) ls y s 0 (@Vnil Te).
    assert (a : succ n + 0 = succ n). lia. exists a. simpl. intuition.
    sym. rewrite Vapp_nil, Vcast_cast, e, Vcast_refl. refl.
    (* m_app_l *)
    rewrite (VSn_eq us) in H. simpl in H. rewrite apps_app in H.
    rewrite <- VSn_eq in H. inversion H; subst; clear H.
    gen (IHn _ _ H0);
      intros [[vs [h1 h2]]|[p [ls [r [s [q [vs [h1 [h2 [h3 h4]]]]]]]]]]; subst.
    (* 1 *)
    left. rewrite app_apps, Vlast_tail.
    exists (Vadd vs (Vlast (Vhead us) us)). intuition.
    rewrite (VSn_add us) at 1. apply Vrel1_add_intro. right. intuition.
    (* 2 *)
    right. rewrite Vcast_refl in h3.
    ex p ls r s (Datatypes.S q) (Vadd vs (Vlast (Vhead us) us)).
    assert (h : p + succ q = succ (p+q)). lia. exists h. split. hyp. split.
    rewrite (VSn_add us) at 1. rewrite h3, Vadd_app. apply Vcast_pi.
    rewrite Vlast_tail. apply app_apps.
    (* m_app_r *)
    left. rewrite (VSn_eq us) in H. simpl in H. rewrite apps_app in H.
    rewrite <- VSn_eq in H. inversion H; subst; clear H.
    rewrite Vlast_tail in H0. exists (Vadd (Vremove_last us) v'). split.
    apply app_apps. rewrite (VSn_add us). apply Vrel1_add_intro. left.
    rewrite Vremove_last_add. intuition.
    (* m_lam *)
    destruct us; simpl in H. discr. rewrite apps_app in H. discr.
  Qed.

  Arguments rewrite_apps_fun [f n us t0] _ : rename.

  Lemma rewrite_aeq_apps_fun : forall f n (us : Tes n) t,
    apps (Fun f) us =>S t ->
    (exists vs, t = apps (Fun f) vs /\ us ==>S vs)
    \/ (exists p (ls : Tes p) r s q (vs : Tes q) (h : p+q=n),
      rule (apps (Fun f) ls) r
      /\ us ~~~ Vcast (Vapp (Vmap (subs s) ls) vs) h
      /\ t ~~ apps (subs s r) vs).

  Proof.
    intros f n us t r. inversion r; subst; clear r. rename v' into t'.
    inv_aeq H; clear H; subst.
    destruct (rewrite_apps_fun H1)
      as [[vs [j1 j2]]|[p [ls [r [s [q [vs [h1 [h2 [h3 h4]]]]]]]]]];
        clear H1; subst.
    left. inv_aeq H0; clear H0; subst. exists us1. intuition.
    exists us0. intuition auto with *. exists vs. intuition auto with *.
    right. rewrite Vcast_refl in i1. inv_aeq H0; clear H0; subst.
    ex p ls r s q vs (Logic.eq_refl (p+q)). split. hyp.
    rewrite Vcast_refl. intuition auto with *. rewrite i0, i2. refl.
  Qed.

  Arguments rewrite_aeq_apps_fun [f n us t0] _ : rename.

End Make.

(****************************************************************************)
(** * CP structure associated to a rewrite system. *)

From CoLoR Require LComp LBeta LEta.

Module CP_beta_eta_rewrite (Import RS : RS_Struct) <: LComp.CP_Struct.

  Module L := L.

  Module Import S := Make RS.
  Module Import B := LBeta.Make L.
  Module Import E := LEta.Make L.

  (** We consider the union of beta-reduction and rewriting. *)

  Definition Rh := beta_top U eta_top U Sh.
  Infix "->Rh" := Rh (at level 70).

  Notation R := (clos_mon Rh).
  Infix "->R" := (clos_mon Rh) (at level 70).

  Notation R_aeq := (clos_aeq R).
  Infix "=>R" := (clos_aeq R) (at level 70).

  Lemma R_aeq_alt : R_aeq == beta_aeq U eta_aeq U S_aeq.

  Proof. unfold Rh. rewrite !clos_mon_union, !clos_aeq_union. refl. Qed.

  (** A term is neutral if it is not a [Lam] nor it is headed by a [Fun]. *)

  Definition neutral (u : Te) :=
    match u with
      | Def.Lam _ _ => False
      | _ =>
        match head u with
          | Def.Fun _ => False
          | _ => True
        end
    end.

  (** CP structure properties not involving reduction. *)

  Global Instance neutral_aeq : Proper (aeq ==> impl) neutral.

  Proof.
    intros u v uv hu. destruct v; inv_aeq uv; subst; simpl in *; auto.
    case_eq (head v1); auto. intros f h.
    assert (a : head u0 = Fun f). apply fun_aeq_r. rewrite i0, h. refl.
    rewrite a in hu. auto.
  Qed.

  Lemma neutral_var : forall x, neutral (Var x).

  Proof. fo. Qed.

  Lemma neutral_app : forall u v, neutral u -> neutral (App u v).

  Proof.
    intros u v hu. simpl. clear v. revert u hu. induction u; simpl; auto.
  Qed.

  Lemma not_neutral_lam : forall x u, ~neutral (Lam x u).

  Proof. fo. Qed.

  Lemma neutral_beta : forall x u v, neutral (App (Lam x u) v).

  Proof. fo. Qed.

  Lemma not_neutral_apps_fun :
    forall f n (ts : Tes n), ~neutral (apps (Fun f) ts).

  Proof.
    intros f n ts. destruct ts; simpl. fo.
    rewrite apps_app. simpl. rewrite head_apps. simpl. fo.
  Qed.

  (** CP structure properties involving reduction. *)

  Global Instance subs_R_aeq : Proper (Logic.eq ==> R_aeq ==> R_aeq) subs.

  Proof.
    eapply stable_same_iff. apply R_aeq_alt. apply stable_union.
    apply stable_union. apply subs_beta_aeq. apply subs_eta_aeq.
    apply subs_S_aeq.
  Qed.

  Global Instance fv_Rh : Proper (Rh --> Subset) fv.

  Proof.
    apply fv_union. apply fv_union. apply fv_beta_top. apply fv_eta_top.
    apply fv_clos_subs. apply fv_rule.
  Qed.

  Lemma not_Rh_var x u : ~ Var x ->Rh u.

  Proof.
    intro r; inversion r; clear r.
    destruct H; inversion H.
    inversion H; subst; clear H. revert H0.
    destruct (rule_ok H1) as [f [n [ls h]]]; subst; clear H1.
    rewrite subs_apps. destruct ls; simpl. discr. rewrite apps_app. discr.
  Qed.

  Lemma Rh_eh x u w : Lam x u ->Rh w -> Lam x u ->eh w.

  Proof.
    intro r; inversion r; clear r.
    destruct H. inversion H. hyp.
    inversion H; subst; clear H. revert H0.
    destruct (rule_ok H1) as [f [n [ls h]]]; subst; clear H1.
    rewrite subs_apps. destruct ls; simpl. discr. rewrite apps_app. discr.
  Qed.

  Lemma Rh_bh x u v w : App (Lam x u) v ->Rh w -> App (Lam x u) v ->bh w.

  Proof.
    intro r; inversion r; clear r.
    destruct H. hyp. inversion H.
    exfalso. inversion H; subst; clear H. revert H0.
    destruct (rule_ok H1) as [f [n [ls h]]]; subst; clear H1.
    rewrite subs_apps. simpl. destruct ls; simpl. discr.
    destruct ls; simpl. discr. rewrite 2!apps_app. discr.
  Qed.

  Lemma not_Rh_app_neutral u v w : neutral u -> ~ App u v ->Rh w.

  Proof.
    intros u_neu r; inversion r; clear r.
    destruct H. destruct u; inversion H; auto. inversion H.
    inversion H; clear H.
    destruct (rule_ok H1) as [f [n [ls i]]]; subst; clear H1.
    rewrite subs_apps in H0. simpl in H0.
    apply (f_equal head) in H0. revert u_neu H0. rewrite head_apps.
    destruct u; simpl; fo. discr. rewrite <- H0 in u_neu. hyp.
  Qed.

  (** Term vector rewriting. *)

  Infix "==>R" := (clos_vaeq R) (at level 70).

  Lemma clos_vaeq_alt n :
    @clos_vaeq n R == @clos_vaeq n beta U @clos_vaeq n eta U @clos_vaeq n S.

  Proof. unfold Rh. rewrite !clos_mon_union, !clos_vaeq_union. refl. Qed.

  (** Inversion lemma for terms of the form [apps (Fun f) us]. *)

  Lemma beta_eta_rewrite_aeq_apps_fun : forall f n (us : Tes n) t,
    apps (Fun f) us =>R t ->
    (exists vs, t = apps (Fun f) vs /\ us ==>R vs)
    \/ (exists p (ls : Tes p) r s q (vs : Tes q) (h : p+q=n),
      rule (apps (Fun f) ls) r
      /\ us ~~~ Vcast (Vapp (Vmap (subs s) ls) vs) h
      /\ t ~~ apps (subs s r) vs).

  Proof.
    intros f n us t h. apply R_aeq_alt in h. destruct h as [[h|h]|h].
    (* beta *)
    left. destruct (beta_aeq_apps_fun h) as [vs [h1 h2]]; subst.
    ex vs. split_all. eapply incl_elim. rewrite clos_vaeq_alt.
    apply incl_union_l. apply incl_union_l. refl. hyp.
    (* eta *)
    left. destruct (eta_aeq_apps_fun h) as [vs [h1 h2]]; subst.
    ex vs. split_all. eapply incl_elim. rewrite clos_vaeq_alt.
    apply incl_union_l. apply incl_union_r. refl. hyp.  
    (* rewrite *)
    destruct (rewrite_aeq_apps_fun h)
      as [[vs [h1 h2]]|[p [ls [r [s [q [vs [h0 [h1 [h2 h3]]]]]]]]]]; clear h.
    left. ex vs. split_all. eapply incl_elim. rewrite clos_vaeq_alt.
    apply incl_union_r. refl. hyp.
    right. ex p ls r s q vs h0. split_all.
  Qed.

  Arguments beta_eta_rewrite_aeq_apps_fun [f n us t0] _ : rename.

  (** Some notations. *)
  (*COQ: can we avoid to repeat these notations already declared in CP_Struct?*)

  Import LComp.

  Notation cp_aeq := (Proper (A.aeq ==> impl)) (only parsing).
  Notation cp_sn := (@cp_sn F X R_aeq).
  Notation cp_red := (@cp_red F X R_aeq).
  Notation cp_neutral := (@cp_neutral F X R_aeq neutral).
  Notation cp := (@cp F X A.aeq R_aeq neutral).

End CP_beta_eta_rewrite.
