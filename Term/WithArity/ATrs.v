(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Adam Koprowski and Hans Zantema, 2007-03-20

rewriting
*)

Set Implicit Arguments.

From CoLoR Require Export AContext ASubstitution.
From CoLoR Require Import ARelation ListNodup LogicUtil VecUtil RelUtil
     ListUtil SN BoolUtil EqUtil NatUtil ListMax VecOrd.
From CoLoR Require ListDec.
From Coq Require Import Morphisms Max.

Section basic_definitions.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).

(***********************************************************************)
(** rules *)

  Record rule : Type := mkRule { lhs : term; rhs : term }.

  Lemma rule_eq : forall a b : rule, (lhs a = lhs b /\ rhs a = rhs b) <-> a = b.

  Proof.
    intros. destruct a. destruct b. split; intros.
    destruct H. simpl in *. subst. refl. rewrite H. simpl. auto.
  Qed.

  Definition beq_rule (a b : rule) : bool :=
    beq_term (lhs a) (lhs b) && beq_term (rhs a) (rhs b).

  Lemma beq_rule_ok : forall a b, beq_rule a b = true <-> a = b.

  Proof.
    destruct a as [a1 a2]. destruct b as [b1 b2]. unfold beq_rule. simpl.
    rewrite andb_eq, !beq_term_ok. split_all.
    subst. refl. inversion H. auto. inversion H. auto.
  Qed.

  Definition eq_rule_dec := dec_beq beq_rule_ok.

  Definition rules := list rule.

  Definition brule (f : term -> term -> bool) a := f (lhs a) (rhs a).

(***********************************************************************)
(** basic definitions and properties on rules *)

  Definition is_notvar_lhs a :=
    match lhs a with
      | Var _ => false
      | _ => true
    end.

  Lemma is_notvar_lhs_elim : forall R, forallb is_notvar_lhs R = true ->
    forall l r, In (mkRule l r) R -> exists f ts, l = Fun f ts.

  Proof.
    intros. rewrite forallb_forall in H. ded (H _ H0). destruct l. discr.
    ex f t. refl.
  Qed.

  Lemma is_notvar_lhs_false : forall R, forallb is_notvar_lhs R = true ->
    forall x r, In (mkRule (Var x) r) R -> False.

  Proof. intros. rewrite forallb_forall in H. ded (H _ H0). discr. Qed.

  Definition is_notvar_rhs a :=
    match rhs a with
      | Var _ => false
      | _ => true
    end.

  Lemma is_notvar_rhs_elim : forall R, forallb is_notvar_rhs R = true ->
    forall l r, In (mkRule l r) R -> exists f ts, r = Fun f ts.

  Proof.
    intros. rewrite forallb_forall in H. ded (H _ H0). destruct r. discr.
    ex f t. refl.
  Qed.

  Lemma is_notvar_rhs_false : forall R, forallb is_notvar_rhs R = true ->
    forall x l, In (mkRule l (Var x)) R -> False.

  Proof. intros. rewrite forallb_forall in H. ded (H _ H0). discr. Qed.

(***********************************************************************)
(** standard rewriting *)

  Section rewriting.

    Variable R : rules.

    (* standard rewrite step *)
    Definition red u v := exists l r c s,
      In (mkRule l r) R /\ u = fill c (sub s l) /\ v = fill c (sub s r).

    (* head rewrite step *)
    Definition hd_red u v := exists l r s,
      In (mkRule l r) R /\ u = sub s l /\ v = sub s r.

    (* internal rewrite step *)
    Definition int_red u v := exists l r c s, c <> Hole /\
      In (mkRule l r) R /\ u = fill c (sub s l) /\ v = fill c (sub s r).

    Definition NF u := forall v, ~red u v.

(***********************************************************************)
(** innermost rewriting *)

    Definition innermost u := forall f us, u = Fun f us -> Vforall NF us.

    Definition inner_red u v := exists l r c s,
      In (mkRule l r) R /\ u = fill c (sub s l) /\ v = fill c (sub s r)
      /\ innermost (sub s l).

    Definition inner_hd_red u v := exists l r s,
      In (mkRule l r) R /\ u = sub s l /\ v = sub s r /\ innermost u.

    Definition inner_int_red u v := exists l r c s, c <> Hole
      /\ In (mkRule l r) R /\ u = fill c (sub s l) /\ v = fill c (sub s r)
      /\ innermost (sub s l).

  End rewriting.

(***********************************************************************)
(** rewrite modulo steps *)

  Section rewriting_modulo.

    Variables (S : relation term) (E R : rules).

    (* relative rewrite step *)
    Definition red_mod := red E # @ red R.

    (* head rewrite step modulo some relation *)
    Definition hd_red_Mod := S @ hd_red R.

    (* relative head rewrite step *)
    Definition hd_red_mod := red E # @ hd_red R.

  End rewriting_modulo.

End basic_definitions.

Arguments is_notvar_lhs_elim [Sig R] _ [l r] _.
Arguments is_notvar_rhs_elim [Sig R] _ [l r] _.

(***********************************************************************)
(** basic tactic for eliminating rewriting hypotheses *)

Ltac redtac := repeat
  match goal with
    | H : red _ _ _ |- _ =>
      let l := fresh "l" in let r := fresh "r" in 
      let c := fresh "c" in let s := fresh "s" in 
      let lr := fresh "lr" in let xl := fresh "xl" in
      let yr := fresh "yr" in
        destruct H as [l [r [c [s [lr [xl yr]]]]]]
    | H : transp (red _) _ _ |- _ => unfold transp in H; redtac
    | H : hd_red _ _ _ |- _ =>
      let l := fresh "l" in let r := fresh "r" in
      let s := fresh "s" in let lr := fresh "lr" in 
      let xl := fresh "xl" in let yr := fresh "yr" in
        destruct H as [l [r [s [lr [xl yr]]]]]
    | H : transp (hd_red _) _ _ |- _ => unfold transp in H; redtac
    | H : int_red _ _ _ |- _ =>
      let l := fresh "l" in let r := fresh "r" in 
      let c := fresh "c" in let cne := fresh "cne" in
      let s := fresh "s" in  let lr := fresh "lr" in 
      let xl := fresh "xl" in let yr := fresh "yr" in
        destruct H as [l [r [c [s [cne [lr [xl yr]]]]]]]
    | H : transp (int_red _) _ _ |- _ => unfold transp in H; redtac
    | H : red_mod _ _ _ _ |- _ =>
      let t := fresh "t" in let h := fresh in
        destruct H as [t h]; destruct h; redtac
    | H : hd_red_mod _ _ _ _ |- _ =>
      let t := fresh "t" in let h := fresh in
        destruct H as [t h]; destruct h; redtac
    | H : hd_red_Mod _ _ _ _ |- _ =>
      let t := fresh "t" in let h := fresh in
        destruct H as [t h]; destruct h; redtac
  end.

(***********************************************************************)
(** monotony properties *)

#[global] Instance red_incl Sig : Proper (incl ==> inclusion) (@red Sig).

Proof. intros R R' RR' t t' tt'. redtac. ex l r c s. split_all. Qed.

#[global] Instance hd_red_incl Sig : Proper (incl ==> inclusion) (@hd_red Sig).

Proof. intros R R' RR' t t' tt'. redtac. ex l r s. split_all. Qed.

#[global] Instance red_mod_incl Sig : Proper (incl ==> incl ==> inclusion) (@red_mod Sig).

Proof. intros E E' EE' R R' RR'. unfold red_mod. rewrite EE', RR'. refl. Qed.

#[global] Instance hd_red_mod_incl Sig :
  Proper (incl ==> incl ==> inclusion) (@hd_red_mod Sig).

Proof. intros E E' EE' R R' RR'. unfold hd_red_mod. rewrite EE', RR'. refl. Qed.

#[global] Instance hd_red_Mod_incl Sig :
  Proper (inclusion ==> incl ==> inclusion) (@hd_red_Mod Sig).

Proof. intros S S' SS' R R' RR'. unfold hd_red_Mod. rewrite SS', RR'. refl. Qed.

(***********************************************************************)
(** basic properties *)

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).
  Notation rule := (rule Sig). Notation rules := (list rule).

  Section rewriting.

    Variable R R' : rules.

    Lemma red_rule : forall l r c s, In (mkRule l r) R ->
      red R (fill c (sub s l)) (fill c (sub s r)).

    Proof. intros. unfold red. ex l r c s. auto. Qed.

    Lemma red_empty : forall t u : term, red nil # t u -> t = u.

    Proof. intros. induction H. redtac. contr. refl. congruence. Qed.

    Lemma red_rule_top : forall l r s,
      In (mkRule l r) R -> red R (sub s l) (sub s r).

    Proof. intros. unfold red. ex l r (@Hole Sig) s. auto. Qed.

    Lemma hd_red_rule : forall l r s,
      In (mkRule l r) R -> hd_red R (sub s l) (sub s r).

    Proof. intros. unfold hd_red. ex l r s. auto. Qed.

    Lemma red_fill : forall t u c, red R t u -> red R (fill c t) (fill c u).

    Proof.
      intros. redtac. unfold red.
      ex l r (AContext.comp c c0) s. split. hyp.
      subst t. subst u. rewrite !fill_fill. auto.
    Qed.

    Lemma context_closed_red : context_closed (red R).

    Proof. intros t u c h. apply red_fill. hyp. Qed.

    Lemma red_sub : forall t u s, red R t u -> red R (sub s t) (sub s u).

    Proof.
      intros. redtac. subst. rewrite !sub_fill, !sub_sub. apply red_rule. hyp.
    Qed.

    Lemma red_subterm : forall u u' t, red R u u' -> subterm_eq u t
      -> exists t', red R t t' /\ subterm_eq u' t'.

    Proof.
      unfold subterm_eq. intros. destruct H0 as [d]. subst t. redtac. subst u.
      subst u'. exists (fill (AContext.comp d c) (sub s r)). split.
      ex l r (AContext.comp d c) s. split. hyp.
      rewrite fill_fill. auto. exists d. rewrite fill_fill. refl.
    Qed.

    Lemma int_red_fun : forall f ts v, int_red R (Fun f ts) v
      -> exists i (vi : terms i) t j (vj : terms j) h t',
        ts = Vcast (Vapp vi (Vcons t vj)) h
        /\ v = Fun f (Vcast (Vapp vi (Vcons t' vj)) h) /\ red R t t'.

    Proof.
      intros. redtac. destruct c. absurd (@Hole Sig = Hole); auto. simpl in xl.
      Funeqtac. ex i t (fill c (sub s l)) j t0 e (fill c (sub s r)).
      split. hyp. split. hyp. unfold red. ex l r c s. auto.
    Qed.

    Lemma red_swap : red (R ++ R') << red (R' ++ R).

    Proof.
      intros x y RR'xy. redtac. ex l r c s. repeat split; auto.
      destruct (in_app_or lr); apply in_or_app; auto.
    Qed.

    Lemma hd_red_swap : hd_red (R ++ R') << hd_red (R' ++ R).

    Proof.
      intros x y RR'xy. redtac. ex l r s. repeat split; auto.
      destruct (in_app_or lr); auto with datatypes.
    Qed.

    Lemma int_red_incl_red : int_red R << red R.

    Proof.
      unfold inclusion, int_red. intros. decomp H. subst x. subst y.
      apply red_rule. hyp.
    Qed.

    Lemma hd_red_incl_red : hd_red R << red R.

    Proof.
      unfold inclusion. intros. redtac. subst x. subst y. apply red_rule_top.
      hyp.
    Qed.

    Lemma WF_red_empty : WF (red (@nil rule)).

    Proof. intro x. apply SN_intro. intros y Exy. redtac. contr. Qed.

    Lemma hd_red_mod_incl_red_mod : forall E, hd_red_mod E R << red_mod E R.

    Proof. intro. unfold hd_red_mod, red_mod. comp. apply hd_red_incl_red. Qed.

    Lemma int_red_preserve_hd : forall u v, int_red R u v ->
      exists f us vs, u = Fun f us /\ v = Fun f vs.

    Proof.
      intros. do 5 destruct H. intuition. destruct x1. congruence.
      simpl in *. ex f
        (Vcast (Vapp t (Vcons (fill x1 (sub x2 x)) t0)) e)
        (Vcast (Vapp t (Vcons (fill x1 (sub x2 x0)) t0)) e). tauto.
    Qed.

    Lemma int_red_rtc_preserve_hd : forall u v, int_red R # u v ->
      u=v \/ exists f us vs, u = Fun f us /\ v = Fun f vs.

    Proof.
      intros. induction H; auto.
      right. apply int_red_preserve_hd. auto.
      destruct IHclos_refl_trans1; destruct IHclos_refl_trans2; subst; auto.
      right. do 3 destruct H1. do 3 destruct H2. split_all. subst.
      Funeqtac. subst. ex x0 x1 x5. auto.
    Qed.

    Lemma red_case : forall t u, red R t u -> hd_red R t u
      \/ exists f ts i (p : i < arity f) u',
        t = Fun f ts /\ red R (Vnth ts p) u' /\ u = Fun f (Vreplace ts p u').

    Proof.
      intros. redtac. destruct c.
      (* Hole *)
      left. subst. simpl. apply hd_red_rule. hyp.
      (* Cont *)
      right. ex f (Vcast (Vapp t0 (Vcons (fill c (sub s l)) t1)) e) i.
      assert (p : i<arity f). lia. ex p (fill c (sub s r)).
      subst. simpl. split_all. rewrite Vnth_cast, Vnth_app.
      destruct (le_gt_dec i i). 2: lia. rewrite Vnth_cons_head.
      apply red_rule. hyp. lia.
      apply args_eq. apply Veq_nth; intros. rewrite Vnth_cast, Vnth_app.
      destruct (le_gt_dec i i0).
      (* 1) i <= i0 *)
      destruct (eq_nat_dec i i0).
      (* a) i = i0 *)
      subst i0. rewrite Vnth_cons_head, Vnth_replace. refl. lia.
      (* b) i <> i0 *)
      rewrite Vnth_replace_neq. 2: hyp. rewrite Vnth_cast, Vnth_app.
      destruct (le_gt_dec i i0). 2: lia. assert (l0=l1).
      apply le_unique.
      subst l1. rewrite !Vnth_cons. destruct (lt_ge_dec 0 (i0-i)).
      apply Vnth_eq. refl. lia.
      (* 2) i > i0 *)
      rewrite Vnth_replace_neq. 2: lia. rewrite Vnth_cast, Vnth_app.
      destruct (le_gt_dec i i0). lia. apply Vnth_eq. refl.
    Qed.

    Lemma red_split : forall t u, red R t u -> hd_red R t u \/ int_red R t u.

    Proof.
      intros t u tu. redtac. destruct c; subst.
      left. apply hd_red_rule. hyp.
      right. ex l r (Cont f e t0 c t1) s. split_all. discr.
    Qed.

  End rewriting.

(***********************************************************************)
(** preservation of variables under reduction *)

  Definition rules_preserve_vars (R : rules) :=
    forall l r, In (mkRule l r) R -> vars r [= vars l.

  Definition brules_preserve_vars (R : rules) :=
    forallb (fun x => ListDec.incl beq_nat (vars (rhs x)) (vars (lhs x))) R.

  Lemma brules_preserve_vars_ok :
    forall R, brules_preserve_vars R = true <-> rules_preserve_vars R.

  Proof.
    intro R. unfold rules_preserve_vars, brules_preserve_vars.
    rewrite forallb_forall. split.
    intros h l r hlr. rewrite <- ListDec.incl_ok, <- (h _ hlr). refl.
    apply beq_nat_ok.
    intros h [l r] hlr. rewrite ListDec.incl_ok. apply h. hyp. apply beq_nat_ok.
  Qed.

  Lemma rules_preserve_vars_cons : forall a R, rules_preserve_vars (a :: R)
    <-> vars (rhs a) [= vars (lhs a) /\ rules_preserve_vars R.

  Proof.
    unfold rules_preserve_vars. split_all. apply H. left. destruct a. refl. fo.
    simpl in H0. destruct H0. subst. hyp. apply H1. hyp.
  Qed.

  Section vars.

    Variables (R : rules) (hyp : rules_preserve_vars R).

    Lemma red_preserve_vars : preserve_vars (red R).

    Proof.
      unfold preserve_vars. intros. redtac. subst t. subst u.
      trans (cvars c ++ vars (sub s r)). apply vars_fill_elim.
      trans (cvars c ++ vars (sub s l)). apply appl_incl.
      apply incl_vars_sub. apply hyp. hyp.
      apply vars_fill_intro.
    Qed.

    Lemma tred_preserve_vars : preserve_vars (red R !).

    Proof.
      unfold preserve_vars. induction 1. apply red_preserve_vars. hyp.
      trans (vars y); hyp.
    Qed.

    Lemma rtred_preserve_vars : preserve_vars (red R #).

    Proof.
      unfold preserve_vars. induction 1. apply red_preserve_vars. hyp.
      refl. trans (vars y); hyp.
    Qed.

    Lemma red_maxvar : forall t u, red R t u -> maxvar u <= maxvar t.

    Proof.
      intros. rewrite !maxvar_lmax. apply incl_lmax.
      apply red_preserve_vars. hyp.
    Qed.

    Lemma red_maxvar0 : forall t u, maxvar t = 0 -> red R t u -> maxvar u = 0.

    Proof.
      intros. cut (maxvar u <= maxvar t). lia. apply red_maxvar. hyp.
    Qed.

    Lemma rtc_red_maxvar : forall t u, red R # t u -> maxvar u <= maxvar t.

    Proof. induction 1. apply red_maxvar. hyp. lia. lia. Qed.

    Lemma rtc_red_maxvar0 : forall t u,
      maxvar t = 0 -> red R # t u -> maxvar u = 0.

    Proof.
      intros. cut (maxvar u <= maxvar t). lia. apply rtc_red_maxvar. hyp.
    Qed.

  End vars.

  Section red_mod.

    Variables (E R : rules)
      (hE : rules_preserve_vars E) (hR : rules_preserve_vars R).

    Lemma red_mod_maxvar : forall t u, red_mod E R t u -> maxvar u <= maxvar t.

    Proof.
      intros. do 2 destruct H. trans (maxvar x).
      apply (red_maxvar hR H0). apply (rtc_red_maxvar hE H).
    Qed.

    Lemma red_mod_maxvar0 : forall t u,
      maxvar t = 0 -> red_mod E R t u -> maxvar u = 0.

    Proof.
      intros. cut (maxvar u <= maxvar t). lia. apply red_mod_maxvar. hyp.
    Qed.

  End red_mod.

  Lemma rules_preserve_vars_incl : forall R S : rules,
    R [= S -> rules_preserve_vars S -> rules_preserve_vars R.

  Proof. fo. Qed.

(***********************************************************************)
(** biggest variable in a list of rules *)

  Definition maxvar_rule (a : rule) :=
    let (l,r) := a in max (maxvar l) (maxvar r).

  Definition fold_max m a := max m (maxvar_rule a).

  Definition maxvar_rules R := fold_left fold_max R 0.

  Lemma maxvar_rules_init : forall R x, fold_left fold_max R x >= x.

  Proof. induction R; simpl; intros. refl. rewrite IHR. apply le_max_l. Qed.

  Lemma maxvar_rules_init_mon : forall R x y,
    x >= y -> fold_left fold_max R x >= fold_left fold_max R y.

  Proof.
    induction R; simpl; intros. hyp. apply IHR. unfold fold_max.
    apply max_ge_compat. hyp. refl.
  Qed.

  Notation rule_dec := (dec_beq (@beq_rule_ok Sig)).
  Notation remove := (remove rule_dec).

  Lemma maxvar_rules_remove : forall a R x y,
    x >= y -> fold_left fold_max R x >= fold_left fold_max (remove a R) y.

  Proof.
    induction R; simpl; intros. hyp. case (rule_dec a0 a); intro. subst a0.
    apply IHR. trans x. apply le_max_l. hyp.
    simpl. apply IHR. apply max_ge_compat. hyp. refl.
  Qed.

  Lemma maxvar_rules_elim : forall a R n,
    In a R -> n > maxvar_rules R -> n > maxvar_rule a.

  Proof.
    unfold maxvar_rules. induction R; simpl; split_all. subst.
    unfold fold_max in H0. simpl in H0. fold fold_max in H0.
    apply le_lt_trans with (fold_left fold_max R (fold_max 0 a)).
    apply maxvar_rules_init. hyp.
    apply IHR. hyp. apply le_lt_trans
    with (fold_left fold_max R (fold_max 0 a0)).
    apply maxvar_rules_init_mon. apply le_max_l. hyp.
  Qed.

(***********************************************************************)
(** rewriting vectors of terms *)

  Section vector.

    Variable R : rules.

    Lemma Vgt_prod_fun : forall f ts ts',
      Vrel1 (red R) ts ts' -> int_red R (Fun f ts) (Fun f ts').

    Proof.
      intros. ded (Vrel1_app_impl H). do 8 destruct H0. destruct H1. redtac.
      subst x1. subst x5. unfold transp, int_red. rewrite H0, H1.
      ex l r (Cont f x4 x0 c x3) s. split. discr. auto.
    Qed.

  End vector.

(***********************************************************************)
(** union of rewrite rules *)

  Section union.

    Variables R R' : rules.

    Lemma red_union : red (R ++ R') << red R U red R'.

    Proof.
      unfold inclusion. intros. redtac. subst x. subst y.
      destruct (in_app_or lr).
      left. apply red_rule. hyp. 
      right. apply red_rule. hyp.
    Qed.

    Lemma red_union_inv : red R U red R' << red (R ++ R').

    Proof.
      intros x y RR'xy.
      destruct RR'xy as [Rxy | Rxy];
        destruct Rxy as [rl [rr [c [s [Rr [dx dy]]]]]]; 
          subst x; subst y; ex rl rr c s; intuition.
    Qed.

    Lemma hd_red_union : hd_red (R ++ R') << hd_red R U hd_red R'.

    Proof.
      unfold inclusion. intros. redtac. subst x. subst y.
      destruct (in_app_or lr).
      left. apply hd_red_rule. hyp. 
      right. apply hd_red_rule. hyp.
    Qed.

    Lemma hd_red_union_inv : hd_red R U hd_red R' << hd_red (R ++ R').

    Proof.
      intros x y RR'xy.
      destruct RR'xy as [Rxy | Rxy];
        destruct Rxy as [rl [rr [s [Rr [dx dy]]]]]; 
          subst x; subst y; ex rl rr s; intuition.
    Qed.

  End union.

(***********************************************************************)
(** properties of rewriting modulo *)

  Section rewriting_modulo_results.

    Variables (S S' : relation term) (E E' R R' : rules).

    Lemma hd_red_mod_of_hd_red_Mod_int :
      hd_red_Mod (int_red E #) R << hd_red_mod E R.

    Proof.
      unfold hd_red_Mod, hd_red_mod.
      apply compose_incl. assert (int_red E # << red E #).
      apply rtc_incl. apply int_red_incl_red. eauto. refl.
    Qed.

    Lemma hd_red_mod_of_hd_red_Mod : hd_red_Mod (red E #) R << hd_red_mod E R.

    Proof. unfold hd_red_Mod, hd_red_mod. refl. Qed.

    Lemma hd_red_Mod_remdup :
      hd_red_Mod S R << hd_red_Mod S (remdup (@eq_rule_dec Sig) R).

    Proof.
      intros. unfold hd_red_Mod. comp. unfold inclusion. intros. redtac.
      ex l r s. split_all. apply incl_remdup. auto.
    Qed.

    Lemma hd_red_mod_remdup :
      hd_red_mod E R << hd_red_mod E (remdup (@eq_rule_dec Sig) R).

    Proof.
      intros. unfold hd_red_mod. comp. unfold inclusion. intros. redtac.
      ex l r s. split_all. apply incl_remdup. auto.
    Qed.

    Lemma red_mod_empty_incl_red : red_mod nil R << red R.

    Proof.
      intros u v Ruv. destruct Ruv as [s' [ss' Ruv]].
      rewrite (red_empty ss'). hyp.
    Qed.

    Lemma red_mod_empty : red_mod nil R == red R.

    Proof.
      split. apply red_mod_empty_incl_red. intros t u h. exists t. split.
      apply rtc_refl. hyp.
    Qed.

    Lemma hd_red_mod_empty_incl_hd_red : hd_red_mod nil R << hd_red R.

    Proof.
      unfold inclusion. intros. do 2 destruct H. ded (red_empty H). subst x0.
      exact H0.
    Qed.

    Lemma WF_red_mod_empty : WF (red_mod E nil).

    Proof.
      intro x. apply SN_intro. intros y Exy. destruct Exy as [z [xz zy]].
      redtac. contr.
    Qed.

    Lemma WF_hd_red_mod_empty : WF (hd_red_mod E nil).

    Proof.
      apply WF_incl with (red_mod E nil).
      apply hd_red_mod_incl_red_mod. apply WF_red_mod_empty.
    Qed.

    Lemma WF_hd_red_Mod_empty : WF (hd_red_Mod S nil).

    Proof.
      apply WF_incl with empty_rel. intros x y h. redtac. contr.
      apply WF_empty_rel.
    Qed.

    Lemma red_mod_fill : forall t u c,
      red_mod E R t u -> red_mod E R (fill c t) (fill c u).

    Proof.
      intros. do 2 destruct H. exists (fill c x); split.
      apply context_closed_rtc. unfold context_closed. apply red_fill. hyp.
      apply red_fill. hyp.
    Qed.

    Lemma context_closed_red_mod : context_closed (red_mod E R).

    Proof. intros t u c h. apply red_mod_fill. hyp. Qed.

    Lemma red_mod_sub : forall t u s,
      red_mod E R t u -> red_mod E R (sub s t) (sub s u).

    Proof.
      intros. do 2 destruct H. exists (sub s x); split.
      apply substitution_closed_rtc. unfold substitution_closed. apply red_sub.
      hyp. apply red_sub. hyp.
    Qed.

  End rewriting_modulo_results.

(***********************************************************************)
(** termination as special case of relative termination *)

  Section termination_as_relative_term.

    Variable R R' : rules.

    Lemma red_incl_red_mod : red R << red_mod nil R.

    Proof. intros u v Ruv. exists u. split. constructor 2. hyp. Qed.

    Lemma hd_red_incl_hd_red_mod : hd_red R << hd_red_mod nil R.

    Proof. intros u v Ruv. exists u. split. constructor 2. hyp. Qed.

  End termination_as_relative_term.

(***********************************************************************)
(** union of rewrite rules modulo *)

  Section union_modulo.

    Variables (S : relation term) (E R R' : rules).

    Lemma red_mod_union : red_mod E (R ++ R') << red_mod E R U red_mod E R'.

    Proof.
      unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
      destruct (in_app_or lr).
      left. exists (fill c (sub s l)); split. hyp. apply red_rule. hyp.
      right. exists (fill c (sub s l)); split. hyp. apply red_rule. hyp.
    Qed.

    Lemma hd_red_Mod_union :
      hd_red_Mod S (R ++ R') << hd_red_Mod S R U hd_red_Mod S R'.

    Proof.
      unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
      destruct (in_app_or lr).
      left. exists (sub s l); split. hyp. apply hd_red_rule. hyp.
      right. exists (sub s l); split. hyp. apply hd_red_rule. hyp.
    Qed.

    Lemma hd_red_mod_union :
      hd_red_mod E (R ++ R') << hd_red_mod E R U hd_red_mod E R'.

    Proof.
      unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
      destruct (in_app_or lr).
      left. exists (sub s l); split. hyp. apply hd_red_rule. hyp.
      right. exists (sub s l); split. hyp. apply hd_red_rule. hyp.
    Qed.

  End union_modulo.

(***********************************************************************)
(** rewriting is invariant under rule renamings *)

  Definition sub_rule s (a : rule) := mkRule (sub s (lhs a)) (sub s (rhs a)).

  Definition sub_rules s := map (sub_rule s).

  Section rule_renaming.

    Variable s1 s2 : @substitution Sig.
    Variable hyp : forall x, sub s1 (sub s2 (Var x)) = Var x.

    Lemma sub_rule_inv : forall x, sub_rule s1 (sub_rule s2 x) = x.

    Proof.
      intros [l r]. unfold sub_rule. simpl. rewrite !sub_inv. refl. hyp. hyp.
    Qed.

    Lemma sub_rules_inv : forall x, sub_rules s1 (sub_rules s2 x) = x.

    Proof.
      induction x. refl. simpl. rewrite sub_rule_inv, IHx. refl.
    Qed.

    Lemma red_ren : forall R, red R << red (map (sub_rule s2) R).

    Proof.
      intros R t u h. redtac. subst.
      rewrite <- (sub_inv hyp l), <- (sub_inv hyp r), sub_sub,
        sub_sub with (s1:=s) (s2:=s1). apply red_rule.
      change (In (sub_rule s2 (mkRule l r)) (map (sub_rule s2) R)).
      apply in_map. hyp.
    Qed.

  End rule_renaming.

(***********************************************************************)
(** internal reduction in some specific subterm *)

  Definition int_red_pos_at (R : rules) i t u :=
    exists f (h : i < arity f) ts, t = Fun f ts
      /\ exists v, red R (Vnth ts h) v /\ u = Fun f (Vreplace ts h v).

  Definition int_red_pos R t u := exists i, int_red_pos_at R i t u.

  Lemma int_red_pos_eq : forall R, int_red_pos R == int_red R.

  Proof.
    intro R. split; intros t u tu.
    (* -> *)
    destruct tu as [i [f [hi [ts [e [v [h1 h2]]]]]]].
    redtac. subst. ex l r.
    (* context *)
    assert (l1 : 0 + i <= arity f). lia. set (v1 := Vsub ts l1).
    assert (l2 : S i + (arity f - S i) <= arity f). lia.
    set (v2 := Vsub ts l2).
    assert (l3 : i + S (arity f - S i) = arity f). lia.
    ex (Cont f l3 v1 c v2) s. split_all. discr.
    (* lhs *)
    simpl. apply args_eq. apply Veq_nth. intros j hj.
    rewrite Vnth_cast, Vnth_app. destruct (le_gt_dec i j).
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (j-i)).
    unfold v2. rewrite Vnth_sub. apply Vnth_eq. clear -l4; lia.
    assert (j=i). clear -l0 g; lia. subst. rewrite (lt_unique _ hi). hyp.
    unfold v1. rewrite Vnth_sub. apply Vnth_eq. refl.
    (* rhs *)
    simpl. apply args_eq. apply Veq_nth. intros j hj.
    rewrite Vnth_cast, Vnth_app. destruct (le_gt_dec i j).
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (j-i)).
    rewrite Vnth_replace_neq. 2: clear -l4; lia. unfold v2. rewrite Vnth_sub.
    apply Vnth_eq. clear -l4; lia.
    assert (j=i). clear -l0 g; lia. subst. apply Vnth_replace.
    rewrite Vnth_replace_neq. 2: clear -g; lia. unfold v1. rewrite Vnth_sub.
    apply Vnth_eq. refl.
    (* <- *)
    redtac. subst. destruct c. cong. ex i f.
    assert (hi : i < arity f). lia. exists hi.
    simpl. exists (Vcast (Vapp t (Vcons (fill c (sub s l)) t0)) e).
    split_all. exists (fill c (sub s r)). split.
    rewrite Vnth_cast, Vnth_app. destruct (le_gt_dec i i).
    rewrite Vnth_cons. destruct (lt_ge_dec 0 (i-i)). lia.
    apply red_rule. hyp. lia.
    apply args_eq. apply Veq_nth. intros k hk.
    rewrite Vnth_cast, Vnth_app. case_eq (le_gt_dec i k); intros l0 H.
    rewrite Vnth_cons. case_eq (lt_ge_dec 0 (k-i)); intros l1 H0.
    rewrite Vnth_replace_neq, Vnth_cast, Vnth_app, H, Vnth_cons, H0.
    refl. lia.
    assert (k=i). lia. subst. sym. apply Vnth_replace.
    rewrite Vnth_replace_neq, Vnth_cast, Vnth_app, H. refl. lia.
  Qed.

(***********************************************************************)
(** minimal (wrt subterm ordering) non-terminating terms *)

  Definition min R t := forall u : term, subterm u t -> ~NT R u.

  Definition NT_min R t := NT R t /\ min R t.

  Lemma min_eq : forall R t, min (red R) t <->
    (forall f ts, t = Fun f ts -> Vforall (fun u => ~NT (red R) u) ts).

  Proof.
    intros R t. split.
    (* -> *)
    intros ht f ts e. apply Vforall_intro. intros u hu.
    apply ht. subst. apply subterm_fun. hyp.
    (* <- *)
    intros h u ut hu. destruct ut as [c [hc e]]. destruct c. cong.
    clear hc. simpl in e.
    set (ts := Vcast (Vapp t0 (Vcons (fill c u) t1)) e0). fold ts in e.
    ded (h f ts e).
    assert (Vin (fill c u) ts). unfold ts. rewrite Vin_cast.
    apply Vin_app_cons.
    assert (NT (red R) (fill c u)). destruct hu as [g [g0 hg]].
    exists (fun k => fill c (g k)). rewrite g0. split_all.
    intro k. apply red_fill. apply hg.
    ded (Vforall_in H H0). contr.
  Qed.

  Lemma int_red_min : forall R t u,
    int_red R t u -> min (red R) t -> min (red R) u.

  Proof.
    intros R t u tu. rewrite !min_eq. intros ht f us hu.
    apply Vforall_intro. intros v hv.
    apply int_red_pos_eq in tu.
    destruct tu as [i [f' [hi [ts [hts [w [h1 h2]]]]]]]. ded (ht _ _ hts).
    clear ht. subst. Funeqtac. subst. destruct (Vin_nth hv) as [j [hj e]].
    clear hv. destruct (eq_nat_dec j i); subst.
    (* j = i *)
    rewrite Vnth_replace. intro hw.
    assert (NT (red R) (Vnth ts hi)). eapply red_NT. apply h1. hyp.
    ded (Vforall_nth hi H). contr.
    (* j <> i *)
    rewrite Vnth_replace_neq. 2: lia. intro hv.
    ded (Vforall_nth hj H). contr.
  Qed.

  Lemma int_red_rtc_min : forall R t u,
    int_red R # t u -> min (red R) t -> min (red R) u.

  Proof.
    induction 1; intro hx. eapply int_red_min. apply H. hyp. hyp.
    apply IHclos_refl_trans2. apply IHclos_refl_trans1. hyp.
  Qed.

(***********************************************************************)
(** minimal infinite rewrite sequences modulo: two functions [f] and
[g] describing an infinite sequence of head [D]-steps modulo arbitrary
internal [R]-steps is minimal if:
- every rule of [D] is applied infinitely often
- the strict subterms of this rewrite sequence terminate wrt [R] *)

  (* strict subterms terminate wrt [R] *)
  Definition Min R (f : nat -> term) :=
    forall i x, subterm x (f i) -> forall g, g 0 = x -> ~IS R g.

  (* every rule of [D] is applied infinitely often *)
  Definition InfRuleApp (D : rules) f g :=
    forall d, In d D -> exists h : nat -> nat,
      forall j, h j < h (S j) /\ hd_red (d :: nil) (g (h j)) (f (S (h j))).

  Definition ISModMin (R D : rules) f g :=
    ISMod (int_red R #) (hd_red D) f g
    /\ InfRuleApp D f g /\ Min (red R) f /\ Min (red R) g.

End S.

Arguments int_red_fun [Sig R f ts v] _.

(***********************************************************************)
(** tactics *)

Ltac is_var_lhs := cut False;
  [tauto | eapply is_notvar_lhs_false; ehyp].

Ltac is_var_rhs := cut False;
  [tauto | eapply is_notvar_rhs_false; ehyp].

Ltac incl_rule Sig := ListDec.incl (@beq_rule_ok Sig).

Ltac set_Sig_to x :=
  match goal with
  | |- WF (@hd_red_Mod ?S _ _) => set (x := S)
  | |- WF (@hd_red_mod ?S _ _) => set (x := S)
  end.

Ltac set_rules_to x :=
  match goal with
  | |- WF (hd_red_Mod _ ?R) => set (x := R)
  | |- WF (hd_red_mod _ ?R) => set (x := R)
  | |- WF (red_mod _ ?R) => set (x := R)
  | |- WF (red ?R) => set (x := R)
  end.

Ltac set_mod_rules_to x :=
  match goal with
  | |- WF (hd_red_mod ?E _) => set (x := E)
  end.

Ltac set_Mod_to x :=
  match goal with
  | |- WF (hd_red_Mod ?S _) => set (x := S)
  | |- WF (hd_red_mod ?E _) => set (x := red E #)
  end.

Ltac hd_red_mod :=
  match goal with
  | |- WF (hd_red_Mod _ _) =>
    eapply WF_incl;
    [(apply hd_red_mod_of_hd_red_Mod || apply hd_red_mod_of_hd_red_Mod_int)
      | idtac]
  | |- WF (hd_red_mod _ _) => idtac
  end.

Ltac termination_trivial :=
  let R := fresh in set_rules_to R; norm R;
  (apply WF_hd_red_mod_empty || apply WF_red_mod_empty || apply WF_red_empty).

Ltac remove_relative_rules E := norm E; rewrite red_mod_empty
  || fail "this certificate cannot be applied on a relative system".

Ltac no_relative_rules :=
  match goal with
    | |- WF (red_mod ?E _) => remove_relative_rules E
    | |- EIS (red_mod ?E _) => remove_relative_rules E
    | |- _ => idtac
  end.

Ltac norm_rules := match goal with |- forallb _ ?R = _ => norm R end.

Ltac get_rule :=
  match goal with |- forallb ?f ?l = _ =>
    match l with context C [ @mkRule ?S ?l ?r] =>
      let x := fresh "r" in set (x := @mkRule S l r);
        let y := fresh "b" in set (y := f x); norm_in y (f x) end end.

Ltac init := set(r:=0); set(r0:=0); set(b:=0); set(b0:=0).

Ltac get_rules := norm_rules; repeat get_rule.
