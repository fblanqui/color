(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-10-14

conversion of a TRS with unary symbols only into an SRS
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil RelUtil SN ListUtil Srs ATrs AUnary VecUtil
     EqUtil NatUtil ListMax.

Section S.

(***********************************************************************)
(** term signature *)

  Variable ASig : Signature.

  Notation term := (term ASig). Notation context := (context ASig).
  Notation rule := (rule ASig). Notation rules := (list rule).

  Variable is_unary_sig : is_unary ASig.

  Notation Fun1 := (Fun1 is_unary_sig). Notation Cont1 := (Cont1 is_unary_sig).
  Notation cont := (cont is_unary_sig). Notation red1 := (red1 is_unary_sig).
  Notation term_ind_forall := (term_ind_forall is_unary_sig).

(***********************************************************************)
(** corresponding string signature *)

  Definition SSig_of_ASig := VSignature.mkSignature (@beq_symb_ok ASig).

  Notation SSig := SSig_of_ASig. Notation string := (string SSig).
  Notation srule := (Srs.rule SSig).

(***********************************************************************)
(** conversion term <-> string *)

  Fixpoint term_of_string (s : string) : term :=
    match s with
      | List.nil => Var 0
      | a :: w => Fun1 a (term_of_string w)
    end.

  Lemma var_term_of_string : forall s, var (term_of_string s) = 0.

  Proof. induction s. refl. simpl term_of_string. rewrite var_fun1. hyp. Qed.

  Fixpoint string_of_term (t : term) : string :=
    match t with
      | Var _ => List.nil
      | Fun f ts => f :: Vmap_first List.nil string_of_term ts
    end.

  Lemma string_of_term_fun1 : forall f t,
    string_of_term (Fun1 f t) = f :: string_of_term t.

  Proof.
    intros. unfold AUnary.Fun1. unfold string_of_term; fold string_of_term.
    rewrite Vmap_first_cast. refl.
  Qed.

  Lemma string_of_term_epi : forall s, string_of_term (term_of_string s) = s.

  Proof.
    induction s; intros. refl. simpl term_of_string.
    rewrite string_of_term_fun1, IHs. refl.
  Qed.

  Lemma term_of_string_epi : forall t, maxvar t = 0 ->
    term_of_string (string_of_term t) = t.

  Proof.
    intro t; pattern t; apply term_ind_forall; clear t.
    simpl in *. intros. subst. refl.
    intros f t IH. rewrite maxvar_fun1. intro.
    rewrite string_of_term_fun1. simpl. rewrite IH. refl. hyp.
  Qed.

  Arguments term_of_string_epi [t] _.

  Lemma string_of_term_sub : forall s l,
    string_of_term (sub s l) = string_of_term l ++ string_of_term (s (var l)).

  Proof.
    intro s. apply term_ind_forall. refl. intros f t IH.
    rewrite sub_fun1, !string_of_term_fun1, IH, var_fun1. refl.
  Qed.

(***********************************************************************)
(** conversion context <-> string *)

  Fixpoint string_of_cont (c : context) : string :=
    match c with
      | Hole => List.nil
      | @Cont _ f _ _ _ _ d _ => f :: string_of_cont d
    end.

  Lemma string_of_cont_cont : forall t,
    string_of_cont (cont t) = string_of_term t.

  Proof.
    apply term_ind_forall. refl. intros f t IH.
    rewrite string_of_term_fun1, cont_fun1. simpl. rewrite IH. refl.
  Qed.

  Lemma string_of_cont_comp : forall c d,
    string_of_cont (comp c d) = string_of_cont c ++ string_of_cont d.

  Proof. induction c; simpl; intros. refl. rewrite IHc. refl. Qed.

  Lemma string_of_term_fill : forall t c,
    string_of_term (fill c t) = string_of_cont c ++ string_of_term t.

  Proof.
    induction c. refl. simpl. rewrite Vmap_first_cast. arity1 is_unary_sig.
    simpl. rewrite IHc. refl.
  Qed.

  Fixpoint cont_of_string (s : string) : context :=
    match s with
      | List.nil => Hole
      | f :: s' => Cont1 f (cont_of_string s')
    end.

(***********************************************************************)
(** conversion string <-> substitution *)

  Definition sub_of_string s := single 0 (term_of_string s).

  Lemma term_of_string_fill : forall c s,
    term_of_string (SContext.fill c s) = fill (cont_of_string (lft c))
    (sub (sub_of_string (rgt c)) (term_of_string s)).

  Proof.
    intros [l r] s. elim l. unfold SContext.fill. simpl.
    elim s. refl. intros. simpl term_of_string. rewrite H, sub_fun1.
    refl.
    unfold SContext.fill. simpl lft. simpl rgt. intros. simpl term_of_string.
    simpl cont_of_string. rewrite fill_cont1. apply args_eq.
    apply Vcast_eq_intro.
    apply Vcons_eq_intro. 2: refl. hyp.
  Qed.

(***********************************************************************)
(** rules *)

  Definition srule_of_rule (x : rule) :=
    Srs.mkRule (string_of_term (lhs x)) (string_of_term (rhs x)).

  Definition srs_of_trs := List.map srule_of_rule.

(***********************************************************************)
(** invariance under reset *)

  Lemma string_of_term_reset :
    forall t, string_of_term (reset t) = string_of_term t.

  Proof.
    intro t; pattern t; apply term_ind_forall; clear t; intros; unfold reset.
    simpl. unfold swap, single. rewrite (beq_refl beq_nat_ok). refl.
    rewrite sub_fun1, !string_of_term_fun1, var_fun1. fold (reset t).
    rewrite H. refl.
  Qed.

  Lemma srule_of_rule_reset :
    forall a, srule_of_rule (reset_rule a) = srule_of_rule a.

  Proof.
    intros [l r]. unfold srule_of_rule, reset_rule. simpl.
    rewrite !string_of_term_reset. refl.
  Qed.

  Lemma srs_of_trs_reset : forall R, srs_of_trs (reset_rules R) = srs_of_trs R.

  Proof.
    unfold srs_of_trs, reset_rules. induction R; simpl; intros. refl.
    rewrite IHR, srule_of_rule_reset. refl.
  Qed.

  Section reset.

    Variables (R : rules) (h1 : rules_preserve_vars R)
      (h2 : forall l r, List.In (mkRule l r) R -> maxvar l = 0).

    Lemma red_of_sred_reset : forall t u,
      Srs.red (srs_of_trs R) t u -> red R (term_of_string t) (term_of_string u).

    Proof.
      intros. Srs.redtac. subst. rewrite !term_of_string_fill.
      destruct (in_map_elim H). destruct H0. destruct x as [l' r'].
      unfold srule_of_rule in H1. simpl in H1. inversion H1.
      rewrite !term_of_string_epi. 3:{ eapply h2. apply H0. }
      2:{ ded (h2 _ _ H0). cut (maxvar r' <= maxvar l'). lia.
      rewrite !maxvar_lmax. apply incl_lmax. apply h1. hyp. }
      apply red_rule. hyp.
    Qed.

  End reset.

(***********************************************************************)
(** rewriting *)

  Section sred_of_red.

    Variables (R : rules) (hR : rules_preserve_vars R).

    Lemma sred_of_red : forall t u,
      red R t u -> Srs.red (srs_of_trs R) (string_of_term t) (string_of_term u).

    Proof.
      intros. rewrite (red1_ok is_unary_sig hR) in H. destruct H. decomp H.
      rewrite H0; clear H0. rewrite H3; clear H3.
      rewrite !string_of_term_fill, !string_of_cont_comp, !string_of_cont_cont.
      simpl. rewrite !app_nil_r.
      set (c := SContext.mkContext (string_of_cont x1) (string_of_cont x2)).
      change (Srs.red (srs_of_trs R) (SContext.fill c (string_of_term x))
        (SContext.fill c (string_of_term x0))). apply Srs.red_rule. clear c.
      change (List.In (srule_of_rule (mkRule x x0)) (srs_of_trs R)).
      apply in_map. hyp.
    Qed.

    Lemma rtc_sred_of_red : forall t u, red R # t u ->
      Srs.red (srs_of_trs R) # (string_of_term t) (string_of_term u).

    Proof.
      induction 1. apply rt_step. apply sred_of_red. hyp.
      apply rt_refl. apply rt_trans with (string_of_term y); hyp.
    Qed.

    Lemma red_of_sred : forall t u,
      Srs.red (srs_of_trs R) t u -> red R (term_of_string t) (term_of_string u).

    Proof.
      intros. rewrite red_reset. apply red_of_sred_reset.
      apply rules_preserve_vars_reset. hyp. intros. destruct (in_map_elim H0).
      destruct H1. unfold reset_rule in H2. inversion H2. rewrite maxvar_var.
      rewrite var_reset. refl. hyp. hyp. rewrite srs_of_trs_reset. hyp. hyp.
      hyp.
    Qed.

    Lemma rtc_red_of_sred : forall t u, Srs.red (srs_of_trs R) # t u ->
      red R # (term_of_string t) (term_of_string u).

    Proof.
      induction 1. apply rt_step. apply red_of_sred. hyp.
      apply rt_refl. apply rt_trans with (term_of_string y); hyp.
    Qed.

  End sred_of_red.

(***********************************************************************)
(** reflexion of termination *)

  Variables (R : rules) (hR : rules_preserve_vars R).

  Section red_mod.

    Variables (E : rules) (hE : rules_preserve_vars E).

    Lemma sred_mod_of_red_mod : forall x y, red_mod E R x y -> Srs.red_mod
      (srs_of_trs E) (srs_of_trs R) (string_of_term x) (string_of_term y).

    Proof.
      intros. do 2 destruct H. exists (string_of_term x0). split.
      apply (rtc_sred_of_red hE). hyp. apply (sred_of_red hR). hyp.
    Qed.

    Lemma WF_red_mod_of_WF_sred_mod :
      WF (Srs.red_mod (srs_of_trs E) (srs_of_trs R)) -> WF (red_mod E R).

    Proof.
      unfold WF. intro H.
      cut (forall s t, s = string_of_term t -> SN (red_mod E R) t).
      intros. apply H0 with (string_of_term x). refl.
      intro s. gen (H s). induction 1. intros. apply SN_intro. intros.
      apply H1 with (string_of_term y). 2: refl. subst x.
      apply sred_mod_of_red_mod. hyp.
    Qed.

(***********************************************************************)
(** preservation of termination *)

    Lemma red_mod_of_sred_mod : forall t u,
      Srs.red_mod (srs_of_trs E) (srs_of_trs R) t u ->
      red_mod E R (term_of_string t) (term_of_string u).

    Proof.
      intros. do 2 destruct H. exists (term_of_string x); split.
      apply rtc_red_of_sred; hyp. apply red_of_sred; hyp.
    Qed.

    Lemma WF_sred_mod_of_WF_red_mod :
      WF (red_mod E R) -> WF (Srs.red_mod (srs_of_trs E) (srs_of_trs R)).

    Proof.
      intros H. cut (forall t, SN (red_mod E R) t -> forall s,
      t = term_of_string s -> SN (Srs.red_mod (srs_of_trs E) (srs_of_trs R)) s).
      intros. intro s. apply H0 with (term_of_string s). apply H. refl.
      induction 1. intros. subst. apply SN_intro; intros.
      apply H1 with (term_of_string y). apply red_mod_of_sred_mod. hyp. refl.
    Qed.

    Lemma WF_red_mod :
      WF (red_mod E R) <-> WF (Srs.red_mod (srs_of_trs E) (srs_of_trs R)).

    Proof.
      split; intro. apply WF_sred_mod_of_WF_red_mod. hyp.
      apply WF_red_mod_of_WF_sred_mod. hyp.
    Qed.

  End red_mod.

  Lemma WF_red : WF (red R) <-> WF (Srs.red (srs_of_trs R)).

  Proof.
    rewrite <- red_mod_empty, <- Srs.red_mod_empty. apply WF_red_mod.
    unfold rules_preserve_vars. simpl. tauto.
  Qed.

End S.

(***********************************************************************)
(** signature functor *)

Module Make (S : ASignature.FSIG) <: VSignature.FSIG.
  Definition Sig := SSig_of_ASig S.Sig.
  Definition Fs := S.Fs.
  Definition Fs_ok := S.Fs_ok.
End Make.

(***********************************************************************)
(** tactics for Rainbow *)

From CoLoR Require Import AVariables.

Ltac as_srs_cond Fs_ok :=
  match goal with
    | |- is_unary _ => is_unary Fs_ok
    | |- rules_preserve_vars _ => rules_preserve_vars
    | |- WF _ => idtac
  end.

Ltac as_srs Fs_ok :=
  (rewrite WF_red_mod || rewrite WF_red); as_srs_cond Fs_ok.
