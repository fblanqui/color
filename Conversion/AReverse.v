(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-10-16

unary TRS reversing
*)

Set Implicit Arguments.

From CoLoR Require Import Srs ATrs SReverse ATerm_of_String String_of_ATerm
     AUnary SN LogicUtil AMorphism EqUtil NatUtil ListUtil VecUtil.

Section S.

  Variable Sig : Signature.

  Variable is_unary_sig : is_unary Sig.

  Notation term := (term Sig).
  Notation rule := (rule Sig). Notation rules := (list rule).

  Notation SSig := (SSig_of_ASig Sig).

  Definition rev_Sig := ASig_of_SSig SSig.

  Notation Sig' := rev_Sig.

(***********************************************************************)
(** signature isomorphism between Sig and Sig' *)

  Lemma is_unary_sig' : is_unary Sig'.

  Proof. intro f. refl. Qed.

  Definition F (f : Sig) : Sig' := f.

  Lemma HF : forall f, arity f = arity (F f).

  Proof. intro. rewrite <- is_unary_sig. refl. Qed.

  Definition G (f : Sig') : Sig := f.

  Lemma HG : forall f, arity f = arity (G f).

  Proof. intro. rewrite <- is_unary_sig. refl. Qed.

  Lemma FG : forall f, F (G f) = f.

  Proof. refl. Qed.

  Lemma GF : forall f, G (F f) = f.

  Proof. refl. Qed.

(***********************************************************************)
(** isomorphism properties *)

  Lemma term_of_string_epi : forall t, maxvar t = 0 ->
    ATerm_of_String.term_of_string (string_of_term t) = Ft HF t.

  Proof.
    intro t; pattern t; apply (term_ind_forall is_unary_sig); clear t; intros.
    simpl. simpl in H. subst. refl.
    rewrite string_of_term_fun1. unfold ATerm_of_String.term_of_string;
      fold (ATerm_of_String.term_of_string (string_of_term t)).
    rewrite H. unfold Fun1. unfold Ft at -1. rewrite Vmap_cast, Vcast_cast.
    simpl Vmap. apply args_eq. rewrite Vcast_refl. refl.
    rewrite maxvar_fun1 in H0. hyp.
  Qed.

  Lemma rule_of_srule_epi : forall a,
    maxvar (lhs a) = 0 -> maxvar (rhs a) = 0 ->
    rule_of_srule (srule_of_rule a) = Fr HF a.

  Proof.
    intros [l r] hl hr. unfold rule_of_srule, srule_of_rule. simpl.
    rewrite !term_of_string_epi; try hyp. refl.
  Qed.

  Lemma trs_of_srs_epi : forall R,
    (forall a, In a R -> maxvar (lhs a) = 0 /\ maxvar (rhs a) = 0) ->
    trs_of_srs (srs_of_trs R) = Fl HF R.

  Proof.
    induction R; intros. refl. simpl. rewrite IHR.
    assert (In a (a::R)). simpl. auto. destruct (H _ H0).
    rewrite rule_of_srule_epi; try hyp. refl.
    intros b h. assert (In b (a::R)). simpl. auto. destruct (H _ H0). intuition.
  Qed.

(***********************************************************************)
(** term and rule reversal *)

  Definition reverse_term (t : term) :=
    ATerm_of_String.term_of_string (ListUtil.rev' (string_of_term t)).

  Definition reverse_rule (e : rule) :=
    let (l,r) := e in mkRule (reverse_term l) (reverse_term r).

  Definition reverse_trs := List.map reverse_rule.

  Notation reverse_srule := (@SReverse.reverse SSig).
  Notation reverse_srs := (List.map reverse_srule).

(***********************************************************************)
(** preservation of variables *)

  Lemma var_reverse_term : forall t, var (reverse_term t) = 0.

  Proof.
    intro t; pattern t; apply (term_ind_forall is_unary_sig); clear t; intros.
    refl. unfold reverse_term.
    rewrite string_of_term_fun1, rev'_cons, term_of_string_app.
    change (var (sub (@ATerm_of_String.sub_of_string SSig (f :: nil))
      (reverse_term t)) = 0).
    rewrite var_sub. 2: apply is_unary_sig'. rewrite H. refl.
  Qed.

  Lemma rules_preserve_vars_reverse_trs :
    forall R, rules_preserve_vars R -> rules_preserve_vars (reverse_trs R).

  Proof.
    induction R; intros. unfold rules_preserve_vars. simpl. tauto.
    simpl. revert H. rewrite !rules_preserve_vars_cons. destruct a as [l r].
    simpl. intuition. rewrite !vars_var; try (hyp||apply is_unary_sig').
    rewrite !var_reverse_term. intuition auto with *.
  Qed.

  Lemma trs_of_srs_reverse_trs : forall R,
    trs_of_srs (reverse_srs (srs_of_trs R)) = reverse_trs R.

  Proof.
    induction R. refl. simpl. destruct a as [l r]. unfold rule_of_srule. simpl.
    rewrite IHR. refl.
  Qed.

(***********************************************************************)
(** relations with reset *)

  Lemma reverse_term_reset : forall t, reverse_term (reset t) = reverse_term t.

  Proof.
    intro t; pattern t; apply (term_ind_forall is_unary_sig); clear t; intros.
    unfold reset, swap, single. simpl. rewrite (beq_refl beq_nat_ok). refl.
    rewrite reset_fun1. unfold reverse_term.
    rewrite !string_of_term_fun1, string_of_term_reset. refl. hyp.
  Qed.

  Lemma reset_reverse_term : forall t, reset (reverse_term t) = reverse_term t.

  Proof.
    intro t; pattern t; apply (term_ind_forall is_unary_sig); clear t; intros.
    refl. unfold reverse_term.
    rewrite !string_of_term_fun1, reset_term_of_string. refl.
  Qed.

  Lemma reverse_trs_reset_rules : forall R,
    reverse_trs (reset_rules R) = reset_rules (reverse_trs R).

  Proof.
    induction R. refl. simpl. destruct a as [l r]. simpl.
    rewrite !reverse_term_reset, IHR. unfold reset_rule. simpl.
    rewrite !reset_reverse_term. refl.
  Qed.

(***********************************************************************)
(** termination *)

  Variables R : rules.
  Variable hR : rules_preserve_vars R.

  Section red_mod.

    Variables E : rules.
    Variable hE : rules_preserve_vars E.

    Lemma WF_red_mod_rev_eq :
      WF (red_mod (reverse_trs E) (reverse_trs R)) <-> WF (red_mod E R).

    Proof.
      intros. sym. rewrite red_mod_reset_eq; try hyp.
      rewrite String_of_ATerm.WF_red_mod; try apply rules_preserve_vars_reset;
        try hyp.
      rewrite <- WF_red_mod_rev_eq, ATerm_of_String.WF_red_mod; try hyp.
      rewrite !trs_of_srs_reverse_trs, !reverse_trs_reset_rules,
        <- red_mod_reset_eq.
      refl. apply is_unary_sig'.
      apply rules_preserve_vars_reverse_trs; hyp.
      apply rules_preserve_vars_reverse_trs; hyp.
    Qed.

  End red_mod.

  Lemma WF_red_rev_eq : WF (red (reverse_trs R)) <-> WF (red R).

  Proof.
    rewrite <- !red_mod_empty.
    assert (nil = reverse_trs nil). refl. rewrite H. apply WF_red_mod_rev_eq.
    unfold rules_preserve_vars. simpl. tauto.
  Qed.

End S.

(***********************************************************************)
(** tactics for Rainbow *)

From CoLoR Require Import AVariables.

Ltac rev_tac_cond Fs_ok :=
  match goal with
    | |- is_unary _ => is_unary Fs_ok
    | |- rules_preserve_vars _ => rules_preserve_vars
    | |- WF _ => idtac
  end.

Ltac rev_tac Fs_ok :=
  (rewrite <- WF_red_rev_eq || rewrite <- WF_red_mod_rev_eq);
  rev_tac_cond Fs_ok.
