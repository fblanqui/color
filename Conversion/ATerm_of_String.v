(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

convert a string into an algebraic term
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import RelUtil.
Require Import SN.
Require Import ListUtil.

Section S.

(***********************************************************************)
(** string signature *)

Require Import Srs.

Variable SSig : VSignature.Signature.

Notation letter := (symbol SSig). Notation string := (string SSig).
Notation srule := (rule SSig). Notation srules := (rules SSig).

(***********************************************************************)
(** corresponding algebraic signature *)

Definition ar (_ : letter) := 1.

Require Import ATrs.

Definition ASig_of_SSig := mkSignature ar (@VSignature.beq_symb_ok SSig).

Notation ASig := ASig_of_SSig.

Notation term := (term ASig). Notation terms := (vector term).
Notation context := (context ASig).

Require Import AUnary.

Lemma is_unary_sig : is_unary ASig.

Proof.
intro. refl.
Qed.

Ltac arity := arity1 is_unary_sig.
Ltac is_unary := try (exact is_unary_sig).

Notation cont := (cont is_unary_sig).
Notation term_ind_forall := (term_ind_forall is_unary_sig).
 
Fixpoint term_of_string (s : string) : term :=
  match s with
    | nil => Var 0
    | a :: w => @Fun ASig a (Vcons (term_of_string w) Vnil)
  end.

Lemma var_term_of_string : forall s, var (term_of_string s) = 0.

Proof.
induction s; auto.
Qed.

(*FIXME: does not work:
Fixpoint string_of_term (t : term) : string :=
  match t with
    | Var _ => nil
    | ATerm.Fun f ts => f :: match ts with
                               | Vcons t _ _ => string_of_term t
                               | _ => nil
                             end
  end.*)

Require Import VecUtil.

Fixpoint string_of_term (t : term) : string :=
  match t with
    | Var _ => nil
    | Fun f ts => f :: Vmap_first nil string_of_term ts
  end.

Lemma string_of_term_epi : forall s, string_of_term (term_of_string s) = s.

Proof.
induction s; simpl; intros. refl. rewrite IHs. refl.
Qed.

Require Import NatUtil.

Lemma term_of_string_epi : forall t, maxvar t = 0 ->
  term_of_string (string_of_term t) = t.

Proof.
intro t; pattern t; apply term_ind_forall; clear t.
simpl in *. intros. subst. refl.
intros f t IH. simpl. rewrite max_0_r. intro h. rewrite (IH h). refl.
Qed.

Implicit Arguments term_of_string_epi [t].

Fixpoint string_of_cont (c : context) : string :=
  match c with
    | Hole => nil
    | Cont f _ _ _ _ d _ => f :: string_of_cont d
  end.

Lemma string_of_term_cont : forall t,
  string_of_term t = string_of_cont (cont t).

Proof.
apply term_ind_forall. refl. intros f t IH. simpl. rewrite IH. refl.
Qed.

Lemma string_of_term_fill : forall t c,
  string_of_term (fill c t) = string_of_cont c ++ string_of_term t.

Proof.
induction c. refl. simpl. rewrite Vmap_first_cast. arity. simpl. rewrite IHc.
refl.
Qed.

Lemma string_of_term_sub : forall s l,
  string_of_term (sub s l) = string_of_term l ++ string_of_term (s (var l)).

Proof.
intro s. apply term_ind_forall. refl. intros f t IH. rewrite sub_fun. simpl.
rewrite IH. refl.
Qed.

(***********************************************************************)
(** contexts *)

Definition cont_of_letter a :=
  @Cont ASig a 0 0 (refl_equal 1) (@Vnil term) Hole Vnil.

Fixpoint cont_of_string (s : string) : context :=
  match s with
    | nil => Hole
    | a :: w => comp (cont_of_letter a) (cont_of_string w)
  end.

(***********************************************************************)
(** rules *)

Definition rule_of_srule (x : srule) :=
  mkRule (term_of_string (Srs.lhs x)) (term_of_string (Srs.rhs x)).

Definition subs_of_string s x :=
  match x with
    | 0 => term_of_string s
    | _ => @Var ASig x
  end.

Lemma term_sfill : forall sc s,
  term_of_string (SContext.fill sc s) = fill (cont_of_string (lft sc))
  (sub (subs_of_string (rgt sc)) (term_of_string s)).

Proof.
intros. destruct sc. elim lft; unfold SContext.fill; simpl.
elim s. refl. intros. simpl. rewrite H. refl.
intros. rewrite H. refl.
Qed.

(***********************************************************************)
(** rewriting *)

Definition trs_of_srs R := map rule_of_srule R.

Lemma rules_preserv_vars_trs_of_srs :
  forall R, rules_preserv_vars (trs_of_srs R).

Proof.
unfold rules_preserv_vars. induction R; simpl; intuition.
unfold rule_of_srule in H0. destruct a. simpl in H0. inversion H0.
repeat rewrite vars_var; is_unary. repeat rewrite var_term_of_string.
unfold incl; simpl; intuition.
Qed.

Ltac preserv_vars := try (apply rules_preserv_vars_trs_of_srs).

Section red_of_sred.

Variable R : srules.

Lemma red_of_sred : forall x y,
  Srs.red R x y -> red (trs_of_srs R) (term_of_string x) (term_of_string y).

Proof.
intros. do 3 destruct H. decomp H. subst x. subst y. repeat rewrite term_sfill.
apply red_rule. change (In (rule_of_srule (Srs.mkRule x0 x1)) (trs_of_srs R)).
unfold trs_of_srs. apply in_map. exact H0.
Qed.

Lemma rtc_red_of_sred : forall x y,
  Srs.red R # x y -> red (trs_of_srs R) # (term_of_string x) (term_of_string y).

Proof.
intros. elim H; intros. apply rt_step. apply red_of_sred. exact H0.
apply rt_refl. eapply rt_trans. apply H1. exact H3.
Qed.

Lemma sred_of_red0 : forall t u,
  red0 (trs_of_srs R) t u -> Srs.red R (string_of_term t) (string_of_term u).

Proof.
intros. destruct H. redtac. subst. repeat rewrite string_of_term_fill.
repeat rewrite string_of_term_sub. rewrite (rules_preserv_vars_var
  is_unary_sig (rules_preserv_vars_trs_of_srs R) lr).
set (c' := mkContext (string_of_cont c) (string_of_term (s (var l)))).
change (Srs.red R (SContext.fill c' (string_of_term l))
  (SContext.fill c' (string_of_term r))). apply Srs.red_rule. clear c'.
destruct (in_map_elim lr). destruct H. destruct x. unfold rule_of_srule in H1.
simpl in H1. inversion H1. repeat rewrite string_of_term_epi. hyp.
Qed.

Lemma rtc_sred_of_red0 : forall t u, red (trs_of_srs R) # t u ->
  maxvar t = 0 -> Srs.red R # (string_of_term t) (string_of_term u).

Proof.
induction 1; intro. apply rt_step. apply sred_of_red0. unfold red0. intuition.
apply rt_refl. apply rt_trans with (string_of_term y). auto.
apply IHclos_refl_trans2. eapply rtc_red_maxvar0.
apply rules_preserv_vars_trs_of_srs. apply H1. apply H.
Qed.
 
End red_of_sred.

(***********************************************************************)
(** reflexion of termination *)

Variables E R : srules.

Lemma red_mod_of_sred_mod : forall x y, Srs.red_mod E R x y ->
  red_mod (trs_of_srs E) (trs_of_srs R) (term_of_string x) (term_of_string y).

Proof.
intros. do 2 destruct H. exists (term_of_string x0). split.
apply rtc_red_of_sred. exact H. apply red_of_sred. exact H0.
Qed.

Lemma WF_red_mod_of_WF_sred_mod :
  WF (red_mod (trs_of_srs E) (trs_of_srs R)) -> WF (Srs.red_mod E R).

Proof.
unfold WF. intro H.
cut (forall t s, t = term_of_string s -> SN (Srs.red_mod E R) s).
intros. apply H0 with (term_of_string x). refl.
intro t. generalize (H t). induction 1. intros. apply SN_intro. intros.
apply H1 with (term_of_string y). 2: refl. subst x. apply red_mod_of_sred_mod.
exact H3.
Qed.

(***********************************************************************)
(** preservation of termination *)

Lemma sred_mod_of_red_mod0 : forall t u,
  red_mod0 (trs_of_srs E) (trs_of_srs R) t u ->
  Srs.red_mod E R (string_of_term t) (string_of_term u).

Proof.
intros. do 3 destruct H. exists (string_of_term x); split.
apply rtc_sred_of_red0; hyp. apply sred_of_red0. unfold red0. intuition.
eapply rtc_red_maxvar0. apply rules_preserv_vars_trs_of_srs. apply H0. apply H.
Qed.

Lemma WF_sred_mod_of_WF_red_mod :
  WF (Srs.red_mod E R) -> WF (red_mod (trs_of_srs E) (trs_of_srs R)).

Proof.
intro. rewrite WF_red_mod0; is_unary; preserv_vars.
cut (forall s, SN (Srs.red_mod E R) s -> forall t, maxvar t = 0 ->
  t = term_of_string s -> SN (red_mod0 (trs_of_srs E) (trs_of_srs R)) t).
(* cut correctness *)
intros. intro t. destruct (eq_nat_dec (maxvar t) 0). Focus 2.
apply SN_intro. intros. destruct H1. absurd_arith.
apply H0 with (string_of_term t). apply H. hyp. rewrite term_of_string_epi.
refl. hyp.
(* proof with cut *)
induction 1; intros. apply SN_intro; intros. assert (h : maxvar y = 0).
apply (red_mod0_maxvar (rules_preserv_vars_trs_of_srs E)
  (rules_preserv_vars_trs_of_srs R) H4). rewrite <- (term_of_string_epi h).
apply H1 with (string_of_term y). 3: refl.
2: rewrite (term_of_string_epi h); hyp. rewrite <- (string_of_term_epi x).
apply sred_mod_of_red_mod0. subst. hyp.
Qed.

Lemma WF_conv :
  WF (Srs.red_mod E R) <-> WF (red_mod (trs_of_srs E) (trs_of_srs R)).

Proof.
split; intro. apply WF_sred_mod_of_WF_red_mod. hyp.
apply WF_red_mod_of_WF_sred_mod. hyp.
Qed.

End S.
