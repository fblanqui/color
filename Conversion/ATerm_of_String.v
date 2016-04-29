(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

convert a string into an algebraic term
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil RelUtil SN VecUtil ListUtil.

Section S.

(***********************************************************************)
(** string signature *)

From CoLoR Require Import Srs.

Variable SSig : VSignature.Signature.

Notation letter := (symbol SSig). Notation string := (string SSig).
Notation srule := (rule SSig). Notation srules := (rules SSig).

(***********************************************************************)
(** corresponding algebraic signature *)

Definition ar (_ : letter) := 1.

From CoLoR Require Import ATrs.

Definition ASig_of_SSig := mkSignature ar (@VSignature.beq_symb_ok SSig).

Notation ASig := ASig_of_SSig.

Notation term := (term ASig). Notation terms := (vector term).
Notation context := (context ASig).

From CoLoR Require Import AUnary.

Lemma is_unary_sig : is_unary ASig.

Proof.
intro. refl.
Qed.

Ltac arity := arity1 is_unary_sig.
Ltac is_unary := try (exact is_unary_sig).

Notation Fun1 := (Fun1 is_unary_sig). Notation Cont1 := (Cont1 is_unary_sig).
Notation cont := (cont is_unary_sig).
Notation term_ind_forall := (term_ind_forall is_unary_sig).

(***********************************************************************)
(** conversion string <-> term *)

Fixpoint term_of_string (s : string) : term :=
  match s with
    | List.nil => Var 0
    | a :: w => @Fun ASig a (Vcons (term_of_string w) Vnil)
  end.

Lemma var_term_of_string : forall s, var (term_of_string s) = 0.

Proof.
induction s; auto.
Qed.

Lemma reset_term_of_string :
  forall s, reset (term_of_string s) = term_of_string s.

Proof.
induction s. refl. unfold reset. simpl. apply args_eq.
fold (reset (term_of_string s)). rewrite IHs. refl.
Qed.

From CoLoR Require Import VecUtil.

Fixpoint string_of_term (t : term) : string :=
  match t with
    | Var _ => List.nil
    | Fun f ts => f :: Vmap_first List.nil string_of_term ts
  end.

Lemma string_of_term_epi : forall s, string_of_term (term_of_string s) = s.

Proof. induction s; simpl; intros. refl. rewrite IHs. refl. Qed.

From CoLoR Require Import NatUtil.

Lemma term_of_string_epi : forall t, maxvar t = 0 ->
  term_of_string (string_of_term t) = t.

Proof.
intro t; pattern t; apply term_ind_forall; clear t.
simpl in *. intros. subst. refl.
intros f t IH. unfold AUnary.Fun1. simpl.
rewrite (Vcast_cons (hS:=is_unary_sig f)), Vcast_refl. simpl.
rewrite max_0_r. intro h. rewrite (IH h). refl.
Qed.

Arguments term_of_string_epi [t] _.

Lemma string_of_term_sub : forall s l,
  string_of_term (sub s l) = string_of_term l ++ string_of_term (s (var l)).

Proof.
intro s. apply term_ind_forall. refl. intros f t IH.
rewrite sub_fun1. simpl.
rewrite !(Vcast_cons (hS:=is_unary_sig f)). simpl.
rewrite IH. refl.
Qed.

(***********************************************************************)
(** conversion string <-> context *)

Fixpoint string_of_cont (c : context) : string :=
  match c with
    | Hole => List.nil
    | @Cont _ f _ _ _ _ d _ => f :: string_of_cont d
  end.

Lemma string_of_cont_cont : forall t,
  string_of_cont (cont t) = string_of_term t.

Proof.
apply term_ind_forall. refl. intros f t IH. simpl.
rewrite !(Vcast_cons (hS:=is_unary_sig f)). simpl. rewrite IH. refl.
Qed.

Lemma string_of_term_fill : forall t c,
  string_of_term (fill c t) = string_of_cont c ++ string_of_term t.

Proof.
induction c. refl. simpl. rewrite Vmap_first_cast. arity. simpl. rewrite IHc.
refl.
Qed.

Fixpoint cont_of_string (s : string) : context :=
  match s with
    | List.nil => Hole
    | a :: w => Cont1 a (cont_of_string w)
  end.

(***********************************************************************)
(** conversion string <-> substitution *)

Definition sub_of_string s := single 0 (term_of_string s).

Lemma term_of_string_fill : forall c s,
  term_of_string (SContext.fill c s) = fill (cont_of_string (lft c))
  (sub (sub_of_string (rgt c)) (term_of_string s)).

Proof.
intros [l r] s. elim l; unfold SContext.fill; simpl.
elim s. refl. intros. simpl. rewrite H. refl.
intros.
rewrite H, (Vcast_cons (hS:=cont_aux is_unary_sig a)), Vcast_refl.
refl.
Qed.

Lemma term_of_string_app : forall s1 s2,
  term_of_string (s1 ++ s2) = sub (sub_of_string s2) (term_of_string s1).

Proof.
induction s1. refl. intro. simpl. apply args_eq. rewrite IHs1. refl.
Qed.

(***********************************************************************)
(** rules *)

Definition rule_of_srule (x : srule) :=
  mkRule (term_of_string (Srs.lhs x)) (term_of_string (Srs.rhs x)).

Definition trs_of_srs R := List.map rule_of_srule R.

Lemma rules_preserve_vars_trs_of_srs :
  forall R, rules_preserve_vars (trs_of_srs R).

Proof.
unfold rules_preserve_vars. induction R; simpl; intuition.
unfold rule_of_srule in H0. destruct a. simpl in H0. inversion H0.
rewrite !vars_var; is_unary. rewrite !var_term_of_string.
unfold incl; simpl; intuition.
Qed.

Ltac preserve_vars := try (apply rules_preserve_vars_trs_of_srs).

(***********************************************************************)
(** rewriting *)

Section red_of_sred.

Variable R : srules.

Lemma red_of_sred : forall x y,
  Srs.red R x y -> red (trs_of_srs R) (term_of_string x) (term_of_string y).

Proof.
intros. do 3 destruct H. decomp H. subst x. subst y.
rewrite !term_of_string_fill.
apply red_rule.
change (List.In (rule_of_srule (Srs.mkRule x0 x1)) (trs_of_srs R)).
unfold trs_of_srs. apply in_map. exact H0.
Qed.

Lemma rtc_red_of_sred : forall x y,
  Srs.red R # x y -> red (trs_of_srs R) # (term_of_string x) (term_of_string y).

Proof.
intros. elim H; intros. apply rt_step. apply red_of_sred. exact H0.
apply rt_refl. eapply rt_trans. apply H1. exact H3.
Qed.

Lemma sred_of_red : forall t u,
  red (trs_of_srs R) t u -> Srs.red R (string_of_term t) (string_of_term u).

Proof.
intros. redtac. subst. rewrite !string_of_term_fill, !string_of_term_sub,
  (rules_preserve_vars_var is_unary_sig (rules_preserve_vars_trs_of_srs R) lr).
set (c' := mkContext (string_of_cont c) (string_of_term (s (var l)))).
change (Srs.red R (SContext.fill c' (string_of_term l))
  (SContext.fill c' (string_of_term r))). apply Srs.red_rule. clear c'.
destruct (in_map_elim lr). destruct H. destruct x. unfold rule_of_srule in H0.
simpl in H0. inversion H0. rewrite !string_of_term_epi. hyp.
Qed.

Lemma rtc_sred_of_red : forall t u, red (trs_of_srs R) # t u ->
  Srs.red R # (string_of_term t) (string_of_term u).

Proof.
induction 1. apply rt_step. apply sred_of_red. hyp.
apply rt_refl. apply rt_trans with (string_of_term y); hyp.
Qed.

End red_of_sred.

(***********************************************************************)
(** reflexion of termination *)

Variable R : srules.

Section red_mod.

Variable E : srules.

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
intro t. gen (H t). induction 1. intros. apply SN_intro. intros.
apply H1 with (term_of_string y). 2: refl. subst x. apply red_mod_of_sred_mod.
exact H3.
Qed.

(***********************************************************************)
(** preservation of termination *)

Lemma sred_mod_of_red_mod : forall t u,
  red_mod (trs_of_srs E) (trs_of_srs R) t u ->
  Srs.red_mod E R (string_of_term t) (string_of_term u).

Proof.
intros. do 2 destruct H. exists (string_of_term x); split.
apply rtc_sred_of_red. hyp. apply sred_of_red. hyp.
Qed.

Lemma WF_sred_mod_of_WF_red_mod :
  WF (Srs.red_mod E R) -> WF (red_mod (trs_of_srs E) (trs_of_srs R)).

Proof.
intro. rewrite WF_red_mod0; is_unary; preserve_vars.
cut (forall s, SN (Srs.red_mod E R) s -> forall t, maxvar t = 0 ->
  t = term_of_string s -> SN (red_mod0 (trs_of_srs E) (trs_of_srs R)) t).
(* cut correctness *)
intros. intro t. destruct (eq_nat_dec (maxvar t) 0). Focus 2.
apply SN_intro. intros. destruct H1. omega.
apply H0 with (string_of_term t). apply H. hyp. rewrite term_of_string_epi.
refl. hyp.
(* proof with cut *)
induction 1; intros. apply SN_intro; intros. assert (h : maxvar y = 0).
apply (red_mod0_maxvar (rules_preserve_vars_trs_of_srs E)
  (rules_preserve_vars_trs_of_srs R) H4). rewrite <- (term_of_string_epi h).
apply H1 with (string_of_term y). 3: refl.
2: rewrite (term_of_string_epi h); hyp. rewrite <- (string_of_term_epi x).
apply sred_mod_of_red_mod. subst.
eapply incl_elim with (R := red_mod0 (trs_of_srs E) (trs_of_srs R)).
apply red_mod0_incl_red_mod. hyp.
Qed.

Lemma WF_red_mod :
  WF (Srs.red_mod E R) <-> WF (red_mod (trs_of_srs E) (trs_of_srs R)).

Proof.
split; intro. apply WF_sred_mod_of_WF_red_mod. hyp.
apply WF_red_mod_of_WF_sred_mod. hyp.
Qed.

End red_mod.

Lemma WF_red : WF (Srs.red R) <-> WF (red (trs_of_srs R)).

Proof. rewrite <- Srs.red_mod_empty, <- red_mod_empty. apply WF_red_mod. Qed.

End S.

(***********************************************************************)
(** signature functor *)

Module Make (S : VSignature.FSIG) <: FSIG.
  Definition Sig := ASig_of_SSig S.Sig.
  Definition Fs := S.Fs.
  Definition Fs_ok := S.Fs_ok.
End Make.

(***********************************************************************)
(** tactics for Rainbow *)

Ltac as_trs := rewrite WF_red_mod || rewrite WF_red.
