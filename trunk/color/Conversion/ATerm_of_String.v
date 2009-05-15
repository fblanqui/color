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

Section S.

(***********************************************************************)
(** string signature *)

Require Import Srs.

Variable SSig : Signature.

Notation string := (list SSig).
Notation letter := (symbol SSig).
Notation srule := (rule SSig).

(***********************************************************************)
(** corresponding algebraic signature *)

Require Import ATrs.

Definition ar (s : letter) := 1.

Definition ASig_of_SSig := mkSignature ar (@VSignature.beq_symb_ok SSig).

Notation ASig := ASig_of_SSig.

Notation term := (term ASig).
Notation Fun := (@Fun ASig).

Fixpoint term_of_string (s : string) : term :=
  match s with
    | nil => Var 0
    | a :: w => Fun a (Vcons (term_of_string w) Vnil)
  end.

(***********************************************************************)
(** contexts *)

Definition cont_of_letter a :=
  @Cont ASig a 0 0 (refl_equal 1) (@Vnil term) Hole Vnil.

Fixpoint cont_of_string (s : string) : context ASig :=
  match s with
    | nil => Hole
    | a :: w => AContext.comp (cont_of_letter a) (cont_of_string w)
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
  term_of_string (SContext.fill sc s) =
  fill (cont_of_string (lft sc))
  (sub (subs_of_string (rgt sc)) (term_of_string s)).

Proof.
intros. destruct sc. elim lft; unfold SContext.fill; simpl.
elim s. refl. intros. simpl. rewrite H. refl.
intros. rewrite H. refl.
Qed.

(***********************************************************************)
(** rewriting *)

Section red_of_sred.

Variable S : list srule.

Definition trs_of_srs := List.map rule_of_srule S.

Notation R := trs_of_srs.

Lemma red_of_sred : forall x y,
  Srs.red S x y -> red R (term_of_string x) (term_of_string y).

Proof.
intros. do 3 destruct H. decomp H. subst x. subst y. repeat rewrite term_sfill.
apply red_rule. change (In (rule_of_srule (Srs.mkRule x0 x1)) R).
unfold trs_of_srs. apply in_map. exact H0.
Qed.

Lemma red_of_sred_rtc : forall x y,
  Srs.red S # x y -> red R # (term_of_string x) (term_of_string y).

Proof.
intros. elim H; intros. apply rt_step. apply red_of_sred. exact H0.
apply rt_refl. eapply rt_trans. apply H1. exact H3.
Qed.

End red_of_sred.

(***********************************************************************)
(** reflexion of termination *)

Variable D S : list srule.

Notation E := (trs_of_srs D).
Notation R := (trs_of_srs S).

Lemma red_mod_of_sred_mod : forall x y,
  Srs.red_mod D S x y -> red_mod E R (term_of_string x) (term_of_string y).

Proof.
intros. do 2 destruct H. exists (term_of_string x0). split.
apply red_of_sred_rtc. exact H. apply red_of_sred. exact H0.
Qed.

Lemma WF_red_mod_of_WF_sred_mod : WF (red_mod E R) -> WF (Srs.red_mod D S).

Proof.
unfold WF. intro H.
cut (forall t s, t = term_of_string s -> SN (Srs.red_mod D S) s).
intros. apply H0 with (term_of_string x). refl.
intro t. generalize (H t). induction 1. intros. apply SN_intro. intros.
apply H1 with (term_of_string y). 2: refl. subst x. apply red_mod_of_sred_mod.
exact H3.
Qed.

End S.
