(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

string rewriting
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil RelUtil ListUtil BoolUtil EqUtil ListDec.
From CoLoR Require Export SContext.

(***********************************************************************)
(** strings *)

Section definition.

Variable Sig : Signature.

Definition string := list Sig.

Definition beq_string := beq_list (@beq_symb Sig).
Definition beq_string_ok := beq_list_ok (@beq_symb_ok Sig).

(***********************************************************************)
(** rules *)

Record rule : Type := mkRule { lhs : string; rhs : string }.

Definition beq_rule (a1 a2 : rule) : bool :=
  let (l1,r1) := a1 in let (l2,r2) := a2 in
    beq_string l1 l2 && beq_string r1 r2.

Lemma beq_rule_ok : forall a1 a2, beq_rule a1 a2 = true <-> a1 = a2.

Proof.
destruct a1 as [l1 r1]. destruct a2 as [l2 r2]. simpl. intuition.
rewrite andb_eq, !beq_string_ok in H. destruct H. subst.
refl. inversion H. subst. rewrite !(beq_refl beq_string_ok). refl.
Qed.

Definition rules := list rule.

(***********************************************************************)
(** rewriting *)

Definition red R : relation string := fun s1 s2 =>
  exists l, exists r, exists c,
    In (mkRule l r) R /\ s1 = fill c l /\ s2 = fill c r.

Definition red_mod E R := red E # @ red R.

End definition.

Arguments mkRule [Sig] _ _.

(***********************************************************************)
(** tactics *)

Ltac redtac := repeat
  match goal with
    | H : red _ ?t ?u |- _ =>
      let l := fresh "l" in 
      let r := fresh "r" in 
      let c := fresh "c" in
      let w := fresh "ww" in
      unfold red in H; destruct H as [l [r [c [? [? ?]]]]]; try subst

    | H : red_mod _ _ _ _ |- _ => 
      do 2 destruct H; redtac
  end.

(***********************************************************************)
(** basic properties *)

Section S.

Variable Sig : Signature.

Notation string := (string Sig). Notation rules := (rules Sig).

Section red.

Variable R : rules.

Lemma red_rule : forall l r c,
  In (mkRule l r) R -> red R (fill c l) (fill c r).

Proof.
intros. unfold red. exists l. exists r. exists c. auto.
Qed.

Lemma red_rule_top : forall l r, In (mkRule l r) R ->
  red R l r.

Proof.
  intros. red. exists l. exists r. exists (mkContext nil nil). 
  repeat split; unfold fill; simpl; trivial || rewrite app_nil_r; trivial. 
Qed.

Lemma red_fill : forall c t u, red R t u -> red R (fill c t) (fill c u).

Proof.
intros. redtac. unfold red.
exists l. exists r. exists (comp c c0). split. hyp.
rewrite !fill_fill. auto.
Qed.

Lemma rtc_red_fill : forall c t u,
  red R # t u -> red R # (fill c t) (fill c u).

Proof.
induction 1. apply rt_step. apply red_fill. hyp. apply rt_refl.
apply rt_trans with (fill c y); hyp.
Qed.

Lemma red_nil : forall x y : string, red nil x y -> x = y.

Proof.
unfold red. intros. decomp H. destruct H1.
Qed.

Lemma red_nil_rtc : forall x y : string, red nil # x y -> x = y.

Proof.
induction 1. apply red_nil. exact H. refl. trans y; hyp.
Qed.

Lemma red_mod_empty_incl_red : red_mod nil R << red R.

Proof.
unfold inclusion. intros. redtac. ded (red_nil_rtc H). subst.
apply red_rule. exact H0.
Qed.

Lemma red_incl_red_mod_empty : red R << red_mod nil R.

Proof.
unfold inclusion. intros. exists x. split. apply rt_refl. exact H.
Qed.

Lemma red_mod_empty : red_mod nil R == red R.

Proof.
split. apply red_mod_empty_incl_red. apply red_incl_red_mod_empty.
Qed.

End red.

Section red_mod.

Variables E R : rules.

Lemma red_mod_fill : forall c t u,
  red_mod E R t u -> red_mod E R (fill c t) (fill c u).

Proof.
intros. do 2 destruct H. exists (fill c x); split.
apply rtc_red_fill. hyp. apply red_fill. hyp.
Qed.

End red_mod.

End S.

(***********************************************************************)
(** tactics *)

From CoLoR Require Import SN.

Ltac remove_relative_rules E := norm E; rewrite red_mod_empty
  || fail "this certificate cannot be applied on a relative system".

Ltac no_relative_rules :=
  match goal with
    | |- WF (red_mod ?E _) => remove_relative_rules E
    | |- EIS (red_mod ?E _) => remove_relative_rules E
    | |- _ => idtac
  end.
