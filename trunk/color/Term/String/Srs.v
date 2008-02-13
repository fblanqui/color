(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

string rewriting
*)

(* $Id: Srs.v,v 1.4 2008-02-13 14:08:16 blanqui Exp $ *)

Set Implicit Arguments.

(***********************************************************************)
(** basic definitions *)

Section definition.

Require Export VSignature.

Variable Sig : Signature.

Require Export List.

Notation string := (list Sig).

Record rule : Set := mkRule { lhs : string; rhs : string }.

Require Export SContext.

Definition red R : relation string := fun s1 s2 =>
  exists l, exists r, exists c,
    In (mkRule l r) R /\ s1 = fill c l /\ s2 = fill c r.

Require Export RelUtil.

Definition red_mod E R := red E # @ red R.

End definition.

Implicit Arguments mkRule [Sig].

(***********************************************************************)
(** tactics *)

Ltac redtac := repeat
  match goal with
    | H : red _ ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r]; destruct H as [c];
      destruct H as [H h1]; destruct h1)
    | H : red_mod _ _ _ _ |- _ => do 2 destruct H; redtac
  end.

(***********************************************************************)
(** basic properties *)

Section S.

Variable Sig : Signature.

Notation string := (list Sig).
Notation rule := (rule Sig).

Variable R : list rule.

Lemma red_rule : forall l r c, In (mkRule l r) R -> red R (fill c l) (fill c r).

Proof.
intros. unfold red. exists l. exists r. exists c. auto.
Qed.

Lemma red_fill : forall c t u, red R t u -> red R (fill c t) (fill c u).

Proof.
intros. redtac. unfold red.
exists l. exists r. exists (comp c c0). split. assumption.
subst t. subst u. do 2 rewrite fill_comp. auto.
Qed.

Lemma red_nil : forall x y : string, red nil x y -> x = y.

Proof.
unfold red. intros. decomp H. destruct H1.
Qed.

Lemma red_nil_rtc : forall x y : string, red nil # x y -> x = y.

Proof.
induction 1. apply red_nil. exact H. refl. transitivity y; assumption.
Qed.

Lemma red_mod_empty_incl_red : red_mod nil R << red R.

Proof.
unfold inclusion. intros. redtac. deduce (red_nil_rtc H). subst x0.
subst x. subst y. apply red_rule. exact H0.
Qed.

Lemma red_incl_red_mod_empty : red R << red_mod nil R.

Proof.
unfold inclusion. intros. exists x. split. apply rt_refl. exact H.
Qed.

Lemma red_mod_empty : red_mod nil R == red R.

Proof.
split. apply red_mod_empty_incl_red. apply red_incl_red_mod_empty.
Qed.

End S.

(***********************************************************************)
(** tactics *)

Require Export SN.

Ltac no_relative_rules :=
  match goal with
    |- WF (@red_mod ?S ?E _) =>
      normalize E; eapply WF_incl; [apply (@red_mod_empty_incl_red S) | idtac]
    | _ => idtac
  end.
