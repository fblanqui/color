(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

rewriting
*)

(* $Id: VTrs.v,v 1.2 2007-01-19 17:22:39 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export VSignature.

Variable Sig : Signature.

Require Export VTerm.

Notation term := (term Sig).
Notation terms := (list term).

(***********************************************************************)
(** rule *)

Record rule : Set := mkRule {
  lhs : term;
  rhs : term
}.

Notation rules := (list rule).

(***********************************************************************)
(** rewrite step *)

Variable R : rules.

Require Export VContext.
Require Export VSubstitution.

Definition red (t1 t2 : term) :=
  exists l, exists r, exists c, exists s,
  In (mkRule l r) R /\ t1 = fill c (app s l) /\ t2 = fill c (app s r).

Definition hd_red (t1 t2 : term) :=
  exists l, exists r, exists s,
  In (mkRule l r) R /\ t1 = app s l /\ t2 = app s r.

Definition int_red (t1 t2 : term) :=
  exists l, exists r, exists c, exists s, c <> Hole
  /\ In (mkRule l r) R /\ t1 = fill c (app s l) /\ t2 = fill c (app s r).

Require Export RelUtil.

Ltac redtac := repeat
  match goal with
    | H : red ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r]; destruct H as [c];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp red _ _ |- _ =>
      unfold transp in H; redtac
    | H : hd_red ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in
      let s := fresh "s" in let h1 := fresh in
      (unfold hd_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp hd_red _ _ |- _ =>
      unfold transp in H; redtac
    | H : int_red ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in let h2 := fresh in
      (unfold int_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [c]; destruct H as [s]; destruct H as [H h1];
      destruct h1 as [h1 h2]; destruct h2)
    | H : transp int_red _ _ |- _ =>
      unfold transp in H; redtac
  end.

Lemma red_rule : forall l r c s, In (mkRule l r) R ->
  red (fill c (app s l)) (fill c (app s r)).

Proof.
intros. unfold red. exists l. exists r. exists c. exists s. auto.
Qed.

Lemma red_rule_top : forall l r s, In (mkRule l r) R ->
  red (app s l) (app s r).

Proof.
intros. unfold red. exists l . exists r. exists (@Hole Sig). exists s. auto.
Qed.

Lemma red_fill : forall c t u,
  red t u -> red (fill c t) (fill c u).

Proof.
intros. redtac. unfold red.
exists l. exists r. exists (VContext.comp c c0). exists s. split. assumption.
subst t. subst u. do 2 rewrite fill_comp. auto.
Qed.

End S.

(***********************************************************************)
(** tactics *)

Ltac redtac := repeat
  match goal with
    | H : red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r]; destruct H as [c];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (red _) _ _ |- _ =>
      unfold transp in H; redtac
    | H : hd_red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in
      let s := fresh "s" in let h1 := fresh in
      (unfold hd_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (hd_red _) _ _ |- _ =>
      unfold transp in H; redtac
    | H : int_red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in let h2 := fresh in
      (unfold int_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [c]; destruct H as [s]; destruct H as [H h1];
      destruct h1 as [h1 h2]; destruct h2)
    | H : transp (int_red _) _ _ |- _ =>
      unfold transp in H; redtac
  end.