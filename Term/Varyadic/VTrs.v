(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

rewriting
*)

Set Implicit Arguments.

From CoLoR Require Export VContext VSubstitution LogicUtil.
From CoLoR Require Import RelUtil.

(***********************************************************************)
(** definition *)

Section def.

  Variable Sig : Signature.

  Notation term := (term Sig).

  Record rule : Type := mkRule { lhs : term; rhs : term }.

  Definition rules := list rule.

  Definition red R t1 t2 := exists l, exists r, exists c, exists s,
    In (mkRule l r) R /\ t1 = fill c (sub s l) /\ t2 = fill c (sub s r).

  Definition hd_red R t1 t2 := exists l, exists r, exists s,
    In (mkRule l r) R /\ t1 = sub s l /\ t2 = sub s r.

  Definition int_red R t1 t2 := exists l, exists r, exists c, exists s,
    c <> Hole
    /\ In (mkRule l r) R /\ t1 = fill c (sub s l) /\ t2 = fill c (sub s r).

  Definition red_mod E R := red E # @ red R.

End def.

(***********************************************************************)
(** tactics *)

Ltac redtac := repeat
  match goal with
    | H : red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r]; destruct H as [c];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (red _) _ _ |- _ => unfold transp in H; redtac
    | H : hd_red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in
      let s := fresh "s" in let h1 := fresh in
      (unfold hd_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (hd_red _) _ _ |- _ => unfold transp in H; redtac
    | H : int_red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in let h2 := fresh in
      (unfold int_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [c]; destruct H as [s]; destruct H as [H h1];
      destruct h1 as [h1 h2]; destruct h2)
    | H : transp (int_red _) _ _ |- _ =>
      unfold transp in H; redtac
  end.

(***********************************************************************)
(** properties *)

Section S.

  Variable Sig : Signature.

  Notation rule := (rule Sig).

  Variable R : list rule.

  Lemma red_rule : forall l r c s,
    In (mkRule l r) R -> red R (fill c (sub s l)) (fill c (sub s r)).

  Proof.
    intros. unfold red. exists l. exists r. exists c. exists s. auto.
  Qed.

  Lemma red_rule_top : forall l r s,
    In (mkRule l r) R -> red R (sub s l) (sub s r).

  Proof.
    intros. unfold red. exists l. exists r. exists (@Hole Sig). exists s. auto.
  Qed.

  Lemma red_fill : forall c t u, red R t u -> red R (fill c t) (fill c u).

  Proof.
    intros. redtac. unfold red.
    exists l. exists r. exists (comp c c0). exists s. split. hyp.
    subst t. subst u. do 2 rewrite fill_fill. auto.
  Qed.

End S.
