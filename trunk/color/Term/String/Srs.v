(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

string rewriting
*)

(* $Id: Srs.v,v 1.1 2007-05-25 16:24:22 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export VSignature.

Variable Sig : Signature.

Require Export List.

Notation string := (list Sig).

(***********************************************************************)
(** rule *)

Record rule : Set := mkRule { lhs : string; rhs : string }.

Notation rules := (list rule).

(***********************************************************************)
(** rewrite step *)

Variable R : rules.

Require Export SContext.

Definition red (s1 s2 : string) := exists l, exists r, exists c,
  In (mkRule l r) R /\ s1 = fill c l /\ s2 = fill c r.

Require Export RelUtil.

Ltac redtac := repeat
  match goal with
    | H : red ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r]; destruct H as [c];
      destruct H as [H h1]; destruct h1)
    | H : transp red _ _ |- _ =>
      unfold transp in H; redtac
  end.

Lemma red_rule : forall l r c, In (mkRule l r) R -> red (fill c l) (fill c r).

Proof.
intros. unfold red. exists l. exists r. exists c. auto.
Qed.

Lemma red_fill : forall c t u, red t u -> red (fill c t) (fill c u).

Proof.
intros. redtac. unfold red.
exists l. exists r. exists (comp c c0). split. assumption.
subst t. subst u. do 2 rewrite fill_comp. auto.
Qed.

End S.

(***********************************************************************)
(** tactics *)

Ltac redtac := repeat
  match goal with
    | H : red ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r]; destruct H as [c];
      destruct H as [H h1]; destruct h1)
    | H : transp red _ _ |- _ =>
      unfold transp in H; redtac
  end.
