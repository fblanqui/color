(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

string rewriting
*)

(* $Id: Srs.v,v 1.2 2007-05-28 16:28:14 blanqui Exp $ *)

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

Definition red R (s1 s2 : string) := exists l, exists r, exists c,
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
    | H : transp red _ _ _ |- _ =>
      unfold transp in H; redtac
  end.

(***********************************************************************)
(** basic properties *)

Section S.

Variable Sig : Signature.

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

End S.
