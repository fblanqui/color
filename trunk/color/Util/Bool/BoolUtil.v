(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-17

general results on booleans
*)

(* $Id: BoolUtil.v,v 1.3 2007-06-19 17:45:51 koper Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export Bool.

(***********************************************************************)
(** decidable relation (into bool) *)

Section BoolRelation.

  Variable A : Set.

  Definition relation_bool :=  A -> A -> bool.

End BoolRelation.

(***********************************************************************)
(** implication *)

Lemma implb_1 : forall b, implb b b = true.

Proof.
induction b; refl.
Qed.

Lemma implb_2 : forall b, implb b true = true.

Proof.
induction b; refl.
Qed.

(***********************************************************************)
(** tactics *)

Ltac booltac e := let H := fresh in let H1 := fresh in
  (assert (H : e = true \/ e = false);
    [case e; auto | destruct H as [H1 | H1]]).

Ltac booltac_simpl e := let H := fresh in let H1 := fresh in
  let t1 := (rewrite H1; simpl) in
  (assert (H : e = true \/ e = false);
    [case e; auto
    | destruct H as [H1 | H1]; [t1 | t1]]).

