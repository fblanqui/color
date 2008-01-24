(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-17

general results on booleans
*)

(* $Id: BoolUtil.v,v 1.5 2008-01-24 13:22:25 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export Bool.

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

(***********************************************************************)
(** boolean equalities *)

Lemma implb1 : forall b, implb b b = true.

Proof.
induction b; refl.
Qed.

Lemma implb2 : forall b, implb b true = true.

Proof.
induction b; refl.
Qed.

(***********************************************************************)
(** introduction and elimination rules for booleans *)

Lemma andb_elim : forall b c, b && c = true -> b = true /\ c = true.

Proof.
intros. destruct b; destruct c; intuition.
Qed.

Implicit Arguments andb_elim [b c].

Lemma andb_intro : forall b c, b = true -> c = true -> b && c = true.

Proof.
intros. subst b. subst c. refl.
Qed.
