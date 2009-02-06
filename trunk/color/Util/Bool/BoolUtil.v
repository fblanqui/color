(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-17

general results on booleans
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Export Bool.

Implicit Arguments orb_false_elim [b1 b2].
Implicit Arguments orb_true_elim [b1 b2].

Hint Rewrite eqb negb_orb negb_andb negb_involutive eqb_negb1 eqb_negb2
  orb_true_r orb_true_l orb_false_r orb_false_l orb_negb_r orb_assoc
  andb_false_r andb_false_l andb_true_r andb_true_l andb_negb_r andb_assoc
  absoption_andb absoption_orb
  xorb_false_r xorb_false_l xorb_nilpotent xorb_assoc_reverse
  : bool.

Ltac bool := autorewrite with bool.

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

Lemma negb_lr : forall x y, negb x = y <-> x = negb y.

Proof.
destruct x; destruct y; intuition.
Qed.
