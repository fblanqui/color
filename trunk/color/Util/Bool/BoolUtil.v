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
(** implication *)

Lemma implb1 : forall b, implb b b = true.

Proof.
induction b; refl.
Qed.

Lemma implb2 : forall b, implb b true = true.

Proof.
induction b; refl.
Qed.

(***********************************************************************)
(** conjunction *)

Lemma andb_elim : forall b c, b && c = true -> b = true /\ c = true.

Proof.
destruct b; destruct c; intuition.
Qed.

Implicit Arguments andb_elim [b c].

Lemma andb_eliml : forall b c, b && c = true -> b = true.

Proof.
destruct b; destruct c; intuition.
Qed.

Implicit Arguments andb_eliml [b c].

Lemma andb_elimr : forall b c, b && c = true -> c = true.

Proof.
destruct b; destruct c; intuition.
Qed.

Implicit Arguments andb_elimr [b c].

Lemma andb_intro : forall b c, b = true -> c = true -> b && c = true.

Proof.
intros. subst b. subst c. refl.
Qed.

Lemma andb_eq : forall b c, b && c = true <-> b = true /\ c = true.

Proof.
split. intro. apply andb_elim. hyp. intuition.
Qed.

(***********************************************************************)
(** negation *)

Lemma negb_lr : forall b c, negb b = c <-> b = negb c.

Proof.
destruct b; destruct c; intuition.
Qed.

(***********************************************************************)
(** disjonction *)

Lemma orb_intror : forall b c, c = true -> b || c = true.

Proof.
intros. subst. bool. refl.
Qed.

Lemma orb_introl : forall b c, c = true -> b || c = true.

Proof.
intros. subst. bool. refl.
Qed.

Lemma orb_eq : forall b c, b || c = true <-> b = true \/ c = true.

Proof.
intuition. destruct b; auto.
Qed.
