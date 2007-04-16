(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-04-14

  Structure of coefficients with addition and multiplication 
used for vector and matrix arithmetics.
*)

(** Carrier with addition and multiplication *)
Module Type CoefType.

  Parameter A : Set.
  Parameter Aplus : A -> A -> A.
  Parameter Amult : A -> A -> A.
  Parameter A0 : A.
  Parameter A1 : A.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).

  Section Axioms.

    Variables m n : A.

    Parameter Aplus_comm : m + n = n + m.
    Parameter Aplus_0_l : A0 + n = n.

    Parameter Amult_comm : m * n = n * m.
    Parameter Amult_0_l : A0 * n = A0.
    Parameter Amult_1_l : A1 * n = n.

  End Axioms.

End CoefType.

(** Some derived results about the structure of coefficients *)
Module Coef (C : CoefType).

  Export C.

  Lemma Aplus_0_r : forall n, n + A0 = n.

  Proof.
    intros. rewrite Aplus_comm. apply Aplus_0_l.
  Qed.

  Lemma Amult_0_r : forall n, n * A0 = A0.

  Proof.
    intros. rewrite Amult_comm. apply Amult_0_l.
  Qed.

  Lemma Amult_1_r : forall n, n * A1 = n.

  Proof.
    intros. rewrite Amult_comm. apply Amult_1_l.
  Qed.

  Hint Rewrite Aplus_0_l Aplus_0_r Amult_0_l Amult_0_r 
    Amult_1_l Amult_1_r : arith.

End Coef.

(** Natural numbers coefficients *)

Require Import Arith.

Module NCoefT <: CoefType.

  Definition A := nat.
  Definition Aplus := plus.
  Definition Amult := mult.
  Definition A0 := 0.
  Definition A1 := 1.
  Definition Aplus_comm := plus_comm.
  Definition Aplus_0_l := plus_0_l.
  Definition Amult_comm := mult_comm.
  Definition Amult_0_l := mult_0_l.
  Definition Amult_1_l := mult_1_l.

End NCoefT.

Module NCoef := Coef NCoefT.

(** Integer coefficients *)

Require Import ZArith.

Module ZCoefT <: CoefType.

  Definition A := Z.
  Definition Aplus := Zplus.
  Definition Amult := Zmult.
  Definition A0 := Z0.
  Definition A1 := Zsucc Z0.
  Definition Aplus_comm := Zplus_comm.
  Definition Aplus_0_l := Zplus_0_l.
  Definition Amult_comm := Zmult_comm.
  Definition Amult_0_l := Zmult_0_l.
  Definition Amult_1_l := Zmult_1_l.

End ZCoefT.

Module ZCoef := Coef ZCoefT.
