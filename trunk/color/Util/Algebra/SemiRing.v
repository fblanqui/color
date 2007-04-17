(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-04-14

  Semi-ring structure.
*)

Require Import Ring.
Require Import Ring_theory.

(** Semi-ring structure type *)
Module Type SemiRingType.

  Parameter A : Set.
  Parameter Aplus : A -> A -> A.
  Parameter Amult : A -> A -> A.
  Parameter A0 : A.
  Parameter A1 : A.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).

  Parameter A_semi_ring : semi_ring_theory A0 A1 Aplus Amult (@eq A).

End SemiRingType.

(** Some derived results about the semi-ring structure *)
Module SemiRing (SR : SemiRingType).

  Export SR.

  Definition Aplus_comm := SRadd_comm A_semi_ring.
  Definition Aplus_assoc := SRadd_assoc A_semi_ring.
  Definition Aplus_0_l := SRadd_0_l A_semi_ring.
  Definition Amult_comm := SRmul_comm A_semi_ring.
  Definition Amult_assoc := SRmul_assoc A_semi_ring.
  Definition Amult_0_l := SRmul_0_l A_semi_ring.
  Definition Amult_1_l := SRmul_1_l A_semi_ring.
  Definition A_plus_mult_distr_l := SRdistr_l A_semi_ring.

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

  Add Ring Aring : A_semi_ring.

End SemiRing.

(** Natural numbers as a semi-ring *)

Require Import Arith.

Module NSemiRingT <: SemiRingType.

  Definition A := nat.
  Definition Aplus := plus.
  Definition Amult := mult.
  Definition A0 := 0.
  Definition A1 := 1.
  Definition Aeq := @eq nat.
  Definition A_semi_ring := natSRth.

End NSemiRingT.

Module NSemiRing := SemiRing NSemiRingT.

(** Integers as a semi-ring *)

Require Import ZArith.

Module ZSemiRingT <: SemiRingType.

  Definition A := Z.
  Definition Aplus := Zplus.
  Definition Amult := Zmult.
  Definition A0 := Z0.
  Definition A1 := Zsucc Z0.
  Definition Aeq := @eq Z.

  Lemma A_semi_ring : semi_ring_theory A0 A1 Aplus Amult Aeq.

  Proof.
    constructor. exact Zplus_0_l. exact Zplus_comm. exact Zplus_assoc.
    exact Zmult_1_l. exact Zmult_0_l. exact Zmult_comm. exact Zmult_assoc.
    exact Zmult_plus_distr_l.
  Qed.

End ZSemiRingT.

Module ZSemiRing := SemiRing ZSemiRingT.
