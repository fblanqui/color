(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-04-14

  Semi-ring structure.
*)

Require Import Ring.
Require Import Ring_theory.
Require Import RelDec.
Require Export Relations.

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

  Import SR.
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

(** Arctic semi-ring over integers with minus infinity and 
    plus-max operations *)

Module ArcticSemiRingT <: SemiRingType.

  Inductive Dom : Set := 
    | Pos (n: nat)
    | MinusInf.

  Definition A := Dom.

   (* max is a <+> operation in the semi-ring *)
  Definition Aplus m n :=
    match m, n with
    | MinusInf, n => n
    | m, MinusInf => m
    | Pos m, Pos n => Pos (max m n)
    end.

   (* plus is a <*> operation in the semi-ring *)
  Definition Amult m n := 
    match m, n with
    | MinusInf, _ => MinusInf
    | _, MinusInf => MinusInf
    | Pos m, Pos n => Pos (m + n)
    end.

  Definition A0 := MinusInf.
  Definition A1 := Pos 0.
  Definition Aeq := @eq A.

  Lemma A_plus_comm : forall m n, Aplus m n = Aplus n m.

  Proof.
    intros. unfold Aplus. destruct m; destruct n; trivial.
    rewrite max_comm. trivial.
  Qed.

  Lemma A_plus_assoc : forall m n p, Aplus m (Aplus n p) = Aplus (Aplus m n) p.

  Proof.
    intros. unfold Aplus.
    destruct m; destruct n; destruct p; trivial.
    rewrite max_assoc. trivial.
  Qed.

  Lemma A_mult_comm : forall m n, Amult m n = Amult n m.

  Proof.
    intros. unfold Amult. destruct m; destruct n; trivial.
    rewrite plus_comm. trivial.
  Qed.

  Lemma A_mult_assoc : forall m n p, Amult m (Amult n p) = Amult (Amult m n) p.

  Proof.
    intros. unfold Amult.
    destruct m; destruct n; destruct p; trivial.
    rewrite plus_assoc. trivial.
  Qed.

  Lemma A_mult_plus_distr : forall m n p,
    Amult (Aplus m n) p = Aplus (Amult m p) (Amult n p).

  Proof.
    intros. unfold Amult, Aplus. 
    destruct m; destruct n; destruct p; trivial.
    destruct (le_dec n n0).
    rewrite max_l. rewrite max_l. trivial. auto with arith. trivial.
    rewrite max_r. rewrite max_r. trivial. auto with arith. trivial.
  Qed.

  Lemma A_semi_ring : semi_ring_theory A0 A1 Aplus Amult Aeq.

  Proof.
    constructor; intros.
    compute; trivial.
    apply A_plus_comm.
    apply A_plus_assoc.
    destruct n; compute; trivial.
    compute; trivial.
    apply A_mult_comm.
    apply A_mult_assoc.
    apply A_mult_plus_distr.
  Qed.

  Lemma arctic_plus_notInf_left : forall (a b : A),
    a <> MinusInf -> Aplus a b <> MinusInf.

  Proof.
    intros. destruct a. 
    destruct b; simpl; discriminate.
    auto. 
  Qed.

  Lemma arctic_mult_notInf : forall (a b : A),
    a <> MinusInf -> b <> MinusInf -> Amult a b <> MinusInf.

  Proof.
    intros. 
    destruct a; auto. 
    destruct b; auto. 
    simpl. discriminate.
  Qed.

End ArcticSemiRingT.

Module ArcticSemiRing := SemiRing ArcticSemiRingT.

(** Semi-ring of booleans with 'or' and 'and' *)

Module BSemiRingT <: SemiRingType.

  Definition A := bool.
  Definition Aplus := orb.
  Definition Amult := andb.
  Definition A0 := false.
  Definition A1 := true.
  Definition Aeq := @eq bool.

  Lemma A_semi_ring : semi_ring_theory A0 A1 Aplus Amult Aeq.

  Proof.
    constructor.
    intros; apply orb_false_l.
    intros; apply orb_comm.
    intros; apply orb_assoc.
    intros; apply andb_true_l.
    intros; apply andb_false_l.
    intros; apply andb_comm.
    intros; apply andb_assoc.
    intros; apply andb_orb_distrib_l.
  Qed.

End BSemiRingT.

Module BSemiRing := SemiRing BSemiRingT.
