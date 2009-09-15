(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski, 2007-04-14

Semi-ring structure.
*)

Require Export Ring.
Require Export Ring_theory.
Require Import RelDec.
Require Import Relations.
Require Import Max.
Require Import Arith.
Require Import Compare.
Require Import LogicUtil.
Require Import Bool.
Require Import RelExtras.
Require Import Setoid.
Require Import EqUtil.
Require Import NatUtil.
Require Import ZUtil.

(***********************************************************************)
(** Semi-ring structure type *)

Module Type SemiRingType.

  Declare Module Export ES : Eqset_dec.

  (*FIXME: move to Eqset ? *)
  Add Setoid A eqA sid_theoryA as A_Setoid.

  Parameter A0 : A.
  Parameter A1 : A.

  Parameter Aplus : A -> A -> A.
  Notation "x + y" := (Aplus x y).

  Add Morphism Aplus with signature eqA ==> eqA ==> eqA as Aplus_mor.

  Parameter Amult : A -> A -> A.
  Notation "x * y" := (Amult x y).

  Add Morphism Amult with signature eqA ==> eqA ==> eqA as Amult_mor.

  Parameter A_semi_ring : semi_ring_theory A0 A1 Aplus Amult eqA.

End SemiRingType.

(***********************************************************************)
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

  Lemma Aplus_0_r : forall n, n + A0 =A= n.

  Proof.
    intros. rewrite Aplus_comm. apply Aplus_0_l.
  Qed.

  Lemma Amult_0_r : forall n, n * A0 =A= A0.

  Proof.
    intros. rewrite Amult_comm. apply Amult_0_l.
  Qed.

  Lemma Amult_1_r : forall n, n * A1 =A= n.

  Proof.
    intros. rewrite Amult_comm. apply Amult_1_l.
  Qed.

  Lemma A_plus_mult_distr_r : forall m n p,
    m * (n + p) =A= m * n + m * p.

  Proof.
    intros. rewrite Amult_comm. 
    rewrite (Amult_comm m n). rewrite (Amult_comm m p).
    apply A_plus_mult_distr_l.
  Qed.

  Hint Rewrite Aplus_0_l Aplus_0_r Amult_0_l Amult_0_r 
    Amult_1_l Amult_1_r : arith.

  Add Ring Aring : A_semi_ring.

End SemiRing.

(***********************************************************************)
(** Natural numbers as a semi-ring *)

Require Import Arith.

Module Nat <: SetA.
  Definition A := nat.
End Nat.

Module Nat_Eqset := Eqset_def Nat.

Module Nat_Eqset_dec <: Eqset_dec.
  Module Export Eq := Nat_Eqset.
  Definition eqA_dec := dec_beq beq_nat_ok.
End Nat_Eqset_dec.

Module NSemiRingT <: SemiRingType.

  Module Export ES := Nat_Eqset_dec.

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Definition A0 := 0.
  Definition A1 := 1.

  Definition Aplus := plus.

  Add Morphism Aplus with signature eqA ==> eqA ==> eqA as Aplus_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Amult := mult.

  Add Morphism Amult with signature eqA ==> eqA ==> eqA as Amult_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition A_semi_ring := natSRth.

End NSemiRingT.

Module NSemiRing := SemiRing NSemiRingT.

(***********************************************************************)
(** BigN natural numbers as a semi-ring *)

Require Import BigN.

Module BigNat_Eqset <: Eqset.
  Definition A := bigN.
  Definition eqA := BigN.eq.
  Definition sid_theoryA : Setoid_Theory A eqA.
  Proof.
    unfold eqA. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. symmetry. hyp.
    unfold Transitive. intros. transitivity y; hyp.
  Qed.
End BigNat_Eqset.

Module BigNat_Eqset_dec <: Eqset_dec.
  Module Export Eq := BigNat_Eqset.
  Lemma eqA_dec : forall x y, {eqA x y}+{~eqA x y}.
  Proof.
    unfold eqA. unfold BigN.eq. intros. apply (dec_beq beq_Z_ok).
  Defined.
End BigNat_Eqset_dec.

Module BigNSemiRingT <: SemiRingType.

  Module Export ES := BigNat_Eqset_dec.

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Definition A0 := BigN.zero.
  Definition A1 := BigN.one.

  Definition Aplus := BigN.add.

  Add Morphism Aplus with signature eqA ==> eqA ==> eqA as Aplus_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Amult := BigN.mul.

  Add Morphism Amult with signature eqA ==> eqA ==> eqA as Amult_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition A_semi_ring := BigNring.

End BigNSemiRingT.

Module BigNSemiRing := SemiRing BigNSemiRingT.

(***********************************************************************)
(** Integers as a semi-ring *)

Require Import ZArith.

Module Int <: SetA.
  Definition A := Z.
End Int.

Module Int_Eqset := Eqset_def Int.

Module Int_Eqset_dec <: Eqset_dec.
  Module Export Eq := Int_Eqset.
  Definition eqA_dec := dec_beq beq_Z_ok.
End Int_Eqset_dec.

Module ZSemiRingT <: SemiRingType.

  Module Export ES := Int_Eqset_dec.

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Definition A0 := 0%Z.
  Definition A1 := 1%Z.

  Definition Aplus := Zplus.

  Add Morphism Aplus with signature eqA ==> eqA ==> eqA as Aplus_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Amult := Zmult.

  Add Morphism Amult with signature eqA ==> eqA ==> eqA as Amult_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_semi_ring : semi_ring_theory A0 A1 Aplus Amult eqA.

  Proof.
    constructor.
    exact Zplus_0_l.
    exact Zplus_comm.
    exact Zplus_assoc.
    exact Zmult_1_l.
    exact Zmult_0_l.
    exact Zmult_comm.
    exact Zmult_assoc.
    exact Zmult_plus_distr_l.
  Qed.

End ZSemiRingT.

Module ZSemiRing := SemiRing ZSemiRingT.

(***********************************************************************)
(** BigZ integers as a semi-ring *)

Require Import BigZ.

Module BigInt_Eqset <: Eqset.
  Definition A := bigZ.
  Definition eqA := BigZ.eq.
  Definition sid_theoryA : Setoid_Theory A eqA.
  Proof.
    unfold eqA. constructor.
    unfold Reflexive. refl.
    unfold Symmetric. symmetry. hyp.
    unfold Transitive. intros. transitivity y; hyp.
  Qed.
End BigInt_Eqset.

Module BigInt_Eqset_dec <: Eqset_dec.
  Module Export Eq := BigInt_Eqset.
  Lemma eqA_dec : forall x y, {eqA x y}+{~eqA x y}.
  Proof.
    unfold eqA. unfold BigZ.eq. intros. apply (dec_beq beq_Z_ok).
  Defined.
End BigInt_Eqset_dec.

Module BigZSemiRingT <: SemiRingType.

  Module Export ES := BigInt_Eqset_dec.

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Definition A0 := BigZ.zero.
  Definition A1 := BigZ.one.

  Definition Aplus := BigZ.add.

  Add Morphism Aplus with signature eqA ==> eqA ==> eqA as Aplus_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Amult := BigZ.mul.

  Add Morphism Amult with signature eqA ==> eqA ==> eqA as Amult_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_semi_ring : semi_ring_theory A0 A1 Aplus Amult eqA.

  Proof.
  constructor.
  exact Zadd_0_l.
  exact Zadd_comm.
  exact Zadd_assoc.
  exact Zmul_1_l.
  exact Zmul_0_l.
  exact Zmul_comm.
  exact Zmul_assoc.
  exact Zmul_add_distr_r.
  Qed.

End BigZSemiRingT.

Module BigZSemiRing := SemiRing BigZSemiRingT.

(***********************************************************************)
(** Arctic semi-ring over naturals with minus infinity and 
    plus-max operations *)

Inductive ArcticDom : Type := 
| Pos (n : nat)
| MinusInf.

Definition beq_ArcticDom x y :=
  match x, y with
    | Pos x', Pos y' => beq_nat x' y'
    | MinusInf, MinusInf => true
    | _, _ => false
  end.

Lemma beq_ArcticDom_ok : forall x y, beq_ArcticDom x y = true <-> x = y.

Proof.
unfold beq_ArcticDom. destruct x; destruct y; simpl; try (intuition; discr).
rewrite beq_nat_ok. intuition. inversion H. refl.
Qed.

Definition is_finite v :=
  match v with
    | MinusInf => false
    | _ => true
  end.

Lemma is_finite_ok : forall v, is_finite v = true <-> v <> MinusInf.

Proof.
  intro. destruct v; simpl; intuition. discriminate.
Qed.

Module Arctic <: SetA.
  Definition A := ArcticDom.
End Arctic.

Module Arctic_Eqset := Eqset_def Arctic.

Module Arctic_Eqset_dec <: Eqset_dec.
  Module Export Eq := Arctic_Eqset.
  Definition eqA_dec := dec_beq beq_ArcticDom_ok.
  (*REMOVE: direct proof to be removed?
  Lemma eqA_dec : forall x y : A, {x=y}+{~x=y}.
  Proof.
    intros. destruct x; destruct y; try solve [right; congruence].
    destruct (eq_nat_dec n0 n).
    subst n. auto.
    right. congruence.
    left. auto.
  Defined.*)
End Arctic_Eqset_dec.

Module ArcticSemiRingT <: SemiRingType.

  Module Export ES := Arctic_Eqset_dec.

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Definition A0 := MinusInf.
  Definition A1 := Pos 0.

  (* max is a <+> operation in the semi-ring *)
  Definition Aplus m n :=
    match m, n with
    | MinusInf, n => n
    | m, MinusInf => m
    | Pos m, Pos n => Pos (max m n)
    end.

  Add Morphism Aplus with signature eqA ==> eqA ==> eqA as Aplus_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  (* plus is a <*> operation in the semi-ring *)
  Definition Amult m n := 
    match m, n with
    | MinusInf, _ => MinusInf
    | _, MinusInf => MinusInf
    | Pos m, Pos n => Pos (m + n)
    end.

  Add Morphism Amult with signature eqA ==> eqA ==> eqA as Amult_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

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

  Import Compare. Import Max.

  Lemma A_mult_plus_distr : forall m n p,
    Amult (Aplus m n) p = Aplus (Amult m p) (Amult n p).

  Proof.
    intros. unfold Amult, Aplus.
    destruct m; destruct n; destruct p; trivial.
    destruct (le_dec n n0).
    rewrite max_l. rewrite max_l. trivial. auto with arith. trivial.
    rewrite max_r. rewrite max_r. trivial. auto with arith. trivial.
  Qed.

  Lemma A_semi_ring : semi_ring_theory A0 A1 Aplus Amult eqA.

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

  Lemma arctic_plus_notInf_left : forall a b,
    a <> MinusInf -> Aplus a b <> MinusInf.

  Proof.
    intros. destruct a. 
    destruct b; simpl; discriminate.
    auto. 
  Qed.

  Lemma arctic_mult_notInf : forall a b,
    a <> MinusInf -> b <> MinusInf -> Amult a b <> MinusInf.

  Proof.
    intros. 
    destruct a; auto. 
    destruct b; auto. 
    simpl. discriminate.
  Qed.

End ArcticSemiRingT.

Module ArcticSemiRing := SemiRing ArcticSemiRingT.

(***********************************************************************)
(** Arctic semi-ring over integers with minus infinity and 
    plus-max operations *)

Require Import ZUtil.

Inductive ArcticBZDom : Type := 
| Fin (z : Z)
| MinusInfBZ.

Definition beq_ArcticBZDom x y :=
  match x, y with
    | Fin x', Fin y' => beq_Z x' y'
    | MinusInfBZ, MinusInfBZ => true
    | _, _ => false
  end.

Lemma beq_ArcticBZDom_ok : forall x y, beq_ArcticBZDom x y = true <-> x = y.

Proof.
unfold beq_ArcticBZDom. destruct x; destruct y; simpl; try (intuition; discr).
rewrite beq_Z_ok. intuition. subst. refl. inversion H. refl.
Qed.

Module ArcticBZ <: SetA.
  Definition A := ArcticBZDom.
End ArcticBZ.

Module ArcticBZ_Eqset := Eqset_def ArcticBZ.

Module ArcticBZ_Eqset_dec <: Eqset_dec.
  Module Export Eq := ArcticBZ_Eqset.
  Definition eqA_dec := dec_beq beq_ArcticBZDom_ok.
  (*REMOVE: direct proof to be removed?
  Lemma eqA_dec : forall x y : A, {x=y}+{~x=y}.
  Proof.
    intros. destruct x; destruct y; try solve [right; congruence].
    destruct (Z_eq_dec z0 z).
    subst z. auto.
    right. congruence.
    left. auto.
  Defined.*)
End ArcticBZ_Eqset_dec.

Module ArcticBZSemiRingT <: SemiRingType.

  Module Export ES := ArcticBZ_Eqset_dec.

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Definition A0 := MinusInfBZ.
  Definition A1 := Fin 0.

  (* max is a <+> operation in the semi-ring *)
  Definition Aplus m n :=
    match m, n with
    | MinusInfBZ, n => n
    | m, MinusInfBZ => m
    | Fin m, Fin n => Fin (Zmax m n)
    end.

  Add Morphism Aplus with signature eqA ==> eqA ==> eqA as Aplus_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  (* plus is a <*> operation in the semi-ring *)
  Definition Amult m n := 
    match m, n with
    | MinusInfBZ, _ => MinusInfBZ
    | _, MinusInfBZ => MinusInfBZ
    | Fin m, Fin n => Fin (m + n)
    end.

  Add Morphism Amult with signature eqA ==> eqA ==> eqA as Amult_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_plus_comm : forall m n, Aplus m n = Aplus n m.

  Proof.
    intros. unfold Aplus. destruct m; destruct n; trivial. 
    rewrite Zmax_comm. refl.
  Qed.

  Lemma A_plus_assoc : forall m n p, Aplus m (Aplus n p) = Aplus (Aplus m n) p.

  Proof.
    intros. unfold Aplus.
    destruct m; destruct n; destruct p; trivial.
    rewrite Zmax_assoc. refl.
  Qed.

  Lemma A_mult_comm : forall m n, Amult m n = Amult n m.

  Proof.
    intros. unfold Amult. destruct m; destruct n; trivial.
    rewrite Zplus_comm. refl.
  Qed.

  Lemma A_mult_assoc : forall m n p, Amult m (Amult n p) = Amult (Amult m n) p.

  Proof.
    intros. unfold Amult.
    destruct m; destruct n; destruct p; trivial.
    rewrite Zplus_assoc. refl.
  Qed.

  Lemma A_mult_plus_distr : forall m n p,
    Amult (Aplus m n) p = Aplus (Amult m p) (Amult n p).

  Proof.
    intros. unfold Amult, Aplus. 
    destruct m; destruct n; destruct p; trivial.
    rewrite Zplus_max_distr_r.
    destruct (Zmax_irreducible_inf z z0); rewrite H; refl.
  Qed.

  Lemma A_semi_ring : semi_ring_theory A0 A1 Aplus Amult eqA.

  Proof.
    constructor; intros.
    compute; trivial.
    apply A_plus_comm.
    apply A_plus_assoc.
    destruct n; unfold eqA; refl.
    unfold eqA. trivial.
    apply A_mult_comm.
    apply A_mult_assoc.
    apply A_mult_plus_distr.
  Qed.

  Lemma arctic_plus_notInf_left : forall (a b : A),
    a <> MinusInfBZ -> Aplus a b <> MinusInfBZ.

  Proof.
    intros. destruct a. 
    destruct b; simpl; discriminate.
    auto. 
  Qed.

  Lemma arctic_mult_notInf : forall (a b : A),
    a <> MinusInfBZ -> b <> MinusInfBZ -> Amult a b <> MinusInfBZ.

  Proof.
    intros. 
    destruct a; auto. 
    destruct b; auto.
    simpl. discriminate.
  Qed.

End ArcticBZSemiRingT.

Module ArcticBZSemiRing := SemiRing ArcticBZSemiRingT.

(***********************************************************************)
(** Semi-ring of booleans with 'or' and 'and' *)

Module Bool <: SetA.
  Definition A := bool.
End Bool.

Module Bool_Eqset := Eqset_def Bool.

Module Bool_Eqset_dec <: Eqset_dec.
  Module Export Eq := Bool_Eqset.
  Definition eqA_dec := bool_dec.
End Bool_Eqset_dec.

Module BSemiRingT <: SemiRingType.

  Module Export ES := Bool_Eqset_dec.

  Add Setoid A eqA sid_theoryA as A_Setoid.

  Definition A0 := false.
  Definition A1 := true.

  Definition Aplus := orb.

  Add Morphism Aplus with signature eqA ==> eqA ==> eqA as Aplus_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Definition Amult := andb.

  Add Morphism Amult with signature eqA ==> eqA ==> eqA as Amult_mor.
  Proof.
    intros. rewrite H. rewrite H0. refl.
  Qed.

  Lemma A_semi_ring : semi_ring_theory A0 A1 Aplus Amult eqA.

  Proof.
    constructor; intros.
    apply orb_false_l.
    apply orb_comm.
    apply orb_assoc.
    apply andb_true_l.
    apply andb_false_l.
    apply andb_comm.
    apply andb_assoc.
    apply andb_orb_distrib_l.
  Qed.

End BSemiRingT.

Module BSemiRing := SemiRing BSemiRingT.
