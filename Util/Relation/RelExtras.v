(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2004-09-06
- William Delobel, 2005-10-07

This file provides some basic results concerning relations that were
missing in the standard library.
*)

Set Implicit Arguments.

From Coq Require Export Relations.
From Coq Require Import Max Arith Setoid Morphisms Basics ZArith.
From CoLoR Require Import LogicUtil RelUtil.

(***********************************************************************)
(** strict order *)

Section StrictOrder.

  Variables (A : Type) (R : relation A).

  Record strict_order : Prop := {
    sord_trans : transitive R;
    sord_irrefl : irreflexive R }.

  Variable so : strict_order.

  Lemma so_not_symmetric : forall a b, R a b -> R b a -> False.

  Proof.
    unfold not; intros a b Rab Rba.
    exact (sord_irrefl so (sord_trans so Rab Rba)).
  Qed.

  Variables (eq : relation A)
            (Req_compat : Proper (eq ==> eq ==> impl) R)
            (eq_Equivalence : Equivalence eq).

  Existing Instance eq_Equivalence.
  Existing Instance Req_compat.

  Lemma so_strict : forall x y, eq x y -> ~R x y.

  Proof. intros x y xy. rewrite xy. apply sord_irrefl. hyp. Qed.

End StrictOrder.

(***********************************************************************)
(** module types for setoids with decidable equality *)

Module Type SetA.
  Parameter A : Type.
End SetA.

Module Type Eqset.

  Parameter A : Type.

  Parameter eqA : relation A.
  Notation "X =A= Y" := (eqA X Y) (at level 70).

  Declare Instance eqA_Equivalence : Equivalence eqA.

  #[global] Hint Resolve (Seq_refl  A eqA eqA_Equivalence) : sets.
  #[global] Hint Resolve (Seq_trans A eqA eqA_Equivalence) : sets.
  #[global] Hint Resolve (Seq_sym   A eqA eqA_Equivalence) : sets.

End Eqset.

Module Type Eqset_dec.

  Declare Module Export Eq : Eqset.

  Parameter eqA_dec : forall x y, {x =A= y} + {~x =A= y}.

End Eqset_dec.

Module Eqset_def (A : SetA) <: Eqset.

  Definition A := A.A.

  Definition eqA := eq (A:=A).

  Instance eqA_Equivalence : Equivalence eqA.

  Proof. unfold eqA. class. Qed.

  #[global] Hint Resolve (Seq_refl  A eqA eqA_Equivalence) : sets.
  #[global] Hint Resolve (Seq_trans A eqA eqA_Equivalence) : sets.
  #[global] Hint Resolve (Seq_sym   A eqA eqA_Equivalence) : sets.

End Eqset_def.

(***********************************************************************)
(** module types for ordered setoids *)

Section Eqset_def_gtA_eqA_compat.

  Variables (A : Type) (gtA : relation A).

  Instance Eqset_def_gtA_eqA_compat : Proper (eq ==> eq ==> impl) gtA.

  Proof.
    intros x x' x_x' y y' y_y' x_y. rewrite <- x_x', <- y_y'; trivial.
  Qed.

End Eqset_def_gtA_eqA_compat.

Module Type Ord.

  Parameter A : Type.

  Declare Module Export S : Eqset with Definition A := A.

  Parameter gtA : relation A.
  Notation "X >A Y" := (gtA X Y) (at level 70).

  Declare Instance gtA_eqA_compat : Proper (eqA ==> eqA ==> impl) gtA.

  #[global] Hint Resolve gtA_eqA_compat : sets.

End Ord.

Module OrdLemmas (Export P : Ord).

  Definition ltA := transp gtA.
  Definition geA x y := ~ ltA x y.
  Definition leA x y := ~ gtA x y.
  Definition AccA := Acc ltA.

  Notation "X <A Y" := (ltA X Y) (at level 70).
  Notation "X >=A Y" := (geA X Y) (at level 70).
  Notation "X <=A Y" := (leA X Y) (at level 70).

  #[global] Hint Unfold ltA geA leA AccA : sets.

(*REMOVE?*)
  Instance gtA_morph : Proper (eqA ==> eqA ==> iff) gtA.

  Proof. intros a b ab c d cd. split; apply gtA_eqA_compat; (hyp||sym;hyp). Qed.

(*REMOVE?*)
  Instance ltA_morph : Proper (eqA ==> eqA ==> iff) ltA.

  Proof. intros a b ab c d cd. split; apply gtA_eqA_compat; (hyp||sym;hyp). Qed.

  Instance AccA_morph : Proper (eqA ==> iff) AccA.

  Proof.
    intros a b eq_ab. split.
    intro acc_a. inversion acc_a. constructor. intros.
    apply H. rewrite eq_ab. hyp.
    intros acc_b. inversion acc_b. constructor. intros.
    apply H. rewrite <- eq_ab. hyp.
  Qed.

End OrdLemmas.

Module Type Poset.

  Parameter A : Type.

  Declare Module Export O : Ord with Definition A := A.

  Parameter gtA_so : strict_order gtA.

  #[global] Hint Resolve (sord_trans gtA_so) : sets.
  #[global] Hint Resolve (sord_irrefl gtA_so) : sets.
  #[global] Hint Resolve (so_not_symmetric gtA_so) : sets.
  #[global] Hint Resolve (so_strict gtA_so gtA_eqA_compat eqA_Equivalence) : sets.

End Poset.

Module nat_ord <: Ord.

  Module natSet <: SetA.
    Definition A := nat.
    Definition eqA_dec := eq_nat_dec.
  End natSet.

  Module S := Eqset_def natSet.

  Definition A := nat.
  Definition gtA := gt.

  Instance gtA_eqA_compat : Proper (eq ==> eq ==> impl) gt.

  Proof. firstorder auto with zarith. Qed.

End nat_ord.

(***********************************************************************)
(** specification *)

Section Specif.

  Inductive sigPS2 (A : Type) (P : A -> Prop) (Q : A -> Set) : Type :=
    existPS2 : forall x, P x -> Q x -> sigPS2 (A:=A) P Q.

  Notation "{ x : A # P & Q }"
    := (sigPS2 (fun x : A => P) (fun x : A => Q)) : type_scope.

  Variables (A : Type) (P Q : A -> Prop).

  Definition proj1_sig2 (e: sig2 P Q) :=
    match e with
    | exist2 _ _ a p q => a
    end.

End Specif.

(***********************************************************************)
(** tactics *)

Ltac rewrite_lr term := apply (proj1 term).
Ltac rewrite_rl term := apply (proj2 term).

Ltac try_solve := 
   simpl in *; try (intros; solve 
     [ contr 
     | discr 
     | auto with terms
     | tauto
     | congruence
     ]).
