(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-18

extension of BigN
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil.

(***********************************************************************)
(** decidability of equality *)

From Bignums Require Export BigN. Import BigN.

From Stdlib Require Import DoubleType.

Section zn2z.

  Variables (w : Type) (eq_dec : forall x y : w, {x=y}+{~x=y}).

  Lemma eq_zn2z_dec : forall x y : zn2z w, {x=y}+{~x=y}.

  Proof. decide equality. Defined.

End zn2z.

Section word.

  (* For backward compatibility. The intended value is Set,
     but we use Type when compiling against an old version
     of the standard library. *)
  Definition univ_of_cycles : Type.
  Proof.
    first [let _ := constr:(word : Set -> nat -> Set) in exact Set | exact Type].
  Defined.

  Variables (w : univ_of_cycles) (eq_dec : forall x y : w, {x=y}+{~x=y}).

  Lemma eq_word_dec : forall n, forall x y : word w n, {x=y}+{~x=y}.

  Proof. induction n; simpl. auto. apply eq_zn2z_dec. hyp. Defined.

End word.

From CoLoR Require Import EqUtil.

(***********************************************************************)
(** properties of ?= on BigN *)
Import ZArith.

Open Scope bigN_scope.

Lemma compare_antisym : forall x y, CompOpp (x?=y) = (y?=x).

Proof. intros x y. rewrite !spec_compare. apply Zcompare_antisym. Qed.

From CoLoR Require Import OrdUtil.

Lemma compare_antisym_eq : forall x y c, (x?=y = CompOpp c) <-> (y?=x = c).

Proof.
  intros. rewrite <- (compare_antisym y x). split; intro.
  rewrite CompOpp_eq in H. hyp. rewrite H. refl.
Qed.

(***********************************************************************)
(** decidability of comparison *)

Lemma bigN_le_gt_dec : forall n m, {n <= m} + {n > m}.

Proof.
  intros. unfold le, lt. destruct (Z_le_gt_dec [n] [m]). left. hyp. right.
  unfold Z.lt. rewrite <- Zcompare_antisym, g. refl.
Defined.
