(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-18

extension of BigZ
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Export BigZ.
Require Import BigNUtil.
Require Import NatUtil.

Lemma eq_bigZ_dec : forall x y : bigZ, {x=y}+{~x=y}.

Proof.
decide equality; apply eq_bigN_dec.
Defined.

Require Import Nbasic.
Import BigZ.

Lemma opp_compare_intro : forall x y, (x?=y) = opp_compare (y?=x).

Proof.
intros. generalize (spec_compare x y). generalize (spec_compare y x).
case (x?=y); case (y?=x); intros; (absurd_arith || refl).
Qed.

Lemma compare_com : forall x y c, (x?=y = c) <-> (y?=x = opp_compare c).

Proof.
intros. rewrite (opp_compare_intro y x). split; intro. rewrite H. refl.
rewrite opp_compare_eq in H. hyp.
Qed.

Lemma bigZ_le_gt_dec : forall n m, {n <= m} + {n > m}.

Proof.
intros. unfold BigZ.le, BigZ.lt. case_eq (n ?= m).
left. discr. left. discr. right. rewrite compare_com. hyp.
Defined.
