(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-18

extension of BigN
*)

Set Implicit Arguments.

Require Import LogicUtil.

(***********************************************************************)
(** decidability of equality *)

Require Import Int31.

Lemma eq_digits_dec : forall x y : digits, {x=y}+{~x=y}.

Proof.
decide equality.
Defined.

Lemma eq_int31_dec : forall x y : int31, {x=y}+{~x=y}.

Proof.
decide equality; apply eq_digits_dec.
Defined.

Ltac bad_case := right; intro; inversion H; contradiction.
Ltac case_tac x y := case (eq_digits_dec x y); [idtac|bad_case].

Require Import BigN. Import BigN.

Lemma eq_BigN_w0_dec : forall x y : w0, {x=y}+{~x=y}.

Proof.
destruct x. destruct y.
case_tac d d30. case_tac d0 d31. case_tac d1 d32. case_tac d2 d33.
case_tac d3 d34. case_tac d4 d35. case_tac d5 d36. case_tac d6 d37.
case_tac d7 d38. case_tac d8 d39. case_tac d9 d40. case_tac d10 d41.
case_tac d11 d42. case_tac d12 d43. case_tac d13 d44. case_tac d14 d45.
case_tac d15 d46. case_tac d16 d47. case_tac d17 d48. case_tac d18 d49.
case_tac d19 d50. case_tac d20 d51. case_tac d21 d52. case_tac d22 d53.
case_tac d23 d54. case_tac d24 d55. case_tac d25 d56. case_tac d26 d57.
case_tac d27 d58. case_tac d28 d59. case_tac d29 d60. intros. subst. auto.
Defined.

Lemma eq_BigN_w1_dec : forall x y : w1, {x=y}+{~x=y}.
Proof.
decide equality; apply eq_BigN_w0_dec.
Defined.

Lemma eq_BigN_w2_dec : forall x y : w2, {x=y}+{~x=y}.
Proof.
decide equality; apply eq_BigN_w1_dec.
Defined.

Lemma eq_BigN_w3_dec : forall x y : w3, {x=y}+{~x=y}.
Proof.
decide equality; apply eq_BigN_w2_dec.
Defined.

Lemma eq_BigN_w4_dec : forall x y : w4, {x=y}+{~x=y}.
Proof.
decide equality; apply eq_BigN_w3_dec.
Defined.

Lemma eq_BigN_w5_dec : forall x y : w5, {x=y}+{~x=y}.
Proof.
decide equality; apply eq_BigN_w4_dec.
Defined.

Lemma eq_BigN_w6_dec : forall x y : w6, {x=y}+{~x=y}.
Proof.
decide equality; apply eq_BigN_w5_dec.
Defined.

Require Import DoubleType.

Section zn2z.

  Variable w : Type.
  Variable eq_dec : forall x y : w, {x=y}+{~x=y}.

  Lemma eq_zn2z_dec : forall x y : zn2z w, {x=y}+{~x=y}.
  Proof.
  decide equality.
  Defined.

End zn2z.

Section word.

  Variable w : Type.
  Variable eq_dec : forall x y : w, {x=y}+{~x=y}.

  Lemma eq_word_dec : forall n, forall x y : word w n, {x=y}+{~x=y}.
  Proof.
  induction n; simpl. auto. apply eq_zn2z_dec. hyp.
  Defined.

End word.

Require Import EqUtil.

Lemma eq_bigN_dec : forall x y : bigN, {x=y}+{~x=y}.

Proof.
induction x; destruct y; try (right; discr).
case (eq_BigN_w0_dec w w7); intro. subst. auto. bad_case.
case (eq_BigN_w1_dec w w7); intro. subst. auto. bad_case.
case (eq_BigN_w2_dec w w7); intro. subst. auto. bad_case.
case (eq_BigN_w3_dec w w7); intro. subst. auto. bad_case.
case (eq_BigN_w4_dec w w7); intro. subst. auto. bad_case.
case (eq_BigN_w5_dec w w7); intro. subst. auto. bad_case.
case (eq_BigN_w6_dec w w7); intro. subst. auto. bad_case.
case (eq_nat_dec n n0); [idtac|bad_case]. intro. subst n0.
case (eq_word_dec eq_BigN_w6_dec _ w w7); intro. subst. auto.
right. intro. inversion H. ded (inj_pairT2 eq_nat_dec H1). contradiction.
Defined.

(***********************************************************************)
(** properties of Nbasic.opp_compare *)

Require Import NatUtil.
Require Export BigN.
Require Import Nbasic.

Lemma opp_compare_intro : forall x y, (x?=y) = opp_compare (y?=x).

Proof.
intros. generalize (spec_compare x y). generalize (spec_compare y x).
case (x?=y); case (y?=x); intros; (absurd_arith || refl).
Qed.

Lemma opp_compare_elim : forall c, opp_compare (opp_compare c) = c.

Proof.
destruct c; refl.
Qed.

Lemma opp_compare_eq : forall c d, opp_compare c = opp_compare d <-> c = d.

Proof.
destruct c; destruct d; simpl; intuition; discr.
Qed.

Lemma compare_com : forall x y c, (x?=y = c) <-> (y?=x = opp_compare c).

Proof.
intros. rewrite (opp_compare_intro y x). split; intro. rewrite H. refl.
rewrite opp_compare_eq in H. hyp.
Qed.

(***********************************************************************)
(** decidability of comparison *)

Lemma bigN_le_gt_dec : forall n m, {n <= m} + {n > m}.

Proof.
intros. unfold le, lt. case_eq (n ?= m).
left. discr. left. discr. right. rewrite compare_com. hyp.
Defined.
