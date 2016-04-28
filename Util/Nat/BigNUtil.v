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

From Coq Require Import Int31.

Lemma eq_digits_dec : forall x y : digits, {x=y}+{~x=y}.

Proof. decide equality. Defined.

Lemma eq_int31_dec : forall x y : int31, {x=y}+{~x=y}.

Proof. (*SLOW*)decide equality; apply eq_digits_dec. Defined.

Ltac bad_case := right; intro; inversion H; contr.
Ltac case_tac x y := case (eq_digits_dec x y); [idtac|bad_case].

From Coq Require Import BigN. Import BigN.

Definition w0 := Cyclic31.Int31Cyclic.t.

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
(*SLOW*)Defined.

Lemma eq_BigN_w1_dec : forall x y : w1, {x=y}+{~x=y}.

Proof. decide equality; apply eq_BigN_w0_dec. Defined.

Lemma eq_BigN_w2_dec : forall x y : w2, {x=y}+{~x=y}.

Proof. decide equality; apply eq_BigN_w1_dec. Defined.

Lemma eq_BigN_w3_dec : forall x y : w3, {x=y}+{~x=y}.

Proof. decide equality; apply eq_BigN_w2_dec. Defined.

Lemma eq_BigN_w4_dec : forall x y : w4, {x=y}+{~x=y}.

Proof. decide equality; apply eq_BigN_w3_dec. Defined.

Lemma eq_BigN_w5_dec : forall x y : w5, {x=y}+{~x=y}.

Proof. decide equality; apply eq_BigN_w4_dec. Defined.

Lemma eq_BigN_w6_dec : forall x y : w6, {x=y}+{~x=y}.

Proof. decide equality; apply eq_BigN_w5_dec. Defined.

From Coq Require Import DoubleType.

Section zn2z.

  Variables (w : Type) (eq_dec : forall x y : w, {x=y}+{~x=y}).

  Lemma eq_zn2z_dec : forall x y : zn2z w, {x=y}+{~x=y}.

  Proof. decide equality. Defined.

End zn2z.

Section word.

  Variables (w : Type) (eq_dec : forall x y : w, {x=y}+{~x=y}).

  Lemma eq_word_dec : forall n, forall x y : word w n, {x=y}+{~x=y}.

  Proof. induction n; simpl. auto. apply eq_zn2z_dec. hyp. Defined.

End word.

From CoLoR Require Import EqUtil.

Lemma eq_bigN_dec : forall x y : bigN, {x=y}+{~x=y}.

Proof.
  induction x; destruct y; try (right; discr).
  case (eq_BigN_w0_dec t0 t1); intro. subst. auto. bad_case.
  case (eq_BigN_w1_dec w w7); intro. subst. auto. bad_case.
  case (eq_BigN_w2_dec w w7); intro. subst. auto. bad_case.
  case (eq_BigN_w3_dec w w7); intro. subst. auto. bad_case.
  case (eq_BigN_w4_dec w w7); intro. subst. auto. bad_case.
  case (eq_BigN_w5_dec w w7); intro. subst. auto. bad_case.
  case (eq_BigN_w6_dec w w7); intro. subst. auto. bad_case.
  case (eq_nat_dec n n0); [idtac|bad_case]. intro. subst n0.
  case (eq_word_dec eq_BigN_w6_dec _ w w7); intro. subst. auto.
  right. intro. inversion H. ded (inj_existT eq_nat_dec H1). contr.
Defined.

(***********************************************************************)
(** properties of ?= on BigN *)

From Coq Require Export BigN.

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
  unfold Zlt. rewrite <- Zcompare_antisym, g. refl.
Defined.
