(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-25

lexicographic ordering
************************************************************************)

(* $Id: Lexico.v,v 1.1 2006-10-26 14:26:06 blanqui Exp $ *)

Set Implicit Arguments.

Require Export RelUtil.

Section lt_lexp.

Variable (A : Set) (ltA eqA : relation A)
  (Hcomp : inclusion (compose ltA eqA) ltA).

Lemma comp_Acc : forall a, Acc ltA a -> forall a', eqA a' a -> Acc ltA a'.

Proof.
intros a Acc_a a' eqa'a. apply Acc_intro. intros a'' lta''a'.
inversion Acc_a as [H]. apply H. apply (incl_elim Hcomp). exists a'. auto.
Qed.

Variable (B : Set) (ltB : relation B).

Inductive lexp : relation (prod A B) :=
| lexp1 : forall a a' b b', ltA a' a -> lexp (a',b') (a,b)
| lexp2 : forall a a' b b', eqA a' a -> ltB b' b -> lexp (a',b') (a,b).

Variable (ltB_well_founded : well_founded ltB)
  (eqA_trans : transitive eqA).

Lemma lexp_Acc_eq : forall a b, Acc lexp (a,b) ->
  forall a', eqA a' a -> Acc lexp (a',b).

Proof.
intros a b Acc_ab a' eqa'a. inversion Acc_ab as [H]. apply Acc_intro.
destruct y as (a'',b'). intro H'. inversion H'; subst a'0 b'0 a0 b0; apply H.
apply lexp1. apply (incl_elim Hcomp). exists a'. auto.
apply lexp2. apply (eqA_trans H3 eqa'a). exact H5.
Qed.

Lemma lexp_Acc :
  forall a, Acc ltA a -> forall b, Acc ltB b -> Acc lexp (a, b).

Proof.
induction 1 as [a Ha1 Ha2]. induction 1 as [b Hb1 Hb2]. apply Acc_intro.
destruct y as (a'',b'). intro H. inversion H; subst a'' b'0 a0 b0.
(* ltA a' a *)
apply Ha2. exact H1. apply ltB_well_founded.
(* eqA a' a /\ ltB b' b *)
apply (@lexp_Acc_eq a). 2: exact H3. apply Hb2. exact H5.
Qed.

Variable ltA_well_founded : well_founded ltA.

Lemma lexp_well_founded : well_founded lexp.

Proof.
unfold well_founded. destruct a as (a,b). apply lexp_Acc.
apply ltA_well_founded. apply ltB_well_founded.
Qed.

Lemma lexp_intro : forall a a' b b',
  ltA a a' \/ (eqA a a' /\ ltB b b') -> lexp (a,b) (a',b').

Proof.
intros. destruct H. apply lexp1. exact H. destruct H. apply lexp2.
exact H. exact H0.
Qed.

End lt_lexp.

Section gt_lexp.

Require Export WfUtil.

Variable (A B : Set) (gtA eqA : relation A) (gtB : relation B)
  (eqA_trans : transitive eqA)
  (Hcomp : inclusion (compose eqA gtA) gtA)
  (gtA_wf : wf gtA) (gtB_wf : wf gtB).

Lemma transp_lexp : inclusion (transp (lexp gtA eqA gtB))
  (lexp (transp gtA) (transp eqA) (transp gtB)).

Proof.
unfold inclusion. destruct x as (a,b). destruct y as (a',b'). intro.
unfold transp in H. inversion H; subst a'0 b'0 a0 b0.
apply lexp1. exact H1. apply lexp2; auto.
Qed.

Lemma lexp_wf : wf (lexp gtA eqA gtB).

Proof.
apply (wf_incl transp_lexp). apply lexp_well_founded.
unfold inclusion, compose, transp. intros. destruct H. destruct H.
apply (incl_elim Hcomp). exists x0. auto. exact gtB_wf.
apply transp_trans. apply eqA_trans. exact gtA_wf.
Qed.

End gt_lexp.

Section gt_lex.

Variable (A : Set) (gtA eqA gtA' : relation A)
  (eqA_trans : transitive eqA)
  (Hcomp : inclusion (compose eqA gtA) gtA)
  (gtA_wf : wf gtA) (gtA'_wf : wf gtA').

Definition lex x y := lexp gtA eqA gtA' (x,x) (y,y).

Lemma lex_wf : wf lex.

Proof.
exact (wf_inv_image (fun x:A => (x,x))
  (lexp_wf eqA_trans Hcomp gtA_wf gtA'_wf)).
Qed.

End gt_lex.