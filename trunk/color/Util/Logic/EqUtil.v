(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general lemmas and tactics
************************************************************************)

(* $Id: EqUtil.v,v 1.1.1.1 2006-09-08 09:07:00 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

(***********************************************************************)
(* decidable equalities *)

Section beq.

Variable A : Set.

Definition dec_eq := forall x y : A, {x=y}+{~x=y}.

Variable eqdec : dec_eq.

Definition beq (x y : A) : bool :=
  match eqdec x y with
    | left _ => true
    | right _ => false
  end.

Lemma beq_refl : forall x, beq x x = true.

Proof.
intro. unfold beq. case (eqdec x x); intros. refl. irrefl.
Qed.

Lemma beq_sym : forall x y, beq x y = beq y x.

Proof.
intros. unfold beq. case (eqdec x y); case (eqdec y x); intros; (refl || irrefl).
Qed.

Require Export Bool.

Lemma beq_trans : forall x y z, implb (beq x y && beq y z) (beq x z) = true.

Proof.
intros. unfold beq. case (eqdec x y); case (eqdec y z); case (eqdec x z); intros;
(refl || (irrefl || idtac)).
Qed.

Lemma beq_true : forall x y, beq x y = true -> x = y.

Proof.
intros x y. unfold beq. case (eqdec x y); intros. auto. discriminate.
Qed.

Lemma beq_false : forall x y, beq x y = false -> x = y -> False.

Proof.
intros x y. unfold beq. case (eqdec x y); intros. discriminate. irrefl.
Qed.

Lemma true_beq : forall x y, x = y -> beq x y = true.

Proof.
intros. rewrite H. rewrite beq_refl. refl.
Qed.

Require Export BoolUtil.

Lemma false_beq : forall x y, x <> y -> beq x y = false.

Proof.
intros. booltac_simpl (beq x y). assert (x=y). apply beq_true. assumption. irrefl.
refl.
Qed.

End beq.

Ltac beqtac eqdec :=
  match goal with
    | _ : ?x = ?y |- _ => subst y; rewrite beq_refl; simpl
    | _ : not (?x = ?y) |- _ => let H := fresh in
      (assert (H : beq eqdec x y = false); [apply false_beq; assumption
	| rewrite H; clear H; simpl])
  end.

Ltac beqtac_simpl x y :=
  match goal with
    | |- context [beq ?eqdec x y] => case (eqdec x y); intro; beqtac eqdec
  end.
