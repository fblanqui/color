(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-17

general results on booleans
*)

(* $Id: BoolUtil.v,v 1.4 2008-01-23 18:22:39 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export Bool.

(***********************************************************************)
(** tactics *)

Ltac booltac e := let H := fresh in let H1 := fresh in
  (assert (H : e = true \/ e = false);
    [case e; auto | destruct H as [H1 | H1]]).

Ltac booltac_simpl e := let H := fresh in let H1 := fresh in
  let t1 := (rewrite H1; simpl) in
  (assert (H : e = true \/ e = false);
    [case e; auto
    | destruct H as [H1 | H1]; [t1 | t1]]).

(***********************************************************************)
(** boolean equalities *)

Lemma implb1 : forall b, implb b b = true.

Proof.
induction b; refl.
Qed.

Lemma implb2 : forall b, implb b true = true.

Proof.
induction b; refl.
Qed.

(***********************************************************************)
(** introduction and elimination rules for booleans *)

Lemma andb_elim : forall b c, b && c = true -> b = true /\ c = true.

Proof.
intros. destruct b; destruct c; intuition.
Qed.

Implicit Arguments andb_elim [b c].

Lemma andb_intro : forall b c, b = true -> c = true -> b && c = true.

Proof.
intros. subst b. subst c. refl.
Qed.

(***********************************************************************)
(** boolean function testing equality *)

Section beq.

Variable A : Type.
Variable beq : A -> A -> bool.
Variable beq_ok : forall x y, beq x y = true <-> x = y.

Lemma beq_refl : forall x, beq x x = true.

Proof.
intro. assert (x=x). refl. rewrite <- beq_ok in H. exact H.
Qed.

Lemma beq_ko : forall x y, beq x y = false <-> x <> y.

Proof.
unfold not. split; intros.
rewrite <- beq_ok in H0. rewrite H in H0. discriminate.
booltac (beq x y). rewrite beq_ok in H1. tauto. exact H1.
Qed.

Lemma eq_dec_beq : forall x y : A, {x=y}+{~x=y}.

Proof.
intros. cut (forall b, beq x y = b -> {x=y}+{~x=y}). intro. eapply H. refl.
destruct b; intro.
rewrite beq_ok in H. left. exact H.
right. rewrite <- beq_ko. exact H.
Qed.

Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Definition beq_eq_dec x y :=
  match eq_dec x y with
    | left _ => true
    | right _ => false
  end.

Lemma beq_eq_dec_ok : forall x y, beq_eq_dec x y = true <-> x = y.

Proof.
intros. unfold beq_eq_dec. case (eq_dec x y); intuition. discriminate.
Qed.

End beq.

Implicit Arguments beq_refl [A beq].
Implicit Arguments eq_dec_beq [A beq].
