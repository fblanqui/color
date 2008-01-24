(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general lemmas and tactics
*)

(* $Id: EqUtil.v,v 1.3 2008-01-24 13:22:25 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Definition dec_eq A := forall x y : A, {x=y}+{~x=y}.

(***********************************************************************)
(** dependent equality on decidable types *)

Require Export EqdepFacts.
Require Export Eqdep_dec.

Section eq_dep.

Variables (U : Type) (eq_dec : forall x y : U, {x=y}+{~x=y}).

Lemma eq_rect_eq : forall (p : U) Q x h, x = eq_rect p Q x p h.
  
Proof.
exact (eq_rect_eq_dec eq_dec).
Qed.

Lemma eq_dep_eq : forall P (p : U) x y, eq_dep U P p x p y -> x = y.

Proof.
exact (eq_rect_eq__eq_dep_eq U eq_rect_eq).
Qed.

Lemma UIP : forall (x y : U) (p1 p2 : x = y), p1 = p2.

Proof.
exact (eq_dep_eq__UIP U eq_dep_eq).
Qed.

Lemma UIP_refl : forall (x : U) (p : x = x), p = refl_equal x.

Proof.
exact (UIP__UIP_refl U UIP).
Qed.

Lemma Streicher_K :
  forall (x : U) (P : x = x -> Prop), P (refl_equal x) -> forall p, P p.

Proof.
exact (K_dec_type eq_dec).
Qed.

Lemma inj_pairT2 : forall P (p : U) x y, existT P p x = existT P p y -> x = y.

Proof.
exact (eq_dep_eq__inj_pairT2 U eq_dep_eq).
Qed.

Lemma inj_pairP2 :
  forall P (x : U) p q, ex_intro P x p = ex_intro P x q -> p = q.

Proof.
intros. apply inj_right_pair with (A:=U).
intros x0 y0; case (eq_dec x0 y0); [left|right]; assumption.
assumption.
Qed.

End eq_dep.

Implicit Arguments UIP_refl [U x].

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

Require Export BoolUtil.

Lemma beq_ko : forall x y, beq x y = false <-> x <> y.

Proof.
unfold not. split; intros.
rewrite <- beq_ok in H0. rewrite H in H0. discriminate.
booltac (beq x y). rewrite beq_ok in H1. tauto. exact H1.
Qed.

Lemma dec_beq : forall x y : A, {x=y}+{~x=y}. 

Proof.
intros. cut (forall b, beq x y = b -> {x=y}+{~x=y}). intro. eapply H. refl.
destruct b; intro.
rewrite beq_ok in H. left. exact H.
right. rewrite <- beq_ko. exact H.
Defined.

End beq.

Implicit Arguments beq_refl [A beq].
Implicit Arguments dec_beq [A beq].

(***********************************************************************)
(** boolean function testing equality from decidability predicate *)

Section eq_dec.

Variable A : Set.
Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Definition beq_dec x y :=
  match eq_dec x y with
    | left _ => true
    | right _ => false
  end.

Lemma beq_dec_ok : forall x y, beq_dec x y = true <-> x = y.

Proof.
intros. unfold beq_dec. case (eq_dec x y); intuition. discriminate.
Qed.

Lemma beq_dec_refl : forall x, beq_dec x x = true.

Proof.
intro. unfold beq_dec. case (eq_dec x x); intros. refl. irrefl.
Qed.

Lemma beq_dec_sym : forall x y, beq_dec x y = beq_dec y x.

Proof.
intros. unfold beq_dec. case (eq_dec x y); case (eq_dec y x); intros;
(refl || irrefl).
Qed.

Require Export Bool.

Lemma beq_dec_trans : forall x y z,
  implb (beq_dec x y && beq_dec y z) (beq_dec x z) = true.

Proof.
intros. unfold beq_dec.
case (eq_dec x y); case (eq_dec y z); case (eq_dec x z);
intros; (refl || (irrefl || idtac)).
Qed.

Lemma beq_dec_true : forall x y, beq_dec x y = true -> x = y.

Proof.
intros x y. unfold beq_dec. case (eq_dec x y); intros. auto. discriminate.
Qed.

Lemma beq_dec_false : forall x y, beq_dec x y = false -> x = y -> False.

Proof.
intros x y. unfold beq_dec. case (eq_dec x y); intros. discriminate. irrefl.
Qed.

Lemma true_beq_dec : forall x y, x = y -> beq_dec x y = true.

Proof.
intros. rewrite H. rewrite beq_dec_refl. refl.
Qed.

Require Export BoolUtil.

Lemma false_beq_dec : forall x y, x <> y -> beq_dec x y = false.

Proof.
intros. booltac_simpl (beq_dec x y). assert (x=y). apply beq_dec_true.
assumption. irrefl. refl.
Qed.

End eq_dec.

Ltac beqtac eq_dec :=
  match goal with
    | _ : ?x = ?y |- _ => subst y; rewrite beq_refl; simpl
    | _ : not (?x = ?y) |- _ => let H := fresh in
      (assert (H : beq_dec eq_dec x y = false);
        [apply false_beq_dec; assumption | rewrite H; clear H; simpl])
  end.

Ltac beqtac_simpl x y :=
  match goal with
    | |- context [beq_dec ?eq_dec x y] =>
      case (eq_dec x y); intro; beqtac eq_dec
  end.
