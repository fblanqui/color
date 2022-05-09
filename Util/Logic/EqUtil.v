(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general lemmas and tactics
*)

Set Implicit Arguments.

From Coq Require Import Structures.Equalities.
From Coq Require Export EqdepFacts Eqdep_dec.
From Coq Require Setoid.

From CoLoR Require Import LogicUtil RelUtil BoolUtil.

(***********************************************************************)
(** Functor providing properties the basic properties of Leibniz
equality on some type. *)

Module LeibnizFacts (Import T : Typ).

  Definition eq : relation t := @Logic.eq t.

  #[global] Instance eq_refl : Reflexive eq.

  Proof. fo. Qed.

  #[global] Instance eq_sym : Symmetric eq.

  Proof. firstorder auto with crelations. Qed.

  #[global] Instance eq_trans : Transitive eq.

  Proof. unfold eq; class. Qed.

End LeibnizFacts.

(***********************************************************************)
(** Type equipped with a boolean equility. *)

Record Bool_eq_type : Type := mkBool_eq_type {
  bet_type :> Type;
  bet_eq : bet_type -> bet_type -> bool;
  bet_ok : forall x y, bet_eq x y = true <-> x = y }.

(***********************************************************************)
(** Properties of Leibniz equality on decidable types. *)

Section eq_dep.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

  Lemma eq_rect_eq : forall (p : A) Q x h, x = eq_rect p Q x p h.
  
  Proof. exact (eq_rect_eq_dec eq_dec). Qed.

  Lemma eq_dep_eq : forall P (p : A) x y, eq_dep A P p x p y -> x = y.

  Proof. exact (eq_rect_eq__eq_dep_eq A eq_rect_eq). Qed.

  Lemma UIP : forall (x y : A) (p1 p2 : x = y), p1 = p2.

  Proof. exact (eq_dep_eq__UIP A eq_dep_eq). Qed.

  Lemma UIP_refl : forall (x : A) (p : x = x), p = eq_refl x.

  Proof. exact (UIP__UIP_refl A UIP). Qed.

  Lemma Streicher_K :
    forall (x : A) (P : x = x -> Prop), P (eq_refl x) -> forall p, P p.

  Proof. exact (K_dec_type eq_dec). Qed.

  Lemma inj_existT :
    forall P (x : A) (p q : P x), existT p = existT q -> p = q.

  Proof. exact (eq_dep_eq__inj_pairT2 A eq_dep_eq). Qed.

  Lemma inj_ex_intro :
    forall P (x : A) p q, ex_intro P x p = ex_intro P x q -> p = q.

  Proof.
    intros. apply inj_right_pair with (A:=A).
    intros x0 y0; case (eq_dec x0 y0); [left|right]; hyp.
    hyp.
  Qed.

End eq_dep.

Arguments UIP_refl [A] _ [x] p.

(***********************************************************************)
(** Properties of a boolean function testing Leibniz equality. *)

Section beq.

  Variable A : Type.
  Variable beq : A -> A -> bool.
  Variable beq_ok : forall x y, beq x y = true <-> x = y.

  Lemma beq_refl : forall x, beq x x = true.

  Proof. intro. ded (beq_ok x x). rewrite H. refl. Qed.

  Lemma beq_ko : forall x y, beq x y = false <-> x <> y.

  Proof.
    intros. destruct (beq_ok x y). case_eq (beq x y); intuition.
    rewrite H1 in H4. discr.
  Defined.

  Lemma dec_beq : forall x y : A, {x=y}+{~x=y}.

  Proof.
    intros. set (b := beq x y). case_eq b; intros.
    left. exact (proj1 (beq_ok x y) H).
    right. intro. unfold b in H. subst. rewrite beq_refl in H. discr.
  Defined.

  Lemma beq_com : forall x y, beq x y = beq y x.

  Proof.
    intros. case_eq (beq x y); intros; sym.
    rewrite beq_ok. sym. rewrite <- beq_ok. hyp.
    rewrite beq_ko. cut (x<>y). auto. rewrite <- beq_ko. hyp.
  Qed.

  Lemma beq_sym : forall x y, beq x y = true -> beq y x = true.

  Proof. intros. rewrite beq_com. exact H. Qed.

  Lemma beq_trans : forall x y z,
    beq x y = true -> beq y z = true -> beq x z = true.

  Proof.
    intros. rewrite beq_ok in H. rewrite beq_ok in H0.
    assert (x = z). apply eq_trans with y; hyp.
    rewrite beq_ok. exact H1.
  Qed.

End beq.

Arguments beq_refl [A beq] _ x.
Arguments dec_beq [A beq] _ x y.
Arguments beq_com [A beq] _ x y.
Arguments beq_ko [A beq] _ x y.

Ltac case_beq beq beq_ok x y := case_eq (beq x y);
  [let h := fresh in intro h; rewrite beq_ok in h;
    match type of h with ?x = ?y => subst y end
    | intro].

(***********************************************************************)
(** Boolean function testing Leibniz equality when it is decidable. *)

Section eq_dec.

  Variable A : Type.
  Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

  Definition beq_dec x y :=
    match eq_dec x y with
      | left _ => true
      | right _ => false
    end.

  Lemma beq_dec_ok : forall x y, beq_dec x y = true <-> x = y.

  Proof. intros. unfold beq_dec. case (eq_dec x y); intuition. discr. Qed.

  Lemma beq_dec_refl : forall x, beq_dec x x = true.

  Proof. intro. unfold beq_dec. case (eq_dec x x); intros. refl. cong. Qed.

  Lemma beq_dec_sym : forall x y, beq_dec x y = beq_dec y x.

  Proof.
    intros. unfold beq_dec.
    case (eq_dec x y); case (eq_dec y x); intros; (refl || cong).
  Qed.

  Lemma beq_dec_trans : forall x y z,
    implb (beq_dec x y && beq_dec y z) (beq_dec x z) = true.

  Proof.
    intros. unfold beq_dec.
    case (eq_dec x y); case (eq_dec y z); case (eq_dec x z);
      intros; (refl || (cong || idtac)).
  Qed.

  Lemma beq_dec_ko : forall x y, beq_dec x y = false <-> x <> y.

  Proof.
    intros. case (eq_dec x y); case_eq (beq_dec x y); intuition.
    subst y. rewrite beq_dec_refl in H. discr.
    rewrite beq_dec_ok in H. contr.
  Qed.

End eq_dec.
