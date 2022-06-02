(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-17

general results on booleans
*)

Set Implicit Arguments.

From Coq Require Import ZArith Lia.
From Coq Require Export Bool.
From Coq Require Setoid.

From CoLoR Require Import LogicUtil.

Arguments orb_false_elim [b1 b2] _.
Arguments orb_true_elim [b1 b2] _.

Global Hint Rewrite negb_orb negb_andb negb_involutive eqb_negb1 eqb_negb2
  orb_true_r orb_true_l orb_false_r orb_false_l orb_negb_r orb_assoc
  andb_false_r andb_false_l andb_true_r andb_true_l andb_negb_r andb_assoc
  absoption_andb absoption_orb
  xorb_false_r xorb_false_l xorb_nilpotent xorb_assoc_reverse
  : bool.

Ltac bool := autorewrite with bool.

(***********************************************************************)
(** equality *)

Lemma false_not_true : forall b, b = false <-> ~(b = true).

Proof. destruct b; intuition. Qed.

Lemma beq_true : forall b c, b = c <-> (b = true <-> c = true).

Proof.
  split; intro h. subst. tauto. destruct c.
  tauto. rewrite false_not_true. intuition.
Qed.

(***********************************************************************)
(** implication *)

Lemma implb1 : forall b, implb b b = true.

Proof. induction b; refl. Qed.

Lemma implb2 : forall b, implb b true = true.

Proof. induction b; refl. Qed.

(***********************************************************************)
(** conjunction *)

Lemma andb_elim : forall b c, b && c = true -> b = true /\ c = true.

Proof. destruct b; destruct c; intuition. Qed.

Arguments andb_elim [b c] _.

Lemma andb_eliml : forall b c, b && c = true -> b = true.

Proof. destruct b; destruct c; intuition. Qed.

Arguments andb_eliml [b c] _.

Lemma andb_elimr : forall b c, b && c = true -> c = true.

Proof. destruct b; destruct c; intuition. Qed.

Arguments andb_elimr [b c] _.

Lemma andb_intro : forall b c, b = true -> c = true -> b && c = true.

Proof. intros. subst b. subst c. refl. Qed.

Lemma andb_eq : forall b c, b && c = true <-> b = true /\ c = true.

Proof. split. intro. apply andb_elim. hyp. intuition. Qed.

Lemma andb_eq_false : forall b c, b && c = false <-> b = false \/ c = false.

Proof. destruct b; destruct c; bool; intuition. Qed.

(***********************************************************************)
(** negation *)

Definition neg (A : Type) (f : A->A->bool) x y := negb (f x y).

Lemma negb_lr : forall b c, negb b = c <-> b = negb c.

Proof. destruct b; destruct c; intuition. Qed.

(***********************************************************************)
(** disjonction *)

Lemma orb_intror : forall b c, c = true -> b || c = true.

Proof. intros. subst. bool. refl. Qed.

Lemma orb_introl : forall b c, c = true -> b || c = true.

Proof. intros. subst. bool. refl. Qed.

Lemma orb_eq : forall b c, b || c = true <-> b = true \/ c = true.

Proof. intuition. destruct b; auto. Qed.

(***********************************************************************)
(** equality *)

Lemma eqb_equiv : forall b b', b = b' <-> (b = true <-> b' = true).

Proof.
  intros b b'. split; intro H. subst b'. refl.
  destruct b. sym. rewrite <- H. refl.
  destruct b'. rewrite H. refl. refl.
Qed.

(***********************************************************************)
(** decidability *)

Section dec.

  Variables (A : Type) (P : A -> Prop)
    (f : A -> bool) (f_ok : forall x, f x = true <-> P x).

  Lemma ko : forall x, f x = false <-> ~P x.

  Proof. intro x. rewrite <- f_ok. destruct (f x); intuition; discr. Qed.

  Lemma dec : forall x, {P x}+{~P x}.

  Proof.
    intro x. case_eq (f x); intros.
    left. rewrite <- f_ok. hyp. right. rewrite <- ko. hyp.
  Defined.

End dec.

Arguments ko [A P f] _ x.
Arguments dec [A P f] _ x.

(***********************************************************************)
(** correspondance between boolean functions and logical connectors *)

Section bool_ok.

  Variables (A : Type) (P Q : A->Prop) (bP bQ : A-> bool)
    (bP_ok : forall x, bP x = true <-> P x)
    (bQ_ok : forall x, bQ x = true <-> Q x).

  Lemma negb_ok : forall x, negb (bP x) = true <-> ~P x.

  Proof. intro. rewrite <- (ko bP_ok). destruct (bP x); simpl; intuition. Qed.

  Lemma andb_ok : forall x, bP x && bQ x = true <-> P x /\ Q x.

  Proof. intro. rewrite andb_eq, bP_ok, bQ_ok. refl. Qed.

  Lemma orb_ok : forall x, bP x || bQ x = true <-> P x \/ Q x.

  Proof. intro. rewrite orb_eq, bP_ok, bQ_ok. refl. Qed.

  Lemma implb_ok : forall x, implb (bP x) (bQ x) = true <-> (P x -> Q x).

  Proof.
    intro x. unfold implb. case_eq (bP x).
    rewrite bP_ok, bQ_ok. tauto.
    rewrite (ko bP_ok). tauto.
  Qed.

End bool_ok.

(***********************************************************************)
(** checking a property (P i) for all i<n *)

Section bforall_lt.

  Variables (P : nat->Prop) (bP : nat->bool)
    (bP_ok : forall x, bP x = true <-> P x).

  Definition forall_lt n := forall i, i < n -> P i.

  Fixpoint bforall_lt_aux b n := b &&
    match n with
      | 0 => true
      | S n' => bforall_lt_aux (bP n') n'
    end.

  Lemma bforall_lt_aux_ok : forall n b,
    bforall_lt_aux b n = true <-> b = true /\ forall_lt n.

  Proof.
    unfold forall_lt. induction n; simpl; intros. bool. firstorder auto with zarith.
    rewrite andb_eq, IHn, bP_ok. intuition.
    destruct (Nat.eq_dec i n). subst. hyp. apply H2. lia.
  Qed.

  Definition bforall_lt := bforall_lt_aux true.

  Lemma bforall_lt_ok : forall n, bforall_lt n = true <-> forall_lt n.

  Proof. intro. unfold bforall_lt. rewrite bforall_lt_aux_ok. tauto. Qed.

End bforall_lt.
