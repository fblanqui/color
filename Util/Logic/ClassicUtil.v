(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

basic classical meta-theorems
*)

Set Implicit Arguments.

From Stdlib Require Export Classical Setoid.
From CoLoR Require Import LogicUtil.

(***********************************************************************)
(** Basic meta-theorems. *)

Lemma contraposee : forall P Q, (~Q -> ~P) -> P -> Q.

Proof. intros. apply NNPP. intro. exact (H H1 H0). Qed.

Lemma not_forall_imply_exists_not : forall A (P : A -> Prop),
  ~(forall x, P x) -> exists x, ~P x.

Proof.
  intros. apply NNPP. intro. apply H. intros. elim (classic (P x)). auto.
  intro. absurd (exists x, ~ P x). exact H0. exists x. exact H1.
Qed.

Arguments not_forall_imply_exists_not [A P] _.

Lemma not_forall_eq : forall (A : Type) (P : A -> Prop),
  ~(forall x, P x) <-> exists x, ~P x.

Proof.
split. apply not_forall_imply_exists_not. apply exists_not_imply_not_forall.
Qed.

Lemma imply_eq : forall P Q : Prop, (P -> Q) <-> (~P \/ Q).

Proof.
split; intro. destruct (classic P). right. auto. left. hyp.
intro. destruct H. absurd P; hyp. hyp.
Qed.

Lemma not_not_eq : forall P : Prop, ~~P <-> P.

Proof. split. apply NNPP. intros h1 h2. absurd P; hyp. Qed.

Lemma not_and_eq : forall P Q : Prop, ~(P /\ Q) <-> ~P \/ ~Q.

Proof.
split; intro. destruct (classic P). right. intro. absurd (P/\Q). hyp. auto.
left. auto. intros [h1 h2]. destruct H. absurd P; hyp. absurd Q; hyp.
Qed.

Lemma not_or_eq : forall P Q : Prop, ~(P \/ Q) <-> ~P /\ ~Q.

Proof.
split. intro. split; intro; absurd (P\/Q); auto.
intros [h1 h2] [h|h]. absurd P; hyp. absurd Q; hyp.
Qed.

Lemma not_imply_eq : forall P Q : Prop, ~(P -> Q) <-> P /\ ~Q.

Proof.
intros. rewrite imply_eq. rewrite not_or_eq. rewrite not_not_eq. refl.
Qed.

(****************************************************************************)
(** Properties of Leibniz equality on [sig]. *)

From CoLoR Require Import FunUtil.

Section sig.

  Variables (A : Type) (P : A -> Prop).

  Lemma sig_eq : forall x y : sig P, proj1_sig x = proj1_sig y <-> x = y.

  Proof.
    intros [x_val x] [y_val y]; simpl. split; intro e.
    subst y_val. rewrite (proof_irrelevance _ x y). refl.
    gen (f_equal (@proj1_sig _ _) e). tauto.
  Qed.

  Lemma inj_proj1_sig : injective (proj1_sig (P:=P)).

  Proof. intros x y e. apply sig_eq. hyp. Qed.

End sig.
