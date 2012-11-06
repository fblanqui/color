(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

general lemmas in classical logic
*)

Set Implicit Arguments.

Require Export Classical.
Require Import LogicUtil Setoid.

(***********************************************************************)
(** basic meta-theorems *)

Lemma contraposee : forall P Q, (~Q -> ~P) -> P -> Q.

Proof. intros. apply NNPP. intro. exact (H H1 H0). Qed.

Lemma not_forall_imply_exists_not : forall A (P : A -> Prop),
  ~(forall x, P x) -> exists x, ~P x.

Proof.
  intros. apply NNPP. intro. apply H. intros. elim (classic (P x)). auto.
  intro. absurd (exists x, ~ P x). exact H0. exists x. exact H1.
Qed.

Implicit Arguments not_forall_imply_exists_not [A P].

(***********************************************************************)
(** basic equivalences *)

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
