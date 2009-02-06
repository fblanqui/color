(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

general lemmas in classical logic
*)

Set Implicit Arguments.

Require Export Classical.

(***********************************************************************)
(** basic meta-theorems *)

Section meta.

Lemma contraposee : forall P Q, (~Q -> ~P) -> P -> Q.

Proof.
intros. apply NNPP. intro. exact (H H1 H0).
Qed.

Variables (A : Type) (P : A -> Prop).

Lemma not_forall_imply_exists_not : ~(forall x, P x) -> exists x, ~P x.

Proof.
intros. apply NNPP. intro. apply H. intros. elim (classic (P x)). auto.
intro. absurd (exists x, ~ P x). exact H0. exists x. exact H1.
Qed.

End meta.

Implicit Arguments not_forall_imply_exists_not [A P].
