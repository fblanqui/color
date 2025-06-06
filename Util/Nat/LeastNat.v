(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha, 2010-04-27

Definitions and proofs about the min of a non empty set of natural
numbers, using classical logic and the axiom of indefinite
description. *)

From Stdlib Require Import Classical_Prop IndefiniteDescription Wf_nat Relations.

Set Implicit Arguments.

(***********************************************************************)
(** unary predicate *)

Section P1.

  Variables (P : nat -> Prop) (exP : exists n, P n).

  Lemma ch_min_proof : has_unique_least_element le P.

  Proof.
    apply dec_inh_nat_subset_has_unique_least_element; auto.
    intros. apply classic.
  Qed.

  Definition ch_min := constructive_indefinite_description _ ch_min_proof.

  Lemma ch_minP : P (proj1_sig ch_min).

  Proof. destruct (proj2_sig ch_min) as [H _]. destruct H. auto. Qed.

  Lemma is_min_ch : forall n, P n -> proj1_sig ch_min <= n.

  Proof.
    destruct (proj2_sig ch_min) as [H _]. destruct H. intros. apply H0. auto.
  Qed.

End P1.

Arguments ch_min [P] _.

(***********************************************************************)
(** binary predicate *)

Section P2.

  Variables (P2 : relation nat) (exP2 : forall m, exists n, P2 m n).

  Fixpoint rec_ch_min n : nat :=
    match n with
      | S n' => proj1_sig (ch_min (exP2 (S (rec_ch_min n'))))
      | 0 => proj1_sig (ch_min (exP2 0))
    end.

  Lemma rec_ch_minP : forall i, P2 (S (rec_ch_min i)) (rec_ch_min (S i)).

  Proof. intros. simpl. apply ch_minP. Qed.

  Lemma is_min_rec_ch : forall i n,
    P2 (S (rec_ch_min i)) n -> (rec_ch_min (S i)) <= n.

  Proof. intros. simpl. apply is_min_ch. auto. Qed.

End P2.
