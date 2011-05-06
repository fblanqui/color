(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha, 2010-04-27

Definitions and proofs about the min of a non empty set of natural
numbers. *)

Require Import Wf_nat ClassicalEpsilon.

Set Implicit Arguments.

(***********************************************************************)
(** unary predicate *)

Section P1.

  Variable P : nat -> Prop.

  Hypothesis exP : exists n, P n.

  Lemma ch_min_proof : has_unique_least_element le P.

  Proof.
    apply dec_inh_nat_subset_has_unique_least_element; auto.
    intros. apply classic.
  Qed.

  Definition ch_min := constructive_indefinite_description _ ch_min_proof.

  Lemma ch_minP : P (projT1 ch_min).

  Proof.
    destruct (projT2 ch_min) as [H _]. destruct H. auto.
  Qed.

  Lemma is_min_ch : forall n, P n -> projT1 ch_min <= n.

  Proof.
    destruct (projT2 ch_min) as [H _]. destruct H.
    intros. apply H0. auto.
  Qed.

End P1.

(***********************************************************************)
(** binary predicate *)

Section P2.

  Variable P2 : nat -> nat -> Prop.

  Hypothesis exP2 : forall m, exists n, P2 m n.

  Fixpoint rec_ch_min n : nat :=
    match n with
      | S n' => projT1 (ch_min _ (exP2 (S (rec_ch_min n'))))
      | 0 => projT1 (ch_min _ (exP2 0))
    end.

  Lemma rec_ch_minP : forall i, P2 (S (rec_ch_min i)) (rec_ch_min (S i)).

  Proof.
    intros. simpl. apply ch_minP.
  Qed.

  Lemma is_min_rec_ch : forall i n,
    P2 (S (rec_ch_min i)) n -> (rec_ch_min (S i)) <= n.

  Proof.
    intros. simpl. apply is_min_ch. auto.
  Qed.

End P2.
