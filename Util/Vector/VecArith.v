(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-04-02

Arithmetic over vectors of natural numbers.
*)

Set Implicit Arguments.

Require Export VecUtil.
Require Export RelUtil.

Section VecArith.

Variables n : nat.

Notation vec := (vector nat).
Notation vecn := (vec n).

(***********************************************************************)
(** [ge] on vectors *)

Definition vec_ge := Vforall2n ge.
Infix ">=v" := vec_ge (at level 70).

Lemma vec_tail_ge : forall n (v v' : vec (S n)), v >=v v' -> Vtail v >=v Vtail v'.

Proof.
  unfold vec_ge. intros.
  apply Vforall2_intro. intros.
  do 2 rewrite Vnth_tail.
  apply (Vforall2_nth ge). assumption.
Qed.

Lemma vec_ge_dec : rel_dec (@vec_ge n).

Proof.
  intros P Q. destruct (Vforall2_dec nat_ge_dec P Q); intuition.
Defined.

Lemma vec_ge_refl : reflexive (@vec_ge n).

Proof.
  intros x. unfold vec_ge. apply Vforall2_intro. intros.
  unfold ge. apply le_refl.
Qed.

Lemma vec_ge_trans : transitive (@vec_ge n).

Proof.
  intros x y z xy yz. unfold vec_ge.
  apply Vforall2_intro. intros.
  unfold ge. apply le_trans with (Vnth y ip).
  apply (Vforall2_nth ge). assumption.
  apply (Vforall2_nth ge). assumption.
Qed.

(***********************************************************************)
(** vector plus *)

Definition zero_vec := Vconst 0 n.

Definition vector_plus (v1 v2 : vecn) := Vmap2 plus v1 v2.
Infix "[+]" := vector_plus (at level 50).

Definition add_vectors i (v : vector vecn i) := Vfold_left vector_plus zero_vec v.

(***********************************************************************)
(** compatibility of [vec_plus] with [vec_ge] *)

Lemma vec_plus_ge_compat : forall vl vl' vr vr', vl >=v vl' -> vr >=v vr' -> vl [+] vr >=v vl' [+] vr'.

Proof.
  unfold vector_plus, vec_ge. intros. apply Vforall2_intro.
  intros. simpl. do 2 rewrite Vmap2_nth.
  unfold ge. apply plus_le_compat.
  apply (Vforall2_nth ge). assumption.
  apply (Vforall2_nth ge). assumption.
Qed.

Lemma vec_plus_ge_compat_r : forall vl vl' vr, vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

Proof.
  intros. apply vec_plus_ge_compat. assumption. exact (vec_ge_refl vr).
Qed.

Lemma vec_plus_ge_compat_l : forall vl vr vr', vr >=v vr' -> vl [+] vr >=v vl [+] vr'.
  
Proof.
  intros. apply vec_plus_ge_compat. exact (vec_ge_refl vl). assumption.
Qed.
 
End VecArith.

(***********************************************************************)
(** Notations *)

Infix ">=v" := vec_ge (at level 70).
Infix "[+]" := vector_plus (at level 50).
