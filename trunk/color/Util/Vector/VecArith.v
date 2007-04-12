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

Lemma vec_tail_ge : forall n (v v' : vec (S n)), v >=v v' -> 
  Vtail v >=v Vtail v'.

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

Lemma vector_plus_comm : forall (v1 v2 : vecn), v1 [+] v2 = v2 [+] v1.

Proof.
Admitted.

Lemma vector_plus_assoc : forall (v1 v2 v3 : vecn),
  v1 [+] (v2 [+] v3) = v1 [+] v2 [+] v3.

Proof.
Admitted.

Lemma vector_plus_nth : forall (vl vr : vecn) i (ip : i < n),
  Vnth (vl [+] vr) ip = Vnth vl ip + Vnth vr ip.

Proof.
Admitted.

Definition add_vectors i (v : vector vecn i) := 
  Vfold_left vector_plus zero_vec v.

Lemma add_vectors_cons : forall i (a : vecn) (v : vector vecn i),
  add_vectors (Vcons a v) = a [+] add_vectors v.

Proof.
Admitted.

Lemma add_vectors_perm : forall i v v' (vs : vector vecn i),
  add_vectors (Vcons v (Vcons v' vs)) = add_vectors (Vcons v' (Vcons v vs)).

Proof.
Admitted.

Lemma add_vectors_nth : forall k (vs : vector vecn k) i (ip : i < n),
  Vnth (add_vectors vs) ip = Vfold_left plus 0 (Vmap (fun v => Vnth v ip) vs).

Proof.
Admitted.

Lemma add_vectors_eq : forall i (v v' : vector vecn i), 
  Vforall2 (@eq vecn) v v' -> add_vectors v = add_vectors v'.

Proof.
Admitted.

Lemma add_vectors_split : forall n (v vl vr : vector vecn n),
  (forall i (ip : i < n), Vnth v ip = Vnth vl ip [+] Vnth vr ip) ->
  add_vectors v = add_vectors vl [+] add_vectors vr.

Proof.
Admitted.

(***********************************************************************)
(** vector addition and zero vector *)

Lemma vector_plus_zero_r : forall v, v [+] zero_vec = v.

Proof.
Admitted.

Lemma vector_plus_zero_l : forall v, zero_vec [+] v = v.

Proof.
Admitted.

Lemma add_vectors_zero : forall i (v : vector vecn i), 
  Vforall (fun v => v = zero_vec) v -> add_vectors v = zero_vec.

Proof.
Admitted.

(***********************************************************************)
(** compatibility of [vec_plus] with [vec_ge] *)

Lemma vec_plus_ge_compat : forall vl vl' vr vr', vl >=v vl' -> vr >=v vr' -> 
  vl [+] vr >=v vl' [+] vr'.

Proof.
  unfold vector_plus, vec_ge. intros. apply Vforall2_intro.
  intros. simpl. do 2 rewrite Vmap2_nth.
  unfold ge. apply plus_le_compat.
  apply (Vforall2_nth ge). assumption.
  apply (Vforall2_nth ge). assumption.
Qed.

Lemma vec_plus_ge_compat_r : forall vl vl' vr, vl >=v vl' -> 
  vl [+] vr >=v vl' [+] vr.

Proof.
  intros. apply vec_plus_ge_compat. assumption. exact (vec_ge_refl vr).
Qed.

Lemma vec_plus_ge_compat_l : forall vl vr vr', vr >=v vr' -> 
  vl [+] vr >=v vl [+] vr'.
  
Proof.
  intros. apply vec_plus_ge_compat. exact (vec_ge_refl vl). assumption.
Qed.
 
End VecArith.

(***********************************************************************)
(** Notations *)

Infix ">=v" := vec_ge (at level 70).
Infix "[+]" := vector_plus (at level 50).

(***********************************************************************)
(** Rewrite hints *)

Hint Rewrite vector_plus_zero_l vector_plus_zero_r add_vectors_cons : arith.

(** Tactics *)

Ltac Vplus_eq := simpl; autorewrite with arith;
  match goal with
  | |- ?vl [+] ?vr = ?vl' [+] ?vr' => 
    replace vl with vl'; [replace vr with vr'; try refl | try refl]
  end.
