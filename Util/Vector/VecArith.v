(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-04-02

Arithmetic over vectors of coefficients.
*)

Set Implicit Arguments.

Require Export VecUtil.
Require Export RelUtil.
Require Export SemiRing.

(** Module with arithmetic over vectors of coefficients *)
Module VectorArith (SRT : SemiRingType).

Module SR := SemiRing SRT.
Export SR.

Notation vec := (vector A).

Definition zero_vec := Vconst A0.

Definition id_vec n i := Vbuild
  (fun j (jp : j < n) =>
    match eq_nat_dec i j with
    | left _ => A1
    | right _ => A0
    end).

(***********************************************************************)
(** vector plus *)

Section VectorPlus.

Variable n : nat.
Notation vecn := (vec n).
Notation zero_vec_n := (zero_vec n).

Definition vector_plus n (v1 v2 : vec n) := Vmap2 Aplus v1 v2.

Infix "[+]" := vector_plus (at level 50).

Lemma vector_plus_nth : forall (vl vr : vecn) i (ip : i < n),
  Vnth (vl [+] vr) ip = Vnth vl ip + Vnth vr ip.

Proof.
  destruct n; intros.
  absurd_arith.
  VSntac vl. VSntac vr. simpl. destruct i. refl.
  rewrite Vmap2_nth. refl.
Qed.

Lemma vector_plus_comm : forall (v1 v2 : vecn), v1 [+] v2 = v2 [+] v1.

Proof.
  intros. apply Veq_nth. intros. do 2 rewrite vector_plus_nth. ring.
Qed.

Lemma vector_plus_assoc : forall (v1 v2 v3 : vecn),
  v1 [+] (v2 [+] v3) = v1 [+] v2 [+] v3.

Proof.
  intros. apply Veq_nth. intros. do 4 rewrite vector_plus_nth. ring.
Qed.

Lemma vector_plus_zero_r : forall v, v [+] zero_vec_n = v.

Proof.
  intros. apply Veq_nth. intros. rewrite vector_plus_nth.
  set (w := Vnth_const A0 ip). fold zero_vec in w. rewrite w. ring.
Qed.

Lemma vector_plus_zero_l : forall v, zero_vec_n [+] v = v.

Proof.
  intros. rewrite vector_plus_comm. apply vector_plus_zero_r.
Qed.

(***********************************************************************)
(** sum of a vector of vectors *)

Definition add_vectors n k (v : vector (vec n) k) := 
  Vfold_left (@vector_plus n) (zero_vec n) v.

Lemma add_vectors_cons : forall i (a : vecn) (v : vector vecn i),
  add_vectors (Vcons a v) = a [+] add_vectors v.

Proof.
  intros. unfold add_vectors. simpl. rewrite vector_plus_comm. refl.
Qed.

Lemma add_vectors_zero : forall k (v : vector vecn k), 
  Vforall (fun v => v = zero_vec_n) v -> add_vectors v = zero_vec_n.

Proof.
  induction k; intros.  
  VOtac. unfold add_vectors. refl.
  VSntac v. unfold add_vectors. simpl.
  replace (Vhead v) with zero_vec_n.
  rewrite vector_plus_zero_r.
  fold (add_vectors (Vtail v)). rewrite IHk. refl.
  apply Vforall_nth_intro. intros.
  rewrite Vnth_tail. exact (Vforall_nth _ v (lt_n_S ip) H).
  rewrite Vhead_nth. symmetry.
  exact (Vforall_nth _ v (lt_O_Sn k) H).
Qed.

Lemma add_vectors_perm : forall i v v' (vs : vector vecn i),
  add_vectors (Vcons v (Vcons v' vs)) = add_vectors (Vcons v' (Vcons v vs)).

Proof.
  intros. unfold add_vectors. simpl.
  rewrite <- vector_plus_assoc. 
  rewrite vector_plus_comm with v' v.
  rewrite vector_plus_assoc. refl.
Qed.

(*
Lemma add_vectors_nth : forall k (vs : vector vecn k) i (ip : i < n),
  Vnth (add_vectors vs) ip = Vfold_left Aplus A0 (Vmap (fun v => Vnth v ip) vs).
*)

Lemma add_vectors_split : forall k (v vl vr : vector vecn k),
  (forall i (ip : i < k), Vnth v ip = Vnth vl ip [+] Vnth vr ip) ->
  add_vectors v = add_vectors vl [+] add_vectors vr.

Proof.
  induction k; intros.
  VOtac. unfold add_vectors. simpl. rewrite vector_plus_zero_r. refl.
  VSntac v. VSntac vl. VSntac vr. do 3 rewrite add_vectors_cons.
  rewrite (IHk (Vtail v) (Vtail vl) (Vtail vr)). do 3 rewrite Vhead_nth.
  rewrite (H 0 (lt_O_Sn k)).
  match goal with
  |- (?A [+] ?B) [+] (?C [+] ?D) = (?A [+] ?C) [+] (?B [+] ?D) =>
    set (X := A); set (Y := B); set (W := C); set (V := D) end.
  do 2 rewrite <- vector_plus_assoc. rewrite (vector_plus_assoc W Y V). 
  rewrite (vector_plus_comm W Y). do 4 rewrite vector_plus_assoc. refl.
  intros. do 3 rewrite Vnth_tail. apply H.
Qed.

End VectorPlus.

Infix "[+]" := vector_plus (at level 50).

(***********************************************************************)
(** dot product *)

Definition dot_product n (l r : vec n) := 
  Vfold_left Aplus A0 (Vmap2 Amult l r).

Lemma dot_product_zero : forall n (v v' : vec n),
  Vforall (fun el => el = A0) v -> dot_product v v' = A0.

Proof.
  induction n; intros.
  VOtac. trivial.
  VSntac v. VSntac v'. unfold dot_product. simpl.
  fold (dot_product (Vtail v) (Vtail v')).
  rewrite IHn. rewrite Vhead_nth. 
  rewrite (Vforall_nth _ v (lt_O_Sn n) H). ring.
  apply Vforall_incl with (S n) v. intros.
  apply Vin_tail. assumption. assumption.
Qed.

Lemma dot_product_id : forall i n (ip : i < n) v,
  dot_product (id_vec n i) v = Vnth v ip.

Proof.
  induction i. intros. 
  destruct n. absurd_arith.

   (* induction base *)
  unfold dot_product. VSntac v. simpl.
  fold (dot_product (Vtail (id_vec (S n) 0)) (Vtail v)).
  rewrite dot_product_zero with (v' := Vtail v).
  unfold id_vec. rewrite Vhead_nth. rewrite Vbuild_nth. simpl. ring.
  apply Vforall_nth_intro. intros. 
  unfold id_vec. rewrite Vnth_tail. rewrite Vbuild_nth. refl.

   (* induction step *)
  intros. destruct n. absurd_arith.
  VSntac v. unfold dot_product. simpl.
  rewrite <- (IHi n (lt_S_n ip) (Vtail v)).
  replace (Vhead (id_vec (S n) (S i))) with A0. 
  ring_simplify. unfold dot_product.
  replace (Vtail (id_vec (S n) (S i))) with (id_vec n i). refl.
  apply Veq_nth. intros. rewrite Vnth_tail.
  unfold id_vec. repeat rewrite Vbuild_nth.
  destruct (eq_nat_dec i i0); destruct (eq_nat_dec (S i) (S i0));
    try solve [refl | absurd_arith].
  rewrite Vhead_nth. unfold id_vec. rewrite Vbuild_nth. refl.
Qed.

Lemma dot_product_comm : forall n (u v : vec n),
  dot_product u v = dot_product v u.

Proof.
  intros. unfold dot_product.
  replace (Vmap2 Amult u v) with (Vmap2 Amult v u). refl.
  apply Veq_nth. intros. do 2 rewrite Vmap2_nth. ring.
Qed.

Lemma dot_product_distr_r : forall n (v vl vr : vec n),
  dot_product v (vl [+] vr) = dot_product v vl + dot_product v vr.

Proof.
  induction n; intros.
  VOtac. unfold dot_product. simpl. ring.
  VSntac v. VSntac vl. VSntac vr. unfold dot_product. simpl.
  fold (Vtail vl [+] Vtail vr). fold (dot_product (Vtail v) (Vtail vl [+] Vtail vr)).
  rewrite IHn. unfold dot_product. ring.
Qed.

Lemma dot_product_distr_l : forall n (v vl vr : vec n),
  dot_product (vl [+] vr) v = dot_product vl v + dot_product vr v.

Proof.
  intros. rewrite dot_product_comm. rewrite dot_product_distr_r. 
  rewrite (dot_product_comm v vl). rewrite (dot_product_comm v vr). refl.
Qed.

Lemma dot_product_cons : forall n al ar (vl vr : vec n),
  dot_product (Vcons al vl) (Vcons ar vr) = al * ar + dot_product vl vr.

Proof.
  intros. unfold dot_product. simpl. ring.
Qed.

Lemma dot_product_distr_mult : forall n a (v v' : vec n),
  a * dot_product v v' = 
  dot_product (Vbuild (fun i ip => a * Vnth v ip)) v'.

Proof.
  induction n; intros.
  VOtac. unfold dot_product. simpl. ring.
  rewrite (VSn_eq (Vbuild (fun i (ip : i < S n) => a * Vnth v ip))).
  VSntac v. VSntac v'. do 2 rewrite dot_product_cons. 
  ring_simplify. rewrite IHn. 
  rewrite Vbuild_tail. rewrite Vbuild_head. simpl. ring_simplify.
  match goal with
  |- _ + dot_product ?X _ = _ + dot_product ?Y _ => replace X with Y end.
  refl. apply Veq_nth. intros. 
  do 2 rewrite Vbuild_nth. rewrite lt_Sn_nS. refl.
Qed.

(***********************************************************************)
(** Rewrite hints *)

Hint Rewrite vector_plus_zero_l vector_plus_zero_r add_vectors_cons : arith.

(** Tactics *)

Ltac Vplus_eq := simpl; (try ring_simplify);
  match goal with
  | |- ?vl [+] ?vr = ?vl' [+] ?vr' => 
    replace vl with vl'; [replace vr with vr'; try refl | try refl]
  end.

End VectorArith.

(** Arithmetic over vectors of natural numbers *)
Module OrdVectorArith (OSRT : OrdSemiRingType).

  Module VA := VectorArith OSRT.SR.
  Export VA.

  Module OSR := OrdSemiRing OSRT.
  Export OSR.

Section VectorGe.

Variable n : nat.
Notation vecn := (vec n).

(***********************************************************************)
(** [ge] on vectors *)

Definition vec_ge := Vforall2n ge.

Infix ">=v" := vec_ge (at level 70).

Lemma vec_tail_ge : forall n (v v' : vec (S n)),
  v >=v v' -> Vtail v >=v Vtail v'.

Proof.
  unfold vec_ge. intros.
  apply Vforall2_intro. intros.
  do 2 rewrite Vnth_tail.
  apply (Vforall2_nth ge). assumption.
Qed.

Lemma vec_ge_dec : rel_dec (@vec_ge n).

Proof.
  intros P Q. destruct (Vforall2_dec ge_dec P Q); intuition.
Defined.

Lemma vec_ge_refl : reflexive (@vec_ge n).

Proof.
  intros x. unfold vec_ge. apply Vforall2_intro. intros.
  apply ge_refl.
Qed.

Lemma vec_ge_trans : transitive (@vec_ge n).

Proof.
  intros x y z xy yz. unfold vec_ge.
  apply Vforall2_intro. intros.
  apply ge_trans with (Vnth y ip).
  apply (Vforall2_nth ge). assumption.
  apply (Vforall2_nth ge). assumption.
Qed.

(***********************************************************************)
(** compatibility of [vec_plus] with [vec_ge] *)

Lemma vec_plus_ge_compat : forall (vl vl' vr vr' : vecn), 
  vl >=v vl' -> vr >=v vr' -> vl [+] vr >=v vl' [+] vr'.

Proof.
  unfold vector_plus, vec_ge. intros. apply Vforall2_intro.
  intros. simpl. do 2 rewrite Vmap2_nth.
  apply plus_ge_compat.
  apply (Vforall2_nth ge). assumption.
  apply (Vforall2_nth ge). assumption.
Qed.

Lemma vec_plus_ge_compat_r : forall (vl vl' vr : vecn), 
  vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

Proof.
  intros. apply vec_plus_ge_compat. assumption. exact (vec_ge_refl vr).
Qed.

Lemma vec_plus_ge_compat_l : forall (vl vr vr' : vecn), 
  vr >=v vr' -> vl [+] vr >=v vl [+] vr'.
  
Proof.
  intros. apply vec_plus_ge_compat. exact (vec_ge_refl vl). assumption.
Qed.

End VectorGe.

Infix ">=v" := vec_ge (at level 70).

End OrdVectorArith.
