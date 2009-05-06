(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski, 2007-04-02

Arithmetic over vectors of coefficients.
*)

Set Implicit Arguments.

Require Import VecUtil.
Require Import RelUtil.
Require Import SemiRing.
Require Import OrdSemiRing.
Require Import NatUtil.
Require Import LogicUtil.
Require Import VecEq.
Require Import Setoid.

(***********************************************************************)
(** Module with arithmetic over vectors of coefficients *)

Module VectorArith (SRT : SemiRingType).

Module Export SR := SemiRing SRT.

Notation vec := (vector A).

Definition zero_vec := Vconst A0.

Definition id_vec n i (ip : i < n) := Vreplace (zero_vec n) ip A1.

Definition eq_vec := @eq_vec A eqA.

Notation "v1 =v v2" := (eq_vec v1 v2) (at level 70).

Add Parametric Relation n : (vec n) (@eq_vec n)
  reflexivity proved by (@eq_vec_refl A eqA sid_theoryA n)
  symmetry proved by (@eq_vec_sym A eqA sid_theoryA n)
  transitivity proved by (@eq_vec_trans A eqA sid_theoryA n)
  as eq_vec_rel.

(***********************************************************************)
(** vector plus *)

Definition vector_plus n (v1 v2 : vec n) := Vmap2 Aplus v1 v2.

Infix "[+]" := vector_plus (at level 50).

Add Parametric Morphism n : (@vector_plus n)
  with signature (@eq_vec n) ==> (@eq_vec n) ==> (@eq_vec n)
  as vector_plus_mor.

Proof.
intros. apply Vforall2n_intro. intros. unfold vector_plus.
repeat rewrite Vnth_map2.
(*FIXME: rewrite H does not work even if Vnth is declared as morphism *)
apply Aplus_mor; apply (Vnth_mor eqA); hyp.
Qed.

Lemma vector_plus_nth : forall n (vl vr : vec n) i (ip : i < n),
  Vnth (vl [+] vr) ip =A= Vnth vl ip + Vnth vr ip.

Proof.
  intros. unfold vector_plus. rewrite Vnth_map2. refl.
Qed.

Lemma vector_plus_comm : forall n (v1 v2 : vec n), v1 [+] v2 =v v2 [+] v1.

Proof.
  intros. apply Vforall2n_intro. intros. do 2 rewrite vector_plus_nth. ring.
Qed.

Lemma vector_plus_assoc : forall n (v1 v2 v3 : vec n),
  v1 [+] (v2 [+] v3) =v v1 [+] v2 [+] v3.

Proof.
  intros. apply Vforall2n_intro. intros. do 4 rewrite vector_plus_nth. ring.
Qed.

Lemma vector_plus_zero_r : forall n (v : vec n), v [+] zero_vec n =v v.

Proof.
  intros. apply Vforall2n_intro. intros. rewrite vector_plus_nth.
  set (w := Vnth_const A0 ip). fold zero_vec in w. rewrite w. ring.
Qed.

Lemma vector_plus_zero_l : forall n (v : vec n), zero_vec n [+] v =v v.

Proof.
  intros. rewrite vector_plus_comm. apply vector_plus_zero_r.
Qed.

(***********************************************************************)
(** sum of a vector of vectors *)

Definition add_vectors n k (v : vector (vec n) k) := 
  Vfold_left (@vector_plus n) (zero_vec n) v.

Add Parametric Morphism n k : (@add_vectors n k)
  with signature (@VecEq.eq_vec _ (@eq_vec n) k) ==> (@eq_vec n)
    as add_vectors_mor.

Proof.
induction x; simpl; intros. VOtac. refl. gen H. VSntac y. unfold add_vectors.
simpl. rewrite (eq_vec_cons (@eq_vec n)). intuition. rewrite H1.
apply vector_plus_mor. 2: refl. eapply Vfold_left_mor with (b := zero_vec n)
  (b' := zero_vec n) (v := x) (v' := Vtail y). apply vector_plus_mor. refl. hyp.
Qed.

Lemma add_vectors_cons : forall n i (a : vec n) (v : vector (vec n) i),
  add_vectors (Vcons a v) =v a [+] add_vectors v.

Proof.
  intros. unfold add_vectors. simpl. rewrite vector_plus_comm. refl.
Qed.

Lemma add_vectors_zero : forall n k (v : vector (vec n) k), 
  Vforall (fun v => v =v zero_vec n) v -> add_vectors v =v zero_vec n.

Proof.
  induction v. refl. rewrite add_vectors_cons. simpl. intuition.
  rewrite H0. rewrite vector_plus_zero_l. hyp.
Qed.

Lemma add_vectors_perm : forall n i v v' (vs : vector (vec n) i),
  add_vectors (Vcons v (Vcons v' vs)) =v add_vectors (Vcons v' (Vcons v vs)).

Proof.
  intros. repeat rewrite add_vectors_cons. repeat rewrite vector_plus_assoc.
  rewrite (vector_plus_comm v v'). refl.
Qed.

Lemma add_vectors_nth : forall n k (vs : vector (vec n) k) i (ip : i < n),
  Vnth (add_vectors vs) ip =A=
  Vfold_left Aplus A0 (Vmap (fun v => Vnth v ip) vs).

Proof.
  induction vs; simpl; intros.
  unfold add_vectors, zero_vec; simpl. rewrite Vnth_const. refl.
  rewrite Vnth_mor. 2: rewrite add_vectors_cons; refl.
  rewrite vector_plus_nth. rewrite IHvs. rewrite Aplus_comm. refl.
Qed.

Lemma add_vectors_split : forall n k (v vl vr : vector (vec n) k),
  (forall i (ip : i < k), Vnth v ip =v Vnth vl ip [+] Vnth vr ip) ->
  add_vectors v =v add_vectors vl [+] add_vectors vr.

Proof.
  induction k; intros.
  VOtac. unfold add_vectors. simpl. rewrite vector_plus_zero_r. refl.
  VSntac v. VSntac vl. VSntac vr. do 3 rewrite add_vectors_cons.
  rewrite (IHk (Vtail v) (Vtail vl) (Vtail vr)). do 3 rewrite Vhead_nth.
  rewrite (H 0 (lt_O_Sn k)).
  match goal with
  |- (?A [+] ?B) [+] (?C [+] ?D) =v (?A [+] ?C) [+] (?B [+] ?D) =>
    set (X := A); set (Y := B); set (W := C); set (V := D) end.
  do 2 rewrite <- vector_plus_assoc. rewrite (vector_plus_assoc W Y V).
  rewrite (vector_plus_comm W Y). do 4 rewrite vector_plus_assoc. refl.
  intros. do 3 rewrite Vnth_tail. apply H.
Qed.

(***********************************************************************)
(** dot product *)

Definition dot_product n (l r : vec n) :=
  Vfold_left Aplus A0 (Vmap2 Amult l r).

Add Parametric Morphism n : (@dot_product n)
  with signature (@eq_vec n) ==> (@eq_vec n) ==> eqA
  as dot_product_mor.

Proof.
induction n; intros. VOtac. refl. gen H0. gen H.
VSntac x. VSntac y. VSntac x0. VSntac y0. intros.
rewrite (eq_vec_cons eqA) in H3. rewrite (eq_vec_cons eqA) in H4. intuition.
unfold dot_product. simpl. unfold dot_product in IHn.
rewrite (IHn _ _ H6 _ _ H7). rewrite H5. rewrite H3. refl.
Qed.

Lemma dot_product_zero : forall n (v v' : vec n),
  Vforall (fun el => el =A= A0) v -> dot_product v v' =A= A0.

Proof.
  induction n; intros.
  VOtac. refl.
  VSntac v. VSntac v'. unfold dot_product. simpl.
  fold (dot_product (Vtail v) (Vtail v')). rewrite IHn.
  assert (Vhead v =A= A0). rewrite Vhead_nth. apply Vforall_nth. hyp.
  rewrite H2. ring.
  apply Vforall_incl with (S n) v. intros.
  apply Vin_tail. assumption. assumption.
Qed.

Lemma dot_product_id : forall i n (ip : i < n) v,
  dot_product (id_vec ip) v =A= Vnth v ip.

Proof.
  induction i. intros. 
  destruct n. absurd_arith.

   (* induction base *)
  VSntac v. unfold id_vec, dot_product. simpl.
  fold (dot_product (Vconst A0 n) (Vtail v)).
  rewrite dot_product_zero. ring.
  apply Vforall_nth_intro. intros.
  rewrite Vnth_const. refl.

   (* induction step *)
  intros. destruct n. absurd_arith.
  VSntac v. unfold dot_product. simpl.
  rewrite <- (IHi n (lt_S_n ip) (Vtail v)).
  ring_simplify. unfold dot_product. refl.
Qed.

Lemma dot_product_comm : forall n (u v : vec n),
  dot_product u v =A= dot_product v u.

Proof.
  induction n. refl. intros. VSntac u. VSntac v. unfold dot_product. simpl.
  unfold dot_product in IHn. rewrite IHn. ring.
Qed.

Lemma dot_product_distr_r : forall n (v vl vr : vec n),
  dot_product v (vl [+] vr) =A= dot_product v vl + dot_product v vr.

Proof.
  induction n; intros.
  VOtac. unfold dot_product. simpl. ring.
  VSntac v. VSntac vl. VSntac vr. unfold dot_product. simpl.
  fold (Vtail vl [+] Vtail vr).
  fold (dot_product (Vtail v) (Vtail vl [+] Vtail vr)).
  rewrite IHn. unfold dot_product. ring.
Qed.

Lemma dot_product_distr_l : forall n (v vl vr : vec n),
  dot_product (vl [+] vr) v =A= dot_product vl v + dot_product vr v.

Proof.
  intros. rewrite dot_product_comm. rewrite dot_product_distr_r. 
  rewrite (dot_product_comm v vl). rewrite (dot_product_comm v vr). refl.
Qed.

Lemma dot_product_cons : forall n al ar (vl vr : vec n),
  dot_product (Vcons al vl) (Vcons ar vr) =A= al * ar + dot_product vl vr.

Proof.
  intros. unfold dot_product. simpl. ring.
Qed.

Lemma dot_product_distr_mult : forall n a (v v' : vec n),
  a * dot_product v v' =A=
  dot_product (Vbuild (fun i ip => a * Vnth v ip)) v'.

Proof.
  induction n; intros.
  VOtac. unfold dot_product. simpl. ring.
  rewrite (VSn_eq (Vbuild (fun i (ip : i < S n) => a * Vnth v ip))).
  VSntac v. VSntac v'. do 2 rewrite dot_product_cons. 
  ring_simplify. rewrite IHn. 
  rewrite Vbuild_tail. rewrite Vbuild_head. simpl. ring_simplify.
  match goal with
  |- _ + dot_product ?X _ =A= _ + dot_product ?Y _ => replace X with Y end.
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

  Module Export VA := VectorArith OSRT.SR.
  Module Export OSR := OrdSemiRing OSRT.

(***********************************************************************)
(** [ge] on vectors *)

Definition vec_ge := Vforall2n ge.

Infix ">=v" := vec_ge (at level 70).

Lemma vec_tail_ge : forall n (v v' : vec (S n)),
  v >=v v' -> Vtail v >=v Vtail v'.

Proof.
  intros. unfold vec_ge. apply Vforall2n_tail. assumption.
Qed.

Lemma vec_ge_dec : forall n, rel_dec (@vec_ge n).

Proof.
  intros n P Q. destruct (Vforall2n_dec ge_dec P Q); intuition.
Defined.

Lemma vec_ge_refl : forall n, reflexive (@vec_ge n).

Proof.
  intros n x. unfold vec_ge. apply Vforall2n_intro. intros.
  apply ge_refl.
Qed.

Lemma vec_ge_trans : forall n, transitive (@vec_ge n).

Proof.
  intros n x y z xy yz. unfold vec_ge.
  apply Vforall2n_intro. intros.
  apply ge_trans with (Vnth y ip).
  apply (Vforall2n_nth ge). assumption.
  apply (Vforall2n_nth ge). assumption.
Qed.

Add Parametric Morphism n : (@vec_ge n)
  with signature (@eq_vec n) ==> (@eq_vec n) ==> iff
    as vec_ge_mor.

Proof.
unfold vec_ge. intros. apply (Vforall2n_mor sid_theoryA). intuition.
transitivity a1. apply eq_ge_compat. symmetry. hyp.
transitivity a2. hyp. apply eq_ge_compat. hyp.
transitivity a1'. apply eq_ge_compat. hyp.
transitivity a2'. hyp. apply eq_ge_compat. symmetry. hyp.
hyp. hyp.
Qed.

Implicit Arguments vec_ge_mor [n x y x0 y0].

(***********************************************************************)
(** compatibility of [vec_plus] with [vec_ge] *)

Lemma vec_plus_ge_compat : forall n (vl vl' vr vr' : vec n), 
  vl >=v vl' -> vr >=v vr' -> vl [+] vr >=v vl' [+] vr'.

Proof.
  unfold vector_plus, vec_ge. intros. apply Vforall2n_intro.
  intros. simpl. do 2 rewrite Vnth_map2.
  apply plus_ge_compat.
  apply (Vforall2n_nth ge). assumption.
  apply (Vforall2n_nth ge). assumption.
Qed.

Lemma vec_plus_ge_compat_r : forall n (vl vl' vr : vec n), 
  vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

Proof.
  intros. apply vec_plus_ge_compat. assumption. exact (vec_ge_refl vr).
Qed.

Lemma vec_plus_ge_compat_l : forall n (vl vr vr' : vec n), 
  vr >=v vr' -> vl [+] vr >=v vl [+] vr'.
  
Proof.
  intros. apply vec_plus_ge_compat. exact (vec_ge_refl vl). assumption.
Qed.

Infix ">=v" := vec_ge (at level 70).

End OrdVectorArith.
