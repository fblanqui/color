(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03

  Matrices as a functor.
*)

Require Import RingCarrier.
Require Import VecUtil.
Require Import RelUtil.

Set Implicit Arguments.

(** functor building matrices structure given a carrier *)
Module Matrix (C : RingCarrier).

  Export C.

   (** basic definitions *)
  Notation vec := (vector A).

   (* Matrix represented by a vector of vectors (in a row-wise fashion) *)
  Definition matrix m n := vector (vec n) m.

   (** accessors *)
  Definition get_row m n (M : matrix m n) i (ip : i < m) := Vnth M ip.

  Definition get_col m n (M : matrix m n) i (ip : i < n) := Vmap (fun v => Vnth v ip) M.

  Definition get_elem m n (M : matrix m n) i j (ip : i < m) (jp : j < n) :=
    Vnth (get_row M ip) jp.

  Lemma get_elem_swap : forall m n (M : matrix m n) i j (ip : i < m) (jp : j < n),
    Vnth (get_row M ip) jp = Vnth (get_col M jp) ip.

  Proof.
    induction M; intros.
    elimtype False. omega.
    destruct i.
    trivial.
    simpl. rewrite IHM. trivial.
  Qed.

  Lemma mat_eq : forall m n (M N : matrix m n),
    (forall i j (ip : i < m) (jp : j < n), get_elem M ip jp = get_elem N ip jp) -> 
    M = N.

  Proof.
    unfold matrix. induction m; simpl; intros.
    VOtac. refl.
    unfold get_elem, get_row in H.
    VSntac M. VSntac N. apply Vcons_eq.
    apply Veq_nth. intros.
    do 2 rewrite Vhead_nth. apply H.
    apply IHm. intros. 
    unfold get_elem, get_row. do 2 rewrite Vnth_tail. apply H.
  Qed.

   (** matrix construction *)

  Definition mat_build_spec : forall m n (gen : forall i j, i < m -> j < n -> A), 
    { M : matrix m n | 
      forall i j (ip : i < m) (jp : j < n), get_elem M ip jp = gen i j ip jp }.

  Proof.
    induction m; intros.
    exists (Vnil (A:=vec n)). intros. elimtype False. omega.
    set (gen_1 := fun j => gen 0 j (lt_O_Sn m)).
    set (gen' := fun i j H => gen (S i) j (lt_n_S H)).
    destruct (IHm n gen') as [Mtl Mtl_spec].
    destruct (Vbuild_spec gen_1) as [Mhd Mhd_spec].
    exists (Vcons Mhd Mtl). intros.    
    destruct i; unfold get_elem; simpl.
    rewrite Mhd_spec. unfold gen_1. rewrite (le_unique (lt_O_Sn m) ip). refl.
    unfold get_elem in Mtl_spec. rewrite Mtl_spec.
    unfold gen'. rewrite (le_unique (lt_n_S (lt_S_n ip)) ip). refl.
  Defined.

  Definition mat_build m n gen : matrix m n := proj1_sig (mat_build_spec gen).

  Lemma mat_build_nth : forall m n gen i j (ip : i < m) (jp : j < n), 
    get_elem (mat_build gen) ip jp = gen i j ip jp.

  Proof.
    intros. unfold mat_build. destruct (mat_build_spec gen). simpl. apply e.
  Qed.

  Definition zero_matrix m n : matrix m n := mat_build (fun i j ip jp => A0).

  Definition id_matrix n : matrix n n := 
    mat_build (fun i j ip jp =>
      match eq_nat_dec i j with
      | left _ => A1
      | right _ => A0
      end).

  Definition inverse_matrix inv m n (M : matrix m n) : matrix m n :=
    mat_build (fun i j ip jp => inv (get_elem M ip jp)).

   (** 1-row and 1-column matrices *)

  Definition row_matrix n := matrix 1 n.
  Definition col_matrix n := matrix n 1.

  Definition vector_to_row_matrix n (v : vec n) : row_matrix n := Vcons v Vnil.

  Definition vector_to_col_matrix n (v : vec n) : col_matrix n := 
    Vmap (fun i => Vcons i Vnil) v.

  Definition access_0 : 0 < 1 := le_n 1.

  Definition row_matrix_to_vector n (m : row_matrix n) := get_row m access_0.
  Definition col_matrix_to_vector n (m : col_matrix n) := get_col m access_0.

  Lemma get_col_col_matrix : forall n (v : vec n) (p : 0 < 1),
    get_col (vector_to_col_matrix v) p = v.

  Proof.
    induction v; intros.
    trivial.
    simpl.
    rewrite IHv. trivial.
  Qed.

  Lemma vector_to_col_matrix_spec : forall n (v : vec n) i (ip : i < n) j (jp : j < 1),
    get_elem (vector_to_col_matrix v) ip jp = Vnth v ip.
  
  Proof.
    intros. unfold get_elem.
    rewrite get_elem_swap.
    destruct j.
    rewrite get_col_col_matrix. trivial.
    elimtype False. omega.
  Qed.

  Lemma vector_to_row_matrix_spec : forall n (v : vec n) i (ip : i < 1) j (jp : j < n),
    get_elem (vector_to_row_matrix v) ip jp = Vnth v jp.

  Proof.
    intros. unfold get_elem.
    destruct i.
    trivial.
    elimtype False. omega.
  Qed.

  Lemma Vnth_col_matrix : forall n (m : col_matrix n) i (ip : i < n),
    Vnth (col_matrix_to_vector m) ip = get_elem m ip access_0.

  Proof.
    induction m; intros.
    elimtype False. omega.
    destruct i.
    trivial.
    simpl. rewrite IHm. trivial.
  Qed.

  Lemma Vnth_row_matrix : forall n (m : row_matrix n) i (ip : i < n),
    Vnth (row_matrix_to_vector m) ip = get_elem m access_0 ip.

  Proof.
    trivial.
  Qed.

   (** matrix operations *)

   (* transposition *)
  Definition mat_transpose m n (M : matrix m n) := 
    mat_build (fun _ _ i j => get_elem M j i).

  Lemma mat_transpose_row_col : forall m n (M : matrix m n) i (ip : i < m),
    get_row M ip = get_col (mat_transpose M) ip.

  Proof.
    intros. apply Veq_nth. intros.  
    unfold mat_transpose, get_col. rewrite Vnth_map.
    match goal with |- _ = Vnth (Vnth ?M ?ip) ?jp => 
      fold (get_row M ip); fold (get_elem M ip jp) end.
    rewrite mat_build_nth. trivial.
  Qed.

  Lemma mat_transpose_idem : forall m n (M : matrix m n),
    mat_transpose (mat_transpose M) = M.

  Proof.
    intros. apply mat_eq. intros.
    unfold mat_transpose. do 2 rewrite mat_build_nth. refl.
  Qed.

   (* addition *)
  Definition vec_plus n (L R : vec n) := Vmap2 Aplus L R.

  Definition mat_plus m n (L R : matrix m n) :=  Vmap2 (@vec_plus n) L R.

  Infix "<+>" := mat_plus (at level 50).

   (* multiplication *)
  Definition dot_product n (l r : vec n) := Vfold_left Aplus A0 (Vmap2 Amult l r).

  Definition vect_matr_prod n p (v : vec n) (M : matrix n p) := 
    Vmap (dot_product v) (mat_transpose M).

  Definition mat_mult m n p (L : matrix m n) (R : matrix n p) :=
    Vmap (fun v => vect_matr_prod v R) L.
  Infix "<*>" := mat_mult (at level 40).

  Lemma mat_mult_spec : forall m n p (M : matrix m n) (N : matrix n p) 
    i (ip : i < m) j (jp : j < p), 
    get_elem (M <*> N) ip jp = dot_product (get_row M ip) (get_col N jp).

  Proof.
    intros. unfold mat_mult, get_elem, get_row, vect_matr_prod.
    do 2 rewrite Vnth_map. fold (get_row (mat_transpose N) jp).
    rewrite mat_transpose_row_col. rewrite (mat_transpose_idem N). refl.
  Qed.

   (** forall *)
  Section Forall.

    Variables (P : A -> Prop) (m n : nat) (M : matrix m n).

    Definition mat_forall := forall i j (ip : i < m) (jp : j < n), P (get_elem M ip jp).

     (* alternative definition *)
    Definition mat_forall' := Vforall (@Vforall A P n) M.

  End Forall.

   (** forall2 *)
  Section Forall2.

    Variables (P : relation A) (m n : nat).

    Definition mat_forall2 (M N : matrix m n):= forall i j (ip : i < m) (jp : j < n), 
      P (get_elem M ip jp) (get_elem N ip jp).

    Definition mat_forall2_intro : forall M N,
      (forall i j (ip : i < m) (jp : j < n), P (get_elem M ip jp) (get_elem N ip jp)) ->
      mat_forall2 M N := fun M N H => H.

  End Forall2.

End Matrix.

(** matrices over natural numbers *)

Module NMatrix := Matrix NCarrier.

Section Matrix_nat.

  Import NMatrix.

   (** 'monotonicity' of matrix multiplication over naturals *)
  Section MatMultMonotonicity.

    Require Import RelMidex.

    Variables (m n p : nat) (M M' : matrix m n) (N N' : matrix n p).

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
    Admitted.

    Definition mat_ge := mat_forall2 ge.
    Infix ">=m" := mat_ge (at level 70).

    Lemma mat_ge_refl : M >=m M.

    Proof.
      unfold mat_ge, mat_forall2. auto.
    Qed.

    Lemma mat_ge_dec : forall m n, rel_dec (@mat_ge m n).

    Proof.
    Admitted.

    Lemma dot_product_mon : forall i (v v' w w' : vec i), v >=v v' -> w >=v w' -> 
      dot_product v w >= dot_product v' w'.

    Proof.
      unfold dot_product. induction v. auto.
      intros. simpl. unfold ge. apply plus_le_compat.
      apply IHv.
      change v with (Vtail (Vcons a v)). apply vec_tail_ge. assumption.
      apply vec_tail_ge. assumption.
      set (p0 := lt_O_Sn n0). apply mult_le_compat.
      change a with (Vnth (Vcons a v) p0). rewrite Vhead_nth.
      apply (Vforall2_nth ge). assumption.
      do 2 rewrite Vhead_nth. apply (Vforall2_nth ge). assumption.
    Qed.

    Lemma dot_product_mon_r : forall i j (jp : j < i) (v v' w w' : vec i),
      v >=v v' -> w >=v w' -> Vnth v jp > 0 ->
      Vnth w jp > Vnth w' jp -> 
      dot_product v w > dot_product v' w'.

    Proof.
      intros i j. generalize i. clear i.
      induction j; intros.
      destruct i. elimtype False. omega.
      VSntac v. VSntac w. VSntac v'. VSntac w'.
      unfold dot_product. simpl.
      fold (dot_product (Vtail v') (Vtail w')). 
      fold (dot_product (Vtail v) (Vtail w)).
      unfold gt. apply plus_le_lt_compat.
      apply dot_product_mon; apply vec_tail_ge; assumption.
      do 4 rewrite Vhead_nth. apply mult_lt_compat_lr.
      apply (Vforall2_nth ge). assumption.
      rewrite (lt_unique (lt_O_Sn i) jp). assumption.
      rewrite (lt_unique (lt_O_Sn i) jp). assumption.
      destruct i. elimtype False. omega.
      VSntac v. VSntac w. VSntac v'. VSntac w'.
      unfold dot_product. simpl.
      fold (dot_product (Vtail v') (Vtail w')). 
      fold (dot_product (Vtail v) (Vtail w)).
      unfold gt. apply plus_lt_le_compat.
      unfold gt in IHj.
      apply IHj with (lt_S_n jp).
      apply vec_tail_ge. assumption.
      apply vec_tail_ge. assumption.
      rewrite Vnth_tail. rewrite (lt_unique (lt_n_S (lt_S_n jp)) jp). assumption.
      do 2 rewrite Vnth_tail. rewrite (lt_unique (lt_n_S (lt_S_n jp)) jp). assumption.
      apply mult_le_compat.
      do 2 rewrite Vhead_nth. apply (Vforall2_nth ge). assumption.
      do 2 rewrite Vhead_nth. apply (Vforall2_nth ge). assumption.
    Qed.

    Lemma mat_mult_mon : M >=m M' -> N >=m N' -> M <*> N >=m M' <*> N'.

    Proof.
      intros. unfold mat_ge, mat_forall2. intros.
      do 2 rewrite mat_mult_spec. apply dot_product_mon.
      unfold vec_ge. apply Vforall2_intro. intros.
      exact (H i i0 ip ip0).
      unfold vec_ge. apply Vforall2_intro. intros.
      do 2 rewrite <- get_elem_swap. exact (H0 i0 j ip0 jp).
    Qed.

  End MatMultMonotonicity.

  Section MatrixConstruction.

    Definition mkMatrix1 (v1 : nat) := Vcons (vec_of_list (v1 :: nil)) Vnil.
    Definition mkMatrix2 (v1 v2 v3 v4 : nat) := 
      Vcons (vec_of_list (v1 :: v2 :: nil)) (Vcons (vec_of_list (v3 :: v4 :: nil)) Vnil).

  End MatrixConstruction.

End Matrix_nat.

(** matrices over integers *)

Module ZMatrix := Matrix ZCarrier.
