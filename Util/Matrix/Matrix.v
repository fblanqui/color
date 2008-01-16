(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03

  Matrices as a functor.
*)

Require Export VecArith.

Set Implicit Arguments.

(** functor building matrices over given a carrier *)
Module Matrix (OSRT : OrdSemiRingType).

  Module OSR := OrdSemiRing OSRT.
  Export OSR.
  Module VA := OrdVectorArith OSRT.
  Export VA.

   (** basic definitions *)

  Notation vec := (vector A).

   (* Matrix represented by a vector of vectors (in a row-wise fashion) *)
  Definition matrix m n := vector (vec n) m.

   (** accessors *)

  Definition get_row m n (M : matrix m n) i (ip : i < m) := Vnth M ip.

  Definition get_col m n (M : matrix m n) i (ip : i < n) := 
    Vmap (fun v => Vnth v ip) M.

  Definition get_elem m n (M : matrix m n) i j (ip : i < m) (jp : j < n) :=
    Vnth (get_row M ip) jp.

  Lemma get_elem_swap : forall m n (M : matrix m n) i j (ip : i < m) 
    (jp : j < n), Vnth (get_row M ip) jp = Vnth (get_col M jp) ip.

  Proof.
    induction M; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHM. trivial.
  Qed.

  Lemma mat_eq : forall m n (M N : matrix m n), 
    (forall i j (ip : i < m) (jp : j < n), 
      get_elem M ip jp = get_elem N ip jp) -> M = N.

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

  Ltac prove_mat_eq := 
    match goal with 
    |- ?L = ?R => apply (mat_eq L R); intros 
    end.

   (** matrix construction *)

  Definition mat_build_spec : forall m n 
    (gen : forall i j, i < m -> j < n -> A), 
    { M : matrix m n | forall i j (ip : i < m) (jp : j < n), 
      get_elem M ip jp = gen i j ip jp }.

  Proof.
    induction m; intros.
    exists (Vnil (A:=vec n)). intros.
    elimtype False. exact (lt_n_O i ip).
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

  Lemma mat_build_elem : forall m n gen i j (ip : i < m) (jp : j < n), 
    get_elem (mat_build gen) ip jp = gen i j ip jp.

  Proof.
    intros. unfold mat_build. destruct (mat_build_spec gen). simpl. apply e.
  Qed.

  Lemma mat_build_nth : forall m n gen i j (ip : i < m) (jp : j < n),
    Vnth (Vnth (mat_build gen) ip) jp = gen i j ip jp.

  Proof.
    intros. fold (get_row (mat_build gen) ip).
    fold (get_elem (mat_build gen) ip jp).
    apply mat_build_elem.
  Qed.

   (** Some elementary matrices *)

  Definition zero_matrix m n : matrix m n := mat_build (fun i j ip jp => A0).

  Definition id_matrix n : matrix n n := Vbuild (fun i ip => id_vec n i).

  Definition inverse_matrix inv m n (M : matrix m n) : matrix m n :=
    mat_build (fun i j ip jp => inv (get_elem M ip jp)).

   (** 1-row and 1-column matrices *)

  Definition row_mat n := matrix 1 n.
  Definition col_mat n := matrix n 1.

  Definition vec_to_row_mat n (v : vec n) : row_mat n := Vcons v Vnil.

  Definition vec_to_col_mat n (v : vec n) : col_mat n := 
    Vmap (fun i => Vcons i Vnil) v.

  Definition access_0 : 0 < 1 := le_n 1.

  Definition row_mat_to_vec n (m : row_mat n) := get_row m access_0.
  Definition col_mat_to_vec n (m : col_mat n) := get_col m access_0.

  Ltac mat_get_simpl :=
    repeat progress unfold get_elem, get_col, get_row, 
      vec_to_col_mat, vec_to_row_mat, col_mat_to_vec, row_mat_to_vec; 
      repeat progress ( try rewrite Vnth_map; try rewrite Vmap2_nth );
        ring_simplify; try refl.

  Lemma get_col_col_mat : forall n (v : vec n) (p : 0 < 1),
    get_col (vec_to_col_mat v) p = v.

  Proof.
    induction v; intros.
    trivial.
    simpl.
    rewrite IHv. trivial.
  Qed.

  Lemma vec_to_col_mat_spec : forall n (v : vec n) i (ip : i < n) j 
    (jp : j < 1), get_elem (vec_to_col_mat v) ip jp = Vnth v ip.
  
  Proof.
    intros. unfold get_elem.
    rewrite get_elem_swap.
    destruct j.
    rewrite get_col_col_mat. trivial.
    absurd_arith.
  Qed.

  Lemma vec_to_row_mat_spec : forall n (v : vec n) i (ip : i < 1) j 
    (jp : j < n), get_elem (vec_to_row_mat v) ip jp = Vnth v jp.

  Proof.
    intros. unfold get_elem.
    destruct i. trivial. absurd_arith.
  Qed.

  Lemma Vnth_col_mat : forall n (m : col_mat n) i (ip : i < n),
    Vnth (col_mat_to_vec m) ip = get_elem m ip access_0.

  Proof.
    induction m; intros. absurd_arith.
    destruct i.
    trivial.
    simpl. rewrite IHm. trivial.
  Qed.

  Lemma Vnth_row_mat : forall n (m : row_mat n) i (ip : i < n),
    Vnth (row_mat_to_vec m) ip = get_elem m access_0 ip.

  Proof.
    trivial.
  Qed.

  Lemma col_mat_to_vec_idem : forall n (v : vec n), 
    col_mat_to_vec (vec_to_col_mat v) = v.

  Proof.
    intros. apply Veq_nth. intros. mat_get_simpl.
  Qed.

  Lemma vec_to_col_mat_idem : forall n (M : col_mat n), 
    vec_to_col_mat (col_mat_to_vec M) = M.

  Proof.
    intros. prove_mat_eq. mat_get_simpl.
    destruct j. rewrite (lt_unique access_0 jp). refl.
    absurd_arith.
  Qed.

  Lemma row_mat_to_vec_idem : forall n (v : vec n), 
    row_mat_to_vec (vec_to_row_mat v) = v.

  Proof.
    intros. apply Veq_nth. intros. mat_get_simpl.
  Qed.

  Lemma vec_to_row_mat_idem : forall n (M : row_mat n), 
    vec_to_row_mat (row_mat_to_vec M) = M.

  Proof.
    intros. prove_mat_eq. mat_get_simpl.
    destruct i. simpl. rewrite (lt_unique access_0 ip). refl.
    absurd_arith.
  Qed.

   (** matrix transposition *)

  Definition mat_transpose m n (M : matrix m n) := 
    mat_build (fun _ _ i j => get_elem M j i).

  Lemma mat_transpose_row_col : forall m n (M : matrix m n) i (ip : i < m),
    get_col (mat_transpose M) ip = get_row M ip.

  Proof.
    intros. apply Veq_nth. intros.  
    mat_get_simpl. unfold mat_transpose.
    rewrite mat_build_nth. trivial.
  Qed.

  Lemma mat_transpose_col_row : forall m n (M : matrix m n) i (ip : i < n),
    get_row (mat_transpose M) ip = get_col M ip.

  Proof.
    intros. apply Veq_nth. intros.
    mat_get_simpl. unfold mat_transpose.
    rewrite mat_build_nth. trivial.
  Qed.

  Lemma mat_transpose_idem : forall m n (M : matrix m n),
    mat_transpose (mat_transpose M) = M.

  Proof.
    intros. prove_mat_eq.
    unfold mat_transpose. do 2 rewrite mat_build_elem. refl.
  Qed.

   (** matrix addition *)

  Definition vec_plus n (L R : vec n) := Vmap2 Aplus L R.

  Definition mat_plus m n (L R : matrix m n) :=  Vmap2 (@vec_plus n) L R.

  Infix "<+>" := mat_plus (at level 50).

  Lemma mat_plus_comm : forall m n (L R : matrix m n), 
    L <+> R = R <+> L.

  Proof.
    intros. prove_mat_eq. unfold mat_plus, vec_plus. mat_get_simpl.
  Qed.

   (** matrix multiplication *)

  Definition mat_mult m n p (L : matrix m n) (R : matrix n p) :=
    mat_build (fun i j ip jp => dot_product (get_row L ip) (get_col R jp)).
  Infix "<*>" := mat_mult (at level 40).

  Lemma mat_mult_elem : forall m n p (M : matrix m n) (N : matrix n p) 
    i (ip : i < m) j (jp : j < p), 
    Vnth (Vnth (M <*> N) ip) jp = dot_product (get_row M ip) (get_col N jp).

  Proof.
    intros. unfold mat_mult. rewrite mat_build_nth. refl.
  Qed.

  Lemma mat_mult_spec : forall m n p (M : matrix m n) (N : matrix n p) 
    i (ip : i < m) j (jp : j < p), 
    get_elem (M <*> N) ip jp = dot_product (get_row M ip) (get_col N jp).

  Proof.
    intros. mat_get_simpl. rewrite mat_mult_elem. refl.
  Qed.

  Lemma mat_mult_row : forall m n p (M : matrix m n) (N : matrix n p) 
    i (ip : i < m),
    get_row (M <*> N) ip = 
    Vbuild (fun j jp => dot_product (get_row M ip) (get_col N jp)).

  Proof.
    intros. apply Veq_nth. intros. mat_get_simpl. 
    rewrite mat_mult_elem. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_col : forall m n p (M : matrix m n) (N : matrix n p) 
    j (jp : j < p),
    get_col (M <*> N) jp = 
    Vbuild (fun i ip => dot_product (get_row M ip) (get_col N jp)).

  Proof.
    intros. apply Veq_nth. intros. mat_get_simpl. 
    rewrite mat_mult_elem. rewrite Vbuild_nth. refl.
  Qed.

  Lemma mat_mult_id_l : forall n p (np : n >= p) (M : matrix n p), 
    id_matrix n <*> M = M.

  Proof.
    intros. prove_mat_eq. rewrite mat_mult_spec.
    unfold id_matrix, get_row. rewrite Vbuild_nth.
    rewrite (dot_product_id ip). mat_get_simpl.
  Qed.

  Lemma zero_matrix_mult_l : forall m n p (M : matrix n p), 
    zero_matrix m n <*> M = zero_matrix m p.

  Proof.
    intros. prove_mat_eq.
    unfold zero_matrix at 2. mat_get_simpl.
    fold (get_row (zero_matrix m n <*> M) ip).
    fold (get_elem (zero_matrix m n <*> M) ip jp).
    rewrite mat_mult_spec. rewrite dot_product_zero. 
    rewrite mat_build_nth. refl.
    apply Vforall_nth_intro. intros.
    unfold zero_matrix. mat_get_simpl. rewrite mat_build_nth. refl.
  Qed.

  Lemma dot_product_assoc : forall m n v v' (M : matrix m n),
    dot_product v (Vbuild (fun i (ip : i < m ) => 
      dot_product (get_row M ip) v')) =
    dot_product (Vbuild (fun j (jp : j < n) =>
      dot_product v (get_col M jp))) v'.
  
  Proof.
    induction m; intros.
     (* induction base *)
    VOtac. repeat rewrite dot_product_zero. refl.
    apply Vforall_nth_intro. intros. rewrite Vbuild_nth. 
    unfold dot_product. trivial.
    apply Vforall_intro. intros. destruct H.
     (* induction case *)
    VSntac v.
    rewrite (VSn_eq (Vbuild (fun i ip => dot_product (get_row M ip) v'))).
    rewrite dot_product_cons. do 2 rewrite Vhead_nth. rewrite Vbuild_nth.
    rewrite Vbuild_tail. unfold matrix in M. VSntac M. simpl.
    match goal with
    |- _ + dot_product _ (Vbuild ?gen) = _ => replace (Vbuild gen) with 
      (Vbuild (fun i ip => dot_product (get_row (Vtail M) ip) v')) end.
    rewrite (IHm n (Vtail v) v' (Vtail M)).    
    set (w := dot_product_cons).
    replace (Vbuild (fun j jp => dot_product (Vcons (Vnth v (lt_O_Sn m)) 
      (Vtail v)) (Vcons (Vnth (Vhead M) jp) (get_col (Vtail M) jp)))) with
    (Vbuild (fun j jp => Vnth v (lt_O_Sn m) * (Vnth (Vhead M) jp)) [+]
    (Vbuild (fun j jp => dot_product (Vtail v) (get_col (Vtail M) jp)))).
    rewrite dot_product_distr_l. rewrite dot_product_distr_mult. refl.
    apply Veq_nth. intros. rewrite vector_plus_nth. do 3 rewrite Vbuild_nth. 
    rewrite dot_product_cons. refl.
    apply Veq_nth. intros. do 2 rewrite Vbuild_nth. 
    rewrite lt_Sn_nS. refl.
  Qed.

  Lemma mat_mult_assoc : forall m n p l 
    (M : matrix m n) (N : matrix n p) (P : matrix p l),
    M <*> (N <*> P) = M <*> N <*> P.

  Proof.
    intros. apply (mat_eq (M <*> (N <*> P))). intros.
    mat_get_simpl. repeat rewrite mat_mult_elem.
    rewrite mat_mult_row. rewrite mat_mult_col.
    apply dot_product_assoc.
  Qed.

   (** matrix-col vector product *)

  Definition mat_vec_prod m n (m : matrix m n) (v : vec n) :=
    col_mat_to_vec (m <*> (vec_to_col_mat v)).

  Lemma mat_vec_prod_distr_vec : forall m n (M : matrix m n) v1 v2,
    mat_vec_prod M (v1 [+] v2) =
    mat_vec_prod M v1 [+] mat_vec_prod M v2.

  Proof.
    intros. unfold mat_vec_prod. apply Veq_nth. intros.
    rewrite vector_plus_nth. mat_get_simpl.
    repeat rewrite mat_mult_elem. rewrite <- dot_product_distr_r.
    match goal with 
    |- dot_product _ ?X = dot_product _ (?Y [+] ?Z) => 
      replace X with (Y [+] Z) 
    end. refl.
    apply Veq_nth. unfold get_col. intros.
    rewrite vector_plus_nth. repeat rewrite Vnth_map.
    simpl. rewrite vector_plus_nth. refl.
  Qed.

  Lemma mat_vec_prod_distr_mat : forall m n (Ml Mr : matrix m n) v,
    mat_vec_prod (Ml <+> Mr) v =
    mat_vec_prod Ml v [+] mat_vec_prod Mr v.

  Proof.
    intros. unfold mat_vec_prod. apply Veq_nth. intros.
    rewrite vector_plus_nth. mat_get_simpl.
    repeat rewrite mat_mult_elem. 
    rewrite dot_product_comm with (u := get_row Ml ip).
    rewrite dot_product_comm with (u := get_row Mr ip).
    rewrite <- dot_product_distr_r.
    rewrite dot_product_comm with 
      (u := get_col (Vmap (fun i => Vcons i Vnil) v) access_0).
    match goal with 
    |- dot_product ?X _ = dot_product (?Y [+] ?Z) _ => 
      replace X with (Y [+] Z) 
    end. refl.
    apply Veq_nth. unfold get_row. intros.
    rewrite vector_plus_nth. unfold mat_plus. rewrite Vmap2_nth.
    rewrite vector_plus_nth. refl.
  Qed.

  Lemma mat_vec_prod_distr_add_vectors : forall m n (M : matrix m n) k v1 v2,
    (forall i (ip : i < k), mat_vec_prod M (Vnth v1 ip) = Vnth v2 ip) ->
    mat_vec_prod M (add_vectors v1) = add_vectors v2.
    
  Proof.
    induction k; intros.
     (* induction base *)
    VOtac. unfold add_vectors. simpl.
    apply Veq_nth. intros.
    unfold mat_vec_prod. rewrite Vnth_col_mat. 
    unfold zero_vec. rewrite Vnth_const.
    rewrite mat_mult_spec. 
    rewrite dot_product_comm. rewrite dot_product_zero. refl.
    apply Vforall_nth_intro. intros.
    rewrite get_col_col_mat. rewrite Vnth_const. refl.
     (* induction step *)
    VSntac v1. VSntac v2. 
    do 2 rewrite add_vectors_cons. rewrite mat_vec_prod_distr_vec. 
    do 2 rewrite Vhead_nth. rewrite H. 
    rewrite (IHk (Vtail v1) (Vtail v2)). refl.
    intros. rewrite Vnth_tail. rewrite H.
    rewrite Vnth_tail. refl.
  Qed.

   (** forall *)

  Section Forall.

    Variables (P : A -> Prop) (m n : nat) (M : matrix m n).

    Definition mat_forall := forall i j (ip : i < m) (jp : j < n), 
      P (get_elem M ip jp).

     (* alternative definition *)
    Definition mat_forall' := Vforall (@Vforall A P n) M.

  End Forall.

   (** forall2 *)

  Section Forall2.

    Variables (P : relation A) (m n : nat).

    Definition mat_forall2 (M N : matrix m n):= forall i j (ip : i < m) 
      (jp : j < n), P (get_elem M ip jp) (get_elem N ip jp).

    Definition mat_forall2_intro : forall M N,
      (forall i j (ip : i < m) (jp : j < n), 
        P (get_elem M ip jp) (get_elem N ip jp)) ->
      mat_forall2 M N := fun M N H => H.

     (* alternative definition *)
    Definition mat_forall2' (M N : matrix m n) := 
      Vforall2n (@Vforall2n A P n) M N.

    Require Import RelMidex.

    Variable P_dec : rel_dec P.

    Lemma mat_forall2'_dec : rel_dec mat_forall2'.

    Proof.
      intros M N. unfold mat_forall2'. do 2 apply Vforall2n_dec. assumption.
    Defined.

    Lemma mat_forall2_equiv1 : forall M N, 
      mat_forall2 M N -> mat_forall2' M N.

    Proof.
      intros. unfold mat_forall2'. do 2 (apply Vforall2_intro; intros). 
      exact (H i i0 ip ip0).
    Qed.

    Lemma mat_forall2_equiv2 : forall M N, 
      mat_forall2' M N -> mat_forall2 M N.

    Proof.
      intros. unfold mat_forall2, get_elem, get_row. intros.
      apply (Vforall2_nth P). apply (Vforall2_nth (@Vforall2n A P n)). 
      assumption.
    Qed.

    Lemma mat_forall2_dec : rel_dec mat_forall2.

    Proof.
      intros M N. destruct (mat_forall2'_dec M N).
      left. apply mat_forall2_equiv2. assumption.
      right. intro. apply n0. apply mat_forall2_equiv1. assumption.
    Defined.

  End Forall2.

  Hint Rewrite mat_mult_id_l zero_matrix_mult_l using simpl : arith.

   (** 'monotonicity' of matrix multiplication over naturals *)
  Section MatMultMonotonicity.

    Require Import RelMidex.

    Variables (m n p : nat) (M M' : matrix m n) (N N' : matrix n p).

    Definition mat_ge := mat_forall2 ge.
    Infix ">=m" := mat_ge (at level 70).

    Lemma mat_ge_refl : M >=m M.

    Proof.
      unfold mat_ge, mat_forall2. 
      intros. apply ge_refl.
    Qed.

    Lemma mat_ge_dec : forall m n, rel_dec (@mat_ge m n).

    Proof.
      intros R Q. unfold mat_ge. apply mat_forall2_dec. exact ge_dec.
    Defined.

    Lemma dot_product_mon : forall i (v v' w w' : vec i), v >=v v' -> 
      w >=v w' -> dot_product v w >>= dot_product v' w'.

    Proof.
      unfold dot_product. induction v. auto with arith. 
      intros. simpl. apply plus_ge_compat.
      apply IHv.
      change v with (Vtail (Vcons a v)). apply vec_tail_ge. assumption.
      apply vec_tail_ge. assumption.
      set (p0 := lt_O_Sn n0). apply mult_ge_compat.
      change a with (Vnth (Vcons a v) p0). rewrite Vhead_nth.
      apply (Vforall2_nth ge). assumption.
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

    Definition mkMatrix1 (v1 : A) := Vcons (vec_of_list (v1 :: nil)) Vnil.
    Definition mkMatrix2 (v1 v2 v3 v4 : A) := 
      Vcons (vec_of_list (v1 :: v2 :: nil)) 
     (Vcons (vec_of_list (v3 :: v4 :: nil)) Vnil).
    Definition mkMatrix3 (v1 v2 v3 v4 v5 v6 v7 v8 v9 : A) := 
      Vcons (vec_of_list (v1 :: v2 :: v3 :: nil)) 
     (Vcons (vec_of_list (v4 :: v5 :: v6 :: nil))
     (Vcons (vec_of_list (v7 :: v8 :: v9 :: nil)) Vnil)).
    Definition mkMatrix4 (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 
      v12 v13 v14 v15 v16 : A) := 
      Vcons (vec_of_list ( v1 ::  v2 ::  v3 ::  v4 :: nil)) 
     (Vcons (vec_of_list ( v5 ::  v6 ::  v7 ::  v8 :: nil))
     (Vcons (vec_of_list ( v9 :: v10 :: v11 :: v12 :: nil))
     (Vcons (vec_of_list (v13 :: v14 :: v15 :: v16 :: nil)) Vnil))).

  End MatrixConstruction.

  Lemma mat_vec_prod_ge_compat : forall i j (M M' : matrix i j) m m', 
    mat_ge M M' -> m >=v m' -> mat_vec_prod M m >=v mat_vec_prod M' m'.

  Proof.
    intros. unfold mat_vec_prod, vec_ge. apply Vforall2_intro. 
    intros. do 2 rewrite Vnth_col_mat. apply mat_mult_mon. assumption.
    unfold mat_ge. intros k l pk pl. do 2 rewrite vec_to_col_mat_spec.
    apply (Vforall2_nth ge). assumption.
  Qed.

  Infix ">=m" := mat_ge (at level 70).

End Matrix.

(** matrices over different domains *)

Module NMatrix := Matrix NOrdSemiRingT.
Module ArcticMatrix := Matrix ArcticOrdSemiRingT.

