(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03-22

Termination criterion based on matrix interpretations.

References:
-  J. Endrullis, J. Waldmann and H. Zantema, "Matrix Interpretations for 
   Proving Termination of Term Rewriting", Proceedings of the 3rd 
   International Joint Conference (IJCAR 2006), 2006.
*)

Set Implicit Arguments.

Require Export Matrix.
Require Import AMonAlg.
Export NMatrix.

(** Interpretation type for matrix interpretations *)
Section FunInt.

  Variables (Sig : Signature) (f : symbol Sig) (dim : nat).

   (* function interpretation : one [dim]x[dim] matrix per argument and
      one vector of dimension [dim] for a constant factor *)
  Record matrixInt (argCnt : nat) : Type := mkMatrixInt {
    const : vector nat dim;
    args : vector (matrix dim dim) argCnt
  }.

  Variable dim_pos : dim > 0.

   (* additional property of interpretation required to ensure strict
      monotonicity of interpretations: upper left corner of every matrix
      needs to be positive *)
  Definition monotone_interpretation n (fi : matrixInt n) := 
    Vforall (fun m => get_elem m dim_pos dim_pos > 0) (args fi).

End FunInt.

(** Module type for proving relative-top termination (in the DP setting) *)
Module Type TMatrixInt_DP.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : dim > 0.
  Parameter trsInt : forall f : sig, matrixInt dim (arity f).

End TMatrixInt_DP.

(** Module type for proving relative termination *)
Module Type TMatrixInt.

  Declare Module MI : TMatrixInt_DP.
  Export MI.

  Parameter matrixInt_monotone : forall f : sig, 
    monotone_interpretation dim_pos (trsInt f).

End TMatrixInt.

Ltac matrixInt_monotonicity := intro f; destruct f; vm_compute; auto with arith.

Module MatrixInt_DP (MI : TMatrixInt_DP).

  Export MI.

  Notation vec := (vec dim).
  Notation mint := (matrixInt dim).
  Notation mat := (matrix dim dim).

  Definition add_matrices i m n (v : vector (matrix m n) i) := 
    Vfold_left (@mat_plus m n) (zero_matrix m n) v.

  Definition vec_at0 (v : vec) := Vnth v dim_pos.

  Notation mat_times_vec := (@mat_vec_prod dim dim).

  Definition mi_eval n (mi : matrixInt dim n) (v : vector vec n) : vec :=
    add_vectors (Vmap2 mat_times_vec (args mi) v) [+] const mi.

  Lemma mi_eval_cons : forall n (mi : matrixInt dim (S n)) v vs,
    mi_eval mi (Vcons v vs) = mat_times_vec (Vhead (args mi)) v [+] 
    mi_eval (mkMatrixInt (const mi) (Vtail (args mi))) vs.

  Proof.
    induction n; intros.
    VOtac. unfold mi_eval. rewrite vector_plus_assoc. 
    simpl. autorewrite with arith. refl.
    VSntac vs. unfold mi_eval. rewrite vector_plus_assoc. 
    simpl. autorewrite with arith. refl.
  Qed.

  (** Monotone algebra instantiated to matrices *)
  Module MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := sig.
    
    Definition I := @mkInterpretation sig vec (@zero_vec dim) 
      (fun f => mi_eval (trsInt f)).

    Definition succeq := @vec_ge dim.

    Definition succ v1 v2 := v1 >=v v2 /\ vec_at0 v1 > vec_at0 v2.
    Notation "x >v y" := (succ x y) (at level 70).

    Definition succeq_trans : transitive succeq := @vec_ge_trans dim.

     (** Monotonicity *)
    Section VecMonotonicity.

      Lemma vec_plus_gt_compat_l : forall vl vl' vr vr',
        vec_at0 vl >= vec_at0 vl' -> vec_at0 vr > vec_at0 vr' -> 
        vec_at0 (vl [+] vr) > vec_at0 (vl' [+] vr').

      Proof.
        unfold vec_at0, vector_plus. intros.
        simpl. do 2 rewrite Vmap2_nth. 
        unfold gt. apply plus_le_lt_compat. assumption. assumption.
      Qed.

      Lemma vec_plus_gt_compat_r : forall vl vl' vr vr', 
        vec_at0 vl > vec_at0 vl' -> vec_at0 vr >= vec_at0 vr' -> 
        vec_at0 (vl [+] vr) > vec_at0 (vl' [+] vr').

      Proof.
        unfold vec_at0, vector_plus. intros.
        simpl. do 2 rewrite Vmap2_nth. 
        unfold gt. apply plus_lt_le_compat. assumption. assumption.
      Qed.

      Variable f : matrix dim dim -> vec -> vec.
      Variable f_mon : forall M v1 v2, v1 >=v v2 -> f M v1 >=v f M v2.
      Variables (a b : vec).

      Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 
        (v2 : vector vec n2) n (M : vector (matrix dim dim) n) i_j, a >=v b ->
        add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j)) >=v 
        add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j)).

      Proof.
        induction v1; intros; simpl.
        destruct n; try solve [absurd_arith].
        unfold add_vectors, succeq, vec_ge. simpl. apply Vforall2_intro. 
        intros. unfold vector_plus. do 2 rewrite Vmap2_nth.
        assert (Vnth (f (Vhead M) a) ip >= Vnth (f (Vhead M) b) ip).
        apply (Vforall2_nth ge). apply f_mon. assumption.
        unfold A, Aplus in * . omega.
        destruct n0; try solve [absurd_arith].
        unfold add_vectors, succeq, vec_ge. simpl. apply Vforall2_intro. 
        intros. unfold vector_plus. do 2 rewrite Vmap2_nth.
        unfold ge. apply plus_le_compat_r.
        match goal with |- ?Hl <= ?Hr => fold (ge Hr Hl) end.
        unfold succeq in IHv1. apply (Vforall2_nth ge).
        unfold add_vectors in IHv1. apply IHv1. assumption.
      Qed.

    End VecMonotonicity.

    Lemma monotone_succeq : monotone I succeq.

    Proof.
      intros f i j i_j vi vj a b ab.
      simpl. unfold mi_eval. apply (@vec_plus_ge_compat_r dim).
      apply vec_add_monotone_map2; trivial.
      intros. unfold succeq, vec_ge. apply Vforall2_intro. intros.
      unfold mat_vec_prod. do 2 rewrite Vnth_col_mat. apply mat_mult_mon.
      apply mat_ge_refl. intros x y xp yp.
      do 2 rewrite vec_to_col_mat_spec.
      apply (Vforall2_nth ge). assumption.
    Qed.

    Lemma succ_wf : WF succ.

    Proof.
      apply wf_WF. 
      apply well_founded_lt_compat with (fun v : vec => vec_at0 v).
      intros. destruct H. omega.
    Qed.

    Lemma succ_succeq_compat : absorb succ succeq.

    Proof.
      intros x z xz. destruct xz as [y [xy yz]]. split.
      apply succeq_trans with y. assumption. destruct yz. assumption.
      apply le_gt_trans with (Vnth y dim_pos). unfold vec_at0.
      apply (Vforall2_nth ge). assumption. 
      destruct yz. assumption.
    Qed.

    Lemma succeq_dec : rel_dec succeq.
  
    Proof.
      intros x y. unfold succeq, vec_ge, Vforall2n. apply Vforall2_dec.
      intros m n. destruct (le_lt_dec n m); intuition.
    Defined.

    Lemma succ_dec : rel_dec succ.
  
    Proof.
      intros x y. destruct (succeq_dec x y).
      destruct (le_gt_dec (vec_at0 x) (vec_at0 y)).
      right. intro H. destruct H. intuition.
      left. split; intuition.
      right. intro H. destruct H. intuition.
    Defined.

    (** decidability of order on terms induced by matrix interpretations *)
    Section OrderDecidability.

      Require Export ABterm.

      Notation bterm := (bterm sig).

      (** symbolic computation of term interpretation *)
      Definition mat_matrixInt_prod n M (mi : mint n) : mint n := 
        mkMatrixInt (mat_times_vec M (const mi)) 
        (Vmap (mat_mult M) (args mi)).

      Definition combine_matrices n k (v : vector (vector mat k) n) :=
        Vbuild (fun i ip => add_matrices (Vmap (fun v => Vnth v ip) v)).

      Lemma combine_matrices_nil : forall i,
        combine_matrices Vnil = Vconst (@zero_matrix dim dim) i.

      Proof.
        intros. apply Veq_nth. intros. unfold combine_matrices.
        rewrite Vnth_const. rewrite Vbuild_nth. trivial.
      Qed.

      Lemma combine_matrices_cons : 
        forall k n v (vs : vector (vector mat k) n),
        combine_matrices (Vcons v vs) = 
        Vmap2 (@mat_plus _ _) v (combine_matrices vs).

      Proof.
        intros. apply Veq_nth. intros.
        unfold combine_matrices, add_matrices. simpl.
        rewrite Vmap2_nth. do 2 rewrite Vbuild_nth. 
        rewrite mat_plus_comm. refl.
      Qed.

      Fixpoint mi_of_term k (t : bterm k) {struct t} : mint (S k) :=
        match t with
        | BVar i ip => 
            let zero_int := Vconst (zero_matrix dim dim) (S k) in
            let args_int := Vreplace zero_int (le_lt_S ip) (id_matrix dim) in
              mkMatrixInt (@zero_vec dim) args_int
        | BFun f v => 
            let f_int := trsInt f in
            let args_int := Vmap (@mi_of_term k) v in
            let args_int' := Vmap2 (@mat_matrixInt_prod (S k)) 
              (args f_int) args_int in
            let res_const := add_vectors (Vcons (const f_int) 
              (Vmap (@const dim (S k)) args_int')) in
            let res_args := combine_matrices (Vmap (@args dim (S k)) 
              args_int') in
            mkMatrixInt res_const res_args
        end.

      Require Export ATrs.

      Definition rule_mi r :=
        let mvl := maxvar (lhs r) in
        let mvr := maxvar (rhs r) in
        let m := max mvl mvr in
        let lt := inject_term (le_max_l mvl mvr) in
        let rt := inject_term (le_max_r mvl mvr) in
          (mi_of_term lt, mi_of_term rt).

      (** order characteristic for symbolically computed interpretation and 
          its decidability *)
      Notation mat_ge := (@mat_ge dim dim).
      Notation vec_ge := (@vec_ge dim).

      Definition mint_ge n (l r : mint n) := 
        Vforall2 mat_ge (args l) (args r) /\ vec_ge (const l) (const r).

      Definition mint_gt n (l r : mint n) := 
        mint_ge l r /\ vec_at0 (const l) > vec_at0 (const r).

      Definition term_ord (ord : forall n, relation (mint n)) l r :=
        let (li, ri) := rule_mi (mkRule l r) in
          ord _ li ri.

      Definition term_ge := term_ord mint_ge.
      Definition term_gt := term_ord mint_gt.

      Lemma mint_ge_dec : forall n, rel_dec (@mint_ge n).

      Proof.
        intros n x y. unfold mint_ge.
        destruct (Vforall2_dec (@mat_ge_dec dim dim) (args x) (args y)); 
          intuition.
        destruct (vec_ge_dec (const x) (const y)); intuition.
      Defined.

      Lemma mint_gt_dec : forall n, rel_dec (@mint_gt n).
      
      Proof.
        intros n x y. unfold mint_gt.
        destruct (mint_ge_dec x y); intuition.
        destruct (le_lt_dec (vec_at0 (const x)) (vec_at0 (const y))); 
          intuition.
      Defined.

      Lemma term_ge_dec : rel_dec term_ge.
    
      Proof.
        intros l r. unfold term_ge, term_ord. simpl.
        match goal with |- {mint_ge ?l ?r} + {~mint_ge ?l ?r} => 
          destruct (mint_ge_dec l r); auto
        end.
      Defined.

      Lemma term_gt_dec : rel_dec term_gt.
    
      Proof.
        intros l r. unfold term_gt, term_ord. simpl.
        match goal with |- {mint_gt ?l ?r} + {~mint_gt ?l ?r} => 
          destruct (mint_gt_dec l r); auto
        end.
      Defined.

      Notation IR_succ := (IR I succ).
      Notation IR_succeq := (IR I succeq).

      Definition mint_eval (val : valuation I) k (mi : mint k) :=
        let coefs := Vbuild (fun i (ip : i < k) => val i) in
         add_vectors (Vcons (const mi) (Vmap2 mat_times_vec (args mi) coefs)).

      Lemma mint_eval_split : forall val k (mi : mint k),
        let coefs := Vbuild (fun i (ip : i < k) => val i) in
          mint_eval val mi = const mi [+] 
          add_vectors (Vmap2 mat_times_vec (args mi) coefs).

      Proof.
        intros. unfold mint_eval, add_vectors. simpl. 
        rewrite vector_plus_comm. refl.
      Qed.

      Lemma mint_eval_var_aux : forall M i k (v : vector vec k) (ip : i < k),
        add_vectors (Vmap2 mat_times_vec (Vreplace (Vconst 
          (zero_matrix dim dim) k) ip M) v) =
        col_mat_to_vec (M <*> (vec_to_col_mat (Vnth v ip))).
        
      Proof.
        induction i; intros.
        destruct k. absurd_arith.
        rewrite Vreplace_head. unfold add_vectors. simpl.
        fold (add_vectors (Vmap2 mat_times_vec 
          (Vconst (zero_matrix dim dim) k) (Vtail v))).
        match goal with |- ?V [+] _ = _ => replace V with (@zero_vec dim) end.
        rewrite vector_plus_zero_l.
        replace (Vhead (A:=vec) v) with (Vnth v ip). refl.
        rewrite Vhead_nth. rewrite (lt_unique (lt_O_Sn k) ip). refl.
        symmetry.  apply add_vectors_zero. apply Vforall_nth_intro. intros.
        rewrite Vmap2_nth. rewrite Vnth_const. 
        unfold mat_vec_prod. rewrite zero_matrix_mult_l.
        apply Veq_nth. intros. rewrite Vnth_col_mat.
        unfold zero_matrix, zero_vec. 
        rewrite mat_build_elem. rewrite Vnth_const. refl.
        destruct k. absurd_arith.
        rewrite Vreplace_tail. simpl. rewrite add_vectors_cons.
        unfold mat_vec_prod at 1. rewrite zero_matrix_mult_l.
        match goal with |- ?V [+] _ = _ => replace V with (@zero_vec dim) end.
        rewrite vector_plus_zero_l. rewrite IHi. rewrite Vnth_tail. 
        rewrite (le_unique (lt_n_S (lt_S_n ip)) ip). refl.
        apply Veq_nth. intros. rewrite Vnth_col_mat.
        unfold zero_matrix, zero_vec. 
        rewrite mat_build_elem. rewrite Vnth_const. refl.
      Qed.

      Lemma mint_eval_eq_term_int_var : forall v (val : valuation I) k 
        (t_b : maxvar_le k (Var v)),
        bterm_int val (inject_term t_b) = 
        mint_eval val (mi_of_term (inject_term t_b)).

      Proof.
        intros. rewrite mint_eval_split.
        change (const (mi_of_term (inject_term t_b))) with (zero_vec dim).
        rewrite vector_plus_zero_l.
        change (args (mi_of_term (inject_term t_b))) with (Vreplace (Vconst 
          (zero_matrix dim dim) (S k)) (le_lt_S (maxvar_var t_b)) 
          (id_matrix dim)).
        rewrite mint_eval_var_aux. simpl. 
        rewrite mat_mult_id_l. rewrite col_mat_to_vec_idem.
        rewrite Vbuild_nth. refl. deduce dim_pos. auto. 
      Qed.

      Lemma mint_eval_const : forall val k (c : vec),
        mint_eval (k:=k) val (mkMatrixInt c (combine_matrices Vnil)) = c.

      Proof.
        intros. unfold mint_eval. simpl. autorewrite with arith.
        match goal with |- _ [+] ?V = _ => replace V with (@zero_vec dim) end.
        autorewrite with arith. refl.
        symmetry. apply add_vectors_zero. apply Vforall_nth_intro. intros.
        rewrite Vmap2_nth. rewrite combine_matrices_nil. rewrite Vnth_const.
        unfold mat_vec_prod. autorewrite with arith. 
        apply Veq_nth. intros. rewrite Vnth_col_mat.
        unfold zero_matrix. rewrite mat_build_elem. 
        unfold zero_vec. rewrite Vnth_const. refl.
      Qed.

      Lemma mint_eval_cons : forall n k val c_hd c_tl a_hd 
        (a_tl : vector (vector mat k) n),
        mint_eval val (mkMatrixInt (c_hd [+] c_tl)
          (combine_matrices (Vcons a_hd a_tl))) =
        mint_eval val (mkMatrixInt c_hd a_hd) [+]
        mint_eval val (mkMatrixInt c_tl (combine_matrices a_tl)).

      Proof.
        intros. unfold mint_eval. simpl.
        set (vali := Vbuild (A := vec) (fun i (_ : i < k) => val i)).
        rewrite combine_matrices_cons.
        autorewrite with arith. repeat rewrite <- vector_plus_assoc.
        simpl. autorewrite with arith.
        Vplus_eq. rewrite vector_plus_assoc.
        rewrite (vector_plus_comm (add_vectors (Vmap2 mat_times_vec a_hd 
          vali)) c_tl). rewrite <- vector_plus_assoc.
        Vplus_eq. apply add_vectors_split. intros.
        repeat rewrite Vmap2_nth. apply mat_vec_prod_distr_mat.
      Qed.

      Lemma mint_eval_mult_factor : forall k val M (mi : mint k),
        mint_eval val (mat_matrixInt_prod M mi) =
        mat_times_vec M (mint_eval val mi).

      Proof.
        unfold mint_eval. intros. simpl. autorewrite with arith. 
        rewrite mat_vec_prod_distr_vec. Vplus_eq.
        set (gen := Vbuild (A:=vec) (fun i (_ : i < k) => val i)).
        rewrite (mat_vec_prod_distr_add_vectors M 
          (Vmap2 mat_times_vec (args mi) gen)
          (Vmap2 mat_times_vec (Vmap (mat_mult M) (args mi)) gen)).
        refl. intros. repeat rewrite Vmap2_nth. rewrite Vnth_map.
        unfold mat_vec_prod. rewrite vec_to_col_mat_idem.
        rewrite mat_mult_assoc. refl.
      Qed.

      Lemma mint_eval_eq_bterm_int_fapp : forall k i fi val
        (v : vector (bterm k) i),
        let arg_eval := Vmap2 (@mat_matrixInt_prod (S k)) (args fi) 
          (Vmap (@mi_of_term k) v) in
          mi_eval fi (Vmap (fun t : bterm k => mint_eval val (mi_of_term t)) 
          v) =
          mint_eval val (mkMatrixInt
          (add_vectors (Vcons (const fi) (Vmap (@const dim (S k)) arg_eval)))
          (combine_matrices (Vmap (@args dim (S k)) arg_eval))).

      Proof.
        induction i; intros.
         (* i = 0 *)
        VOtac. simpl.
        unfold mi_eval, add_vectors. simpl. autorewrite with arith.
        symmetry. apply mint_eval_const.
         (* i > 0 *)
        VSntac v. simpl mi_eval.
        rewrite mi_eval_cons. rewrite IHi. simpl.
        rewrite add_vectors_perm.
        rewrite (add_vectors_cons (i := S i) (mat_vec_prod (Vhead (args fi))
                 (const (Vhead (Vmap (mi_of_term (k:=k)) v))))).
        rewrite mint_eval_cons. Vplus_eq.
        rewrite Vmap_tail. refl.
        rewrite H. simpl.
        fold (mat_matrixInt_prod (Vhead (args fi)) (mi_of_term (Vhead v))).
        apply mint_eval_mult_factor.
      Qed.

      Lemma mint_eval_eq_bterm_int : forall val t k (t_b : maxvar_le k t),
        bterm_int val (inject_term t_b) = 
        mint_eval val (mi_of_term (inject_term t_b)).

      Proof.
        intros val t. pattern t. apply term_ind_forall; intros.
        apply mint_eval_eq_term_int_var.
        rewrite inject_term_eq. rewrite bterm_int_fun. unfold bterms_int.
        rewrite (@Vmap_eq _ _ (bterm_int val) 
          (fun (t : bterm k) => mint_eval val (mi_of_term t))).
        simpl. apply mint_eval_eq_bterm_int_fapp.
        apply Vforall_nth_intro. intros.
        rewrite inject_terms_nth. apply (Vforall_nth _ v ip H).
      Qed.

      Lemma mint_eval_eq_term_int : forall t (val : valuation I) k
        (t_b : maxvar_le k t),
        term_int val t = mint_eval val (mi_of_term (inject_term t_b)).

      Proof.
        intros. rewrite <- (term_int_eq_bterm_int val t_b).
        apply mint_eval_eq_bterm_int.
      Qed.

      Lemma mint_eval_equiv : forall l r (val : valuation I),
        let (li, ri) := rule_mi (mkRule l r) in
        let lev := term_int val l in
        let rev := term_int val r in
        let lv := mint_eval val li in
        let rv := mint_eval val ri in
          lv = lev /\ rv = rev.

      Proof.
        intros. simpl. split.
        rewrite (mint_eval_eq_term_int val (le_max_l (maxvar l) (maxvar r))). 
        refl.
        rewrite (mint_eval_eq_term_int val (le_max_r (maxvar l) (maxvar r))). 
        refl.
      Qed.

      Lemma mint_eval_mon_succeq_args : forall k (val : vector vec k) 
        (mi mi' : mint k), mint_ge mi mi' -> 
          add_vectors (Vmap2 mat_times_vec (args mi) val) >=v 
          add_vectors (Vmap2 mat_times_vec (args mi') val).

      Proof.
        destruct mi. generalize val. clear val. induction args0. intros.
        destruct mi'. VOtac. 
        unfold mint_eval, add_vectors. simpl.
        apply (vec_ge_refl (@zero_vec dim)).
        intros. destruct mi'. VSntac args1.
        unfold mint_eval, add_vectors. simpl.
        destruct H. apply (@vec_plus_ge_compat dim).
        apply (IHargs0 (Vtail val) (mkMatrixInt const1 (Vtail (args1)))).
        split. simpl. change args0 with (Vtail (Vcons a args0)). 
        apply Vforall2_tail. assumption. assumption.
        apply mat_vec_prod_ge_compat.
        change a with (Vhead (Vcons a args0)). do 2 rewrite Vhead_nth.
        apply (Vforall2_nth mat_ge). assumption.
        apply (vec_ge_refl (Vhead val)).
      Qed.

      Lemma mint_eval_mon_succeq : forall (val : valuation I) k 
        (mi mi' : mint k), mint_ge mi mi' -> 
        mint_eval val mi >=v mint_eval val mi'.

      Proof.
        intros. unfold mint_eval, add_vectors. simpl.
        apply (@vec_plus_ge_compat dim).
        exact (mint_eval_mon_succeq_args _ H).
        destruct H. assumption.
      Qed.

      Lemma mint_eval_mon_succ : forall (val : valuation I) k 
        (mi mi' : mint k), mint_gt mi mi' -> 
        mint_eval val mi >v mint_eval val mi'.

      Proof.
        intros. destruct H. split.
        apply mint_eval_mon_succeq. assumption.
        unfold mint_eval, add_vectors. simpl.
        apply vec_plus_gt_compat_l. 
        unfold vec_at0. apply (Vforall2_nth ge). 
        exact (mint_eval_mon_succeq_args _ H). assumption.
      Qed.

      Lemma term_ge_incl_succeq : term_ge << IR_succeq.

      Proof.
        intros l r lr v. destruct (mint_eval_equiv l r v). simpl in * .
        rewrite <- H. rewrite <- H0.
        apply mint_eval_mon_succeq. assumption.
      Qed.

      Lemma term_gt_incl_succ : term_gt << IR_succ.

      Proof.
        intros l r lr v. destruct (mint_eval_equiv l r v). simpl in * .
        rewrite <- H. rewrite <- H0.
        apply mint_eval_mon_succ. assumption.
      Qed.

      Definition succ' := term_gt.
      Definition succ'_sub := term_gt_incl_succ.
      Definition succ'_dec := term_gt_dec.

      Definition succeq' := term_ge.
      Definition succeq'_sub := term_ge_incl_succeq.
      Definition succeq'_dec := term_ge_dec.

    End OrderDecidability.

  End MonotoneAlgebra.

  Export MonotoneAlgebra.
  Module MAR := MonotoneAlgebraResults MonotoneAlgebra.
  Export MAR.

End MatrixInt_DP.

Module MatrixInt (MI : TMatrixInt).

  Export MI.

  Module MI_DP := MatrixInt_DP MI.MI.
  Export MI_DP.

  Module ExtendedMonotoneAlgebra <: ExtendedMonotoneAlgebraType.

    Module MA := MI_DP.MonotoneAlgebra.
    Export MA.

    Section VecMonotonicity.
      
      Variable f : matrix dim dim -> vec -> vec.
      Variable f_mon : forall M v1 v2, get_elem M dim_pos dim_pos > 0 ->
        v1 >=v v2 -> vec_at0 v1 > vec_at0 v2 -> 
        vec_at0 (f M v1) > vec_at0 (f M v2).

      Variables (a b : vec).

      Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 
        (v2 : vector vec n2)  n (M : vector (matrix dim dim) n) i_j,  
        Vforall (fun m => get_elem m dim_pos dim_pos > 0) M ->
        a >=v b -> vec_at0 a > vec_at0 b ->
        vec_at0 (add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j))) >
        vec_at0 (add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j))).

      Proof.
        induction v1; intros; simpl.
        destruct n; [absurd_arith | idtac].
        unfold add_vectors, vec_at0, vector_plus. simpl.
        do 2 rewrite Vmap2_nth. 
        unfold gt. apply plus_lt_compat_l.
        unfold vec_at0 in f_mon. apply f_mon; try assumption.
        apply (Vforall_in (x:=Vhead M) H). apply Vin_head.
        destruct n0; [absurd_arith | idtac].
        unfold add_vectors, vec_at0, vector_plus. simpl.
        do 2 rewrite Vmap2_nth.
        unfold gt. apply plus_lt_compat_r.
        match goal with |- ?Hl < ?Hr => fold (gt Hr Hl) end.
        unfold vec_at0, add_vectors in IHv1. 
        apply IHv1; try assumption.
        apply Vforall_incl with (S n0) M. 
        intros. VSntac M. simpl. auto.
        assumption.
      Qed.

    End VecMonotonicity.

    Lemma monotone_succ : monotone I succ.

    Proof.
      intros f i j i_j vi vj a b ab. split.
      apply monotone_succeq. destruct ab. assumption.
      simpl. unfold mi_eval. apply vec_plus_gt_compat_r.
      apply vec_add_monotone_map2; try solve [destruct ab; assumption].
      intros. unfold vec_at0. unfold mat_vec_prod. 
      do 2 rewrite Vnth_col_mat.
      do 2 rewrite mat_mult_spec. apply dot_product_mon_r with 0 dim_pos.
      unfold vec_ge. apply Vforall2_intro. auto.
      unfold vec_ge. apply Vforall2_intro. intros.
      do 2 rewrite get_col_col_mat. destruct ab.
      apply (Vforall2_nth ge). assumption.
      assumption.
      do 2 rewrite get_col_col_mat. assumption.
      apply matrixInt_monotone.
      auto with arith.
    Qed.

  End ExtendedMonotoneAlgebra.

  Export ExtendedMonotoneAlgebra.
  Module EMAR := ExtendedMonotoneAlgebraResults ExtendedMonotoneAlgebra.
  Export EMAR.

End MatrixInt.
