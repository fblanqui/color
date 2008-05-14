(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Export Matrix.
Require Export AMonAlg.

Section MatrixLinearFunction.

  Variables (A : Set) (matrix : nat -> nat -> Set) (dim : nat).

   (* function interpretation : one [dim]x[dim] matrix per argument and
      one vector of dimension [dim] for a constant factor *)
  Record matrixInt (dim : nat) (argCnt : nat) : Type := mkMatrixInt {
    const : vector A dim;
    args : vector (matrix dim dim) argCnt
  }.

End MatrixLinearFunction.

Module Type MatrixMethodConf.

  Declare Module OSRT : OrdSemiRingType.
  Module M := Matrix OSRT.
  Export OSRT.
  Export M.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : dim > 0.

  Notation vec := (vec dim).
  Notation matrixInt := (matrixInt A matrix).
  Notation mint := (matrixInt dim).

  Parameter trsInt : forall f : sig, mint (arity f).
  Parameter vec_invariant : vec -> Prop.
  Parameter inv_id_matrix : 
    vec_invariant (Vreplace (Vconst A0 dim) dim_pos A1).

End MatrixMethodConf.

Module MatrixBasedInt (MC : MatrixMethodConf).

  Export MC.

  Section MBI.

  Notation mat := (matrix dim dim).
  Implicit Arguments mkMatrixInt [A matrix dim argCnt].

  Definition vec_at0 (v : vec) := Vnth v dim_pos.
  Definition dom := { v : vec | vec_invariant v }.

  Definition dom2vec (d : dom) : vec := proj1_sig d.

  Definition add_matrices i m n (v : vector (matrix m n) i) := 
    Vfold_left (@mat_plus m n) (zero_matrix m n) v.

  Notation mat_times_vec := (@mat_vec_prod dim dim).

  Definition mi_eval_aux n (mi : matrixInt dim n) (v : vector vec n) : vec :=
    add_vectors (Vmap2 mat_times_vec (args mi) v) [+] const mi.

  Variable mi_eval_ok : forall f v,
    vec_invariant (mi_eval_aux (trsInt f) (Vmap dom2vec v)).

  Definition mi_eval f (v : vector dom (arity f)) : dom :=
    exist (fun v => vec_invariant v) (mi_eval_aux (trsInt f) (Vmap dom2vec v))
    (mi_eval_ok f v).

  Lemma mi_eval_cons : forall n (mi : matrixInt dim (S n)) v vs,
    mi_eval_aux mi (Vcons v vs) = 
      mat_times_vec (Vhead (args mi)) v [+] 
      mi_eval_aux (mkMatrixInt (const mi) (Vtail (args mi))) vs.

  Proof.
    induction n; intros; unfold mi_eval, mi_eval_aux.
    VOtac. simpl. rewrite vector_plus_assoc. 
    simpl. autorewrite with arith. refl.
    VSntac vs. simpl. rewrite vector_plus_assoc. 
    simpl. autorewrite with arith. refl.
  Qed.
  
  Definition dom_zero : dom.

  Proof.
    exists (Vreplace (Vconst A0 dim) dim_pos A1).
    apply inv_id_matrix.
  Defined.

  Definition I := @mkInterpretation sig dom dom_zero mi_eval.
  
  Variable succ : relation dom.
  Notation "x >v y" := (succ x y) (at level 70).

  Definition succeq (x y : dom) := (dom2vec x) >=v (dom2vec y).

  Lemma succeq_trans : transitive succeq.
      
  Proof.
    intros x y z xy yz. unfold succeq.
    apply (vec_ge_trans (dom2vec x) (dom2vec y)); assumption.
  Qed.

  (** Monotonicity *)
  Section VecMonotonicity.
    
    Variable f : matrix dim dim -> vec -> vec.
    Variable f_mon : forall M v1 v2, v1 >=v v2 -> f M v1 >=v f M v2.
    Variables (a b : vec).

    Lemma vec_add_weak_monotone_map2 : forall n1 (v1 : vector vec n1) n2 
      (v2 : vector vec n2) n (M : vector (matrix dim dim) n) i_j, a >=v b ->
      add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j)) >=v 
      add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j)).

    Proof.
      induction v1; intros; simpl.
      destruct n; try solve [absurd_arith].
      unfold add_vectors, succeq, vec_ge. simpl. apply Vforall2_intro. 
      intros. unfold vector_plus. do 2 rewrite Vmap2_nth.
      assert (Vnth (f (Vhead M) a) ip >>= Vnth (f (Vhead M) b) ip).
      apply (Vforall2_nth ge). apply f_mon. assumption.
      apply plus_ge_compat. apply ge_refl. assumption.
      destruct n0; try solve [absurd_arith].
      unfold add_vectors, succeq, vec_ge. simpl. apply Vforall2_intro. 
      intros. unfold vector_plus. do 2 rewrite Vmap2_nth.
      apply plus_ge_compat. 
      apply (Vforall2_nth ge). unfold add_vectors in IHv1. apply IHv1.
      assumption. apply ge_refl.
    Qed.
  
  End VecMonotonicity.

  Lemma monotone_succeq : monotone I succeq.

  Proof.
    intros f i j i_j vi vj a b ab.
    simpl. unfold mi_eval, mi_eval_aux, succeq. simpl. 
    apply (@vec_plus_ge_compat_r dim).
    do 2 rewrite Vmap_cast. do 2 rewrite Vmap_app. simpl.
    apply vec_add_weak_monotone_map2; trivial.
    intros. unfold succeq, vec_ge. apply Vforall2_intro. intros.
    unfold mat_vec_prod. do 2 rewrite Vnth_col_mat. apply mat_mult_mon.
    apply mat_ge_refl. intros x y xp yp.
    do 2 rewrite vec_to_col_mat_spec.
    apply (Vforall2_nth ge). assumption.
  Qed.

  Lemma succeq_dec : rel_dec succeq.
  
  Proof.
    intros x y. unfold succeq, vec_ge, Vforall2n. apply Vforall2_dec.
    intros m n. apply ge_dec.
  Defined.

  (** decidability of order on terms induced by matrix interpretations *)
  Section OrderDecidability.

    Require Import ABterm.

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
            (Vmap (@const A matrix dim (S k)) args_int')) in
          let res_args := combine_matrices (Vmap (@args A matrix dim (S k)) 
            args_int') in
          mkMatrixInt res_const res_args
      end.

    Require Import ATrs.

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

    Definition term_ord (ord : forall n, relation (mint n)) l r :=
      let (li, ri) := rule_mi (mkRule l r) in
        ord _ li ri.

    Variable mint_gt : forall n (l r : mint n), Prop.
    Variable mint_gt_dec : forall n, rel_dec (@mint_gt n).

    Definition term_ge := term_ord mint_ge.
    Definition term_gt := term_ord mint_gt.

    Lemma mint_ge_dec : forall n, rel_dec (@mint_ge n).

    Proof.
      intros n x y. unfold mint_ge.
      destruct (Vforall2_dec (@mat_ge_dec dim dim) (args x) (args y)); 
        intuition.
      destruct (vec_ge_dec (const x) (const y)); intuition.
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

    Definition mint_eval (val : valuation I) k (mi : mint k) : vec :=
      let coefs := Vbuild (fun i (ip : i < k) => dom2vec (val i)) in
        add_vectors (Vcons (const mi) (Vmap2 mat_times_vec (args mi) coefs)).

    Lemma mint_eval_split : forall val k (mi : mint k),
      let coefs := Vbuild (fun i (ip : i < k) => dom2vec (val i)) in
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
      unfold add_vectors. simpl.
      fold (add_vectors (Vmap2 mat_times_vec 
        (Vconst (zero_matrix dim dim) k) (Vtail v))).
      match goal with |- ?V [+] _ = _ => replace V with (@zero_vec dim) end.
      rewrite vector_plus_zero_l.
      replace (Vhead v) with (Vnth v ip). refl.
      rewrite Vhead_nth. rewrite (lt_unique (lt_O_Sn k) ip). refl.
      symmetry. apply add_vectors_zero. apply Vforall_nth_intro. intros.
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
      dom2vec (bterm_int val (inject_term t_b)) = 
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
      rewrite Vbuild_nth. refl. ded dim_pos. auto. 
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
      set (vali := Vbuild (A := vec) (fun i (_ : i < k) => dom2vec (val i))).
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
      set (gen := Vbuild (A:=vec) (fun i (_ : i < k) => dom2vec (val i))).
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
        mi_eval_aux fi (Vmap 
            (fun t : bterm k => mint_eval val (mi_of_term t)) v) =
        mint_eval val (mkMatrixInt
          (add_vectors (Vcons (const fi) (Vmap 
            (@const A matrix dim (S k)) arg_eval)))
          (combine_matrices (Vmap (@args A matrix dim (S k)) arg_eval))).

    Proof.
      induction i; intros.
       (* i = 0 *)
      VOtac. simpl.
      unfold mi_eval_aux, add_vectors. simpl. autorewrite with arith.
      symmetry. apply mint_eval_const.
       (* i > 0 *)
      VSntac v. simpl mi_eval_aux.
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

    Lemma mint_eval_eq_bterm_int : forall (val : valuation I) t k 
      (t_b : maxvar_le k t),
      dom2vec (bterm_int val (inject_term t_b)) =
      mint_eval val (mi_of_term (inject_term t_b)).

    Proof.
      intros val t. pattern t. apply term_ind_forall; intros.
      apply mint_eval_eq_term_int_var.
      rewrite inject_term_eq. rewrite bterm_int_fun. unfold bterms_int.
      unfold fint. simpl dom2vec.
      rewrite Vmap_map.
      rewrite (@Vmap_eq _ _ (fun x => dom2vec (bterm_int val x)) 
        (fun (t : bterm k) => mint_eval val (mi_of_term t))).
      simpl. apply mint_eval_eq_bterm_int_fapp.
      apply Vforall_nth_intro. intros.
      rewrite inject_terms_nth. apply (Vforall_nth _ v ip H).
    Qed.

    Lemma mint_eval_eq_term_int : forall t (val : valuation I) k
      (t_b : maxvar_le k t),
      dom2vec (term_int val t) = 
      mint_eval val (mi_of_term (inject_term t_b)).

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
        lv = dom2vec lev /\ rv = dom2vec rev.

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

    Lemma term_ge_incl_succeq : term_ge << IR_succeq.

    Proof.
      intros l r lr v. destruct (mint_eval_equiv l r v). simpl in * .
      unfold succeq. rewrite <- H. rewrite <- H0.
      apply mint_eval_mon_succeq. assumption.
    Qed.

    Definition succeq' := term_ge.
    Definition succeq'_sub := term_ge_incl_succeq.
    Definition succeq'_dec := term_ge_dec.

  End OrderDecidability.

  End MBI.

End MatrixBasedInt.
