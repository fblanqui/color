(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Johannes Waldmann, 2010-04
*)

Set Implicit Arguments.

Require Import AMonAlg Matrix OrdSemiRing VecUtil SN RelUtil LogicUtil Setoid
  VecEq VecOrd AMatrixBasedInt.

(** Module type for proving termination with matrix interpretations *)
Module Type TTropicalBasedInt.

  Declare Module Export OSR : OrdSemiRingType.
  Module Export M := Matrix OSR.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : dim > 0.
  Parameter trsInt : forall f : sig, matrixInt A matrix dim (arity f).

End TTropicalBasedInt.

Module TropicalBasedInt (TBI : TTropicalBasedInt).

  Export TBI.

  Module Conf <: MatrixMethodConf.

    Module Export M := TBI.M.
    Module Export OSRT := TBI.OSR.

    Definition sig := sig.
    Definition dim := dim.
    Definition dim_pos := dim_pos.

    Definition trsInt := trsInt.
    Notation vec := (vec dim).
    Definition vec_at0 (v : vec) := Vnth v dim_pos.

     (* TODO: for refactoring we should change this condition to a
        predicate on [vec_at0], which would be general enough to 
        cover all three: arctic/arctic-below-zero/tropical *)
    Definition vec_invariant (v : vec) := A0 >> vec_at0 v.

    Variable A0_gt_A1 : A0 >> A1.

    Lemma inv_id_matrix : 
      vec_invariant (Vreplace (Vconst A0 dim) dim_pos A1).

    Proof.
      unfold vec_invariant, vec_at0. rewrite Vnth_replace. exact A0_gt_A1.
    Qed.

  End Conf.

  Module Export MBI := MatrixBasedInt Conf.

  Section ABI.

    Notation matrixInt := (matrixInt A matrix).
    Notation mint := (matrixInt dim).
    Notation mat := (matrix dim dim).

    Definition Sig := sig.
    Notation PlusInf := A0.

    Variable A0_min : forall x, x >>= PlusInf.
    Variable ge_gt_eq : forall x y, x >>= y -> x >> y \/ x =A= y.

    Definition gtx x y := x >> y \/ (x =A= PlusInf /\ y =A= PlusInf).
    Notation "x >_0 y" := (gtx x y) (at level 70).

    Add Morphism gtx with signature eqA ==> eqA ==> iff as gtx_mor.

    Proof.
      unfold gtx. intuition. left. rewrite <- H. rewrite <- H0. hyp. right.
      split. trans x. sym. hyp. hyp. trans x0. sym.
      hyp. hyp.
      left. rewrite H. rewrite H0. hyp. right. split.
      trans y; hyp. trans y0; hyp.
    Qed.

    Lemma gtx_trans : transitive gtx.

    Proof.
      unfold gtx. intros x y z. intuition.
      left. apply OSR.gt_trans with y; hyp.
      rewrite H2. rewrite H0 in H1. auto.
      rewrite H. rewrite H2 in H1. auto.
    Qed.

    Definition succ_vec := vec_prod gtx.
    Definition succ (x y : dom) := succ_vec (dom2vec x) (dom2vec y).
    Notation "x >v y" := (succ x y) (at level 70).

    Lemma trans_succ : transitive succ.

    Proof.
      unfold succ. apply Rof_trans with (f:=dom2vec). unfold succ_vec.
      apply vec_prod_trans. apply gtx_trans.      
    Qed.

    Lemma ge_gtx_compat : forall x y z, x >>= y -> y >_0 z -> x >_0 z.

    Proof.
      unfold gtx. intuition. left. apply ge_gt_compat with y; hyp.
      rewrite H2. rewrite H0 in H. destruct (ge_gt_eq H); intuition.
    Qed.

    Variable succ_wf : WF succ.

    Variable gtx_plus_compat : forall m m' n n',
      m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.

    Variable gtx_mult_compat : forall m m' n n',
      m >_0 m' -> n >>= n' -> m * n >_0 m' * n'.

    Lemma succ_succeq_compat : absorb succ succeq.

    Proof.
      intros x z xz. destruct xz as [y [xy yz] ].
      unfold succ, succ_vec. apply Vforall2n_intro. intros.
      apply ge_gtx_compat with (Vnth (dom2vec y) ip).
      apply Vforall2n_nth. hyp.
      apply Vforall2n_nth. hyp.
    Qed.

    Lemma gtx_dec : rel_dec gtx.

    Proof.
      intros x y. destruct (gt_dec x y).
      left. left. hyp.
      destruct (eqA_dec x PlusInf).
      destruct (eqA_dec y PlusInf).
      left. right. auto.
      right. unfold gtx. intuition.
      right. unfold gtx. intuition.
    Defined.

    Lemma succ_dec : rel_dec succ.
  
    Proof.
      intros x y. unfold succ.
      apply (Vforall2n_dec gtx_dec (dom2vec x) (dom2vec y)).
    Defined.

    Variable mi_eval_ok : forall f v,
      vec_invariant (mi_eval_aux (trsInt f) (Vmap dom2vec v)).

    Notation I := (MBI.I mi_eval_ok).
    Notation IR_succ := (IR I succ).

    Definition mat_gt := mat_forall2 gtx (m:=dim) (n:=dim).
    Definition vec_gt := Vforall2n gtx (n:=dim).

    Definition mint_gt n (l r : mint n) := 
      Vforall2n mat_gt (args l) (args r) /\ vec_gt (const l) (const r).

    Definition term_gt := MBI.term_gt mint_gt.

    Lemma mat_gt_dec : rel_dec mat_gt.

    Proof.
      unfold mat_gt. apply mat_forall2_dec. exact gtx_dec.
    Defined.

    Lemma vec_gt_dec : rel_dec vec_gt.
      
    Proof.
      unfold vec_gt. apply Vforall2n_dec. exact gtx_dec.
    Defined.

    Lemma mint_gt_dec : forall n, rel_dec (@mint_gt n).
      
    Proof.
      intros n x y. unfold mint_gt.
      destruct (Vforall2n_dec mat_gt_dec (args x) (args y)); 
        intuition.
      destruct (vec_gt_dec (const x) (const y)); intuition.      
    Defined.

    Lemma Vfold_left_gtx_compat : forall n (v v' : vector A n),
      (forall i (ip: i < n), Vnth v ip >_0 Vnth v' ip) ->
      Vfold_left Aplus A0 v >_0 Vfold_left Aplus A0 v'.

    Proof.
      induction v; simpl; intros.
      VOtac. simpl. right. intuition.
      VSntac v'. simpl. apply gtx_plus_compat.
      apply IHv. intros. 
      apply Vforall2n_nth. change v with (Vtail (Vcons h v)). 
      apply Vforall2n_tail. apply Vforall2n_intro. hyp.
      change h with (Vhead (Vcons h v)). do 2 rewrite Vhead_nth.
      apply (H _ (Lt.lt_O_Sn n)).
    Qed.

    Section Matrix.

      Variables (m n p : nat) (M M' : matrix m n) (N N' : matrix n p).

      Notation vge := vec_ge.
      Notation vgt := (Vforall2n gtx).
      Notation mge := mat_ge.
      Notation mgt := (mat_forall2 gtx).

      Lemma arctic_dot_product_mon : forall i (v v' w w' : vector A i), 
        vgt v v' -> vge w w' -> dot_product v w >_0 dot_product v' w'.

      Proof.
        unfold dot_product. induction v; intros; simpl.
        right. intuition.
        apply gtx_plus_compat.
        apply IHv.
        change v with (Vtail (Vcons h v)). apply Vforall2n_tail. hyp.
        apply vec_prod_tail. hyp.
        apply gtx_mult_compat. change h with (Vhead (Vcons h v)). 
        do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
        do 2 rewrite Vhead_nth. apply Vforall2n_nth. hyp.
      Qed.

      Lemma mat_arctic_mult_mon : mgt M M' -> mge N N' -> 
        mgt (M <*> N) (M' <*> N').

      Proof.
        intros. unfold mat_forall2. intros.
        do 2 rewrite mat_mult_spec. apply arctic_dot_product_mon.
        apply Vforall2n_intro. intros. 
        exact (H i i0 ip ip0).
        unfold vge. apply Vforall2n_intro. intros.
        do 2 rewrite <- get_elem_swap. exact (H0 i0 j ip0 jp).
      Qed.

    End Matrix.

    Lemma mat_vec_prod_gt_compat : forall (M M' : mat) m m', 
      mat_gt M M' -> m >=v m' -> 
      vec_gt (mat_vec_prod M m) (mat_vec_prod M' m').

    Proof.
      intros. unfold mat_vec_prod, vec_gt. apply Vforall2n_intro. 
      intros. do 2 rewrite Vnth_col_mat. 
      apply mat_arctic_mult_mon. hyp.
      intros k l pk pl. do 2 rewrite vec_to_col_mat_spec.
      apply Vforall2n_nth. hyp.
    Qed.

    Lemma mint_eval_mon_succ : forall (val : valuation I) k 
      (mi mi' : mint k), mint_gt mi mi' -> 
      succ_vec (mint_eval val mi) (mint_eval val mi').

    Proof.
      intros. unfold succ_vec. apply Vforall2n_intro. intros. destruct H.
      eapply gtx_mor. apply (Vnth_mor eqA); rewrite mint_eval_split; refl.
      apply (Vnth_mor eqA). rewrite mint_eval_split. refl.
      do 2 rewrite vector_plus_nth.
      apply gtx_plus_compat. 
      apply Vforall2n_nth. hyp.
      do 2 rewrite add_vectors_nth.
      apply Vfold_left_gtx_compat. intros.
      do 2 rewrite Vnth_map. do 2 rewrite Vnth_map2.
      set (eval := Vnth (Vbuild (fun i (_ : i < k) => val i)) ip0).
      apply Vforall2n_nth. apply mat_vec_prod_gt_compat.
      apply Vforall2n_nth. hyp.
      apply vec_ge_refl.
    Qed.

    Lemma term_gt_incl_succ : term_gt << IR_succ.

    Proof.
      intros l r lr v. destruct (mint_eval_equiv l r v). simpl in *.
      unfold succ. unfold succ_vec. symmetry in H. symmetry in H0.
      rewrite (Vforall2n_mor sid_theoryA gtx_mor H H0).
      apply mint_eval_mon_succ. hyp.
    Qed.

    Definition succ' := term_gt.
    Definition succ'_sub := term_gt_incl_succ.
    Definition succ'_dec := term_gt_dec mint_gt mint_gt_dec.

  End ABI.

End TropicalBasedInt.
