(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

From CoLoR Require Import AMonAlg Matrix OrdSemiRing VecUtil SN RelUtil
     LogicUtil AMatrixBasedInt.
From Coq Require Import Setoid Morphisms.

(** Module type for proving termination with matrix interpretations *)
Module Type TArcticBasedInt.

  Declare Module Export OSR : OrdSemiRingType.
  Module Export M := Matrix OSR.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : dim > 0.
  Parameter trsInt : forall f : sig, matrixInt A matrix dim (arity f).

End TArcticBasedInt.

Module ArcticBasedInt (ABI : TArcticBasedInt).

  Export ABI.

  Module Conf <: MatrixMethodConf.

    Module Export M := ABI.M.
    Module Export OSRT := ABI.OSR.

    Definition sig := sig.
    Definition dim := dim.
    Definition dim_pos := dim_pos.

    Definition trsInt := trsInt.
    Notation vec := (vec dim).
    Definition vec_at0 (v : vec) := Vnth v dim_pos.

    Definition vec_invariant (v : vec) := vec_at0 v >>= A1.

    Lemma inv_id_matrix : 
      vec_invariant (Vreplace (Vconst A0 dim) dim_pos A1).

    Proof.
      unfold vec_invariant, vec_at0. rewrite Vnth_replace. apply ge_refl.
    Qed.

  End Conf.

  Module Export MBI := MatrixBasedInt Conf.

  Section ABI.

    Notation matrixInt := (matrixInt A matrix).
    Notation mint := (matrixInt dim).
    Notation mat := (matrix dim dim).

    Definition Sig := sig.
    Notation MinusInf := A0.

    Variable A0_min : forall x, x >>= MinusInf.
    Variable ge_gt_eq : forall x y, x >>= y -> x >> y \/ x =A= y.

    Definition gtx x y := x >> y \/ (x =A= MinusInf /\ y =A= MinusInf).
    Notation "x >_0 y" := (gtx x y) (at level 70).

    Global Instance gtx_mor : Proper (eqA ==> eqA ==> iff) gtx.

    Proof.
      intros x x' xx' y y' yy'. unfold gtx. intuition.
      left. rewrite <- xx', <- yy'. hyp. right.
      split. trans x; hyp. trans y; hyp.
      left. rewrite xx', yy'. hyp. right. split.
      trans x'; hyp. trans y'; hyp.
    Qed.

    #[global] Instance gtx_trans : Transitive gtx.

    Proof.
      unfold gtx. intros x y z. intuition.
      left. apply OSR.gt_trans with y; hyp.
      rewrite H2. rewrite H0 in H1. auto.
      rewrite H. rewrite H2 in H1. auto.
    Qed.

    Definition succ_vec {n} := Vforall2 gtx (n:=n).
    Definition succ (x y : dom) := succ_vec (dom2vec x) (dom2vec y).
    Notation "x >v y" := (succ x y) (at level 70).

    #[global] Instance trans_succ : Transitive succ.

    Proof.
      change (Transitive (Rof succ_vec dom2vec)). apply Rof_trans.
      apply Vforall2_trans. class.
    Qed.

    (*FIXME: Proper*)
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

    Lemma succ_succeq_compat : absorbs_left succ succeq.

    Proof.
      intros x z xz. destruct xz as [y [xy yz] ].
      unfold succ, succ_vec. apply Vforall2_intro_nth. intros.
      apply ge_gtx_compat with (Vnth (dom2vec y) ip).
      apply Vforall2_elim_nth. hyp.
      apply Vforall2_elim_nth. hyp.
    Qed.

    Lemma gtx_dec : rel_dec gtx.

    Proof.
      intros x y. destruct (gt_dec x y).
      left. left. hyp.
      destruct (eqA_dec x MinusInf).
      destruct (eqA_dec y MinusInf).
      left. right. auto.
      right. unfold gtx. intuition.
      right. unfold gtx. intuition.
    Defined.

    Lemma succ_dec : rel_dec succ.
  
    Proof.
      intros x y. unfold succ.
      apply (Vforall2_dec gtx_dec (dom2vec x) (dom2vec y)).
    Defined.

    Variable mi_eval_ok : forall f v,
      vec_invariant (mi_eval_aux (trsInt f) (Vmap dom2vec v)).

    Notation I := (MBI.I mi_eval_ok).
    Notation IR_succ := (IR I succ).

    Definition mat_gt := mat_forall2 gtx (m:=dim) (n:=dim).
    Definition vec_gt := Vforall2 gtx (n:=dim).

    Definition mint_gt n (l r : mint n) := 
      Vforall2 mat_gt (args l) (args r) /\ vec_gt (const l) (const r).

    Definition term_gt := MBI.term_gt mint_gt.

    Lemma mat_gt_dec : rel_dec mat_gt.

    Proof.
      unfold mat_gt. apply mat_forall2_dec. exact gtx_dec.
    Defined.

    Lemma vec_gt_dec : rel_dec vec_gt.
      
    Proof.
      unfold vec_gt, rel_dec. apply Vforall2_dec. exact gtx_dec.
    Defined.

    Lemma mint_gt_dec : forall n, rel_dec (@mint_gt n).
      
    Proof.
      intros n x y. unfold mint_gt.
      destruct (Vforall2_dec mat_gt_dec (args x) (args y)); 
        intuition.
      destruct (vec_gt_dec (const x) (const y)); intuition.      
    Defined.

    Lemma Vfold_left_rev_gtx_compat : forall n (v v' : vector A n),
      (forall i (ip: i < n), Vnth v ip >_0 Vnth v' ip) ->
      Vfold_left_rev Aplus A0 v >_0 Vfold_left_rev Aplus A0 v'.

    Proof.
      induction v; simpl; intros.
      VOtac. simpl. right. intuition.
      VSntac v'. simpl. apply gtx_plus_compat.
      apply IHv. intros. 
      apply Vforall2_elim_nth. change v with (Vtail (Vcons h v)). 
      apply Vforall2_tail. apply Vforall2_intro_nth. hyp.
      change h with (Vhead (Vcons h v)). rewrite !Vhead_nth.
      apply (H _ (Lt.lt_O_Sn n)).
    Qed.

    Section Matrix.

      Variables (m n p : nat) (M M' : matrix m n) (N N' : matrix n p).

      Notation vge := (Vforall2 ge).
      Notation vgt := (Vforall2 gtx).
      Notation mge := mat_ge.
      Notation mgt := (mat_forall2 gtx).

      Lemma arctic_dot_product_mon : forall i (v v' w w' : vector A i), 
        vgt v v' -> vge w w' -> dot_product v w >_0 dot_product v' w'.

      Proof.
        unfold dot_product. induction v; intros; simpl.
        right. intuition.
        apply gtx_plus_compat.
        apply IHv.
        change v with (Vtail (Vcons h v)). apply Vforall2_tail. hyp.
        apply Vforall2_tail. hyp.
        apply gtx_mult_compat. change h with (Vhead (Vcons h v)). 
        rewrite !Vhead_nth. apply Vforall2_elim_nth. hyp.
        rewrite !Vhead_nth. apply Vforall2_elim_nth. hyp.
      Qed.

      Lemma mat_arctic_mult_mon :
        mgt M M' -> mge N N' -> mgt (M <*> N) (M' <*> N').

      Proof.
        intros. unfold mat_forall2. intros.
        rewrite !mat_mult_spec. apply arctic_dot_product_mon.
        apply Vforall2_intro_nth. intros. 
        exact (H i i0 ip ip0).
        apply Vforall2_intro_nth. intros.
        rewrite <- !get_elem_swap. exact (H0 i0 j ip0 jp).
      Qed.

    End Matrix.

    Lemma mat_vec_prod_gt_compat : forall (M M' : mat) m m', 
      mat_gt M M' -> m >=v m' -> 
      vec_gt (mat_vec_prod M m) (mat_vec_prod M' m').

    Proof.
      intros. unfold mat_vec_prod, vec_gt. apply Vforall2_intro_nth. 
      intros. rewrite !Vnth_col_mat. 
      apply mat_arctic_mult_mon. hyp.
      intros k l pk pl. rewrite !vec_to_col_mat_spec.
      apply Vforall2_elim_nth. hyp.
    Qed.

    Lemma mint_eval_mon_succ : forall (val : valuation I) k 
      (mi mi' : mint k), mint_gt mi mi' -> 
      succ_vec (mint_eval val mi) (mint_eval val mi').

    Proof.
      intros. unfold succ_vec. apply Vforall2_intro_nth. intros. destruct H.
      eapply gtx_mor. eapply Vforall2_elim_nth; rewrite mint_eval_split; refl.
      eapply Vforall2_elim_nth. rewrite mint_eval_split. refl.
      rewrite !vector_plus_nth.
      apply gtx_plus_compat. 
      apply Vforall2_elim_nth. hyp.
      rewrite !add_vectors_nth.
      apply Vfold_left_rev_gtx_compat. intros.
      rewrite !Vnth_map, !Vnth_map2.
      set (eval := Vnth (Vbuild (fun i (_ : i < k) => val i)) ip0).
      apply Vforall2_elim_nth. apply mat_vec_prod_gt_compat.
      apply Vforall2_elim_nth. hyp. refl.
    Qed.

    Lemma term_gt_incl_succ : term_gt << IR_succ.

    Proof.
      intros l r lr v. destruct (mint_eval_equiv l r v). simpl in *.
      unfold succ. unfold succ_vec. symmetry in H. symmetry in H0.
      rewrite (Vforall2_aux_Proper gtx_mor _ _ H _ _ H0).
      apply mint_eval_mon_succ. hyp.
    Qed.

    Definition succ' := term_gt.
    Definition succ'_sub := term_gt_incl_succ.
    Definition succ'_dec := term_gt_dec mint_gt mint_gt_dec.

  End ABI.

End ArcticBasedInt.
