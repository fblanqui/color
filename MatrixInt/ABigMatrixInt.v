(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-04-29 (bigN)
- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Hans Zantema, 2007-03-22

Termination criterion based on matrix interpretations.

References:
-  J. Endrullis, J. Waldmann and H. Zantema, "Matrix Interpretations for 
   Proving Termination of Term Rewriting", Proceedings of the 3rd 
   International Joint Conference (IJCAR 2006), 2006.
*)

Set Implicit Arguments.

From Coq Require Import Setoid.
From CoLoR Require Import LogicUtil Matrix OrdSemiRing VecUtil AMonAlg
     SN RelUtil AWFMInterpretation NatUtil BigNUtil AMatrixBasedInt.
Import BigNMatrix.

(** Module type for proving termination with matrix interpretations *)
Module Type TMatrixInt.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : (dim > 0)%nat.
  Parameter trsInt : forall f : sig, matrixInt bigN matrix dim (arity f).

End TMatrixInt.

Definition matrixInt := @matrixInt A matrix.
Definition mkMatrixInt := @mkMatrixInt A matrix.

Module MatrixInt (Export MI : TMatrixInt).

  Module Conf <: MatrixMethodConf.

    Module Export OSRT := BigNOrdSemiRingT.
    Module Export M := Matrix OSRT.

    Definition sig := sig.
    Definition dim := dim.
    Definition dim_pos := dim_pos.

    Definition trsInt := trsInt.
    Notation vec := (vec dim).
    Definition vec_invariant (v : vec) := True.

    Lemma inv_id_matrix : 
      vec_invariant (Vreplace (Vconst A0 dim) dim_pos A1).

    Proof.
      compute. trivial.
    Qed.

  End Conf.

  Module MBI := MatrixBasedInt Conf.

  (** Monotone algebra instantiated to matrices *)
  Module MonotoneAlgebra <: MonotoneAlgebraType.

    Export MBI.

    Notation mint := (matrixInt dim).

    Lemma mi_eval_ok : forall f v,
      vec_invariant (mi_eval_aux (trsInt f) (Vmap dom2vec v)).

    Proof.
      compute. trivial.
    Qed.

    Definition I := MBI.I mi_eval_ok.

    Definition succeq := MBI.succeq.
    Definition refl_succeq := MBI.refl_succeq.
    Definition monotone_succeq := @MBI.monotone_succeq mi_eval_ok.
    Definition trans_succeq := MBI.trans_succeq.

    Definition succeq' := MBI.succeq'.
    Definition succeq'_sub := @MBI.succeq'_sub mi_eval_ok.
    Definition succeq'_dec := MBI.succeq'_dec.

    Definition Sig := sig.
    
    Definition succ_vec v1 v2 := v1 >=v v2 /\ vec_at0 v1 > vec_at0 v2.
    Definition succ := Rof succ_vec dom2vec.

    Lemma trans_succ : transitive succ.

    Proof.
      apply Rof_trans. unfold succ_vec.
      intros v1 v2 v3 h12 h23. intuition. trans v2; hyp.
      apply gt_trans with (vec_at0 v2); hyp.
    Qed.

    Lemma succ_wf : WF succ.

    Proof.
      apply WF_incl with (Rof gt (fun v : dom => vec_at0 (dom2vec v))).
      unfold succ, succ_vec, Rof, gt. intros x y. intuition.
      apply WF_inverse. apply gt_WF.
    Qed.

    Lemma succ_succeq_compat : absorbs_left succ succeq.

    Proof.
      intros x z xz. destruct xz as [y [xy yz]]. split.
      apply trans_succeq with y. hyp. destruct yz. hyp.
      apply ge_gt_compat with (Vnth (dom2vec y) dim_pos). unfold MBI.vec_at0.
      apply Vforall2_elim_nth. hyp. 
      destruct yz. hyp.
    Qed.

    Lemma succ_dec : rel_dec succ.
  
    Proof.
      apply intersection_dec. apply succeq_dec. intros x y. apply gt_dec.
    Defined.

    Notation IR_succ := (IR I succ).

    Definition mint_gt n (l r : mint n) := 
      mint_ge l r /\ vec_at0 (const l) > vec_at0 (const r).

    Definition term_gt := MBI.term_gt mint_gt.

    Lemma vec_plus_gt_compat_l : forall vl vl' vr vr',
      vec_at0 vl >= vec_at0 vl' -> vec_at0 vr > vec_at0 vr' -> 
      vec_at0 (vl [+] vr) > vec_at0 (vl' [+] vr').

    Proof.
      unfold MBI.vec_at0, vector_plus. intros. rewrite !Vnth_map2.
      unfold Aplus. apply plus_gt_compat_r; hyp.
    Qed.

    Lemma mint_eval_mon_succ : forall (val : valuation I) k 
      (mi mi' : mint k), mint_gt mi mi' -> 
      succ_vec (mint_eval val mi) (mint_eval val mi').

    Proof.
      intros. destruct H. split.
      apply mint_eval_mon_succeq. hyp.
      unfold mint_eval, add_vectors. simpl.
      apply vec_plus_gt_compat_l. 
      unfold MBI.vec_at0. apply (Vforall2_elim_nth (R:=ge)). 
      exact (mint_eval_mon_succeq_args _ H). hyp.
    Qed.

    Lemma term_gt_incl_succ : term_gt << IR_succ.

    Proof.
      intros l r lr v. destruct (mint_eval_equiv l r v). simpl in * .
      unfold succ, Rof, I, succ_vec. symmetry in H. symmetry in H0.
      rewrite (vec_ge_mor H H0),
        (Vforall2_elim_nth dim_pos H), (Vforall2_elim_nth dim_pos H0).
      change (succ_vec (mint_eval v
        (mi_of_term (ABterm.inject_term (Nat.le_max_l (maxvar l) (maxvar r)))))
      (mint_eval v (mi_of_term
        (ABterm.inject_term (Nat.le_max_r (maxvar l) (maxvar r)))))).
      apply mint_eval_mon_succ. hyp.
    Qed.

    Lemma mint_gt_dec : forall n, rel_dec (@mint_gt n).
      
    Proof.
      intro. apply intersection_dec. apply mint_ge_dec.
      intros x y. apply gt_dec.
    Defined.

    Definition succ' := term_gt.
    Definition succ'_sub := term_gt_incl_succ.
    Definition succ'_dec := term_gt_dec mint_gt mint_gt_dec.

    Section ExtendedMonotoneAlgebra.

      Section VecMonotonicity.

        Lemma vec_plus_gt_compat_r : forall vl vl' vr vr', 
          vec_at0 vl > vec_at0 vl' -> vec_at0 vr >= vec_at0 vr' -> 
          vec_at0 (vl [+] vr) > vec_at0 (vl' [+] vr').

        Proof.
          unfold MBI.vec_at0, vector_plus. intros.
          simpl. rewrite !Vnth_map2. 
          unfold Aplus, Peano.gt. apply plus_gt_compat_l; hyp.
        Qed.
      
        Variable f : matrix dim dim -> vec -> vec.
        Variable f_mon : forall M v1 v2, get_elem M dim_pos dim_pos > 0 ->
          v1 >=v v2 -> vec_at0 v1 > vec_at0 v2 -> 
          vec_at0 (f M v1) > vec_at0 (f M v2).
        
        Variables (a b : vec).

        Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 
          (v2 : vector vec n2)  n (M : vector (matrix dim dim) n) i_j,  
          Vforall (fun m => get_elem m dim_pos dim_pos > 0) M ->
          a >=v b -> vec_at0 a > vec_at0 b ->
          vec_at0 (add_vectors 
            (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j))) >
          vec_at0 (add_vectors 
            (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j))).

        Proof.
          induction v1; intros; simpl.
          destruct n. lia.

          rewrite !Vcast_cons.
          unfold add_vectors, MBI.vec_at0, vector_plus. simpl.
          rewrite !Vnth_map2.
          unfold Aplus. apply plus_gt_compat_r. apply eq_ge_compat. refl.
          unfold MBI.vec_at0 in f_mon. apply f_mon; try hyp.
          apply (Vforall_in (x:=Vhead M) H). apply Vin_head.

          destruct n0. lia.
          rewrite !Vcast_cons.
          unfold add_vectors, MBI.vec_at0, vector_plus. simpl.
          rewrite !Vnth_map2.
          unfold Aplus. apply plus_gt_compat_l. 2: apply eq_ge_compat; refl.
          match goal with |- gt ?Hl ?Hr => fold (gt Hr Hl) end.
          unfold MBI.vec_at0, add_vectors in IHv1.
          apply IHv1; try hyp.
          apply Vforall_incl with (S n0) M.
          intros. VSntac M. simpl. auto.
          hyp.
        Qed.

      End VecMonotonicity.

      Lemma dot_product_mon_r : forall i j (jp : (j < i)%nat) 
        (v v' w w' : vector bigN i),
        v >=v v' -> w >=v w' -> Vnth v jp > A0 ->
        Vnth w jp > Vnth w' jp -> 
        dot_product v w > dot_product v' w'.

      Proof.
        intros i j. gen i. clear i.
        induction j; intros.
        destruct i. lia.
        VSntac v. VSntac w. VSntac v'. VSntac w'.
        unfold dot_product. simpl.
        fold (dot_product (Vtail v') (Vtail w')). 
        fold (dot_product (Vtail v) (Vtail w)).
        unfold Aplus, Peano.gt. apply plus_gt_compat_r.
        apply dot_product_mon; apply Vforall2_tail; hyp.
        rewrite !Vhead_nth. apply mult_lt_compat_lr.
        apply (Vforall2_elim_nth (R:=ge)). hyp.
        rewrite (lt_unique (Nat.lt_0_succ i) jp). hyp.
        rewrite (lt_unique (Nat.lt_0_succ i) jp). hyp.
        destruct i. lia.
        VSntac v. VSntac w. VSntac v'. VSntac w'.
        unfold dot_product. simpl.
        fold (dot_product (Vtail v') (Vtail w')). 
        fold (dot_product (Vtail v) (Vtail w)).
        unfold Aplus, Peano.gt. apply plus_gt_compat_l.
        apply IHj with (lt_S_n jp).
        apply Vforall2_tail. hyp.
        apply Vforall2_tail. hyp.
        rewrite Vnth_tail, lt_nS_Sn. hyp.
        rewrite !Vnth_tail, lt_nS_Sn. hyp.
        apply BigN.mul_le_mono;
          rewrite !Vhead_nth; apply (Vforall2_elim_nth (R:=ge)); hyp.
      Qed.

      (* additional property of interpretation required to ensure strict
         monotonicity of interpretations: upper left corner of every matrix
         needs to be positive *)
      Definition monotone_interpretation n (fi : matrixInt dim n) := 
        Vforall (fun m => get_elem m dim_pos dim_pos > 0) (args fi).

      Variable matrixInt_monotone : forall f : sig, 
        monotone_interpretation (trsInt f).

      Lemma monotone_succ : monotone I succ.

      Proof.
        intros f i j i_j vi vj a b ab. split.
        apply monotone_succeq. destruct ab. hyp.
        simpl. unfold mi_eval_aux. apply vec_plus_gt_compat_r.
        rewrite !Vmap_cast, !Vmap_app. simpl.    
        apply vec_add_monotone_map2; try solve [destruct ab; hyp].
        intros. unfold MBI.vec_at0. unfold mat_vec_prod. 
        rewrite !Vnth_col_mat, !mat_mult_spec.
        apply dot_product_mon_r with 0%nat dim_pos.
        unfold ge. apply Vforall2_intro_nth. intros. apply BigN.le_refl.
        unfold ge. apply Vforall2_intro_nth. intros.
        rewrite !get_col_col_mat. destruct ab.
        apply (Vforall2_elim_nth (R:=ge)). hyp.
        hyp.
        rewrite !get_col_col_mat. hyp.
        apply matrixInt_monotone. apply BigN.le_refl.
      Qed.

    End ExtendedMonotoneAlgebra.

  End MonotoneAlgebra.

  Export MonotoneAlgebra.

  Module Export MAR := MonotoneAlgebraResults MonotoneAlgebra.

  Ltac matrixInt_monotonicity := 
    let f := fresh "f" in
    first 
    [ solve [
      apply monotone_succ; intro f; destruct f; 
        vm_compute; repeat split; auto with arith
      ]
    | fail 10 "Failed to prove monotonicity of given matrix interpretation"
    ].

  Ltac prove_termination := MAR.prove_termination matrixInt_monotonicity.

End MatrixInt.
