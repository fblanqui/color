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

Require Import LogicUtil.
Require Import Setoid.
Require Import AMatrixBasedInt.
Require Import Matrix.
Import BigNMatrix.
Require Import OrdSemiRing.
Require Import VecUtil.
Require Import AMonAlg.
Require Import SN.
Require Import RelUtil.
Require Import AWFMInterpretation.
Require Import VecEq.
Require Import NatUtil.
Require Import BigNUtil.

(** Module type for proving termination with matrix interpretations *)
Module Type TMatrixInt.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : (dim > 0)%nat.
  Parameter trsInt : forall f : sig, matrixInt bigN matrix dim (arity f).

End TMatrixInt.

Definition matrixInt := @matrixInt A matrix.
Definition mkMatrixInt := @mkMatrixInt A matrix.

Module MatrixInt (MI : TMatrixInt).

  Export MI.

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
    Definition refl_succeq := MBI.succeq_refl.
    Definition monotone_succeq := @MBI.monotone_succeq mi_eval_ok.

    Definition succeq' := MBI.succeq'.
    Definition succeq'_sub := @MBI.succeq'_sub mi_eval_ok.
    Definition succeq'_dec := MBI.succeq'_dec.

    Definition Sig := sig.
    
    Definition succ_vec v1 v2 := v1 >=v v2 /\ vec_at0 v1 > vec_at0 v2.
    Definition succ v1 v2 := succ_vec (dom2vec v1) (dom2vec v2).

    Lemma succ_wf : WF succ.

    Proof.
      apply WF_incl with (Rof gt (fun v : dom => vec_at0 (dom2vec v))).
      unfold succ, succ_vec, Rof, gt. intros x y. intuition.
      apply WF_inverse. apply gt_WF.
    Qed.

    Lemma succ_succeq_compat : absorb succ succeq.

    Proof.
      intros x z xz. destruct xz as [y [xy yz]]. split.
      apply succeq_trans with y. assumption. destruct yz. assumption.
      apply ge_gt_compat with (Vnth (dom2vec y) dim_pos). unfold MBI.vec_at0.
      apply (Vforall2n_nth ge). assumption. 
      destruct yz. assumption.
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
      unfold MBI.vec_at0, vector_plus. intros. do 2 rewrite Vnth_map2.
      unfold Aplus. apply plus_gt_compat_r; assumption.
    Qed.

    Lemma mint_eval_mon_succ : forall (val : valuation I) k 
      (mi mi' : mint k), mint_gt mi mi' -> 
      succ_vec (mint_eval val mi) (mint_eval val mi').

    Proof.
      intros. destruct H. split.
      apply mint_eval_mon_succeq. assumption.
      unfold mint_eval, add_vectors. simpl.
      apply vec_plus_gt_compat_l. 
      unfold MBI.vec_at0. apply (Vforall2n_nth ge). 
      exact (mint_eval_mon_succeq_args _ H). assumption.
    Qed.

    Lemma term_gt_incl_succ : term_gt << IR_succ.

    Proof.
      intros l r lr v. destruct (mint_eval_equiv l r v). simpl in * .
      unfold succ, I, succ_vec. symmetry in H. symmetry in H0.
      rewrite (vec_ge_mor H H0).
      rewrite (Vnth_mor _ H dim_pos). rewrite (Vnth_mor _ H0 dim_pos).
      change (succ_vec (mint_eval v
        (mi_of_term (ABterm.inject_term (Max.le_max_l (maxvar l) (maxvar r)))))
      (mint_eval v (mi_of_term
        (ABterm.inject_term (Max.le_max_r (maxvar l) (maxvar r)))))).
      apply mint_eval_mon_succ. assumption.
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
          simpl. do 2 rewrite Vnth_map2. 
          unfold Aplus, Peano.gt. apply plus_gt_compat_l; assumption.
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
          destruct n; [absurd_arith | idtac].
          unfold add_vectors, MBI.vec_at0, vector_plus. simpl.
          do 2 rewrite Vnth_map2.
          unfold Aplus. apply plus_gt_compat_r. apply eq_ge_compat. refl.
          unfold MBI.vec_at0 in f_mon. apply f_mon; try assumption.
          apply (Vforall_in (x:=Vhead M) H). apply Vin_head.
          destruct n0; [absurd_arith | idtac].
          unfold add_vectors, MBI.vec_at0, vector_plus. simpl.
          do 2 rewrite Vnth_map2.
          unfold Aplus. apply plus_gt_compat_l. 2: apply eq_ge_compat; refl.
          match goal with |- gt ?Hl ?Hr => fold (gt Hr Hl) end.
          unfold MBI.vec_at0, add_vectors in IHv1.
          apply IHv1; try assumption.
          apply Vforall_incl with (S n0) M.
          intros. VSntac M. simpl. auto.
          assumption.
        Qed.

      End VecMonotonicity.

      Lemma dot_product_mon_r : forall i j (jp : (j < i)%nat) 
        (v v' w w' : vector bigN i),
        v >=v v' -> w >=v w' -> Vnth v jp > A0 ->
        Vnth w jp > Vnth w' jp -> 
        dot_product v w > dot_product v' w'.

      Proof.
        intros i j. generalize i. clear i.
        induction j; intros.
        destruct i. absurd_arith.
        VSntac v. VSntac w. VSntac v'. VSntac w'.
        unfold dot_product. simpl.
        fold (dot_product (Vtail v') (Vtail w')). 
        fold (dot_product (Vtail v) (Vtail w)).
        unfold Aplus, Peano.gt. apply plus_gt_compat_r.
        apply dot_product_mon; apply vec_tail_ge; assumption.
        do 4 rewrite Vhead_nth. apply mult_lt_compat_lr.
        apply (Vforall2n_nth ge). assumption.
        rewrite (lt_unique (lt_O_Sn i) jp). assumption.
        rewrite (lt_unique (lt_O_Sn i) jp). assumption.
        destruct i. absurd_arith.
        VSntac v. VSntac w. VSntac v'. VSntac w'.
        unfold dot_product. simpl.
        fold (dot_product (Vtail v') (Vtail w')). 
        fold (dot_product (Vtail v) (Vtail w)).
        unfold Aplus, Peano.gt. apply plus_gt_compat_l.
        apply IHj with (lt_S_n jp).
        apply vec_tail_ge. assumption.
        apply vec_tail_ge. assumption.
        rewrite Vnth_tail. rewrite lt_nS_Sn. assumption.
        do 2 rewrite Vnth_tail. rewrite lt_nS_Sn. assumption.
        apply BigN.mul_le_mono.
        do 2 rewrite Vhead_nth. apply (Vforall2n_nth ge). assumption.
        do 2 rewrite Vhead_nth. apply (Vforall2n_nth ge). assumption.
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
        apply monotone_succeq. destruct ab. assumption.
        simpl. unfold mi_eval_aux. apply vec_plus_gt_compat_r.
        do 2 rewrite Vmap_cast. do 2 rewrite Vmap_app. simpl.    
        apply vec_add_monotone_map2; try solve [destruct ab; assumption].
        intros. unfold MBI.vec_at0. unfold mat_vec_prod. 
        do 2 rewrite Vnth_col_mat.
        do 2 rewrite mat_mult_spec. apply dot_product_mon_r with 0%nat dim_pos.
        unfold vec_ge, ge. apply Vforall2n_intro. intros. apply BigN.le_refl.
        unfold vec_ge, ge. apply Vforall2n_intro. intros.
        do 2 rewrite get_col_col_mat. destruct ab.
        apply (Vforall2n_nth ge). assumption.
        assumption.
        do 2 rewrite get_col_col_mat. assumption.
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
    | fail "Failed to prove monotonicity of given matrix interpretation"
    ].

  Ltac prove_termination := MAR.prove_termination matrixInt_monotonicity.

End MatrixInt.
