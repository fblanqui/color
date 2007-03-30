(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03-22

Termination criterion based on matrix interpretations.

References:
-  J. Endrullis, J. Waldmann and H. Zantema, "Matrix Interpretations for Proving
   Termination of Term Rewriting", Proceedings of the 3rd International Joint
   Conference (IJCAR 2006), 2006.
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

Ltac matrixInt_monotonicity := intro f; destruct f; compute; auto with arith.

Module MatrixInt_DP (MI : TMatrixInt_DP).

  Export MI.

  Notation vec := (vector nat dim).
  Notation mint := (matrixInt dim).
  Notation mat := (matrix dim dim).

  Definition zero_vec := Vconst 0 dim.

  Definition vector_plus (v1 v2 : vec) := Vmap2 plus v1 v2.
  Infix "[+]" := vector_plus (at level 50).

  Definition add_vectors n (v : vector vec n) := Vfold_left vector_plus zero_vec v.

  Definition vec_at0 (v : vec) := Vnth v dim_pos.

  Definition mat_vect_prod (m : mat) (v : vec) := 
    col_matrix_to_vector (mat_mult m (vector_to_col_matrix v)).

  Definition mi_eval n (mi : matrixInt dim n) (v : vector vec n) : vec :=
    add_vectors (Vmap2 mat_vect_prod (args mi) v) [+] const mi.

  Module MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := sig.
    
    Definition I := @mkInterpretation sig vec zero_vec (fun f => mi_eval (trsInt f)).

    Definition succeq (v1 v2 : vec) := Vforall2n ge v1 v2.
    Notation "x >=v y" := (succeq x y) (at level 70).

    Definition succ v1 v2 := v1 >=v v2 /\ vec_at0 v1 > vec_at0 v2.
    Notation "x >v y" := (succ x y) (at level 70).

    Lemma succeq_trans : transitive succeq.

    Proof.
      intros x y z xy yz. unfold succeq. 
      apply Vforall2_intro. intros.
      unfold ge. apply le_trans with (Vnth y ip).
      apply (Vforall2_nth ge). assumption.
      apply (Vforall2_nth ge). assumption.
    Qed.

    Section VecMonotonicity.

      Variables (n : nat) (vl vl' vr : vec).

      Lemma vec_plus_monotone_r : vl >=v vl' -> vl [+] vr >=v vl' [+] vr.

      Proof.
        unfold vector_plus, succeq. intros. apply Vforall2_intro.
        intros. simpl. do 2 rewrite Vmap2_nth.
        unfold ge. apply plus_le_compat_r.
        apply (Vforall2_nth ge). assumption.
      Qed.

      Variable f : matrix dim dim -> vec -> vec.
      Variable f_mon : forall M v1 v2, v1 >=v v2 -> f M v1 >=v f M v2.
      Variables (a b : vec).

      Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 (v2 : vector vec n2) 
        n (M : vector (matrix dim dim) n) i_j, a >=v b ->
        add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j)) >=v 
        add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j)).

      Proof.
        induction v1; intros; simpl.
        destruct n0; try solve [elimtype False; omega].
        unfold add_vectors, succeq. simpl. apply Vforall2_intro. intros.
        unfold vector_plus. do 2 rewrite Vmap2_nth.
        assert (Vnth (f (Vhead M) a) ip >= Vnth (f (Vhead M) b) ip).
        apply (Vforall2_nth ge). apply f_mon. assumption.
        omega.
        destruct n1; try solve [elimtype False; omega].
        unfold add_vectors, succeq. simpl. apply Vforall2_intro. intros.
        unfold vector_plus. do 2 rewrite Vmap2_nth.
        unfold ge. apply plus_le_compat_r.
        match goal with |- ?Hl <= ?Hr => fold (ge Hr Hl) end.
        unfold succeq in IHv1. apply (Vforall2_nth ge).
        unfold add_vectors in IHv1. apply IHv1. assumption.
      Qed.

    End VecMonotonicity.

    Lemma monotone_succeq : monotone I succeq.

    Proof.
      intros f i j i_j vi vj a b ab.
      simpl. unfold mi_eval. apply vec_plus_monotone_r.
      apply vec_add_monotone_map2; trivial.
      intros. unfold succeq. apply Vforall2_intro. intros.
      unfold mat_vect_prod. do 2 rewrite Vnth_col_matrix. apply mat_mult_mon.
      apply mat_ge_refl. intros x y xp yp.
      do 2 rewrite vector_to_col_matrix_spec.
      apply (Vforall2_nth ge). assumption.
    Qed.

    Lemma succ_wf : WF succ.

    Proof.
      apply wf_WF. apply well_founded_lt_compat with (fun v : vec => vec_at0 v).
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
      intros x y. unfold succeq, Vforall2n. apply Vforall2_dec.
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
      
      Variables (n : nat) (vl vl' vr : vec).

      Lemma vec_plus_monotone_r : vec_at0 vl > vec_at0 vl' ->
        vec_at0 (vl [+] vr) > vec_at0 (vl' [+] vr).

      Proof.
        unfold vec_at0, vector_plus. intros.
        simpl. do 2 rewrite Vmap2_nth. 
        unfold gt. apply plus_lt_compat_r. assumption.
      Qed.

      Variable f : matrix dim dim -> vec -> vec.
      Variable f_mon : forall M v1 v2, get_elem M dim_pos dim_pos > 0 ->
        v1 >=v v2 -> vec_at0 v1 > vec_at0 v2 -> vec_at0 (f M v1) > vec_at0 (f M v2).

      Variables (a b : vec).

      Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 (v2 : vector vec n2) 
        n (M : vector (matrix dim dim) n) i_j,  
        Vforall (fun m => get_elem m dim_pos dim_pos > 0) M ->
        a >=v b -> vec_at0 a > vec_at0 b ->
        vec_at0 (add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j))) >
        vec_at0 (add_vectors (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j))).

      Proof.
        induction v1; intros; simpl.
        destruct n0; [solve [elimtype False; omega] | idtac].
        unfold add_vectors, vec_at0, vector_plus. simpl.
        do 2 rewrite Vmap2_nth. 
        unfold gt. apply plus_lt_compat_l.
        unfold vec_at0 in f_mon. apply f_mon; try assumption.
        apply (Vforall_in (x:=Vhead M) H). apply Vin_head.
        destruct n1; [solve [elimtype False; omega] | idtac].
        unfold add_vectors, vec_at0, vector_plus. simpl.
        do 2 rewrite Vmap2_nth.
        unfold gt. apply plus_lt_compat_r.
        match goal with |- ?Hl < ?Hr => fold (gt Hr Hl) end.
        unfold vec_at0, add_vectors in IHv1. 
        apply IHv1; try assumption.
        apply Vforall_incl with (S n1) M. 
        intros. VSntac M. simpl. auto.
        assumption.
      Qed.

    End VecMonotonicity.

    Lemma monotone_succ : monotone I succ.

    Proof.
      intros f i j i_j vi vj a b ab. split.
      apply monotone_succeq. destruct ab. assumption.
      simpl. unfold mi_eval. apply vec_plus_monotone_r.
      apply vec_add_monotone_map2; try solve [destruct ab; assumption].
      intros. unfold vec_at0. unfold mat_vect_prod. do 2 rewrite Vnth_col_matrix.
      do 2 rewrite mat_mult_spec. apply dot_product_mon_r with 0 dim_pos.
      unfold vec_ge. apply Vforall2_intro. auto.
      unfold vec_ge. apply Vforall2_intro. intros.
      do 2 rewrite get_col_col_matrix. destruct ab.
      apply (Vforall2_nth ge). assumption.
      assumption.
      do 2 rewrite get_col_col_matrix. assumption.
      apply matrixInt_monotone.
    Qed.

  End ExtendedMonotoneAlgebra.

  Export ExtendedMonotoneAlgebra.
  Module EMAR := ExtendedMonotoneAlgebraResults ExtendedMonotoneAlgebra.
  Export EMAR.

End MatrixInt.
