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

Require Import Matrix.
Require Import AMonAlg.

Import NMatrix.

Section FunInt.

  Variables (Sig : Signature) (f : symbol Sig) (dim : nat).
  
  Record funInt : Type := mkFunInt {
    const : vector nat dim;
    args : vector (matrix dim dim) (arity f)
  }.

End FunInt.

Module Type TMatrixInt.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : dim > 0.
  Parameter matrixInt : forall f : sig, funInt sig f dim.

End TMatrixInt.

Module MatrixInt (MI: TMatrixInt).

  Import MI.

  Notation vec := (vector nat dim).

  Definition zero_vec := Vconst 0 dim.

  Definition vector_sum (v1 v2 : vec) := Vmap2 plus v1 v2.

  Definition vector_add n (v : vector vec n) := Vfold_left vector_sum zero_vec v.

  Definition matrix_int (f : sig) (args_int : vector vec (arity f)) :=
    let fint := matrixInt f in
    let compute_coef m v := col_matrix_to_vector (mat_mult m (vector_to_col_matrix v)) in
      vector_add (Vcons (const fint) (Vmap2 compute_coef (args fint) args_int)).

  Definition vec_at0 (v : vec) := Vnth v dim_pos.

  Module MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := sig.
    
    Definition I := @mkInterpretation sig vec zero_vec matrix_int.

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

      Variables (n : nat) (vl : vec) (vr vr' : vector vec n).

      Lemma vec_add_monotone_cons : vector_add vr >=v vector_add vr' -> 
        vector_add (Vcons vl vr) >=v vector_add (Vcons vl vr').

      Proof.
        unfold vector_add, vector_sum, succeq. intros. apply Vforall2_intro.
        intros. simpl. do 2 rewrite Vmap2_nth.
        unfold ge. apply plus_le_compat_r.
        apply (Vforall2_nth ge). assumption.
      Qed.

      Variable f : matrix dim dim -> vec -> vec.
      Variable f_mon : forall M v1 v2, v1 >=v v2 -> f M v1 >=v f M v2.
      Variables (a b : vec).

      Lemma vec_add_monotone_map2 : forall n1 (v1 : vector vec n1) n2 (v2 : vector vec n2) 
        n (M : vector (matrix dim dim) n) i_j, a >=v b ->
        vector_add (Vmap2 f M (Vcast (Vapp v1 (Vcons a v2)) i_j)) >=v 
        vector_add (Vmap2 f M (Vcast (Vapp v1 (Vcons b v2)) i_j)).

      Proof.
        induction v1; intros; simpl.
        destruct n0; try solve [elimtype False; omega].
        unfold vector_add, succeq. simpl. apply Vforall2_intro. intros.
        unfold vector_sum. do 2 rewrite Vmap2_nth.
        assert (Vnth (f (Vhead M) a) ip >= Vnth (f (Vhead M) b) ip).
        apply (Vforall2_nth ge). apply f_mon. assumption.
        omega.
        destruct n1; try solve [elimtype False; omega].
        unfold vector_add, succeq. simpl. apply Vforall2_intro. intros.
        unfold vector_sum. do 2 rewrite Vmap2_nth.
        unfold ge. apply plus_le_compat_r.
        match goal with |- ?Hl <= ?Hr => fold (ge Hr Hl) end.
        unfold succeq in IHv1. apply (Vforall2_nth ge).
        unfold vector_add in IHv1. apply IHv1. assumption.
      Qed.

    End VecMonotonicity.

    Lemma monotone_succeq : monotone I succeq.

    Proof.
      intros f i j i_j vi vj a b ab.
      simpl. unfold matrix_int. apply vec_add_monotone_cons.
      apply vec_add_monotone_map2; trivial.
      intros. unfold succeq. apply Vforall2_intro. intros.
      do 2 rewrite Vnth_col_matrix. apply mat_mult_mon.
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

End MatrixInt.
