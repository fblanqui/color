(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

From CoLoR Require Import AArcticBasedInt Matrix OrdSemiRing VecUtil AMonAlg SN
     RelUtil NatUtil AWFMInterpretation LogicUtil AMatrixBasedInt BoolUtil
     ListUtil.
Import ArcticMatrix.

Definition matrixInt := @matrixInt A matrix.
Definition mkMatrixInt := @mkMatrixInt A matrix.

(***********************************************************************)
(** Condition for an arctic interpretation to be valid *)

Section Somewhere_finite.

  Variable dim : nat.
  Variable dim_pos : dim > 0.

  Definition somewhere_finite n (fi : matrixInt dim n) := 
    Vexists (fun m => get_elem m dim_pos dim_pos <> MinusInf) (args fi)
    \/ Vnth (const fi) dim_pos <> MinusInf.

  Definition bsomewhere_finite n (fi : matrixInt dim n) :=
    bVexists (fun m => is_finite (get_elem m dim_pos dim_pos)) (args fi)
    || is_finite (Vnth (const fi) dim_pos).

  Lemma bsomewhere_finite_ok : forall n (fi : matrixInt dim n),
    bsomewhere_finite fi = true <-> somewhere_finite fi.

  Proof.
    intros. unfold bsomewhere_finite, somewhere_finite.
    rewrite orb_eq, is_finite_ok, bVexists_ok. refl. intro. apply is_finite_ok.
  Qed.

  Variable sig : Signature.
  Variable trsInt : forall f : sig, matrixInt dim (arity f).

  Variable Fs : list sig.
  Variable Fs_ok : forall f : sig, In f Fs.

  Lemma fin_somewhere_finite :
    forallb (fun f => bsomewhere_finite (trsInt f)) Fs = true ->
    forall f : sig, somewhere_finite (trsInt f).

  Proof.
    rewrite forallb_forall. intros H f. rewrite <- bsomewhere_finite_ok.
    apply H. apply Fs_ok.
  Qed.

End Somewhere_finite.

Arguments fin_somewhere_finite [dim] _ [sig] _ [Fs] _ _ _.

Ltac somewhere_finite Fs_ok :=
  apply (fin_somewhere_finite _ _ Fs_ok);
    (check_eq || fail 10 "invalid arctic interpretation").

(***********************************************************************)
(** Module type for proving termination with an arctic interpretation *)

Module Type TArcticInt.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : dim > 0.
  Parameter trsInt : forall f : sig, matrixInt dim (arity f).
  Parameter trsIntOk : forall f : sig, somewhere_finite dim_pos (trsInt f).

End TArcticInt.

Module ArcticInt (Import AI : TArcticInt).
  
  Module AB <: TArcticBasedInt.
    
    Module OSR := ArcticOrdSemiRingT.
    Module M := ArcticMatrix.
    Definition sig := sig.
    Definition dim := dim.
    Definition dim_pos := dim_pos.
    Definition trsInt := trsInt.

  End AB.

  Module Export AIBase := ArcticBasedInt AB.

  Module Export MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := Sig.

    Lemma mat_times_vec_at0_positive n (m : matrix n n)
      (v : vector A n) (dim_pos : n > 0) :
      get_elem m dim_pos dim_pos <> MinusInf ->   
      Vnth v dim_pos <> MinusInf ->
      Vnth (mat_vec_prod m v) dim_pos <> MinusInf.

    Proof.
      destruct n; intros. lia.
      VSntac v. unfold matrix in m. VSntac m. 
      unfold mat_vec_prod, col_mat_to_vec, get_col. rewrite Vnth_map. 
      set (w := mat_mult_spec). unfold get_elem, get_row in w. rewrite w.
      simpl. VSntac (Vhead m). unfold dot_product. 
      simpl. rewrite Aplus_comm. apply arctic_plus_notInf_left.
      apply arctic_mult_notInf. 
      rewrite H2 in H. unfold get_elem in H. simpl in H.
      rewrite Vhead_nth, <- (Vnth_eq (Vhead m) dim_pos (Nat.lt_0_succ n)); trivial.
      rewrite H1 in H0. hyp.
    Qed.

    Notation mat_times_vec := (@mat_vec_prod dim dim).
    Notation mint := (matrixInt dim).

    Notation "x >_0 y" := (gtx x y) (at level 70).

    Lemma gtx_plus_compat : forall m m' n n',
      m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.

    Proof.
      intros. destruct H. destruct H0.
      left. apply plus_gt_compat; hyp.
      destruct H0. rewrite H0, H1, !Aplus_0_r. left. hyp.
      destruct H. rewrite H, H1, !Aplus_0_l. hyp.
    Qed.

    Lemma gtx_mult_compat : forall m m' n n',
      m >_0 m' -> n >>= n' -> m * n >_0 m' * n'.

    Proof.
      intros.
      destruct m; destruct m'; destruct n; destruct n';
        destruct H; destruct H0; simpl;
        try solve
          [ exfalso; auto
          | intuition; discr
          | left; simpl; auto
          | left; simpl in *; lia
          | right; auto
          ].
      left. simpl. injection H0. intro. subst n. simpl in H. lia.
    Qed.

    Lemma eval_some_notInf : forall n (mi : mint n) (v : vector dom n),
      Vexists (fun m => get_elem m dim_pos dim_pos <> MinusInf) (args mi) ->
      Vfold_left_rev Aplus A0
      (Vmap (fun v => Vnth v dim_pos)
        (Vmap2 mat_times_vec (args mi) (Vmap dom2vec v))) <> MinusInf.
      
    Proof.
      induction n; intros; simpl; destruct mi.
      VOtac. auto.
      simpl in H. VSntac args. rewrite H0 in H; simpl. destruct H.
      rewrite Aplus_comm. apply arctic_plus_notInf_left.
      apply mat_times_vec_at0_positive. hyp.
      VSntac v. simpl. destruct (Vhead v). 
      unfold vec_invariant, Conf.vec_at0 in v0. simpl in *.
      apply ge_A1_not_minusInf. hyp.
      apply arctic_plus_notInf_left. 
      rewrite <- Vmap_tail.
      apply (IHn (mkMatrixInt const (Vtail args))). hyp.
    Qed.

    Lemma mi_eval_at0 : forall n (mi : matrixInt dim n) (v : vector dom n),
      somewhere_finite dim_pos mi ->
      vec_at0 (mi_eval_aux mi (Vmap dom2vec v)) <> MinusInf.

    Proof.
      intros. unfold mi_eval_aux, vec_at0. 
      rewrite vector_plus_nth. destruct H.
      rewrite add_vectors_nth. apply arctic_plus_notInf_left.
      apply eval_some_notInf. hyp.
      rewrite Aplus_comm. apply arctic_plus_notInf_left. hyp.
    Qed.

    Lemma mi_eval_ok : forall f v,
      vec_invariant (mi_eval_aux (trsInt f) (Vmap dom2vec v)).

    Proof.
      intros. unfold vec_invariant, Conf.vec_at0. 
      apply not_minusInf_ge_A1.
      set (w := mi_eval_at0). unfold vec_at0 in w. apply w.
      apply trsIntOk.
    Qed.

    Definition I := I mi_eval_ok.

    Definition succ := AIBase.succ.
    Definition succ' := AIBase.succ'.
    Definition succ'_sub := @AIBase.succ'_sub gtx_plus_compat gtx_mult_compat
      mi_eval_ok.
    Definition succ'_dec := AIBase.succ'_dec.

    Definition succeq := MBI.succeq.
    Definition succeq' := MBI.succeq'.
    Definition succeq'_sub := @MBI.succeq'_sub mi_eval_ok.
    Definition succeq'_dec := MBI.succeq'_dec.

    Definition refl_succeq := MBI.refl_succeq.
    Definition monotone_succeq := @MBI.monotone_succeq mi_eval_ok.
    Definition trans_succeq := MBI.trans_succeq.
    Definition trans_succ := AIBase.trans_succ.

    Definition succ_succeq_compat := AIBase.succ_succeq_compat ge_gt_eq.

    Lemma succ_wf : WF succ.

    Proof.
      apply WF_incl with 
        (fun x y => vec_at0 (dom2vec x) >> vec_at0 (dom2vec y)).
      intros x y xy.
      destruct
        (@Vforall2_elim_nth _ _ gtx _ (dom2vec x) (dom2vec y) _ dim_pos xy). 
      hyp.
      destruct H. destruct x.
      absurd (Vnth x dim_pos = A0).
      apply ge_A1_not_minusInf. hyp. hyp.
      fold (@Rof dom A gt (fun v => vec_at0 (dom2vec v))).
      apply WF_inverse. apply gt_WF.
    Qed.
  
  End MonotoneAlgebra.

  Ltac prove_cc_succ Fs_ok :=
    fail 10 "arctic matrices cannot be used for proving total termination".

End ArcticInt.
