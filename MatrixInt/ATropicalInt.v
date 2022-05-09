(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Johannes Waldmann, 2010-04
*)

Set Implicit Arguments.

From CoLoR Require Import ATropicalBasedInt Matrix OrdSemiRing VecUtil AMonAlg
     SN RelUtil NatUtil AWFMInterpretation LogicUtil AMatrixBasedInt BoolUtil
     ListUtil.
From Coq Require Import Structures.Equalities.

(* TODO: this should be moved to Matrix.v *)
Module Import TropicalMatrix := Matrix TropicalOrdSemiRingT.

Definition matrixInt := @matrixInt A matrix.
Definition mkMatrixInt := @mkMatrixInt A matrix.

(***********************************************************************)
(** Condition for a tropical interpretation to be valid *)

Section Somewhere_tfinite.

  Variable dim : nat.
  Variable dim_pos : dim > 0.

  Definition somewhere_tfinite n (fi : matrixInt dim n) := 
    Vexists (fun m => get_elem m dim_pos dim_pos <> PlusInf) (args fi)
    \/ Vnth (const fi) dim_pos <> PlusInf.

  Definition bsomewhere_tfinite n (fi : matrixInt dim n) :=
    bVexists
    (fun m => tropical_is_finite (get_elem m dim_pos dim_pos)) (args fi)
    || tropical_is_finite (Vnth (const fi) dim_pos).

  Lemma bsomewhere_tfinite_ok : forall n (fi : matrixInt dim n),
    bsomewhere_tfinite fi = true <-> somewhere_tfinite fi.

  Proof.
    intros. unfold bsomewhere_tfinite, somewhere_tfinite.
    rewrite orb_eq, tropical_is_finite_ok, bVexists_ok. refl.
    intro. apply tropical_is_finite_ok.
  Qed.

  Variable sig : Signature.
  Variable trsInt : forall f : sig, matrixInt dim (arity f).

  Variable Fs : list sig.
  Variable Fs_ok : forall f : sig, In f Fs.

  Lemma fin_somewhere_tfinite :
    forallb (fun f => bsomewhere_tfinite (trsInt f)) Fs = true ->
    forall f : sig, somewhere_tfinite (trsInt f).

  Proof.
    rewrite forallb_forall. intros H f. rewrite <- bsomewhere_tfinite_ok.
    apply H. apply Fs_ok.
  Qed.

End Somewhere_tfinite.

Arguments fin_somewhere_tfinite [dim] _ [sig] _ [Fs] _ _ _.

Ltac somewhere_tfinite Fs_ok :=
  apply (fin_somewhere_tfinite _ _ Fs_ok);
    (check_eq || fail 10 "invalid tropical interpretation").

(***********************************************************************)
(** Module type for proving termination with a tropical interpretation *)

Module Type TTropicalInt.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : dim > 0.
  Parameter trsInt : forall f : sig, matrixInt dim (arity f).
  Parameter trsIntOk : forall f : sig, somewhere_tfinite dim_pos (trsInt f).

End TTropicalInt.

Module TropicalInt (Import AI : TTropicalInt).
  
  Module AB <: TTropicalBasedInt.
    
    Module OSR := TropicalOrdSemiRingT.
    Module M := TropicalMatrix.
    Definition sig := sig.
    Definition dim := dim.
    Definition dim_pos := dim_pos.
    Definition trsInt := trsInt.

  End AB.

  Module Export AIBase := TropicalBasedInt AB.

  Module Export MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := Sig.

    Lemma mat_times_vec_at0_positive n (m : matrix n n)
      (v : vector A n) (dim_pos : n > 0) :
      get_elem m dim_pos dim_pos <> PlusInf ->   
      Vnth v dim_pos <> PlusInf ->
      Vnth (mat_vec_prod m v) dim_pos <> PlusInf.

    Proof.
      destruct n; intros. lia.
      VSntac v. unfold matrix in m. VSntac m. 
      unfold mat_vec_prod, col_mat_to_vec, get_col. rewrite Vnth_map. 
      set (w := mat_mult_spec). unfold get_elem, get_row in w. rewrite w.
      simpl. VSntac (Vhead m). unfold dot_product.
      simpl. rewrite Aplus_comm. apply tropical_plus_notInf_left.
      apply tropical_mult_notInf. 
      rewrite H2 in H. unfold get_elem in H. simpl in H.
      rewrite Vhead_nth, <- (Vnth_eq (Vhead m) dim_pos (lt_O_Sn n)); trivial.
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
      Vexists (fun m => get_elem m dim_pos dim_pos <> PlusInf) (args mi) ->
      Vfold_left_rev Aplus A0
      (Vmap (fun v => Vnth v dim_pos)
        (Vmap2 mat_times_vec (args mi) (Vmap dom2vec v))) <> PlusInf.
      
    Proof.
      induction n; intros; simpl; destruct mi.
      VOtac. auto.
      simpl in H. VSntac args. rewrite H0 in H; simpl. destruct H.
      rewrite Aplus_comm. apply tropical_plus_notInf_left.
      apply (@mat_times_vec_at0_positive dim). hyp.
      VSntac v. simpl. destruct (Vhead v). 
      unfold vec_invariant, Conf.vec_at0 in v0. simpl in *.
       (* TODO... change - specific to tropical... *)
      intuition. clear H1. rewrite H2 in v0. contr.
      apply tropical_plus_notInf_left. 
      rewrite <- Vmap_tail.
      apply (IHn (mkMatrixInt const (Vtail args))). hyp.
    Qed.

    Lemma mi_eval_at0 : forall n (mi : matrixInt dim n) (v : vector dom n),
      somewhere_tfinite dim_pos mi ->
      vec_at0 (mi_eval_aux mi (Vmap dom2vec v)) <> PlusInf.

    Proof.
      intros. unfold mi_eval_aux, vec_at0. 
      rewrite vector_plus_nth. destruct H.
      rewrite add_vectors_nth. apply tropical_plus_notInf_left.
      apply eval_some_notInf. hyp.
      rewrite Aplus_comm. apply tropical_plus_notInf_left. hyp.
    Qed.

    Lemma mi_eval_ok : forall f v,
      vec_invariant (mi_eval_aux (trsInt f) (Vmap dom2vec v)).

    Proof.
      intros. unfold vec_invariant, Conf.vec_at0.
      apply tropical_plus_inf_max.
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

    Definition succ_succeq_compat := AIBase.succ_succeq_compat ge_gt_eq.

    Lemma succ_wf : WF succ.

    Proof.
      apply WF_incl with 
        (fun x y => vec_at0 (dom2vec x) >> vec_at0 (dom2vec y)).
      intros x y xy.
      destruct (@Vforall2_elim_nth _ _ gtx _ (dom2vec x) (dom2vec y) _ dim_pos xy). 
      hyp.
      destruct H. destruct x.
       (* TODO: change, specific for tropical *)
      absurd (A0 = Vnth x dim_pos).
      unfold vec_invariant in v.
      intro eq. clear H xy. rewrite eq in v. exact (gt_irrefl _ v).
      intuition.
      fold (@Rof dom A gt (fun v => vec_at0 (dom2vec v))).
      apply WF_inverse. apply gt_WF.
    Qed.

    #[global] Instance trans_succ : Transitive succ.

    Proof.
      change (transitive (Rof succ_vec dom2vec)). apply Rof_trans.
      apply Vforall2_trans. class.
    Qed.
  
  End MonotoneAlgebra.

  Ltac prove_cc_succ Fs_ok :=
    fail 10 "tropical matrices cannot be used for proving total termination".

End TropicalInt.
