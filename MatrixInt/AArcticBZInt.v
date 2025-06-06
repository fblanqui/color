(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

From Stdlib Require Import ZArith Lia.
From CoLoR Require Import LogicUtil Matrix AMonAlg AArcticBasedInt VecUtil
     OrdSemiRing SN RelUtil AMatrixBasedInt ListUtil.
Import ArcticBZMatrix.

Definition matrixInt := @matrixInt A matrix.
Definition mkMatrixInt := @mkMatrixInt A matrix.

(***********************************************************************)
(** Condition for an arctic BZ interpretation to be valid *)

Section Absolute_finite.

  Variable dim : nat.
  Variable dim_pos : (dim > 0)%nat.  

  Definition absolute_finite n (fi : matrixInt dim n) := 
    Vnth (const fi) dim_pos >>= A1.

  Definition babsolute_finite n (fi : matrixInt dim n) :=
    is_above_zero (Vnth (const fi) dim_pos).

  Lemma babsolute_finite_ok : forall n (fi : matrixInt dim n),
    babsolute_finite fi = true <-> absolute_finite fi.

  Proof.
    intros. unfold babsolute_finite, absolute_finite.
    rewrite is_above_zero_ok. tauto.
  Qed.

  Variable sig : Signature.
  Variable trsInt : forall f : sig, matrixInt dim (arity f).

  Variable Fs : list sig.
  Variable Fs_ok : forall f : sig, In f Fs.

  Lemma fin_absolute_finite :
    forallb (fun f => babsolute_finite (trsInt f)) Fs = true ->
    forall f : sig, absolute_finite (trsInt f).

  Proof.
    rewrite forallb_forall. intros H f. rewrite <- babsolute_finite_ok.
    apply H. apply Fs_ok.
  Qed.

End Absolute_finite.

(***********************************************************************)
(** Module type for proving termination with matrix interpretations *)

Module Type TArcticBZInt.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : (dim > 0)%nat.
  Parameter trsInt : forall f : sig, matrixInt dim (arity f).
  Parameter trsIntOk : forall f : sig, absolute_finite dim_pos (trsInt f).

End TArcticBZInt.

Module ArcticBZInt (Import AI : TArcticBZInt).

  Module AB <: TArcticBasedInt.
    
    Module OSR := ArcticBZOrdSemiRingT.
    Module M := ArcticBZMatrix.
    Definition sig := sig.
    Definition dim := dim.
    Definition dim_pos := dim_pos.
    Definition trsInt := trsInt.

  End AB.

  Module Export AIBase := ArcticBasedInt AB.

  Module Export MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := Sig.

    Lemma mi_eval_at0 : forall n (mi : matrixInt dim n) (v : vector dom n),
      absolute_finite dim_pos mi ->
      vec_at0 (mi_eval_aux mi (Vmap dom2vec v)) >>= A1.

    Proof.
      intros. unfold mi_eval_aux, vec_at0.
      rewrite vector_plus_nth, Aplus_comm. 
      apply arctic_plus_ge_monotone. exact H.
    Qed.

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
      left. simpl. injection H0. intro. subst z1. simpl in H. lia.
    Qed.

    Lemma mi_eval_ok : forall f v,
      vec_invariant (mi_eval_aux (trsInt f) (Vmap dom2vec v)).

    Proof.
      intros. unfold vec_invariant, Conf.vec_at0. 
      set (w := mi_eval_at0). unfold vec_at0 in w. apply w.
      apply trsIntOk.
    Qed.

    Definition I := I mi_eval_ok.

    Definition succ := AIBase.succ.
    Definition succ' := AIBase.succ'.
    Definition succ'_sub :=
      @AIBase.succ'_sub gtx_plus_compat gtx_mult_compat mi_eval_ok.
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
      apply wf_transp_WF.
      unfold succ, transp.
      apply well_founded_lt_compat with (f := 
        (fun d: dom => 
          match vec_at0 (dom2vec d) with
          | Fin x => Z.abs_nat x
          | MinusInfBZ => 0%nat
          end
        )
      ).
      intros x y xy. destruct x. destruct y. simpl. 
      cut (ge (vec_at0 x) A1). 2: hyp.
      cut (ge (vec_at0 x0) A1). 2: hyp.
      cut (gtx (vec_at0 x0) (vec_at0 x)).
      gen (vec_at0 x0). gen (vec_at0 x).
      clear x x0 v v0 xy. intros x y xy x_lb y_lb.
      destruct x; destruct y; arctic_ord.
(*FIXME: this should be solved by arctic_ord *)
unfold A1, OSR.SR.A1 in *.
assert ((z >= 0)%Z).
apply fin_ge_impl_ge; hyp.
assert ((z0 >= 0)%Z).
apply fin_ge_impl_ge; hyp.
      destruct xy. simpl in H1.
      apply Zabs_nat_lt. lia.
      destruct H1; discr.
destruct x_lb; [ contr | discr ].
destruct y_lb; [ contr | discr ].
destruct y_lb; [ contr | discr ].
      unfold vec_at0. apply Vforall2_elim_nth. hyp.
    Qed.
  
  End MonotoneAlgebra.

(***********************************************************************)
(** tactics *)

  Ltac prove_cc_succ Fs_ok :=
    fail 10 "arctic matrices cannot be used for proving total termination".

End ArcticBZInt.

Arguments fin_absolute_finite [dim] _ [sig] _ [Fs] _ _ _.

Ltac absolute_finite Fs_ok :=
  apply (fin_absolute_finite _ _ Fs_ok);
    (check_eq || fail 10 "invalid below-zero arctic interpretation").
