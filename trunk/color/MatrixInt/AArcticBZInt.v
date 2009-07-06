(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-03-19 (setoid)
- Adam Koprowski and Johannes Waldmann, 2008-01
*)

Set Implicit Arguments.

Require Import Matrix.
Import ArcticBZMatrix.
Require Import AMonAlg.
Require Import AArcticBasedInt.
Require Import VecUtil.
Require Import OrdSemiRing.
Require Import SN.
Require Import RelUtil.
Require Import ZArith.
Require Import AMatrixBasedInt.

Local Open Scope Z_scope.

Definition matrixInt := @matrixInt A matrix.
Definition mkMatrixInt := @mkMatrixInt A matrix.

Section Absolute_finite.

  Variable dim : nat.
  Variable dim_pos : (dim > 0)%nat.  

  Definition absolute_finite n (fi : matrixInt dim n) := 
    Vnth (const fi) dim_pos >>= A1.

End Absolute_finite.

(** Module type for proving termination with matrix interpretations *)
Module Type TArcticBZInt.

  Parameter sig : Signature.
  Parameter dim : nat.
  Parameter dim_pos : (dim > 0)%nat.
  Parameter trsInt : forall f : sig, matrixInt dim (arity f).
  Parameter trsIntOk : forall f : sig, absolute_finite dim_pos (trsInt f).

End TArcticBZInt.

Module ArcticBZInt (AI : TArcticBZInt).

  Import AI.
  
  Module AB <: TArcticBasedInt.
    
    Module OSR := ArcticBZOrdSemiRingT.
    Module M := ArcticBZMatrix.
    Definition sig := sig.
    Definition dim := dim.
    Definition dim_pos := dim_pos.
    Definition trsInt := trsInt.

  End AB.

  Module Export AIBase := ArcticBasedInt AB.

  (** Monotone algebra instantiated to matrices *)
  Module MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := Sig.

    Lemma mi_eval_at0 : forall n (mi : matrixInt dim n) (v : vector dom n),
      absolute_finite dim_pos mi ->
      vec_at0 (mi_eval_aux mi (Vmap dom2vec v)) >>= A1.

    Proof.
      intros. unfold mi_eval_aux, vec_at0.
      rewrite vector_plus_nth. rewrite Aplus_comm. 
      apply arctic_plus_ge_monotone. exact H.
    Qed.

    Notation "x >_0 y" := (gtx x y) (at level 70).

    Lemma gtx_plus_compat : forall m m' n n',
      m >_0 m' -> n >_0 n' -> m + n >_0 m' + n'.

    Proof.
      intros. destruct H. destruct H0.
      left. apply plus_gt_compat; assumption.
      destruct H0. rewrite H0. rewrite H1.
      do 2 rewrite Aplus_0_r. left. assumption.
      destruct H. rewrite H. rewrite H1.
      do 2 rewrite Aplus_0_l. assumption.
    Qed.

    Lemma gtx_mult_compat : forall m m' n n',
      m >_0 m' -> n >>= n' -> m * n >_0 m' * n'.

    Proof.
      intros.
      destruct m; destruct m'; destruct n; destruct n';
        destruct H; destruct H0; simpl;
        try solve
          [ elimtype False; auto
          | intuition; discriminate
          | left; simpl; auto
          | left; simpl in *; omega
          | right; auto
          ].
      left. simpl. injection H0. intro. subst z1. simpl in H. omega.
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

    Definition refl_succeq := MBI.succeq_refl.
    Definition monotone_succeq := @MBI.monotone_succeq mi_eval_ok.

    Definition succ_succeq_compat := AIBase.succ_succeq_compat ge_gt_eq.

    Lemma succ_wf : WF succ.

    Proof.
      apply wf_transp_WF.
      unfold succ, transp.
      apply well_founded_lt_compat with (f := 
        (fun d: dom => 
          match vec_at0 (dom2vec d) with
          | Fin x => Zabs_nat x
          | MinusInfBZ => 0%nat
          end
        )
      ).
      intros x y xy. destruct x. destruct y. simpl. 
      cut (ge (vec_at0 x) A1). 2: assumption.
      cut (ge (vec_at0 x0) A1). 2: assumption.
      cut (gtx (vec_at0 x0) (vec_at0 x)).
      generalize (vec_at0 x0). generalize (vec_at0 x).
      clear x x0 v v0 xy. intros x y xy x_lb y_lb.
      destruct x; destruct y; arctic_ord.
(* x-man, this should be solved by arctic_ord *)
unfold A1, OSR.SR.A1 in *.
assert (z >= 0).
apply fin_ge_impl_ge; assumption.
assert (z0 >= 0).
apply fin_ge_impl_ge; assumption.
      destruct xy. simpl in H1.
      apply Zabs_nat_lt. omega.
      destruct H1; discriminate.
destruct x_lb; [ contradiction | discriminate ].
destruct y_lb; [ contradiction | discriminate ].
destruct y_lb; [ contradiction | discriminate ].
      unfold vec_at0. apply (Vforall2n_nth gtx). assumption.
    Qed.
  
  End MonotoneAlgebra.

  Export MonotoneAlgebra.

  Module Export MAR := MonotoneAlgebraResults MonotoneAlgebra.

  Ltac noTerminationProofs := 
    fail "Arctic matrices cannot be used for proving total termination".

  Ltac prove_termination := MAR.prove_termination noTerminationProofs.

End ArcticBZInt.

Ltac showArcticBZIntOk := solve
  [let f := fresh "f" in let s := fresh "s" in
    intro f; destruct f as [s | s]; destruct s; vm_compute; auto]
  || fail "invalid below-zero arctic interpretation".
