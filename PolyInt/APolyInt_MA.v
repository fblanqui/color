(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-04-25

Polynomial interpretations in the setting of monotone algebras.
*)

From CoLoR Require Import APolyInt AMonAlg ZUtil RelUtil PositivePolynom ATrs
  MonotonePolynom LogicUtil BoolUtil.
From Stdlib Require List.

Module Type TPolyInt.
  Parameter sig : Signature.
  Parameter trsInt : PolyInterpretation sig.
  Parameter trsInt_wm : PolyWeakMonotone trsInt.
End TPolyInt.

Module PolyInt (Export PI : TPolyInt).

(*FIXME: remove this layer*)
  Module Export MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := sig.
    
    Definition I := Int_of_PI trsInt_wm.

    Definition succ := Dgt.
    Definition succeq := Dge.

    Definition refl_succeq := refl_Dge.
    Definition trans_succ := trans_Dgt.
    Definition trans_succeq := trans_Dge.

    Lemma monotone_succeq : AWFMInterpretation.monotone I succeq.

    Proof.
      unfold I. apply pi_monotone_eq.
    Qed.

    Definition succ_wf := WF_Dgt.

    Lemma succ_succeq_compat : absorbs_left succ succeq.

    Proof.
      unfold succ, succeq. intros p q pq. destruct pq as [r [pr rq]].
      unfold Dgt, Dlt, transp. apply Z.lt_le_trans with (val r); auto.
    Qed.

    Definition rulePoly_gt l r := rulePoly_gt trsInt (@mkRule sig l r).

    Definition succ' l r := coef_pos (rulePoly_gt l r).

    Definition bsucc' l r := bcoef_pos (rulePoly_gt l r).

    Lemma bsucc'_ok : forall l r, bsucc' l r = true <-> succ' l r.

    Proof.
      intros l r. unfold bsucc', succ'. apply bcoef_pos_ok.
    Qed.

    Lemma succ'_dec : rel_dec succ'.

    Proof.
      intros l r. unfold succ'. eapply dec. apply bcoef_pos_ok.
    Defined.

    Definition rulePoly_ge l r := rulePoly_ge trsInt (@mkRule sig l r).

    Definition succeq' l r := coef_pos (rulePoly_ge l r).

    Definition bsucceq' l r := bcoef_pos (rulePoly_ge l r).

    Lemma bsucceq'_ok : forall l r, bsucceq' l r = true <-> succeq' l r.

    Proof.
      intros l r. unfold bsucceq', succeq'. apply bcoef_pos_ok.
    Qed.

    Lemma succeq'_dec : rel_dec succeq'.

    Proof.
      intros l r. unfold succeq'. eapply dec. apply bcoef_pos_ok.
    Defined.

    Lemma succ'_sub : succ' << IR I succ.

    Proof.
      intros t u tu. unfold I, succ. set (r := mkRule t u).
      change t with (lhs r). change u with (rhs r).
      apply pi_compat_rule. hyp.
    Qed.

    Lemma succeq'_sub : succeq' << IR I succeq.

    Proof.
      intros t u tu. unfold I, succ. set (r := mkRule t u).
      change t with (lhs r). change u with (rhs r).
      apply pi_compat_rule_weak. hyp.
    Qed.

    Section ExtendedMonotoneAlgebra.

      Lemma monotone_succ : PolyStrongMonotone trsInt ->
        AWFMInterpretation.monotone I succ.

      Proof.
        unfold I. apply pi_monotone.
      Qed.

    End ExtendedMonotoneAlgebra.

    Import List.

    Section fin_Sig.

      Variable Fs : list Sig.
      Variable Fs_ok : forall f : Sig, In f Fs.

      Lemma fin_monotone_succ :
        forallb (fun f => bpstrong_monotone (trsInt f)) Fs = true ->
        AWFMInterpretation.monotone I succ.

      Proof.
        intro H. apply monotone_succ. intro f. rewrite <- bpstrong_monotone_ok.
        rewrite forallb_forall in H. apply H. apply Fs_ok.
      Qed.

    End fin_Sig.

  End MonotoneAlgebra.

(***********************************************************************)
(** tactics for Rainbow *)

  Arguments fin_monotone_succ [Fs] _ _ _ _ _ _ _ _ _ _ _.

  Ltac prove_cc_succ Fs_ok :=
    apply IR_context_closed; apply (fin_monotone_succ Fs_ok);
      (check_eq || fail 10 "could not prove the monotony of this polynomial interpretation").

End PolyInt.
