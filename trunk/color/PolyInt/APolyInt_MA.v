(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-04-25

Polynomial interpretations in the setting of monotone algebras.
*)

Require Export APolyInt.
Require Export AMonAlg.

Module Type TPolyInt.

  Parameter sig : Signature.
  Parameter trsInt : forall f : sig, poly (arity f).
  Parameter trsInt_monotone : forall f : sig, pmonotone (trsInt f).

End TPolyInt.

Module PolyInt (PI : TPolyInt).

  Export PI.

  (** Monotone algebra instantiated to polynomials *)
  Module MonotoneAlgebra <: MonotoneAlgebraType.

    Definition Sig := sig.
    
    Definition PI := mkPolyInterpretation sig trsInt trsInt_monotone.
    Definition I := Int_of_PI PI.

    Definition succ := Dgt.
    Definition succeq := Dge.

    Lemma monotone_succeq : AWFMInterpretation.monotone I succeq.

    Proof.
      unfold I. apply pi_monotone_eq.
    Qed.

    Definition succ_wf := WF_Dgt.

    Lemma succ_succeq_compat : absorb succ succeq.

    Proof.
      unfold succ, succeq. intros p q pq. destruct pq as [r [pr rq]].
      unfold Dgt, Dlt, transp. apply Zlt_le_trans with (val r); auto.
    Qed.

    Definition succ' (l r : term sig) := coef_pos (rulePoly_gt PI (mkRule l r)).
    Definition succeq' (l r : term sig) := coef_pos (rulePoly_ge PI (mkRule l r)).

    Lemma succ'_sub : succ' << IR I succ.

    Proof.
      intros t u tu. unfold I, succ. set (r := mkRule t u).
      change t with (lhs r). change u with (rhs r).
      apply pi_compat_rule. assumption.
    Qed.

    Lemma succeq'_sub : succeq' << IR I succeq.

    Proof.
      intros t u tu. unfold I, succ. set (r := mkRule t u).
      change t with (lhs r). change u with (rhs r).
      apply pi_compat_rule_weak. assumption.
    Qed.

    Lemma succ'_dec : rel_dec succ'.

    Proof.
      intros l r. unfold succ', coef_pos.
      apply lforall_dec. intro p.
      destruct (fst p). 
      left. intuition.
      left. intuition.
      right. intuition.
    Defined.

    Lemma succeq'_dec : rel_dec succeq'.

    Proof.
      intros l r. unfold succeq', coef_pos.
      apply lforall_dec. intro p.
      destruct (fst p).
      left. intuition.
      left. intuition.
      right. intuition.
    Defined.

  End MonotoneAlgebra.

  Export MonotoneAlgebra.
  Module MAR := MonotoneAlgebraResults MonotoneAlgebra.
  Export MAR.

  Module ExtendedMonotoneAlgebra <: ExtendedMonotoneAlgebraType.

    Module MA := MonotoneAlgebra.
    Export MA.

    Lemma monotone_succ : AWFMInterpretation.monotone I succ.

    Proof.
      unfold I. apply pi_monotone.
    Qed.

  End ExtendedMonotoneAlgebra.

  Export ExtendedMonotoneAlgebra.
  Module EMAR := ExtendedMonotoneAlgebraResults ExtendedMonotoneAlgebra.
  Export EMAR.

End PolyInt.
