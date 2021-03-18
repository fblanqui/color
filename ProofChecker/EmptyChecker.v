(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-24

A termination solver that knows how to deal with empty problems.
*)

From CoLoR Require Import ListUtil Problem ATrs SN LogicUtil.

Set Implicit Arguments.

Section EmptySolver.

  Variable Sig : Signature.

  Definition is_problem_empty (Pb : Problem Sig) :=
    match Pb with
    | FullTerm R => is_empty R
    | RelTerm T R => is_empty R
    | RelTopTerm T R => is_empty R
    end.

  Lemma empty_solver Pb : is_problem_empty Pb = true -> Prob_WF Pb.
  Proof.
    unfold Prob_WF; destruct Pb; simpl; intros; destruct R;
      try solve [termination_trivial | discr].
  Qed.

End EmptySolver.

#[global] Hint Resolve empty_solver : rainbow.
