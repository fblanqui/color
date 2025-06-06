(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-24

A machinery to check termination proofs.
*)

From Stdlib Require Import Relations List.
From CoLoR Require Import SN ATrs ARelation Problem Proof EmptyChecker.
From CoLoR Require PolyChecker.

Set Implicit Arguments.

Section ProofChecker.

Variable Sig : Signature.

Inductive TerminationAnalysisResult (P : Problem Sig) :=
| TerminationEstablished (Prf : Prob_WF P)
| Error.

Arguments TerminationEstablished [P] _.
Arguments Error {P}.

Program Fixpoint check_proof (Pb : Problem Sig) (Prf : TerminationProof Sig) 
  : TerminationAnalysisResult Pb :=

  match Prf with
  | TP_PolyInt PI Prf' =>
      match PolyChecker.polySolver PI Pb with
      | None => Error
      | Some Pb' => 
          match check_proof Pb' Prf' with
          | Error => Error
          | TerminationEstablished _ => TerminationEstablished _
          end
      end

  | TP_ProblemEmpty _ => 
      match EmptyChecker.is_problem_empty Pb with
      | true => TerminationEstablished _
      | _ => Error
      end
  end.

Next Obligation.
Proof.
  auto with rainbow.
Qed.

End ProofChecker.
