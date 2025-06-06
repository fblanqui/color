(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-24

A specification of a termination problem.
*)

From Stdlib Require Import List Relations.
From CoLoR Require Import ATrs SN.

Set Implicit Arguments.

Section TerminationProblem.

  Variable Sig : Signature.

  Notation term := (term Sig).
  Notation rule := (rule Sig).
  Notation trs := (list rule).

  Inductive Problem : Type :=
  | FullTerm (R : trs)
  | RelTerm (T R : trs)
  | RelTopTerm (T R : trs).

  Definition prob_red (P : Problem) : relation term :=
    match P with
    | FullTerm R => red R
    | RelTerm T R => red_mod T R
    | RelTopTerm T R => hd_red_mod T R
    end.

  Definition Prob_WF (P : Problem) := WF (prob_red P).

End TerminationProblem.
