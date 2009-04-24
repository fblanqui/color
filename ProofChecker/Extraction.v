(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-24

A set-up for extraction of a certified termination proof checker.
*)

Require ProofChecker.

Set Extraction Optimize.
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].

Print Assumptions ProofChecker.check_proof.
Recursive Extraction Library ProofChecker.
