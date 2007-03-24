(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03

  Carrier type for matrices.
*)

Require Import Arith.

Module Type Carrier.

  Parameter A : Set.
  Parameter Aplus : A -> A -> A.
  Parameter Amult : A -> A -> A.
  Parameter A0 : A.

End Carrier.

Module NCarrier <: Carrier.

  Definition A := nat.
  Definition Aplus := plus.
  Definition Amult := mult.
  Definition A0 := 0.

End NCarrier.
