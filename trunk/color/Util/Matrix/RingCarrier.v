(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski and Hans Zantema, 2007-03

  Carrier type for rings (without inversion).
*)

Module Type RingCarrier.

  Parameter A : Set.
  Parameter Aplus : A -> A -> A.
  Parameter Amult : A -> A -> A.
  Parameter A0 : A.
  Parameter A1 : A.

  Notation "x + y" := (Aplus x y).
  Notation "x * y" := (Amult x y).

End RingCarrier.

Require Import Arith.

Module NCarrier <: RingCarrier.

  Definition A := nat.
  Definition Aplus := plus.
  Definition Amult := mult.
  Definition A0 := 0.
  Definition A1 := 1.

End NCarrier.

Require Import ZArith.

Module ZCarrier <: RingCarrier.

  Definition A := Z.
  Definition Aplus := Zplus.
  Definition Amult := Zmult.
  Definition A0 := Z0.
  Definition A1 := Zsucc Z0.

End ZCarrier.
