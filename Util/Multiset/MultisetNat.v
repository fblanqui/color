(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-10-17

multisets of natural numbers
*)

Set Implicit Arguments.

From Stdlib Require Import Arith.
From CoLoR Require Import MultisetTheory MultisetOrder MultisetList RelExtras.

Module Nat.
  Definition A := nat.
End Nat.

Module NatSet <: Eqset := Eqset_def Nat.

Module NatSet_dec.

  Module Export Eq := NatSet.

  Definition eqA_dec := eq_nat_dec.

End NatSet_dec.

Module MSetCore := MultisetList.MultisetList NatSet_dec.

Module Export MSetTheory := MultisetTheory.Multiset MSetCore.

Module Export MSetOrd := MultisetOrder.MultisetOrder MSetCore.
