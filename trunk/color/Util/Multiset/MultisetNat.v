(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-10-17

multisets of natural numbers
*)

Set Implicit Arguments.

Require Import MultisetTheory.
Require Import MultisetOrder.
Require Import MultisetList.
Require Import RelExtras.

Module Nat.
  Definition A := nat.
End Nat.

Module Eqset := Eqset_def Nat.

Module MSetCore := MultisetList.MultisetList Eqset.

Module MSetTheory := MultisetTheory.Multiset MSetCore.

Export MSetTheory.

Module MSetOrd := MultisetOrder.MultisetOrder MSetCore.

Export MSetOrd.
