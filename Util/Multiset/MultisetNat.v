(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-10-17

multisets of natural numbers
*)

Set Implicit Arguments.

Require Import Arith.
Require Import MultisetTheory.
Require Import MultisetOrder.
Require Import MultisetList.
Require Import RelExtras.

Module Nat.
  Definition A := nat.
End Nat.

Module NatSet <: Eqset := Eqset_def Nat.

Module NatSet_dec.

  Module Eq := NatSet.
  Export Eq.

  Definition eqA_dec := eq_nat_dec.

End NatSet_dec.

Module MSetCore := MultisetList.MultisetList NatSet_dec.

Module MSetTheory := MultisetTheory.Multiset MSetCore.
 (* FIXME, the notation below is introduced only because otherwise 
    doing 'Export LMO' results in an error: "Scope sets_scope is not
    declared". This, I believe, should not be the case and maybe is
    a temporary flaw of the development version of Coq 8.2. *)
Notation "'XXX'" := I : sets_scope.
Export MSetTheory.

Module MSetOrd := MultisetOrder.MultisetOrder MSetCore.
Export MSetOrd.
