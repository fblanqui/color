(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

dependent choice axiom
*)

Set Implicit Arguments.

From CoLoR Require Import RelUtil.

Axiom dep_choice : forall (A : Type) (a : A) (R : relation A),
  classic_left_total R -> exists f, IS R f /\ f 0 = a.
