(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

dependent choice axiom
*)

Set Implicit Arguments.

Require Import RelUtil.

Axiom dep_choice : forall (B : Type) (b : B) (T : relation B),
  classic_left_total T -> exists f, IS T f /\ f 0 = b.
