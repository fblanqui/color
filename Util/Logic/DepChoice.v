(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

dependent choice axiom
*)

(* $Id: DepChoice.v,v 1.1 2007-08-08 09:33:43 blanqui Exp $ *)

Set Implicit Arguments.

Require Export RelUtil.

Axiom dep_choice : forall (B : Type) (b : B) (T : relation B),
  classic_left_total T -> exists f, IS T f.
