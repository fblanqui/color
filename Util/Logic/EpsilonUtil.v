(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2014-12-11

basic consequences of ClassicalEpsilon.constructive_indefinite_description
*)

Set Implicit Arguments.

From Stdlib Require Import ClassicalEpsilon.

Arguments constructive_indefinite_description [A P] _.

Notation cid := constructive_indefinite_description.
