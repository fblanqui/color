(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-01-17

Axiom stating the equivalence between WF and ~IS.

IS_NotSN proves that, if R is finitely branching, then:
  WF R -> (forall f, ~IS R f)

NotSN_IS proves under the axiom of dependent choice (DepChoice) and
using classical logic that:
  (forall f, ~IS R f) -> WF R
*)

Set Implicit Arguments.

Require Import RelUtil SN.

Axiom WF_notIS : forall A (R : relation A), WF R <-> forall f, ~IS R f.
