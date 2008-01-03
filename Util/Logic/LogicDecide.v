(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-07-24

 results and definitions about decidability
*)

Set Implicit Arguments.

Definition prop_dec A (P : A -> Prop) := forall x, {P x}+{~P x}.

