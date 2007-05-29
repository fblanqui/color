(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-10

signature for algebraic terms with no arity
*)

(* $Id: VSignature.v,v 1.3 2007-05-29 11:58:35 blanqui Exp $ *)

Set Implicit Arguments.

Notation variable := nat (only parsing).

Record Signature : Type := mkSignature {
  symbol :> Set;
  eq_symbol_dec : forall f g : symbol, {f=g}+{~f=g}
}.

Implicit Arguments eq_symbol_dec [s].