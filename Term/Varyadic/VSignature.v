(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-10

signature for algebraic terms with no arity
************************************************************************)

(* $Id: VSignature.v,v 1.1.1.1 2006-09-08 09:06:59 blanqui Exp $ *)

Set Implicit Arguments.

Notation variable := nat (only parsing).

Record Signature : Type := mkSignature {
  symbol :> Set;
  eq_symb_dec : forall f g : symbol, {f=g}+{~f=g}
}.

Implicit Arguments eq_symb_dec [s].