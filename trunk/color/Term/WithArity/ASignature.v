(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09

signature for algebraic terms with arity
*)

(* $Id: ASignature.v,v 1.2 2007-01-19 17:22:40 blanqui Exp $ *)

Set Implicit Arguments.

Notation variable := nat (only parsing).

Record Signature : Type := mkSignature {
  symbol :> Set;
  arity : symbol -> nat;
  eq_symb_dec : forall f g : symbol, {f=g}+{~f=g}
}.

Implicit Arguments arity [s].
Implicit Arguments eq_symb_dec [s].
