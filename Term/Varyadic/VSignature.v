(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-10

signature for algebraic terms with no arity
*)

Set Implicit Arguments.

Notation variable := nat (only parsing).

Record Signature : Type := mkSignature {
  symbol :> Type;
  beq_symb : symbol -> symbol -> bool;
  beq_symb_ok : forall x y, beq_symb x y = true <-> x = y
  (*eq_symbol_dec : forall f g : symbol, {f=g}+{~f=g}*)
}.

Implicit Arguments mkSignature [symbol beq_symb].
Implicit Arguments beq_symb [s].
Implicit Arguments beq_symb_ok [s x y].

Require Import EqUtil.

Definition eq_symb_dec Sig := dec_beq (@beq_symb_ok Sig).

Implicit Arguments eq_symb_dec [Sig].
