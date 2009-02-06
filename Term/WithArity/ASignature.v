(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09

signature for algebraic terms with arity
*)

Set Implicit Arguments.

(** Variables are represented by natural numbers. *)

Notation variable := nat (only parsing).

(** Signature with a decidable set of symbols of fixed arity. *)
(* FIXME: beq_symb should replace eq_symbol_dec *)

Record Signature : Type := mkSignature {
  symbol :> Type;
  arity : symbol -> nat;
  eq_symbol_dec : forall f g : symbol, {f=g}+{~f=g}
}.

Implicit Arguments arity [s].
Implicit Arguments eq_symbol_dec [s].

(** Module type for signatures. *)

Module Type SIGNATURE.
  Parameter Sig : Signature.
End SIGNATURE.

(** Boolean equality from a signature. *)

Require Import EqUtil.

Section S.

Variable Sig : Signature.

Notation eq_symbol_dec := (@eq_symbol_dec Sig).

Definition beq_symb := beq_dec eq_symbol_dec.

Lemma beq_symb_ok : forall f g, beq_symb f g = true <-> f = g.

Proof.
exact (beq_dec_ok eq_symbol_dec).
Qed.

End S.
