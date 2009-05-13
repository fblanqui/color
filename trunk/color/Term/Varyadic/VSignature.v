(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-10

signature for algebraic terms with no arity
*)

Set Implicit Arguments.

(***********************************************************************)
(** Variables are represented by natural numbers. *)

Notation variable := nat (only parsing).

(***********************************************************************)
(** Signature with a decidable set of symbols of fixed arity. *)

Record Signature : Type := mkSignature {
  symbol :> Type;
  beq_symb : symbol -> symbol -> bool;
  beq_symb_ok : forall x y, beq_symb x y = true <-> x = y
}.

Implicit Arguments mkSignature [symbol beq_symb].
Implicit Arguments beq_symb [s].
Implicit Arguments beq_symb_ok [s x y].

Require Import EqUtil.

Definition eq_symb_dec Sig := dec_beq (@beq_symb_ok Sig).

Implicit Arguments eq_symb_dec [Sig].

(***********************************************************************)
(** Tactic for proving beq_symb_ok *)

Ltac beq_symb_ok_tac := intros f g; split;
  [destruct f; destruct g; simpl; intro; (discriminate || reflexivity)
    | intro; subst g; destruct f; reflexivity].
