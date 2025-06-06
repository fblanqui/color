(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-24

A specification of termination proofs.
*)

Set Implicit Arguments.

From Stdlib Require Import ZArith List.
From CoLoR Require Import ASignature.

Section Proof.

Variable Sig : Signature.

(** [trsInt si] is a representation for an interpretation assigning type 
    [si] to a function symbol. It is represented by a list of pairs: 
    [(f, fi)], where [f] is a function symbol and [fi] is its 
    interpretation. *)
Definition trsInt symInt := list (Sig * symInt).

(** [monomial] is a monomial in representation of a polynomial. 
    A monomial [C * x_0^i_0 * ... * x_n^i_n] is represented as:
    [(C, i_0::...::i_n)]. *)
Definition monomial := (Z * list nat)%type.

(** [polynomial] is a list of monomials so [m_0 + ... + m_n] becomes 
    [m_0::...::m_n]. *)
Definition polynomial := list monomial.

Inductive TerminationProof :=
| TP_PolyInt (PI: trsInt polynomial) (Prf : TerminationProof)
| TP_ProblemEmpty.

End Proof.
