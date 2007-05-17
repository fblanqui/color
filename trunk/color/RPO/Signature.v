(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

recursive path orderings are monotonic well-founded strict orders
*)

(* $Id: Signature.v,v 1.3 2007-05-17 15:30:54 koper Exp $ *)

Require Export VSignature.

Variable Sig : Signature.

Require Export VTerm.

Notation term := (term Sig).
Notation terms := (list term).

(***********************************************************************)
(** eqset module of terms *)

Require Import RelExtras.

Module Term <: Eqset.

  Definition A := term.

  Definition eqA := eq (A := term).

  Require Import Setoid.

  Lemma sid_theoryA : Setoid_Theory A eqA.
  Proof.
    constructor.
    unfold eqA; simpl; trivial.
    unfold eqA; intros; subst; trivial.
    unfold eqA; intros; subst; trivial.
  Qed.

End Term.

(***********************************************************************)
(** precedence *)

Parameter leF : Sig -> Sig -> Prop.

Require Export Preorder.

Parameter leF_preorder : preorder Sig leF.

Definition ltF := ltA Sig leF.
Definition eqF := eqA Sig leF.

Infix "=F=" := eqF (at level 50).
Infix "<F" := ltF (at level 50).
Infix "<=F" := leF (at level 50).
