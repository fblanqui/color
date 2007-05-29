(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

recursive path orderings are monotonic well-founded strict orders
*)

(* $Id: VPrecedence.v,v 1.2 2007-05-29 17:41:53 koper Exp $ *)

Require Export VSignature.
Require Export VTerm.
Require Export Preorder.

Module Type VPrecedenceType.

  Parameter Sig : Signature.

  Notation term := (term Sig).
  Notation terms := (list term).

  Parameter leF : Sig -> Sig -> Prop.

  (***********************************************************************)
  (** precedence *)

  Definition ltF := ltA Sig leF.
  Definition eqF := eqA Sig leF.

  Parameter ltF_wf : well_founded ltF.
  Parameter ltF_dec : rel_dec ltF.
  Parameter leF_preorder : preorder Sig leF.

  Infix "=F=" := eqF (at level 50).
  Infix "<F" := ltF (at level 50).
  Infix "<=F" := leF (at level 50).

End VPrecedenceType.

Module VPrecedence (P : VPrecedenceType).

  Export P.

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

  Definition ltF := ltA Sig leF.
  Definition eqF := eqA Sig leF.

  Infix "=F=" := eqF (at level 50).
  Infix "<F" := ltF (at level 50).
  Infix "<=F" := leF (at level 50).

End VPrecedence.

