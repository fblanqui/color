(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

recursive path orderings are monotonic well-founded strict orders
*)

Require Import VSignature.
Require Import VTerm.
Require Import RelMidex.
Require Import Preorder.
Require Import Setoid.

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
  Parameter leF_dec : rel_dec leF.
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
    Notation "X =A= Y" := (eqA X Y) (at level 70).

    Lemma sid_theoryA : Setoid_Theory A eqA.
    Proof.
      constructor; unfold Reflexive, Symmetric, Transitive.
      unfold eqA; simpl; trivial.
      unfold eqA; intros; subst; trivial.
      unfold eqA; intros; subst; trivial.
    Qed.

  End Term.

  Module Term_dec <: Eqset_dec.

    Module Export Eq := Term.

    Definition eqA_dec := @term_eq_dec Sig.

  End Term_dec.

  (***********************************************************************)
  (** precedence *)

  Definition ltF := ltA Sig leF.
  Definition eqF := eqA Sig leF.

  Infix "=F=" := eqF (at level 50).
  Infix "<F" := ltF (at level 50).
  Infix "<=F" := leF (at level 50).

End VPrecedence.
