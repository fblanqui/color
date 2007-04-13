(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-03-21
- Frederic Blanqui , 2007-04-13

equality on relations
*)

(* $Id: RelEq.v,v 1.1 2007-04-13 13:21:03 blanqui Exp $ *)

Set Implicit Arguments.

Require Export RelUtil.

Lemma same_relation_refl : forall A, reflexive (same_relation A).

Proof.
intuition.
Qed.

Lemma same_relation_sym : forall A, symmetric (same_relation A).

Proof.
unfold symmetric, same_relation. intuition.
Qed.

Lemma same_relation_trans : forall A, transitive (same_relation A).

Proof.
unfold transitive, same_relation. intuition.
Qed.

Add Relation relation same_relation
  reflexivity proved by (same_relation_refl)
  symmetry proved by (same_relation_sym)
  transitivity proved by (same_relation_trans)
    as same_relation_rel.

Notation "R == S" := (same_relation _ R S) (at level 70).

Definition union : forall A, relation A -> relation A -> relation A := union.

Add Morphism union
  with signature same_relation ==> same_relation ==> same_relation
  as union_morph.

Proof.
unfold same_relation. intuition; union; assumption.
Qed.
