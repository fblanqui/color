(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-26

infinite sets
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import Relations.
Require Import Setoid.

Section defs.

Variable A : Type.

Definition set := A -> Prop.

Definition incl : relation set := fun R S => forall x, R x -> S x.

Definition equiv : relation set := fun R S => forall x, R x <-> S x.

Definition empty : set := fun _ => False.

Definition union (R S : set) : set := fun x : A => R x \/ S x.

End defs.

Infix "[=" := incl (at level 70).
Infix "===" := equiv (at level 70).
Infix "++" := union (right associativity, at level 60).

(***********************************************************************)
(** inclusion *)

Section incl.

Variable A : Type. Notation set := (set A).

Lemma incl_refl : forall R : set, R [= R.

Proof.
unfold incl. auto.
Qed.

Lemma incl_trans : forall R S T : set, R [= S -> S [= T -> R [= T.

Proof.
unfold incl. auto.
Qed.

Lemma incl_appl : forall R S : set, R [= R ++ S.

Proof.
unfold incl, union. auto.
Qed.

Lemma incl_appr : forall R S : set, R [= S ++ R.

Proof.
unfold incl, union. auto.
Qed.

End incl.

Add Parametric Relation (A : Type) : (set A) (@incl A)
  reflexivity proved by (@incl_refl A)
  transitivity proved by (@incl_trans A)
  as incl_rel.

(***********************************************************************)
(** equality *)

Section equiv.

Variable A : Type. Notation set := (set A).

Lemma equiv_refl : forall R : set, R === R.

Proof.
firstorder.
Qed.

Lemma equiv_trans : forall R S T : set, R === S -> S === T -> R === T.

Proof.
firstorder.
Qed.

Lemma equiv_sym : forall R S : set, R === S -> S === R.

Proof.
firstorder.
Qed.

Lemma equiv_elim : forall R S : set, R === S <-> R [= S /\ S [= R.

Proof.
firstorder.
Qed.

End equiv.

Add Parametric Relation (A : Type) : (set A) (@equiv A)
  reflexivity proved by (@equiv_refl A)
  symmetry proved by (@equiv_sym A)
  transitivity proved by (@equiv_trans A)
  as equiv_rel.
