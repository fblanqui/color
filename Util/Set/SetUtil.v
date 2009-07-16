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

Definition single a : set := fun x : A => x = a.

Definition add a R := union (single a) R.

End defs.

Infix "[=" := incl (at level 70).
Infix "[=]" := equiv (at level 70).
Infix "++" := union (right associativity, at level 60).
Infix "::" := add (at level 60, right associativity).

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

Lemma equiv_refl : forall R : set, R [=] R.

Proof.
firstorder.
Qed.

Lemma equiv_trans : forall R S T : set, R [=] S -> S [=] T -> R [=] T.

Proof.
firstorder.
Qed.

Lemma equiv_sym : forall R S : set, R [=] S -> S [=] R.

Proof.
firstorder.
Qed.

Lemma equiv_elim : forall R S : set, R [=] S <-> R [= S /\ S [= R.

Proof.
firstorder.
Qed.

End equiv.

Add Parametric Relation (A : Type) : (set A) (@equiv A)
  reflexivity proved by (@equiv_refl A)
  symmetry proved by (@equiv_sym A)
  transitivity proved by (@equiv_trans A)
  as equiv_rel.

(***********************************************************************)
(** union *)

Add Parametric Morphism (A : Type) : (@union A)
  with signature (@incl A) ==> (@incl A) ==> (@incl A)
    as incl_app.

Proof.
firstorder.
Qed.

Add Parametric Morphism (A : Type) : (@union A)
  with signature (@equiv A) ==> (@equiv A) ==> (@equiv A)
    as equiv_app.

Proof.
firstorder.
Qed.

Section union.

Variable A : Type. Notation set := (set A). Notation empty := (@empty A).

Lemma empty_union_l : forall R, empty ++ R [=] R.

Proof.
firstorder.
Qed.

Lemma empty_union_r : forall R, R ++ empty [=] R.

Proof.
firstorder.
Qed.

End union.

(***********************************************************************)
(** add *)

Add Parametric Morphism (A : Type) : (@add A)
  with signature (@eq A) ==> (@incl A) ==> (@incl A)
    as add_incl.

Proof.
firstorder.
Qed.

Add Parametric Morphism (A : Type) : (@add A)
  with signature (@eq A) ==> (@equiv A) ==> (@equiv A)
    as add_equiv.

Proof.
firstorder.
Qed.

(***********************************************************************)
(** image *)

Section image.

Variables (A B : Type) (f : A -> B).

Definition image (R : set A) : set B := fun b : B => exists a, R a /\ b = f a.

Definition image_union : forall R S, image (R ++ S) [=] image R ++ image S.

Proof.
firstorder.
Qed.

Definition image_add : forall a R, image (a :: R) [=] f a :: image R.

Proof.
intros. unfold add. rewrite image_union. apply equiv_app.
unfold image, single. split; intro. do 2 destruct H. subst. refl.
subst. exists a. auto. refl.
Qed.

End image.
