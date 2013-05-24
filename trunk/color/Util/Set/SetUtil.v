(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-06-26

Infinite sets
*)

Set Implicit Arguments.

Require Import LogicUtil RelUtil Morphisms.

Section defs.

  Variable X : Type.

  Definition set := X -> Prop.

  Definition incl : relation set := fun A B => forall x, A x -> B x.

  Definition equiv : relation set := fun A B => forall x, A x <-> B x.

  Definition empty : set := fun _ => False.

  Definition union (A B : set) : set := fun x => A x \/ B x.

  Definition singleton x0 : set := fun x => x = x0.

  Definition add x0 A := union (singleton x0) A.

End defs.

Arguments incl {X} A B.
Arguments equiv {X} A B.
Arguments empty {X} _.

Infix "[=" := incl (at level 70).
Infix "[=]" := equiv (at level 70).
Infix "++" := union (right associativity, at level 60).
Infix "::" := add (at level 60, right associativity).

(***********************************************************************)
(** Inclusion. *)

Instance incl_rel A : PreOrder (@incl A).

Proof. fo. Qed.

Lemma incl_appl : forall X (A B : set X), A [= A ++ B.

Proof. unfold incl, union. auto. Qed.

Lemma incl_appr : forall X (A B : set X), A [= B ++ A.

Proof. unfold incl, union. auto. Qed.

(***********************************************************************)
(** Equality. *)

Lemma equiv_elim : forall X (A B : set X), A [=] B <-> A [= B /\ B [= A.

Proof. fo. Qed.

Instance equiv_rel A : Equivalence (@equiv A).

Proof. fo. Qed.

(*TODO? define a meta-theorem when same_relation is defined as the
equivalence relation associated to incl (inter R (transp R))?*)

Instance incl_equiv1 A1 B (f : set A1 -> relation B) :
  Proper (incl ==> inclusion) f -> Proper (equiv ==> same_relation) f.

Proof.
  intros hf s1 s1'. rewrite equiv_elim. intros [s1s1' s1's1].
  split; apply hf; hyp.
Qed.

Instance incl_equiv2 A1 A2 B (f : set A1 -> set A2 -> relation B) :
  Proper (incl ==> incl ==> inclusion) f ->
  Proper (equiv ==> equiv ==> same_relation) f.

Proof.
  intros hf s1 s1'. rewrite equiv_elim. intros [s1s1' s1's1] s2 s2'.
  rewrite equiv_elim. intros [s2s2' s2's2]. split; apply hf; hyp.
Qed.

(***********************************************************************)
(** Union. *)

Instance union_incl A : Proper (incl ==> incl ==> incl) (@union A).

Proof. fo. Qed.

Instance union_equiv A : Proper (equiv ==> equiv ==> equiv) (@union A).

Proof. fo. Qed.

Lemma empty_union_l : forall X (A : set X), empty ++ A [=] A.

Proof. fo. Qed.

Lemma empty_union_r : forall X (A : set X), A ++ empty [=] A.

Proof. fo. Qed.

(***********************************************************************)
(** Add. *)

Instance add_incl A : Proper (eq ==> incl ==> incl) (@add A).

Proof. intros x x' xx'. subst x'. fo. Qed.

Instance add_equiv A : Proper (eq ==> equiv ==> equiv) (@add A).

Proof. intros x x' xx'. subst x'. fo. Qed.

(***********************************************************************)
(** Image by a function. *)

Section image.

  Variables (X Y : Type) (f : X -> Y).

  Definition image (A : set X) : set Y := fun y => exists x, A x /\ y = f x.

  Lemma image_singleton x : image (singleton x) [=] singleton (f x).

  Proof.
    intro y. split.
    intros [a [h1 h2]]. unfold singleton in *. subst. refl.
    unfold singleton. intro h. exists x. auto.
  Qed.

  Lemma image_union A B : image (A ++ B) [=] image A ++ image B.

  Proof. fo. Qed.

  Lemma image_add x A : image (x :: A) [=] f x :: image A.

  Proof. unfold add. rewrite image_union, image_singleton. refl. Qed.

End image.
