(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-05-10


* Knaster-Tarski theorem
*)

Set Implicit Arguments.

Require Import LogicUtil RelUtil Morphisms SetUtil.

(****************************************************************************)
(** * We assume given a set [A] equipped with a transitive relation [<=]
and a relation [==] containing [inter_transp <=] (reflexivity is not
needed). *)

Section tarski.

  Variables (A : Type) (le eq : relation A) (le_Trans : Transitive le).

  Existing Instance le_Trans.

  Infix "<=" := le (at level 70).
  Infix "==" := eq (at level 70).

  Variable eq_compat : forall x y, x <= y -> y <= x -> x == y.

(****************************************************************************)
(** Definitions of the notions of (least) upper/(greatest) lower bound. *)

  Definition is_sup a (P : set A) := forall x, P x -> x <= a.

  Definition is_inf a (P : set A) := forall x, P x -> a <= x.

  Definition is_lub a P := is_sup a P /\ forall a', is_sup a' P -> a <= a'.

  Definition is_glb a P := is_inf a P /\ forall a', is_inf a' P -> a' <= a.

(****************************************************************************)
(** lub's and glb's are unique modulo [==]. *)

  Lemma lub_is_uniq : forall P a b, is_lub a P -> is_lub b P -> a == b.

  Proof. fo. Qed.

  Lemma glb_is_uniq : forall P a b, is_glb a P -> is_glb b P -> a == b.

  Proof. fo. Qed.

(****************************************************************************)
(** Definition of the least and greatest fixpoints of a monotone
function [f], when one can compute a lub and glb for every subset of
[A] ([A] is a complete lattice). *)

  Variables (lub glb : set A -> A)
    (lub_ok : forall P, is_lub (lub P) P)
    (glb_ok : forall P, is_glb (glb P) P).

  Section lfp.

    Variables (f : A -> A) (f_mon : Proper (le ==> le) f).

    Definition lfp := glb (fun x => f x <= x).

    Lemma lfp_eq : lfp == f lfp.

    Proof.
      unfold lfp. set (P x := f x <= x). set (a := glb P).
      destruct (glb_ok P) as [a_inf a_glb].
      (* f a <= a *)
      assert (Pa : f a <= a).
      apply a_glb. intros x Px. trans (f x). apply f_mon. apply a_inf. hyp. hyp.
      (* a <= f a *)
      assert (h : a <= f a). apply a_inf. apply f_mon. hyp.
      (* conclusion *)
      fo.
    Qed.

    Definition gfp := lub (fun x => x <= f x).

    Lemma gfp_eq : gfp == f gfp.

    Proof.
      unfold gfp. set (P x := x <= f x). set (a := lub P).
      destruct (lub_ok P) as [a_sup a_lub].
      (* a <= f a *)
      assert (Pa : a <= f a).
      apply a_lub. intros x Px. trans (f x). hyp. apply f_mon. apply a_sup. hyp.
      (* f a <= a *)
      assert (h : f a <= a). apply a_sup. apply f_mon. hyp.
      (* conclusion *)
      fo.
    Qed.

  End lfp.

(****************************************************************************)
(** Extensionality of fixpoints: two fixpoints are equivalent modulo
[==] if their functions are pointwise equivalent modulo [==], [==] is
reflexive, [<=] is compatible with [==], and two glb's (resp. lub's)
are equivalent modulo [==] if their arguments are equivalent modulo
[SetUtil.equiv]. *)

  Variables (eq_refl : Reflexive eq)
    (le_eq : Proper (eq ==> eq ==> iff) le)
    (glb_equiv : Proper (equiv ==> eq) glb)
    (lub_equiv : Proper (equiv ==> eq) lub).

  Existing Instance eq_refl.
  Existing Instance le_eq.
  Existing Instance glb_equiv.
  Existing Instance lub_equiv.

  Lemma lfp_ext : forall f g, (forall x, f x == g x) -> lfp f == lfp g.

  Proof.
    intros f g fg. unfold lfp. apply glb_equiv. intro x. rewrite fg. refl.
  Qed.

  Lemma gfp_ext : forall f g, (forall x, f x == g x) -> gfp f == gfp g.

  Proof.
    intros f g fg. unfold lfp. apply lub_equiv. intro x. rewrite fg. refl.
  Qed.

End tarski.

Arguments lfp_eq [A le eq] _ _ [glb] _ [f] _.
Arguments gfp_eq [A le eq] _ _ [lub] _ [f] _.

(****************************************************************************)
(** * Example of complete lattice: the powerset of some set [X]. *)

Require Import Basics.

Section powerset.

  Variable X : Type.

  Notation A := (set X).
  Notation set_le := (@incl X).
  Notation set_eq := (@equiv X).

  Lemma set_le_trans : Transitive set_le.

  Proof. fo. Qed.

  Lemma set_eq_compat : forall x y : A, x [= y -> y [= x -> x [=] y.

  Proof. fo. Qed.

  Section lub.

    Variable P : set A.

    Definition set_lub : A := fun x => exists S, P S /\ S x.

    Lemma set_lub_ok : is_lub set_le set_lub P.

    Proof. fo. Qed.

    Definition set_glb : A := fun x => forall S, P S -> S x.

    Lemma set_glb_ok : is_glb set_le set_glb P.

    Proof. fo. Qed.

  End lub.

  Definition set_lfp := lfp set_le set_glb.
  Definition set_gfp := gfp set_le set_lub.

  Definition set_lfp_eq := lfp_eq set_le_trans set_eq_compat set_glb_ok.
  Definition set_gfp_eq := gfp_eq set_le_trans set_eq_compat set_lub_ok.

  Instance set_eq_refl : Reflexive set_eq.

  Proof. fo. Qed.

  Instance set_le_eq : Proper (set_eq ==> set_eq ==> iff) set_le.

  Proof. fo. Qed.

  Instance set_glb_equiv : Proper (equiv ==> set_eq) set_glb.

  Proof. fo. Qed.

  Instance set_lub_equiv : Proper (equiv ==> set_eq) set_lub.

  Proof. fo. Qed.

  Definition set_lfp_ext := lfp_ext set_eq_refl set_le_eq set_glb_equiv.
  Definition set_gfp_ext := lfp_ext set_eq_refl set_le_eq set_lub_equiv.

End powerset.

Arguments set_lub {X} _ _.
Arguments set_glb {X} _ _.
Arguments set_lfp {X} _ _.
Arguments set_lfp_eq {X} [f] _ _.
Arguments set_gfp_eq {X} [f] _ _.
Arguments set_lfp_ext {X} [f g] _ _.
Arguments set_gfp_ext {X} [f g] _ _.
