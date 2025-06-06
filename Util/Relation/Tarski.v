(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-05-10

* Knaster-Tarski theorem
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil RelUtil SetUtil.
From Stdlib Require Import Morphisms Basics.

(****************************************************************************)
(** * We assume given a set [A] equipped with a transitive relation [<=]
and a relation [==] containing [inter_transp <=] (reflexivity is not
needed). *)

Section tarski.

  Variables (A : Type) (le eq : relation A).

  Infix "<=" := le (at level 70).
  Infix "==" := eq (at level 70).

  Variable eq_ok : forall x y, x <= y -> y <= x -> x == y.

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

    Variables (le_trans : Transitive le)
              (f : A -> A) (f_mon : Proper (le ==> le) f).

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

(** The least fixpoint can be reached by transfinite iteration. *)

    (*COQ: see https://coq.inria.fr/bugs/show_bug.cgi?id=4506 *)
    Unset Elimination Schemes.

    Inductive K : set A :=
    | Kf x : K x -> K (f x)
    | Klub S : S [<=] K -> K (lub S).

    Set Elimination Schemes.

    Section K_ind.

      Variables (P : A -> Prop) (Pf : forall x, K x -> P x -> P (f x))
                (Plub : forall S, S [<=] K -> S [<=] P -> P (lub S)).

      Fixpoint K_ind y (h : K y) : P y :=
        match h in K y return P y with
        | Kf g => Pf g (K_ind g)
        | Klub QK => Plub QK (fun x g => K_ind (QK x g))
        end.

    End K_ind.

    Lemma lfp_eq_lub : eq (lub K) lfp.

    Proof.
      eapply glb_is_uniq. 2: apply glb_ok.
      destruct (lub_ok K) as [h1 h2]. split.
      intros x hx. apply h2. induction 1.
      trans (f x). apply f_mon. hyp. hyp.
      destruct (lub_ok S) as [g1 g2]. apply g2. hyp.
      intros y hy. apply hy. apply h1. apply Kf. apply Klub. refl.
    Qed.

    Lemma lfp_ind (P : A -> Prop) :
      Proper (eq ==> impl) P ->
      (forall x, P x -> P (f x)) -> (forall S, S [<=] P -> P (lub S)) -> P lfp.

    Proof.
      intros Peq Pf Plub. rewrite <- lfp_eq_lub. apply Plub. induction 1.
      apply Pf. hyp. apply Plub. hyp.
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
    intros f g fg. unfold lfp. apply glb_equiv. intro x.
    unfold mem. rewrite fg. refl.
  Qed.

  Lemma gfp_ext : forall f g, (forall x, f x == g x) -> gfp f == gfp g.

  Proof.
    intros f g fg. unfold lfp. apply lub_equiv. intro x.
    unfold mem. rewrite fg. refl.
  Qed.

End tarski.

Arguments lfp_eq [A le eq] _ [glb] _ _ [f] _.
Arguments gfp_eq [A le eq] _ [lub] _ _ [f] _.

(****************************************************************************)
(** * Example of complete lattice: the powerset of some set [X]. *)

Section powerset.

  Variable X : Type.

  Notation A := (set X).
  Notation set_le := (@subset X).
  Notation set_eq := (@equiv X).

  Global Instance set_le_trans : Transitive set_le.

  Proof. fo. Qed.

  Lemma set_eq_ok : forall x y : A, x [<=] y -> y [<=] x -> x [=] y.

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

  Definition set_lfp_eq := lfp_eq set_eq_ok set_glb_ok set_le_trans.
  Definition set_gfp_eq := gfp_eq set_eq_ok set_lub_ok set_le_trans.

  Global Instance set_eq_refl : Reflexive set_eq.

  Proof. fo. Qed.

  Global Instance set_le_eq : Proper (set_eq ==> set_eq ==> iff) set_le.

  Proof. fo. Qed.

  Global Instance set_glb_equiv : Proper (equiv ==> set_eq) set_glb.

  Proof. fo. Qed.

  Global Instance set_lub_equiv : Proper (equiv ==> set_eq) set_lub.

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

(****************************************************************************)
(** * Least fixpoint over a sigma type. *)

Section sig.

  Variables (A : Type) (le eq : relation A)
            (eq_ok : forall x y, le x y -> le y x -> eq x y)
            (lub glb : set A -> A)
            (lub_ok : forall S, is_lub le (lub S) S)
            (glb_ok : forall S, is_glb le (glb S) S)
            (P : A -> Prop).

  Notation B := (sig P).

  Notation pr1 := (@proj1_sig A P).
  Notation pr2 := (@proj2_sig A P).

  Definition le_sig := Rof le pr1.
  Definition eq_sig := Rof eq pr1.

  Lemma eq_sig_ok x y : le_sig x y -> le_sig y x -> eq_sig x y.

  Proof. fo. Qed.

  Definition pr (R : set B) : set A := fun x => exists h : P x, R (exist h).

  Variable glb_prop : forall S : set A, (forall x, S x -> P x) -> P (glb S).

  Definition glb_sig (R : set B) : B.

  Proof.
    assert (h : P (glb (pr R))). apply glb_prop. intros x [h _]. hyp.
    exact (exist h).
  Defined.

  Lemma glb_sig_ok R : is_glb le_sig (glb_sig R) R.

  Proof.
    destruct (glb_ok (pr R)) as [h1 h2]. split.
    intros [x Px] Rx. unfold le_sig, Rof, glb_sig. simpl. apply h1. ex Px. hyp.
    intros x x_inf. unfold le_sig, Rof, glb_sig. simpl. apply h2.
    intros y [Py Ry]. apply (x_inf (exist Py)). hyp.
  Qed.

  Variable lub_prop : forall S : set A, (forall x, S x -> P x) -> P (lub S).

  Definition lub_sig (R : set B) : B.

  Proof.
    assert (h : P (lub (pr R))). apply lub_prop. intros x [h _]. hyp.
    exact (exist h).
  Defined.

  Lemma lub_sig_ok R : is_lub le_sig (lub_sig R) R.

  Proof.
    destruct (lub_ok (pr R)) as [h1 h2]. split.
    intros [x Px] Rx. unfold le_sig, Rof, lub_sig. simpl. apply h1. ex Px. hyp.
    intros x x_inf. unfold le_sig, Rof, lub_sig. simpl. apply h2.
    intros y [Py Ry]. apply (x_inf (exist Py)). hyp.
  Qed.

  Variable le_trans : Transitive le.

  Global Instance le_sig_trans : Transitive le_sig.

  Proof. apply Rof_trans. hyp. Qed.

  Variables (f : A -> A) (f_prop : forall x, P x -> P (f x)).

  Definition lift (x : B) : B := exist (f_prop (pr2 x)).

  Variable f_mon : Proper (le ==> le) f.

  Lemma lift_mon : Proper (le_sig ==> le_sig) lift.

  Proof. fo. Qed.

  Definition lfp_lift := pr1 (lfp le_sig glb_sig lift).

  Lemma lfp_lift_prop : P lfp_lift.

  Proof.
    unfold lfp_lift. destruct (lfp le_sig glb_sig lift) as [x Px]. hyp.
  Qed.

  Global Instance proj1_sig_eq : Proper (eq_sig ==> eq) pr1.

  Proof. fo. Qed.

  Lemma lfp_lift_eq : eq lfp_lift (f lfp_lift).

  Proof.
    ded (lfp_eq eq_sig_ok glb_sig_ok le_sig_trans lift_mon).
    apply proj1_sig_eq in H. hyp.
  Qed.

End sig.

Arguments lfp_lift [A] _ [glb P] _ [f] _.
Arguments lfp_lift_eq [A le eq] _ [glb] _ [P] _ _ [f] _ _.
Arguments lfp_lift_prop [A le glb P] _ [f] _.
