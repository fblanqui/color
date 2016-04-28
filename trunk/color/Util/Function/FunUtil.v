(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2014-12-11

useful definitions and lemmas on functions
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil.

(****************************************************************************)
(** Some properties of functions. *)

Section functions.

  Variables (A B : Type) (f : A -> B).

  Definition injective := forall x y, f x = f y -> x = y.

  Definition surjective := forall y, exists x, y = f x.

  Definition bijective := injective /\ surjective.

End functions.

(****************************************************************************)
(** Function composition. *)

Section comp.

  Variables (A B C : Type) (f : B -> C) (g : A -> B).

  Definition comp x := f (g x).

  Lemma inj_comp : injective f -> injective g -> injective comp.

  Proof.
    intros f_inj g_inj x y e. apply f_inj in e. apply g_inj in e. hyp.
  Qed.

  Lemma inj_comp_elim : injective comp -> injective g.

  Proof.
    intros comp_inj x y e. apply comp_inj. unfold comp. rewrite e. refl.
  Qed.

  Lemma surj_comp : surjective f -> surjective g -> surjective comp.

  Proof.
    intros f_surj g_surj z. destruct (f_surj z) as [y hy].
    destruct (g_surj y) as [x hx]. ex x. subst. refl.
  Qed.

  Lemma surj_comp_elim : surjective comp -> surjective f.

  Proof.
    intros comp_surj y. destruct (comp_surj y) as [x e]. subst. ex (g x). refl.
  Qed.

  Lemma bij_comp : bijective f -> bijective g -> bijective comp.

  Proof.
    intros f_bij g_bij. split. apply inj_comp; fo. apply surj_comp; fo.
  Qed.

End comp.

Infix "o" := comp (at level 70).

(****************************************************************************)
(** Inverse of a surjective function, using Hilbert's epsilon operator. *)

From CoLoR Require Import EpsilonUtil.

Section inverse.

  Variables (A B : Type) (f : A -> B) (f_surj : surjective f).

  Definition inverse : B -> A.

  Proof. intro y. destruct (cid (f_surj y)) as [x _]. exact x. Defined.

  Lemma inverse_eq y : f (inverse y) = y.

  Proof. unfold inverse. destruct (cid (f_surj y)) as [x e]. auto. Qed.

  Lemma inj_inverse : injective inverse.

  Proof.
    intros x y e. apply (f_equal f) in e. rewrite !inverse_eq in e. hyp.
  Qed.

End inverse.

(****************************************************************************)
(** Tactics for injectivity, surjective and bijectivity. *)

Ltac inj :=
  match goal with
    | |- injective (_ o _) => apply inj_comp; inj
    | |- injective (inverse _) => apply inj_inverse; inj
    | |- injective _ => auto
  end.

Ltac surj :=
  match goal with
    | |- surjective (_ o _) => apply surj_comp; surj
    | |- surjective _ => auto
  end.

Ltac bij :=
  match goal with
    | |- bijective (_ o _) => apply bij_comp; bij
    | |- bijective _ => hyp || (split; [inj | surj])
  end.
