(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2007-02-20

excluded middle and decidability for relations.
*)

From Stdlib Require Import Relations.

From CoLoR Require Import LogicUtil.

Set Implicit Arguments.

Section S.

  Variables (A : Type) (R : relation A).

  Definition rel_midex := forall x y : A, R x y \/ ~R x y.

  Definition rel_dec := forall x y, {R x y} + {~R x y}.

  Lemma rel_dec_midex : rel_dec -> rel_midex.

  Proof. do 3 intro. destruct (X x y); tauto. Qed.

  Definition fun_rel_dec (f : A->A->bool) :=
    forall x y, if f x y then R x y else ~R x y.

  Lemma bool_rel_dec : {f : A->A->bool | fun_rel_dec f} -> rel_dec.

  Proof. intros (f,H) x y. gen (H x y). case (f x y); intros; tauto. Qed.

  Lemma rel_dec_bool : rel_dec -> {f : A->A->bool | fun_rel_dec f}.

  Proof.
    intro H. exists (fun x y : A => if H x y then true else false).
    intros x y. destruct (H x y); trivial.
  Qed.

  Lemma fun_rel_dec_true : forall f x y, fun_rel_dec f -> f x y = true -> R x y.

  Proof. intros. set (w := H x y). rewrite H0 in w. hyp. Qed.

  Lemma fun_rel_dec_false : forall f x y,
    fun_rel_dec f -> f x y = false -> ~R x y.

  Proof. intros. set (w := H x y). rewrite H0 in w. hyp. Qed.

(***********************************************************************)
(** Leibniz equality relation *)

  Definition eq_midex := forall x y : A, x=y \/ x<>y.

  Definition eq_dec := forall x y : A, {x=y}+{x<>y}.

  Lemma eq_dec_midex : eq_dec -> eq_midex.

  Proof. do 3 intro. destruct (X x y); tauto. Qed.

End S.
