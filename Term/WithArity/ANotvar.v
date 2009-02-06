(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2004-12-22

properties of function-headed terms
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import ATerm.
Require Import AContext.

Section S.

Variable Sig : Signature.

Notation term := (term Sig).

Fixpoint notvar (t : term) : Prop :=
  match t with
    | Var _ => False
    | _ => True
  end.

Lemma notvar_elim : forall t,
  notvar t -> exists f : Sig, exists ts, t = Fun f ts.

Proof.
intro t. case t; simpl; intros. contradiction. exists f. exists v. refl.
Qed.

Lemma notvar_var : forall v, ~ notvar (Var v).

Proof.
auto.
Qed.

Require Import ASubstitution.

Lemma notvar_sub : forall s t, notvar t -> notvar (sub s t).

Proof.
intros s t. case t; simpl; intros. contradiction. exact I.
Qed.


Lemma notvar_fill : forall c t, notvar t -> notvar (fill c t).

Proof.
intro c. case c; simpl; intros. exact H. exact I.
Qed.

Lemma notvar_fillsub : forall c s t, notvar t -> notvar (fill c (sub s t)).

Proof.
intros. apply notvar_fill. apply notvar_sub. assumption. 
Qed.

End S.
