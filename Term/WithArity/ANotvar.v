(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2004-12-22

properties of function-headed terms
*)

(* $Id: ANotvar.v,v 1.3 2007-05-16 15:04:49 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

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

Require Export ASubstitution.

Lemma notvar_app : forall s t, notvar t -> notvar (app s t).

Proof.
intros s t. case t; simpl; intros. contradiction. exact I.
Qed.


Lemma notvar_fill : forall c t, notvar t -> notvar (fill c t).

Proof.
intro c. case c; simpl; intros. exact H. exact I.
Qed.

Lemma notvar_fillapp : forall c s t, notvar t -> notvar (fill c (app s t)).

Proof.
intros. apply notvar_fill. apply notvar_app. assumption. 
Qed.

End S.
