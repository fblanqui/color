(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2004-12-22

properties of function-headed terms
*)

(* $Id: ANotvar.v,v 1.2 2007-01-19 17:22:40 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Definition notvar t := exists f : Sig, exists ts, t = Fun f ts.

Lemma notvar_var : forall v, ~ notvar (Var v).

Proof.
unfold not. intros. unfold notvar in H.
destruct H as [f]. destruct H as [ts]. discriminate.
Qed.

Require Export ASubstitution.

Lemma notvar_app : forall s t, notvar t -> notvar (app s t).

Proof.
intros. unfold notvar in H. destruct H as [f]. destruct H as [ts].
rewrite H. simpl. unfold notvar. exists f. exists (Vmap (app s) ts). refl.
Qed.


Lemma notvar_fill : forall c t, notvar t -> notvar (fill c t).

Proof.
intros. unfold notvar in H. destruct H as [f]. destruct H as [ts].
rewrite H. destruct c. simpl. unfold notvar. exists f. exists ts. reflexivity.
simpl. unfold notvar. exists f0.
exists (Vcast (Vapp v (Vcons (fill c (Fun f ts)) v0)) e). reflexivity.
Qed.

Lemma notvar_fillapp : forall c s t, notvar t -> notvar (fill c (app s t)).

Proof.
intros. apply notvar_fill. apply notvar_app. assumption. 
Qed.

End S.
