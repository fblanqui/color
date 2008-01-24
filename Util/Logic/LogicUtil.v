(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general lemmas and tactics
*)

(* $Id: LogicUtil.v,v 1.11 2008-01-24 13:22:25 blanqui Exp $ *)

Set Implicit Arguments.

Require Export Setoid.

Definition prop_dec A (P : A -> Prop) := forall x, {P x}+{~P x}.

(***********************************************************************)
(** tactics *)

Ltac refl := reflexivity.

Ltac gen h := generalize h.

Ltac deduce h := gen h; intro.

Ltac decomp h := decompose [and or ex] h; clear h.

Ltac irrefl :=
  match goal with
    | _ : ?x <> ?x |- _ => absurd (x=x); [assumption | refl]
    | _ : ?x <> ?y, _ : ?x = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?y = ?x |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?x = ?z, _ : ?z = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?x = ?z, _ : ?y = ?z |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?z = ?x, _ : ?z = ?y |- _ => subst y; irrefl
    | _ : ?x <> ?y, _ : ?z = ?x, _ : ?y = ?z |- _ => subst y; irrefl
  end.

Ltac normalize e :=
  let x := fresh in set (x := e); vm_compute in x; subst x.

Ltac normalize_in H e :=
  let x := fresh in set (x := e) in H; vm_compute in x; subst x.

(***********************************************************************)
(** basic meta-theorems *)

Section meta.

Lemma contraposee_inv : forall P Q : Prop, (P -> Q) -> ~Q -> ~P.

Proof.
intros. intro. apply H0. exact (H H1).
Qed.

Variables (A : Type) (P : A -> Prop).

Lemma not_exists_imply_forall_not : ~(exists x, P x) -> forall x, ~P x.

Proof.
intros. intro. apply H. exists x. exact H0.
Qed.

Lemma forall_not_imply_not_exists : (forall x, ~(P x)) -> ~(exists x, P x).

Proof.
intros. intro. destruct H0. exact (H x H0).
Qed.

Lemma exists_not_imply_not_forall : (exists x, ~(P x)) -> ~(forall x, P x).

Proof.
intros. destruct H. intro. deduce (H0 x). contradiction.
Qed.

End meta.
