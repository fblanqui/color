(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general lemmas and tactics
*)

(* $Id: LogicUtil.v,v 1.9 2008-01-16 14:52:20 blanqui Exp $ *)

Set Implicit Arguments.

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
(** dependent equality on decidable types *)

Require Export EqdepFacts.
Require Export Eqdep_dec.

Section eq_dep.

Variables (U : Type) (eq_dec : forall x y : U, {x=y}+{~x=y}).

Lemma eq_rect_eq : forall (p : U) Q x h, x = eq_rect p Q x p h.
  
Proof.
exact (eq_rect_eq_dec eq_dec).
Qed.

Lemma eq_dep_eq : forall P (p : U) x y, eq_dep U P p x p y -> x = y.

Proof.
exact (eq_rect_eq__eq_dep_eq U eq_rect_eq).
Qed.

Lemma UIP : forall (x y : U) (p1 p2 : x = y), p1 = p2.

Proof.
exact (eq_dep_eq__UIP U eq_dep_eq).
Qed.

Lemma UIP_refl : forall (x : U) (p : x = x), p = refl_equal x.

Proof.
exact (UIP__UIP_refl U UIP).
Qed.

Lemma Streicher_K :
  forall (x : U) (P : x = x -> Prop), P (refl_equal x) -> forall p, P p.

Proof.
exact (K_dec_type eq_dec).
Qed.

Lemma inj_pairT2 : forall P (p : U) x y, existT P p x = existT P p y -> x = y.

Proof.
exact (eq_dep_eq__inj_pairT2 U eq_dep_eq).
Qed.

Lemma inj_pairP2 :
  forall P (x : U) p q, ex_intro P x p = ex_intro P x q -> p = q.

Proof.
intros. apply inj_right_pair with (A:=U).
intros x0 y0; case (eq_dec x0 y0); [left|right]; assumption.
assumption.
Qed.

End eq_dep.

Implicit Arguments UIP_refl [U x].

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
