(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22

lemmas and tactics on Coq's FSets
*)

(* $Id: FSetUtil.v,v 1.1 2008-05-15 14:43:57 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Require Import FSets.
Require Import FSetAVL.
Require Import FSetFacts.

Module Make (X: OrderedType). Export X.

Module XSet := FSetAVL.Make (X). Export XSet.
Module XSetEqProp := EqProperties (XSet). Export XSetEqProp.
Module XSetProp := Properties (XSet). Export XSetProp.
Module XSetFacts := Facts (XSet). Export XSetFacts.

(***********************************************************************)
(* lemmas and hints on Equal *)

Notation "s [=] t" := (Equal s t) (at level 70, no associativity).

Hint Rewrite union_assoc inter_assoc diff_inter_empty diff_inter_all
  : Equal.

Implicit Arguments remove_1 [s x y].
Implicit Arguments remove_3 [s x y].
Implicit Arguments singleton_1 [x y].
Implicit Arguments union_1 [s s' x].

Lemma In_remove_neq : forall x y s, In x (remove y s) -> ~E.eq y x.

Proof.
unfold not. intros. apply (remove_1 H0 H).
Qed.

Lemma remove_3 : forall x y s, In x (remove y s) -> In x s /\ ~E.eq y x.

Proof.
intuition. apply (remove_3 H). ded (In_remove_neq H). contradiction.
Qed.

Lemma remove_singleton : forall x, remove x (singleton x) [=] empty.

Proof.
unfold Equal. intuition. destruct (remove_3 H). ded (singleton_1 H0).
ded (remove_1 H2 H). contradiction. rewrite empty_iff in H. contradiction.
Qed.

Hint Rewrite remove_singleton : Equal.

Ltac lft := apply union_2; try hyp.
Ltac rgt := apply union_3; try hyp.

Ltac Equal_intro := unfold Equal; intuition.
Ltac Subset_intro := unfold Subset; intuition.

Ltac In_elim :=
  match goal with
    | H : In _ (union _ _) |- _ => destruct (union_1 H); clear H; In_elim
    | H : In _ (remove _ _) |- _ => destruct (remove_3 H); clear H; In_elim
    | _ => idtac
  end.

Ltac In_intro :=
  match goal with
    | |- In _ (singleton _) => apply singleton_2; refl
    | |- In _ (union _ _) =>
      (apply union_2; In_intro) || (apply union_3; In_intro)
    | |- In _ (remove _ _) => apply remove_2; [hyp | In_intro]
    | _ => hyp
  end.

Ltac Equal := Equal_intro; In_elim; try In_intro.
Ltac Subset := Subset_intro; In_elim; try In_intro.

Lemma union_empty_left : forall s, union empty s [=] s.

Proof.
Equal. rewrite empty_iff in H0. contradiction.
Qed.

Lemma union_empty_right : forall s, union s empty [=] s.

Proof.
Equal. rewrite empty_iff in H0. contradiction.
Qed.

Hint Rewrite union_empty_left union_empty_right : Equal.

Lemma remove_union : forall x s s',
  remove x (union s s') [=] union (remove x s) (remove x s').

Proof.
Equal.
Qed.

Hint Rewrite remove_union : Equal.

Lemma union_idem : forall s t, union s (union s t) [=] union s t.

Proof.
Equal.
Qed.

Hint Rewrite union_idem : Equal.

Lemma union_idem_2 : forall s t u,
  union s (union t (union s u)) [=] union s (union t u).

Proof.
Equal.
Qed.

Lemma union_idem_3 : forall s t u,
  union (union s t) (union s u) [=] union s (union t u).

Proof.
Equal.
Qed.

Lemma union_sym_2 : forall s t u, union s (union t u) [=] union t (union s u).

Proof.
Equal.
Qed.

(***********************************************************************)
(* lemmas and hints on mem *)

Hint Rewrite empty_b singleton_b remove_b add_b union_b inter_b diff_b
  : mem.

Lemma eqb_refl : forall x, ME.eqb x x = true.

Proof.
intro. unfold ME.eqb. case (ME.eq_dec x x). refl.
intro. absurd (E.eq x x). exact n. apply E.eq_refl.
Qed.

Hint Rewrite eqb_refl : mem.

End Make.
