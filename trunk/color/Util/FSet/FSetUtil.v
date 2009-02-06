(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22

lemmas and tactics on Coq's FSets
*)

Set Implicit Arguments.

Require Import LogicUtil.

Require Import FSets.
Require Import FSetAVL.
Require Import FSetFacts.

Module Make (X : OrderedType). Export X.

Module XSet := FSetAVL.Make (X). Export XSet.
Module XSetEqProp := EqProperties (XSet). Export XSetEqProp.
Module XSetProp := Properties (XSet). Export XSetProp.
Module XSetFacts := Facts (XSet). Export XSetFacts.

(***********************************************************************)
(* lemmas and hints on Equal *)

Notation "s [=] t" := (Equal s t) (at level 70, no associativity).

Hint Rewrite union_assoc inter_assoc diff_inter_empty diff_inter_all
  : Equal.

Ltac Equal := autorewrite with Equal.

Implicit Arguments remove_1 [s x y].
Implicit Arguments remove_3 [s x y].
Implicit Arguments singleton_1 [x y].
Implicit Arguments union_1 [s s' x].

Lemma In_remove_neq : forall x y s, In x (remove y s) -> ~X.eq y x.

Proof.
unfold not. intros. apply (remove_1 H0 H).
Qed.

Lemma remove_3 : forall x y s, In x (remove y s) -> In x s /\ ~X.eq y x.

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

Ltac In_elim := repeat
  match goal with
    | H : In ?x (singleton _) |- _ => ded (singleton_1 H); subst x; clear H
    | H : In _ (union _ _) |- _ => destruct (union_1 H); clear H
    | H : In _ (remove _ _) |- _ => destruct (remove_3 H); clear H
    | H : In _ empty |- _ => rewrite empty_iff in H; contradiction
  end.

Ltac In_intro :=
  match goal with
    | |- In _ (singleton _) => apply singleton_2; refl
    | |- In _ (union _ _) =>
      (apply union_2; In_intro) || (apply union_3; In_intro)
    | |- In _ (remove _ _) => apply remove_2; [hyp | In_intro]
    | _ => hyp
  end.

Ltac Equal_tac := Equal_intro; In_elim; try In_intro.
Ltac Subset_tac := Subset_intro; In_elim; try In_intro.

Lemma notin_union : forall x s s', ~In x (union s s') <-> ~In x s /\ ~In x s'.

Proof.
intuition. apply H. In_intro. apply H. In_intro. In_elim; intuition.
Qed.

Lemma notin_singleton : forall x y, ~In x (singleton y) <-> ~X.eq y x.

Proof.
intuition. ded (singleton_2 H0). apply H. hyp.
ded (singleton_1 H0). apply H. hyp.
Qed.

Ltac notIn_elim := repeat
  match goal with
    | H : ~In _ (union _ _) |- _ => rewrite notin_union in H; destruct H
    | H : ~In _ (singleton _) |- _ => rewrite notin_singleton in H
  end.

Lemma union_empty_left : forall s, union empty s [=] s.

Proof.
Equal_tac.
Qed.

Lemma union_empty_right : forall s, union s empty [=] s.

Proof.
Equal_tac.
Qed.

Hint Rewrite union_empty_left union_empty_right : Equal.

Lemma remove_union : forall x s s',
  remove x (union s s') [=] union (remove x s) (remove x s').

Proof.
Equal_tac.
Qed.

Hint Rewrite remove_union : Equal.

Lemma union_idem : forall s, union s s [=] s.

Proof.
Equal_tac.
Qed.

Hint Rewrite union_idem : Equal.

Lemma union_idem_1 : forall s t, union s (union s t) [=] union s t.

Proof.
Equal_tac.
Qed.

Hint Rewrite union_idem_1 : Equal.

Lemma union_idem_2 : forall s t u,
  union s (union t (union s u)) [=] union s (union t u).

Proof.
Equal_tac.
Qed.

Hint Rewrite union_idem_2 : Equal.

Lemma union_idem_3 : forall s t u,
  union (union s t) (union s u) [=] union s (union t u).

Proof.
Equal_tac.
Qed.

Hint Rewrite union_idem_3 : Equal.

Lemma union_sym_2 : forall s t u, union s (union t u) [=] union t (union s u).

Proof.
Equal_tac.
Qed.

(***********************************************************************)
(* lemmas and hints on mem *)

Hint Rewrite empty_b singleton_b remove_b add_b union_b inter_b diff_b
  : mem.

Ltac mem := autorewrite with mem.

Lemma eqb_refl : forall x, eqb x x = true.

Proof.
intro. unfold eqb. case (eq_dec x x). refl.
intro. absurd (X.eq x x). exact n. apply X.eq_refl.
Qed.

Hint Rewrite eqb_refl : mem.

Lemma mem_In : forall x s, mem x s = true <-> In x s.

Proof.
intuition. apply mem_2. hyp. apply mem_1. hyp.
Qed.

Lemma subset_Subset : forall s t, subset s t = true <-> Subset s t.

Proof.
intuition. apply subset_2. hyp. apply subset_1. hyp.
Qed.

Lemma equal_Equal : forall s t, equal s t = true <-> Equal s t.

Proof.
intuition. apply equal_2. hyp. apply equal_1. hyp.
Qed.

End Make.
