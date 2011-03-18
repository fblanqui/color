(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22

lemmas and tactics on Coq's FSets
*)

Set Implicit Arguments.

Require Import LogicUtil FSets FSetAVL FSetFacts RelUtil BoolUtil.

Module Make (X : OrderedType).

Module Export XSet := FSetAVL.Make X.
Module Export XSetEqProps := EqProperties XSet.
Module Export XSetProps := Properties XSet.
Module Export XSetFacts := Facts XSet.
Module Export XSetOrdProps := OrdProperties XSet.

Import X.

Lemma eqb_ok : forall x y, eqb x y = true <-> eq x y.

Proof.
intros x y. unfold eqb. destruct (eq_dec x y); intuition. discr.
Qed.

Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
Notation "s [<>] t" := (~Equal s t) (at level 70, no associativity).

Implicit Arguments remove_1 [s x y].
Implicit Arguments remove_3 [s x y].
Implicit Arguments singleton_1 [x y].
Implicit Arguments union_1 [s s' x].

Hint Rewrite union_assoc inter_assoc diff_inter_empty diff_inter_all
  : Equal.

Ltac Equal := autorewrite with Equal.

(***********************************************************************)
(** properties of is_empty *)

Lemma is_empty_eq : forall s, is_empty s = true <-> s [=] empty.

Proof.
intro s. split; intro hs.
apply empty_is_empty_1. rewrite is_empty_iff. hyp.
rewrite <- is_empty_iff. apply empty_is_empty_2. hyp.
Qed.

Lemma mem_is_empty {x s} : mem x s = true -> is_empty s = false.

Proof.
rewrite false_not_true. unfold not. rewrite <- is_empty_iff, <- mem_iff.
firstorder.
Qed.

(***********************************************************************)
(** properties of In *)

Lemma In_remove_neq : forall x y s, In x (remove y s) -> ~eq y x.

Proof.
unfold not. intros. apply (remove_1 H0 H).
Qed.

Lemma remove_3 : forall x y s, In x (remove y s) -> In x s /\ ~eq y x.

Proof.
intuition. apply (remove_3 H). ded (In_remove_neq H). contradiction.
Qed.

(***********************************************************************)
(** tactics for In, Equal and Subset *)

Ltac lft := apply union_2; try hyp.
Ltac rgt := apply union_3; try hyp.

Ltac Equal_intro := unfold Equal; intuition.
Ltac Subset_intro := unfold Subset; intuition.

Lemma remove_singleton : forall x, remove x (singleton x) [=] empty.

Proof.
Equal_intro. destruct (remove_3 H). ded (singleton_1 H0).
ded (remove_1 H2 H). contradiction. rewrite empty_iff in H. contradiction.
Qed.

Hint Rewrite remove_singleton : Equal.

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

(***********************************************************************)
(** lemmas and tactics for ~In *)

Lemma notin_union : forall x s s', ~In x (union s s') <-> ~In x s /\ ~In x s'.

Proof.
intuition. apply H. In_intro. apply H. In_intro. In_elim; intuition.
Qed.

Lemma notin_singleton : forall x y, ~In x (singleton y) <-> ~eq y x.

Proof.
intuition. ded (singleton_2 H0). apply H. hyp.
Qed.

Ltac notIn_elim := repeat
  match goal with
    | H : ~In _ (union _ _) |- _ => rewrite notin_union in H; destruct H
    | H : ~In _ (singleton _) |- _ => rewrite notin_singleton in H
  end.

(***********************************************************************)
(** more equalities *)

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

Lemma subset_empty : forall s, s [<=] empty -> s [=] empty.

Proof.
intros. rewrite double_inclusion. intuition.
Qed.

(***********************************************************************)
(** lemmas, hints and tactics on mem *)

Hint Rewrite empty_b singleton_b remove_b add_b union_b inter_b diff_b
  : mem.

Ltac mem := autorewrite with mem.

Lemma eqb_refl : forall x, eqb x x = true.

Proof.
intro. unfold eqb. case (eq_dec x x). refl.
intro. absurd (eq x x). exact n. apply eq_refl.
Qed.

Hint Rewrite eqb_refl : mem.

Lemma mem_In : forall x s, mem x s = true <-> In x s.

Proof.
intuition. apply mem_2. hyp.
Qed.

Lemma subset_Subset : forall s t, subset s t = true <-> Subset s t.

Proof.
intuition. apply subset_2. hyp.
Qed.

Lemma equal_Equal : forall s t, equal s t = true <-> Equal s t.

Proof.
intuition. apply equal_2. hyp.
Qed.

Lemma rel_equal_Equal : rel equal == Equal.

Proof.
apply rel_eq. apply equal_Equal.
Qed.

(***********************************************************************)
(** remove *)

Lemma remove_empty : forall x, remove x empty [=] empty.

Proof.
intros x y. split; intro H; In_elim.
Qed.

(***********************************************************************)
(** fold *)

Section fold.

  Variables (A : Type) (eqA : A->A->Prop) (heqA : Equivalence eqA).

  Definition feq f f' :=
    forall x x', eq x x' -> forall a a', eqA a a' -> eqA (f x a) (f' x' a').

  Global Instance feq_Sym : Symmetric eqA -> Symmetric feq.

  Proof.
    firstorder.
  Qed.

  Global Instance Proper_m' :
    Proper (feq ==> impl) (Proper (eq ==> eqA ==> eqA)).

  Proof.
    intros f f' ff' fm x x' xx' a a' aa'. transitivity (f x a).
    symmetry. apply ff'; refl. apply ff'; hyp.
  Qed.

  Global Instance Proper_m :
    Proper (feq ==> iff) (Proper (eq ==> eqA ==> eqA)).

  Proof.
    split; apply Proper_m'; auto. symmetry. hyp.
  Qed.

  Global Instance transpose_m : Proper (feq ==> impl) (transpose eqA).

  Proof.
    intros f f' ff' hf x y z. transitivity (f x (f y z)).
    symmetry. apply ff'. refl. apply ff'; refl.
    rewrite hf. apply ff'. refl. apply ff'; refl.
  Qed.

  Global Instance fold_m : forall f,
    Proper (eq ==> eqA ==> eqA) f -> Proper (Equal ==> eqA ==> eqA) (fold f).

  Proof.
    intros f f_m s s' ss' a a' aa'. transitivity (fold f s' a).
    apply fold_equal; hyp. apply fold_init; hyp.
  Qed.

  Lemma fold_m_ext : forall f,
    Proper (eq ==> eqA ==> eqA) f -> transpose eqA f ->
    forall f', feq f f' -> forall s s', s [=] s' -> forall a a', eqA a a' ->
      eqA (fold f s a) (fold f' s' a').

  Proof.
    intros f fm ft f' ff' s s' ss' a a' aa';
      gen aa'; gen a'; gen a; gen ss'; gen s'.
    pattern s; apply set_induction_bis; clear s.
    (* Equal *)
    intros s s' ss' h t s't a a' aa'. transitivity (fold f s a).
    apply fold_equal; auto. symmetry. hyp. apply h. transitivity s'; hyp. hyp.
    (* empty *)
    intros s' e a a' aa'. transitivity (fold f' empty a').
    hyp. apply fold_m; try hyp||refl. rewrite <- ff'. hyp.
    (* add *)
    intros x s nxs h s' e a a' aa'. transitivity (fold f' (add x s) a').
    repeat rewrite fold_add; unfold compat_op; try rewrite <- ff'; auto.
    apply ff'. refl. apply h. refl. hyp.
    apply fold_m; auto. rewrite <- ff'. hyp. refl.
  Qed.

End fold.
 
End Make.
