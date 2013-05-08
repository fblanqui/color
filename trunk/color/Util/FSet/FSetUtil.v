(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22

* Lemmas and tactics extending Coq's library FSet.
*)

Set Implicit Arguments.

Require Import LogicUtil FSets FSetFacts RelUtil BoolUtil.

Module Make (Export XSet : FSetInterface.S).

  Module Export XSetEqProps := EqProperties XSet.
  Module Export XSetProps := Properties XSet.
  Module Export XSetFacts := Facts XSet.
  Module Export XSetOrdProps := OrdProperties XSet.

  Notation "s [=] t" := (Equal s t) (at level 70, no associativity).
  Notation "s [<=] t" := (Subset s t) (at level 70, no associativity).
  Notation "s [<>] t" := (~Equal s t) (at level 70, no associativity).

  Implicit Arguments remove_1 [s x y].
  Implicit Arguments remove_3 [s x y].
  Implicit Arguments singleton_1 [x y].
  Implicit Arguments union_1 [s s' x].

(***********************************************************************)
(** database of Equal-ity lemmas. *)

  Hint Rewrite union_assoc inter_assoc diff_inter_empty diff_inter_all
    : Equal.

  Ltac Equal := autorewrite with Equal.

(***********************************************************************)
(** database of equality lemmas on [mem]. *)

  Hint Rewrite empty_b singleton_b remove_b add_b union_b inter_b diff_b
    : mem.

  Ltac mem := autorewrite with mem.

(***********************************************************************)
(** Tactic putting a set built from intersections and unions into a
"disjunctive normal form", i.e. a union of intersections. *)

  Ltac dnf := repeat
    match goal with
      | |- context [inter (union ?a _) _] => rewrite union_inter_1 with (s:=a)
      | |- context [inter ?a (union _ _)] =>
        rewrite inter_sym with (s:=a); rewrite union_inter_1 with (s'':=a)
    end.

(***********************************************************************)
(** boolean equality on [X] *)

  Lemma eqb_ok : forall x y, eqb x y = true <-> E.eq x y.

  Proof. intros x y. unfold eqb. destruct (eq_dec x y); intuition. discr. Qed.

  Lemma eqb_refl : forall x, eqb x x = true.

  Proof.
    intro x. unfold eqb. destruct (eq_dec x x). refl. absurd (x=x); auto.
  Qed.

  Hint Rewrite eqb_refl : mem.

  Lemma eqb_sym : forall x y, eqb x y = eqb y x.

  Proof. intros x y. apply eqb_equiv. repeat rewrite eqb_ok. fo. Qed.

(***********************************************************************)
(** empty *)

  Lemma is_empty_eq : forall s, is_empty s = true <-> s [=] empty.

  Proof.
    intro s. split; intro hs.
    apply empty_is_empty_1. rewrite is_empty_iff. hyp.
    rewrite <- is_empty_iff. apply empty_is_empty_2. hyp.
  Qed.

  Lemma mem_is_empty {x s} : mem x s = true -> is_empty s = false.

  Proof.
    rewrite false_not_true. unfold not. rewrite <- is_empty_iff, <- mem_iff.
    fo.
  Qed.

  Lemma subset_empty : forall s, s [<=] empty -> s [=] empty.

  Proof. intros. rewrite double_inclusion. intuition. Qed.

  Lemma empty_subset : forall s, s [=] empty <-> s [<=] empty.

  Proof. intuition. Qed.

(***********************************************************************)
(** remove *)

  Lemma In_remove_neq : forall x y s, In x (remove y s) -> ~E.eq y x.

  Proof. intros x y s. set_iff. tauto. Qed.

  Lemma remove_3 : forall x y s, In x (remove y s) -> In x s /\ ~E.eq y x.

  Proof. intros x y s. set_iff. tauto. Qed.

  Lemma remove_singleton : forall x, remove x (singleton x) [=] empty.

  Proof. intros x y. set_iff. tauto. Qed.

  Hint Rewrite remove_singleton : Equal.

  Lemma remove_union : forall x s s',
    remove x (union s s') [=] union (remove x s) (remove x s').

  Proof. intros x s s' y. set_iff. tauto. Qed.

  Hint Rewrite remove_union : Equal.

  Lemma remove_empty : forall x, remove x empty [=] empty.

  Proof. intros x y. set_iff. tauto. Qed.

(***********************************************************************)
(** Subset *)

  Lemma Subset_antisym : forall s t, s [=] t <-> (s [<=] t /\ t [<=] s).

  Proof. intuition. Qed.

(***********************************************************************)
(** ~In *)

  Lemma notin_union : forall x s s', ~In x (union s s') <-> ~In x s /\ ~In x s'.

  Proof. intros x s s'. set_iff. tauto. Qed.

  Lemma notin_singleton : forall x y, ~In x (singleton y) <-> ~E.eq y x.

  Proof. intros x y. set_iff. refl. Qed.

  Ltac notIn_elim := repeat
    match goal with
      | H : ~In _ (union _ _) |- _ => rewrite notin_union in H; destruct H
      | H : ~In _ (singleton _) |- _ => rewrite notin_singleton in H
    end.

(***********************************************************************)
(** union *)

  Lemma union_empty_l : forall s, union empty s [=] s.

  Proof. intros s x. set_iff. tauto. Qed.

  Hint Rewrite union_empty_l : Equal.

  Lemma union_empty_r : forall s, union s empty [=] s.

  Proof. intros s x. set_iff. tauto. Qed.

  Hint Rewrite union_empty_r : Equal.

  Lemma union_idem : forall s, union s s [=] s.

  Proof. intros s x. set_iff. tauto. Qed.

  Hint Rewrite union_idem : Equal.

  Lemma union_idem_1 : forall s t, union s (union s t) [=] union s t.

  Proof. intros s t x. set_iff. tauto. Qed.

  Hint Rewrite union_idem_1 : Equal.

  Lemma union_idem_2 : forall s t u,
    union s (union t (union s u)) [=] union s (union t u).

  Proof. intros s t u x. set_iff. tauto. Qed.

  Hint Rewrite union_idem_2 : Equal.

  Lemma union_idem_3 : forall s t u,
    union (union s t) (union s u) [=] union s (union t u).

  Proof. intros s t u x. set_iff. tauto. Qed.

  Hint Rewrite union_idem_3 : Equal.

  Lemma union_sym_2 : forall s t u, union s (union t u) [=] union t (union s u).

  Proof. intros s t u x. set_iff. tauto. Qed.

  Lemma union_empty : forall a b,
    union a b [=] empty <-> a [=] empty /\ b [=] empty.

  Proof.
    intros a b. repeat rewrite empty_subset. split; intro h.
    split; trans (union a b).
    apply union_subset_1. hyp. apply union_subset_2. hyp.
    apply union_subset_3; tauto.
  Qed.

  Lemma union_empty_subset : forall a b,
    union a b [<=] empty <-> (a [<=] empty /\ b [<=] empty).

  Proof. intros a b. repeat rewrite <- empty_subset. apply union_empty. Qed.

(***********************************************************************)
(** difference *)

  Lemma diff_union : forall a b c,
    diff (union a b) c  [=] union (diff a c) (diff b c).

  Proof. intros a b c x. set_iff. tauto. Qed.

(***********************************************************************)
(** intersection *)

  Lemma inter_empty_l : forall a, inter empty a [=] empty.

  Proof. intros a x. set_iff. tauto. Qed.

  Lemma inter_empty_r : forall a, inter a empty [=] empty.

  Proof. intros a x. set_iff. tauto. Qed.

  Lemma inter_empty : forall a b,
    inter a b [=] empty <-> (forall x, In x a -> ~In x b). 

  Proof.
    intros a b. split; intro h.
    intros x h1 h2. rewrite <- empty_iff with (x:=x), <- h. apply inter_3; hyp.
    intro x. set_iff. fo.
  Qed.

(***********************************************************************)
(** some equivalences *)

  Lemma mem_In : forall x s, mem x s = true <-> In x s.

  Proof. intuition. Qed.

  Lemma subset_Subset : forall s t, subset s t = true <-> Subset s t.

  Proof. intuition. Qed.

  Lemma equal_Equal : forall s t, equal s t = true <-> Equal s t.

  Proof. intuition. Qed.

  Lemma rel_equal_Equal : rel equal == Equal.

  Proof. apply rel_eq. apply equal_Equal. Qed.

  Lemma mem_if : forall x xs (b : bool),
    mem x (if b then xs else empty) = b && mem x xs.

  Proof. intros x xs b. destruct b; simpl. refl. rewrite empty_b. refl. Qed.

(***********************************************************************)
(** Compatibility of set operations wrt inclusion. *)

  Instance add_s : Proper (E.eq ==> Subset ==> Subset) add.

  Proof. intros x y xy s t st z. rewrite xy, st. auto. Qed.

  Instance inter_s : Proper (Subset ==> Subset ==> Subset) inter.

  Proof. intros a a' aa' b b' bb' x. set_iff. rewrite aa', bb'. auto. Qed.

  Instance union_s : Proper (Subset ==> Subset ==> Subset) union.

  Proof. intros a a' aa' b b' bb' x. set_iff. rewrite aa', bb'. auto. Qed.

  Instance diff_s : Proper (Subset ==> Subset --> Subset) diff.

  Proof. intros a a' aa' b b' b'b x. set_iff. rewrite aa', b'b. auto. Qed.

(***********************************************************************)
(** fold *)

  Section fold.

    Variables (A : Type) (eqA : A->A->Prop) (heqA : Equivalence eqA).

    Definition feq f f' :=
      forall x x', E.eq x x' -> forall a a', eqA a a' -> eqA (f x a) (f' x' a').

    Global Instance feq_Sym : Symmetric eqA -> Symmetric feq.

    Proof. fo. Qed.

    Global Instance Proper_m' :
      Proper (feq ==> impl) (Proper (E.eq ==> eqA ==> eqA)).

    Proof.
      intros f f' ff' fm x x' xx' a a' aa'. trans (f x a).
      sym. apply ff'; refl. apply ff'; hyp.
    Qed.

    Global Instance Proper_m :
      Proper (feq ==> iff) (Proper (E.eq ==> eqA ==> eqA)).

    Proof. split; apply Proper_m'; auto. sym. hyp. Qed.

    Global Instance transpose_m : Proper (feq ==> impl) (transpose eqA).

    Proof.
      intros f f' ff' hf x y z. trans (f x (f y z)).
      sym. apply ff'. refl. apply ff'; refl.
      rewrite hf. apply ff'. refl. apply ff'; refl.
    Qed.

    Global Instance fold_m : forall f, Proper (E.eq ==> eqA ==> eqA) f ->
      Proper (Equal ==> eqA ==> eqA) (fold f).

    Proof.
      intros f f_m s s' ss' a a' aa'. trans (fold f s' a).
      apply fold_equal; hyp. apply fold_init; hyp.
    Qed.

    Lemma fold_m_ext : forall f, Proper (E.eq ==> eqA ==> eqA) f ->
      transpose eqA f ->
      forall f', feq f f' -> forall s s', s [=] s' -> forall a a', eqA a a' ->
        eqA (fold f s a) (fold f' s' a').

    Proof.
      intros f fm ft f' ff' s s' ss' a a' aa'; revert s' ss' a a' aa'.
      pattern s; apply set_induction_bis; clear s.
      (* Equal *)
      intros s s' ss' h t s't a a' aa'. trans (fold f s a).
      apply fold_equal; auto. sym. hyp. apply h. trans s'; hyp. hyp.
      (* empty *)
      intros s' e a a' aa'. trans (fold f' empty a').
      rewrite 2!fold_empty. hyp.
      apply fold_m; try hyp||refl. rewrite <- ff'. hyp.
      (* add *)
      intros x s nxs h s' e a a' aa'. trans (fold f' (add x s) a').
      repeat rewrite fold_add; unfold compat_op; try rewrite <- ff'; auto.
      apply ff'. refl. apply h. refl. hyp.
      apply fold_m; auto. rewrite <- ff'. hyp. refl.
    Qed.

  End fold.

End Make.
