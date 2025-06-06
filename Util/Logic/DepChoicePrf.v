(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

proof of dependent choice in classical logic + axiom of choice
*)

Set Implicit Arguments.

From Stdlib Require Import ClassicalChoice.
From CoLoR Require Import RelUtil LogicUtil.

Section S.

  Variables (A : Type) (a : A) (R : relation A) (h : left_total R).

  Definition next_elt x := proj1_sig (h x).

  Inductive G : nat -> A -> Prop :=
  | G0 : G 0 a
  | GS : forall i x, G i x -> G (S i) (next_elt x).

  Lemma G_is_classic_left_total : classic_left_total G.

  Proof.
    intro. elim x. exists a. exact G0.
    intros. destruct H. exists (next_elt x0). exact (GS H).
  Qed.

  Lemma G_is_functional : functional G.

  Proof.
    unfold functional. induction x; intros; inversion H; inversion H0.
    subst y. subst z. refl. rewrite (IHx _ _ H2 H5). refl.
  Qed.

  Lemma choice_imply_dep_choice : exists f, IS R f.

  Proof.
    destruct (choice G G_is_classic_left_total) as [f H]. exists f.
    assert (forall i x, G i x -> x = f i). intros. ded (H i).
    exact (G_is_functional H0 H1).
    assert (f 0 = a). ded (H 0). inversion H1. refl.
    assert (forall i, f (S i) = next_elt (f i)). induction i.
    ded (H 1). inversion H2. inversion H5. rewrite H1. subst x. refl.
    ded (H (S (S i))). inversion H2. ded (H0 _ _ H5). subst x. refl.
    intro. rewrite H2. exact (proj2_sig (h (f i))).
  Qed.

End S.
