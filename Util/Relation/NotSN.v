(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

properties of ~SN terms (using classical logic)
*)

Set Implicit Arguments.

From Stdlib Require Import Relations.
From CoLoR Require Import ClassicUtil SN LogicUtil.

Section S.

  Variables (A : Type) (R : relation A) (x : A) (h : ~SN R x).

  Lemma notSN_succ : exists y, R x y /\ ~SN R y.

  Proof.
    cut (~(forall y, R x y -> SN R y)).
    intro. ded (not_forall_imply_exists_not H). destruct H0.
    ded (imply_to_and _ _ H0). exists x0. auto.
    eapply contraposee_inv. apply SN_intro. exact h.
  Qed.

End S.
