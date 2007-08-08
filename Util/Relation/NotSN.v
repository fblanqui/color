(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

properties of ~SN terms (using classical logic)
*)

(* $Id: NotSN.v,v 1.1 2007-08-08 09:33:43 blanqui Exp $ *)

Set Implicit Arguments.

Require Export ClassicUtil.
Require Export SN.

Section S.

Variables (A : Type) (R : relation A) (x : A) (h : ~SN R x).

Lemma notSN_succ : exists y, R x y /\ ~SN R y.

Proof.
cut (~(forall y, R x y -> SN R y)).
intro. deduce (not_forall_imply_exists_not H). destruct H0.
deduce (imply_to_and _ _ H0). exists x0. auto.
eapply contraposee_inv. apply SN_intro. exact h.
Qed.

End S.
