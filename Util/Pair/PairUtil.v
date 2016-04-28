(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-17

general results on pairs
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil.

Section S.

  Variables (A B : Type)
            (eqdecA : forall x y : A, {x=y}+{~x=y})
            (eqdecB : forall x y : B, {x=y}+{~x=y}).

  Lemma eq_pair_dec : forall x y : A*B, {x=y}+{~x=y}.

  Proof.
    intros (x1,x2) (y1,y2). case (eqdecA x1 y1); intro.
    subst y1. case (eqdecB x2 y2); intro. subst y2. auto.
    right. unfold not. intro. injection H. intro. cong.
    right. unfold not. intro. injection H. intros. cong.
  Qed.

End S.
