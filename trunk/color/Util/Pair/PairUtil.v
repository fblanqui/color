(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-17

general results on pairs
************************************************************************)

(* $Id: PairUtil.v,v 1.1.1.1 2006-09-08 09:07:00 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export EqUtil.

Section S.

Variables (A B : Set) (eqdecA : dec_eq A) (eqdecB : dec_eq B).

Notation pair := (prod A B).

Lemma eq_pair_dec : dec_eq pair.

Proof.
unfold dec_eq. intros (x1,x2) (y1,y2).
case (eqdecA x1 y1); intro. subst y1. case (eqdecB x2 y2); intro. subst y2. auto.
right. unfold not. intro. injection H. intro. irrefl.
right. unfold not. intro. injection H. intros. irrefl.
Qed.

End S.
