(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02

basic definitions on functions taking vectors as arguments
************************************************************************)

(* $Id: NaryFunction.v,v 1.1.1.1 2006-09-08 09:07:00 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export RelUtil.

Variables A : Set.

Require Export VecUtil.

Notation vec := (vector A).

Definition naryFunction n := vec n -> A.

Variables (n : nat) (f : naryFunction n).

Definition Vmonotone_i (R : relation A) i j (H : i + S j = n) :=
  forall vi vj, monotone R (fun z => f (Vcast (Vapp vi (Vcons z vj)) H)).

Implicit Arguments Vmonotone_i [i j].

Lemma Vmonotone_i_transp : forall R i j (H : i + S j = n),
  Vmonotone_i R H -> Vmonotone_i (transp R) H.

Proof.
unfold Vmonotone_i. intros R i j H H' vi vj. apply monotone_transp. apply H'.
Qed.

Definition Vmonotone R := forall i j (H : i + S j = n), Vmonotone_i R H.

Lemma Vmonotone_transp : forall R : relation A,
  Vmonotone R -> Vmonotone (transp R).

Proof.
unfold Vmonotone. intros R H i j H'. apply Vmonotone_i_transp. apply H.
Qed.

End S.

Implicit Arguments Vmonotone_i [A n i j].

(***********************************************************************)

Section preserv.

Variables (A : Set) (P : A->Prop) (n : nat) (f : naryFunction A n).

Definition preserv := forall v, Vforall P v -> P (f v).

Definition restrict (H : preserv) : naryFunction (sig P) n :=
  fun v => exist P (f (Vmap (@proj1_sig _ _) v)) (H _ (Vforall_of_vsig v)).

End preserv.
