(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

~SN terms give infinite sequences (using classical logic and dependent choice)
*)

(* $Id: NotSN_IS.v,v 1.2 2008-05-14 12:26:56 blanqui Exp $ *)

Set Implicit Arguments.

Require Export DepChoice.
Require Export NotSN.

Section S.

Variables (A : Type) (R : relation A) (a : A) (h : ~SN R a).

Lemma notSN_IS : exists f, IS R f.

Proof.
set (P := fun x => ~SN R x). set (B := sig P). set (T := Rof R (@proj1_sig A P)).
assert (forall x, exists y, T x y).
intro. destruct x. unfold T. simpl. ded (notSN_succ p). decomp H.
exists (exist P x0 H2). simpl. exact H1.
set (b := exist P a h). ded (@dep_choice B b T H). destruct H0 as [g].
set (f := fun x => proj1_sig (g x)). exists f. intro. unfold f.
ded (H0 i). destruct (g i). destruct (g (S i)). unfold T in H1. simpl in H1.
exact H1.
Qed.

End S.
