(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

~SN terms give infinite sequences (using classical logic and dependent choice)
*)

Set Implicit Arguments.

Require Import DepChoice.
Require Import NotSN.
Require Import SN.
Require Import RelUtil.
Require Import LogicUtil.

Section S.

Variables (A : Type) (R : relation A) (a : A) (h : ~SN R a).

Lemma notSN_IS : exists f, IS R f /\ f 0 = a.

Proof.
set (P := fun x => ~SN R x). set (B := sig P).
set (T := Rof R (@proj1_sig A P)). assert (forall x, exists y, T x y).
intro. destruct x. unfold T. simpl. ded (notSN_succ p). decomp H.
exists (exist P x0 H2). simpl. exact H1.
set (b := exist P a h). ded (@dep_choice B b T H). destruct H0 as [g Hg].
set (f := fun x => proj1_sig (g x)). exists f. split; unfold f; auto.
intro. ded (proj1 Hg i). destruct (g i). destruct (g (S i)). unfold T in H0.
simpl in H0. exact H0.
rewrite (proj2 Hg). simpl; refl.
Qed.

End S.
