(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

finitely branching well-founded relations have no infinite sequences
*)

Set Implicit Arguments.

Require Import RelUtil.
Require Import RedLength.
Require Import SN.
Require Import LogicUtil.

Section S.

Variables (A : Type) (R : relation A) (FB : finitely_branching R).

Section false.

Variable WF : WF R.

Notation len := (len FB WF).

Lemma WF_notIS : forall f, IS R f -> False.

Proof.
intros. assert (forall i, len (f i) + i <= len (f 0)).
induction i; intros. omega.
assert (len (f i) > len (f (S i))). apply R_len. apply H. omega.
ded (H0 (S (len (f 0)))). omega.
Qed.

End false.

Lemma IS_notWF : non_terminating R -> ~WF R.

Proof.
unfold not. intros. destruct H. eapply WF_notIS. hyp. apply H.
Qed.

End S.