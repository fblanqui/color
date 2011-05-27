(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2011-01-17

Axiom stating the equivalence between SN and ~NT.

Note however that:

- In IS_NotSN_FB, it is proved that, if R is finitely branching, then:
    WF R -> (forall f, ~IS R f)

We could use this for proving:
  SN R x -> ~NT R x

by taking the set of reducts of x for A.

- In NotSN_IS, it is proved under the axiom of dependent choice
(DepChoice) and using classical logic that:
  SN R x <- ~NT R x
    WF R <- (forall f, ~IS R f)
*)

Set Implicit Arguments.

Require Import RelUtil SN.

Axiom SN_notNT : forall A (R : relation A) x, SN R x <-> ~NT R x.

Require Import LogicUtil.

Lemma WF_notIS : forall A (R : relation A), WF R <-> forall f, ~IS R f.

Proof.
intros A R. split.
intros wf f hf. ded (wf (f 0)). rewrite SN_notNT in H. apply H. exists f. auto.
intros h x. rewrite SN_notNT. intros [f [h0 hf]]. eapply h. apply hf.
Qed.

Require Import ClassicUtil.

Lemma notWF_IS : forall A (R : relation A), ~WF R <-> exists f, IS R f.

Proof.
intros A R. rewrite WF_notIS. rewrite not_forall_eq.
intuition; destruct H as [f hf]; exists f. apply NNPP. hyp. auto.
Qed.
