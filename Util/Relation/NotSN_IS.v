(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-08-08

~SN terms give infinite sequences (using classical logic and dependent choice)
*)

Set Implicit Arguments.

Require Import DepChoice NotSN SN RelUtil LogicUtil.

Section S.

  Variables (A : Type) (R : relation A).

  Lemma notSN_NT : forall a, ~SN R a -> NT R a.

  Proof.
    intros a h. set (P := fun x => ~SN R x). set (B := sig P).
    set (T := Rof R (@proj1_sig A P)). assert (forall x, exists y, T x y).
    intro. destruct x. unfold T. simpl. ded (notSN_succ p). decomp H.
    exists (exist P x0 H2). hyp.
    set (b := exist P a h). ded (@dep_choice _ b _ H). destruct H0 as [g Hg].
    set (f := fun x => proj1_sig (g x)). exists f. split; unfold f; auto.
    rewrite (proj2 Hg). refl.
    intro. ded (proj1 Hg i). destruct (g i). destruct (g (S i)). hyp.
  Qed.

  Require Import ClassicUtil.

  Lemma notNT_SN : forall a, ~NT R a -> SN R a.

  Proof.
    intros a ha. apply NNPP. intro h. ded (notSN_NT h). contr.
  Qed.

  Lemma notWF_EIS : ~WF R -> EIS R.

  Proof.
    unfold EIS, WF. rewrite not_forall_eq. intros [a h].
    destruct (notSN_NT h). exists x. intuition.
  Qed.

End S.
