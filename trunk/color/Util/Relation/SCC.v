(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

Strongly Connected Components (SCC) of a graph seen as a relation
*)

Set Implicit Arguments.

From CoLoR Require Import Cycle Path ListUtil RelUtil LogicUtil.

Section S.

  Variable A : Type.

  Section definition.

    Variable R : relation A.

(** Definition of SCC seen as a relation : are x and y in the same SCC ? *) 

    Definition SCC x y := R! x y /\ R! y x.

(** Basic properties *)

    Lemma SCC_trans : forall x y z, SCC x y -> SCC y z -> SCC x z.

    Proof.
      intros. unfold SCC in *. destruct H; destruct H0.
      split; eapply t_trans; eauto; auto.
    Qed.

    Lemma SCC_sym : forall x y, SCC x y -> SCC y x.

    Proof. intros. unfold SCC in *. destruct H; split; hyp. Qed.

    Lemma cycle_in_SCC : forall x l, cycle R x l -> forall y, In y l -> SCC x y.

    Proof.
      intros. unfold SCC. unfold cycle in H.
      gen (in_elim H0); intros.
      destruct H1; destruct H1; subst.
      apply path_app_elim in H.
      destruct H.
      apply path_clos_trans in H; apply path_clos_trans in H1.
      split; auto.
    Qed.

    Lemma SCC_in_cycle : forall x y, SCC x y -> exists l, cycle R x l /\ In y l.

    Proof.
      intros.
      destruct H.
      apply clos_trans_path in H; apply clos_trans_path in H0.
      destruct H; destruct H0.
      exists (x0++y::x1).
      split; auto with *.
      unfold cycle.
      apply path_app; auto.
    Qed.

    Lemma cycle_in_SCC_bound : forall x l, cycle R x l -> SCC x x.

    Proof.
      intros; unfold SCC; unfold cycle in H.
      split; apply path_clos_trans in H; auto.
    Qed.

  End definition.

  Section inclusion.

    Variables R1 R2 : relation A.

    Lemma SCC_incl : R1 << R2 -> SCC R1 << SCC R2.

    Proof.
      intros.
      unfold inclusion; unfold SCC.
      intros.
      destruct H0.
      assert (R1! << R2!).
      apply tc_incl; hyp.
      split; unfold inclusion in H2.
      apply (H2 x y); hyp.
      apply (H2 y x); hyp.
    Qed.

  End inclusion.

End S.
