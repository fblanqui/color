(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2007-02-20

sub-relation, restriction, etc.
*)

From CoLoR Require Import ListShrink RelUtil ListUtil LogicUtil.

Set Implicit Arguments.

Section On_Rel_Gen.

  Variable A : Type.

  Section restriction.

    Variables (R : relation A) (l : list A).

    Definition restriction x y := In x l /\ In y l /\ R x y.

    Definition is_restricted := forall x y, R x y -> In x l /\ In y l.

    Lemma incl_restriction : restriction << R.

    Proof. unfold restriction. repeat intro. tauto. Qed.

    Lemma restriction_dec : eq_dec A -> rel_dec R -> rel_dec restriction.

    Proof.
      unfold restriction. intros H H0 x y. destruct (H0 x y).
      destruct (In_dec H x l). destruct (In_dec H y l). 
      constructor. tauto. constructor 2. tauto. constructor 2. tauto.
      constructor 2. tauto.
    Qed.

    Lemma restriction_midex :
      eq_midex A -> rel_midex R -> rel_midex restriction.

    Proof.
      unfold restriction. do 4 intro. destruct (H0 x y).
      destruct (In_midex H x l). destruct (In_midex H y l). 
      constructor. tauto. constructor 2. tauto. constructor 2. tauto.
      constructor 2. tauto.
    Qed.

  End restriction.

  Lemma restriction_monotonic : forall (R' R'' : relation A) l,
    R' << R'' -> restriction R' l << restriction R'' l.

  Proof. unfold restriction. repeat intro. pose (H x y). tauto. Qed.

  Lemma restricted_restriction : forall R l, is_restricted (restriction R l) l.

  Proof. unfold restriction, is_restricted. tauto. Qed.

  Lemma restricted_clos_trans : forall R l,
    is_restricted R l -> is_restricted (clos_trans R) l.

  Proof. unfold is_restricted. intros. induction H0. apply H. hyp. tauto. Qed. 

  Lemma clos_trans_restricted_pair : forall R x y,
    is_restricted R (x::y::nil) -> clos_trans R x y -> R x y.

  Proof.
    intros. induction H0. hyp. 
    destruct (restricted_clos_trans H H0_).
    destruct H1. rewrite H1 in H. rewrite H1. tauto.
    destruct H1. rewrite H1 in H. rewrite H1. tauto.
    contr.
  Qed.

  Lemma clos_trans_restricted_pair_bis : forall R x y,
    is_restricted R (x::y::nil) -> clos_trans R y x -> R y x.

  Proof.
    intros. induction H0. hyp. 
    destruct (restricted_clos_trans H H0_).
    destruct H1. rewrite H1 in H. rewrite H1. tauto.
    destruct H1. rewrite H1 in H. rewrite H1. tauto.
    contr.
  Qed.

  Lemma clos_trans_restriction : forall (R : relation A) x y,
    R x y -> clos_trans (restriction R (x :: y :: nil)) x y.

  Proof. intros. constructor. unfold restriction. simpl. tauto. Qed.

End On_Rel_Gen.
