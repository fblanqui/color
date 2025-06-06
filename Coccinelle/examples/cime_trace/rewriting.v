From Stdlib Require Import Lia Relations Wellfounded.
From Stdlib Require Inclusion.
From CoLoR Require Import term.
From CoLoR Require equational_theory. (* mainly for one_step...*)

Notation "'SN'" := Acc.
Notation "'termine'" := well_founded.

Section Inclusion.
  Variable A : Type.
  Variable R1  R2 : A->A->Prop. 
  Hypothesis Incl : inclusion _ R1 R2.

  Theorem SN_incl : forall x : A , SN R2 x -> SN R1 x. 
    unfold transp.
    intros.
    eapply Inclusion.Acc_incl ; eauto.
  Qed.

  Theorem termine_incl : termine R2 -> termine R1. 
    unfold transp.
    intros.
    eapply Inclusion.wf_incl ; eauto.
  Qed.

End Inclusion.

Section Terminaison.
  Variable T:Type.
  Variable R: T -> T -> Prop.

  Declare Scope rewriting.
  
  Notation "T -R> U" := (R U T) (at level 80) : rewriting.

  Open Scope rewriting.

  Definition Retoile := clos_refl_trans _ R.

  Theorem no_infinite_sequence2 : forall x : T , SN R x ->
    ~(exists f : nat -> T , f 0 = x /\ forall i : nat , f i -R> f (i+1)) . 
    intros.
    induction H.
    intuition.
    elim H1.
    intros.
    apply (H0 (x0 1)).
    intuition.
    subst.
    apply (H4 0).
    exists ( fun i => (x0 (i+1))).
    intuition.
  Qed.
  
  Variable f : T -> nat.

  Hypothesis H_compat : forall x y: T, x -R> y -> f y < f x.

  Theorem termine_gt_compat : termine R.
  Proof.
    red .
    cut (forall n a, f a < n -> Acc R a).
    intros H a.
    apply (H (S (f a))); auto with arith.
    induction n.
    intros; absurd (f a < 0); auto with arith.
    intros a ltSma.
    apply Acc_intro.
    intros b ltfafb.
    apply IHn.
    assert (f b < f a).
    apply H_compat.
    trivial.
    lia.
  Qed.

  Inductive R2 (y x: T) : Prop :=
    R2_intro: forall (z:T), x -R> z -> z -R> y -> R2 y x.

  Lemma termineR2aux :
    termine R -> forall x, SN R2 x /\ (forall y, R y x -> SN R2 y).
    intros.
    apply Acc_ind 
      with (R:=R) (P:=fun x =>  (SN R2 x) /\ (forall y, R y x -> (SN R2 y))).
    intuition.
    apply Acc_intro.
    intros.
    elim H2.
    intros.
    generalize (H1 z H3).
    intuition.
    generalize (H1 y H2).
    intuition.
    apply H.
  Qed.

  Theorem termineR2 : termine R -> termine R2.
    intros rtermine.
    red.
    intros a.
    generalize (termineR2aux rtermine).
    intros hyp.
    decompose [and] (hyp a).
    auto.
  Qed.

End Terminaison.
