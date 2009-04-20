(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Solange Coupet-Grimal and William Delobel, 2006-01-09

useful results on accessibility
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import RelUtil.
Require Export Wellfounded.

Implicit Arguments wf_incl [A R1 R2].

(***********************************************************************)
(** transitive closure *)

Section rtc.

Variables (A : Type) (R : relation A).

Lemma Acc_rtc : forall x y, clos_refl_trans R x y -> Acc R y -> Acc R x.

Proof.
induction 1.
intro. eapply Acc_inv. apply H0. assumption.
auto.
intro. apply IHclos_refl_trans1. apply IHclos_refl_trans2. assumption.
Qed.

Lemma Acc_tc_ind : forall P : A->Prop,
  (forall x, (forall y, clos_trans R y x -> P y) -> P x)
  -> forall x, Acc R x -> P x.

Proof.
intros. eapply Acc_ind with (R := clos_trans R). clear x H0. intros.
apply H. intros. apply H1. assumption.
apply Acc_clos_trans. assumption.
Qed.

End rtc.

(***********************************************************************)
(** symmetric product *)

Section symprod.

Variable A : Type.
Variable B : Type.
Variable leA : A -> A -> Prop.
Variable leB : B -> B -> Prop.

Notation Symprod := (symprod A B leA leB).

Lemma Acc_symprod_fst : forall x, Acc Symprod x -> Acc leA (fst x).

Proof.
induction 1. destruct x. simpl. apply Acc_intro. intros. ded (H0 (y,b)).
apply H2. apply left_sym. assumption.
Qed.

Lemma Acc_symprod_snd : forall x, Acc Symprod x -> Acc leB (snd x).

Proof.
induction 1. destruct x. simpl. apply Acc_intro. intros. ded (H0 (a,y)).
apply H2. apply right_sym. assumption.
Qed.

Lemma Acc_symprod_invl : forall x y, Acc Symprod (x,y) -> Acc leA x.

Proof.
intros. ded (Acc_symprod_fst H). assumption.
Qed.

Lemma Acc_symprod_invr : forall x y, Acc Symprod (x,y) -> Acc leB y.

Proof.
intros. ded (Acc_symprod_snd H). assumption.
Qed.

Lemma Acc_symprod_inv : forall x y, Acc Symprod (x,y) -> Acc leA x /\ Acc leB y.

Proof.
intros. split. eapply Acc_symprod_invl. apply H. eapply Acc_symprod_invr.
apply H.
Qed.

End symprod.

(***********************************************************************)
(** restricted accessibility *)

Section RestrictedAcc.

  Variable A : Type.
  Variable P : A -> Prop.

  Inductive Restricted_acc (R : relation A) : A -> Prop :=
    | Restricted_acc_cons : forall a, 
      (forall a', P a' -> R a' a -> Restricted_acc R a') -> Restricted_acc R a.

  Lemma Restricted_acc_eq_acc : forall (R : relation A) a,
    (Acc (fun a a' => P a /\ R a a') a) <-> Restricted_acc R a.

  Proof.
    intros R a.
    split.
    (* => *)
    intro acc_a; induction acc_a as [a acc_a IHa].
    constructor; trivial.
    intros a' Pa' Ha'.
    apply IHa; split; trivial.
    (* <= *)
    intro Raa; induction Raa as [a Raa IHa].
    constructor.
    intros a' Ha'; elim Ha'; clear Ha'; intros Pa' Ra'a.
    apply (IHa a' Pa' Ra'a).
  Qed.

End RestrictedAcc.

(***********************************************************************)
(** list of accessible arguments *)

Require Import List.

Definition accs (A : Type) R l := forall a : A, In a l -> Acc R a.

(***********************************************************************)
(** simulation and morphisms *)

Section Accessibility.

  Variables A B : Type.
  Variables R : relation A.

  Definition mimic (P : relation A) := forall x x', P x x' ->
    (forall y', R y' x' -> exists2 y, R y x & P y y').

  Lemma Acc_mimic : forall x (P: relation A),
    Acc R x -> mimic P -> forall x', P x x' -> Acc R x'.
      
  Proof.
    induction 1.
    intros mim x' Pxx'.
    constructor.
    intros y' Ry'x'.
    unfold mimic in mim.
    destruct (mim x x' Pxx' y' Ry'x') as [y Ryx Pyy'].
    apply H0 with y; trivial.
  Qed.

  Variables x y : A.

  Section AccHomo.

    Variable T : B -> B -> Prop.
    Variable z : B.
    Variable morphism : A -> B -> Prop.
    Variable comp : forall x y x',
      morphism x' x -> T y x -> exists2 y': A, R y' x' & morphism y' y.

    Lemma Acc_homo :
      forall x, Acc R x -> forall x', morphism x x' -> Acc T x'.
      
    Proof.
      induction 1.
      intros x' x0x'.
      constructor.
      intros w Twx'.
      destruct (comp x0x' Twx') as [x1 Rx x1w].
      eapply H0; eauto.
    Qed.

  End AccHomo.
  
  Section AccIso.

    Variable T : B -> B -> Prop.
    Variable z : B.
    Variable iso : A -> B -> Prop.
    Variable iso_comp : forall x y' x',
      iso x x' -> T y' x' -> {y: A | R y x & iso y y'}.

    Lemma Acc_iso : iso x z -> Acc R x -> Acc T z.

    Proof.
      intros iso_x_z Acc_x; generalize z iso_x_z; clear iso_x_z z.
      induction Acc_x as [x Acc_x Hind].
      intros z iso_x_z.
      constructor.
      intros z' T_z'_z.
      elim (iso_comp iso_x_z T_z'_z).
      intros x' Rx' iso_x'_z'.
      apply Hind with x'; assumption.
    Qed.

  End AccIso.

  Lemma Acc_eq_rel : forall S,
    (forall a b, R a b <-> S a b) -> Acc R x -> Acc S x.

  Proof.
    induction 2.
    constructor.
    intros z Szx; apply H1.
    exact (proj2 (H z x) Szx).
  Qed.

End Accessibility.

(***********************************************************************)
(** transp *)

Section Transposition.

  Variable A : Type.
  Variable R : A -> A -> Prop.
    
  Lemma transp_transp_wf :
    well_founded R -> well_founded (transp (transp R)).

  Proof.
    intros R_wf x.
    apply Acc_eq_rel with R.
    apply transp_transp_R_eq_R.
    auto.
  Qed.

End Transposition.
