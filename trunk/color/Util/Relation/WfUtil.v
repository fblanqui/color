(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Solange Coupet-Grimal and William Delobel, 2006-01-09

useful results on accessibility
************************************************************************)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export RelUtil.
Require Export Wellfounded.

(***********************************************************************)
(* the way wellfoundedness is usually used in rewriting *)

Notation "'wf' R" := (well_founded (transp R)) (at level 70).
Notation "'sn' R" := (Acc (transp R)) (at level 0).

Section S.

Variables (A : Set) (R : relation A).

(***********************************************************************)
(* transitive closure *)

Lemma Acc_rtc : forall x y, clos_refl_trans R x y -> Acc R y -> Acc R x.

Proof.
induction 1.
intro. eapply Acc_inv. apply H0. assumption.
auto.
intro. apply IHclos_refl_trans1. apply IHclos_refl_trans2. assumption.
Qed.

Require Export Wellfounded.

Lemma Acc_tc_ind : forall P : A->Prop,
  (forall x, (forall y, clos_trans R y x -> P y) -> P x)
  -> forall x, Acc R x -> P x.

Proof.
intros. eapply Acc_ind with (R := clos_trans R). clear x H0. intros.
apply H. intros. apply H1. assumption.
apply Acc_clos_trans. assumption.
Qed.

End S.

(***********************************************************************)
(* symmetric product *)

Section symprod.

Variable A : Set.
Variable B : Set.
Variable leA : A -> A -> Prop.
Variable leB : B -> B -> Prop.

Notation Symprod := (symprod A B leA leB).

Lemma Acc_symprod_fst : forall x, Acc Symprod x -> Acc leA (fst x).

Proof.
induction 1. destruct x. simpl. apply Acc_intro. intros. deduce (H0 (y,b)).
apply H2. apply left_sym. assumption.
Qed.

Lemma Acc_symprod_snd : forall x, Acc Symprod x -> Acc leB (snd x).

Proof.
induction 1. destruct x. simpl. apply Acc_intro. intros. deduce (H0 (a,y)).
apply H2. apply right_sym. assumption.
Qed.

Lemma Acc_symprod_invl : forall x y, Acc Symprod (x,y) -> Acc leA x.

Proof.
intros. deduce (Acc_symprod_fst H). assumption.
Qed.

Lemma Acc_symprod_invr : forall x y, Acc Symprod (x,y) -> Acc leB y.

Proof.
intros. deduce (Acc_symprod_snd H). assumption.
Qed.

Lemma Acc_symprod_inv : forall x y, Acc Symprod (x,y) -> Acc leA x /\ Acc leB y.

Proof.
intros. split. eapply Acc_symprod_invl. apply H. eapply Acc_symprod_invr. apply H.
Qed.

End symprod.

(***********************************************************************)
(* inverse image *)

Section inverse.

Variables (A B : Set) (R : relation B) (f : A->B).

Let Rof x y := R (f x) (f y).

Lemma transp_Rof : inclusion (fun x y => Rof y x) (fun x y => transp R (f x) (f y)).

Proof.
unfold transp, inclusion. auto.
Qed.

Lemma wf_inv_image : wf R -> wf Rof.

Proof.
intro. eapply wf_incl. apply transp_Rof.
apply wf_inverse_image with (R := transp R). assumption.
Qed.

End inverse.

(***********************************************************************)
(* restricted accessibility *)

Section RestrictedAcc.

  Variable A : Set.
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
