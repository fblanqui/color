(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Solange Coupet-Grimal and William Delobel, 2006-01-09

useful results on accessibility
*)

Set Implicit Arguments.

From Coq Require Import Morphisms Basics.
From Coq Require Export Wellfounded.
From CoLoR Require Import LogicUtil RelUtil.

Arguments wf_incl [A R1 R2] _ _ _.

(***********************************************************************)
(** Compatibility of accessibility wrt relation inclusion/equivalence. *)

Global Instance Acc_incl A : Proper (incl --> eq ==> impl) (@Acc A).

Proof.
  intros R R' R'R x x' xx'. subst x'. induction 1. apply Acc_intro. fo.
Qed.

Global Instance Acc_same A : Proper (same ==> eq ==> iff) (@Acc A).

Proof.
  intros R R' [RR' R'R] x x' xx'. subst x'. split; intro h.
  rewrite R'R. hyp. rewrite RR'. hyp.
Qed.

(*TODO: try to remove*)
Lemma Acc_eq_rel : forall A (R S : relation A) x,
  (forall a b, R a b <-> S a b) -> Acc R x -> Acc S x.

Proof.
  induction 2. constructor. intros z Szx; apply H1. exact (proj2 (H z x) Szx).
Qed.

Global Instance well_founded_incl A :
  Proper (incl --> impl) (@well_founded A).

Proof. intros R R' R'R h. intro x. rewrite <- R'R. fo. Qed.

Global Instance well_founded_same A : Proper (same ==> iff) (@well_founded A).

Proof.
  intros R R' [RR' R'R]. split; intro h. rewrite R'R. hyp. rewrite RR'. hyp.
Qed.

(***********************************************************************)
(** Transitive closure. *)

Section rtc.

  Variables (A : Type) (R : relation A).

  Lemma Acc_rtc : forall x y, clos_refl_trans R x y -> Acc R y -> Acc R x.

  Proof.
    induction 1.
    intro. eapply Acc_inv. apply H0. hyp.
    auto.
    intro. apply IHclos_refl_trans1. apply IHclos_refl_trans2. hyp.
  Qed.

  Lemma Acc_tc_ind : forall P : A->Prop,
    (forall x, (forall y, clos_trans R y x -> P y) -> P x)
    -> forall x, Acc R x -> P x.

  Proof.
    intros. eapply Acc_ind with (R := clos_trans R). clear x H0. intros.
    apply H. intros. apply H1. hyp.
    apply Acc_clos_trans. hyp.
  Qed.

End rtc.

(***********************************************************************)
(** Symmetric product. *)

Section symprod.

  Variables (A B : Type) (leA : relation A) (leB : relation B).

  Notation Symprod := (symprod leA leB).

  Lemma Acc_symprod_fst x : Acc Symprod x -> Acc leA (fst x).

  Proof.
    induction 1. destruct x. simpl. apply Acc_intro. intros. ded (H0 (y,b)).
    apply H2. apply left_sym. hyp.
  Qed.

  Lemma Acc_symprod_snd x : Acc Symprod x -> Acc leB (snd x).

  Proof.
    induction 1. destruct x. simpl. apply Acc_intro. intros. ded (H0 (a,y)).
    apply H2. apply right_sym. hyp.
  Qed.

  Lemma Acc_symprod_invl x y : Acc Symprod (x,y) -> Acc leA x.

  Proof. intros. ded (Acc_symprod_fst H). hyp. Qed.

  Lemma Acc_symprod_invr x y : Acc Symprod (x,y) -> Acc leB y.

  Proof. intros. ded (Acc_symprod_snd H). hyp. Qed.

  Lemma Acc_symprod_inv x y : Acc Symprod (x,y) -> Acc leA x /\ Acc leB y.

  Proof.
    intros. split. eapply Acc_symprod_invl. apply H. eapply Acc_symprod_invr.
    apply H.
  Qed.

End symprod.

(***********************************************************************)
(** Restricted accessibility. *)

Section RestrictedAcc.

  Variables (A : Type) (P : A -> Prop).

  Inductive Restricted_acc (R : relation A) : A -> Prop :=
  | Restricted_acc_cons : forall a,
    (forall a', P a' -> R a' a -> Restricted_acc R a') -> Restricted_acc R a.

  Lemma Restricted_acc_eq_acc : forall R a,
    Acc (fun a a' => P a /\ R a a') a <-> Restricted_acc R a.

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
(** List of accessible arguments. *)

From Coq Require Import List.

Definition Accs (A : Type) R l := forall a : A, In a l -> Acc R a.

(***********************************************************************)
(** Simulation and morphisms. *)

Section Accessibility.

  Variables (A B : Type) (R : relation A).

  Definition mimic (P : relation A) := forall x x', P x x' ->
    forall y', R y' x' -> exists2 y, R y x & P y y'.

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

    Variable T : relation B.
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

    Variable T : relation B.
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
      apply Hind with x'; hyp.
    Qed.

  End AccIso.

End Accessibility.

(***********************************************************************)
(** Wellfounded fixpoints: we extend [Fix_F_inv] to any relation [eq]. *)

Arguments Fix [A R] _ [P] _ _.
Arguments Fix_eq [A R] _ [P F] _ _.
Arguments Fix_F [A R P] _ [x] _.
Arguments Fix_F_eq [A R P] _ [x] _.
Arguments Fix_F_inv [A R] _ [P] _ _ [x] _ _.

Section Fix.

  Variables (A : Type) (R : relation A) (Rwf : well_founded R)
    (P : A -> Type) (F : forall x : A, (forall y : A, R y x -> P y) -> P x)
    (eq : forall x, relation (P x))
    (F_ext : forall x (f g : forall y, R y x -> P y),
      (forall y (p : R y x), eq (f y p) (g y p)) -> eq (F f) (F g)).

  Notation Fix_F := (Fix_F F).
  Notation Fix_F_eq := (Fix_F_eq F).
  Notation Fix := (Fix Rwf F).
  Infix "==" := eq (at level 70).

  Lemma Fix_F_inv : forall x (r s : Acc R x), Fix_F r == Fix_F s.

  Proof.
    intro x; induction (Rwf x); intros.
    rewrite <- (Fix_F_eq r), <- (Fix_F_eq s); intros.
    apply F_ext; auto.
  Qed.

  Lemma Fix_eq : forall x, Fix x == F (fun y (p : R y x) => Fix y).

  Proof.
    intro x; unfold Wf.Fix.
    rewrite <- Fix_F_eq.
    apply F_ext; intros.
    apply Fix_F_inv.
  Qed.

End Fix.

Arguments Fix_F_inv [A R] _ [P] _ _ _ [x] _ _.
Arguments Fix_eq [A R] _ [P F eq] _ _.

(***********************************************************************)
(** A well-founded relation is irreflexive. *)

Lemma wf_irrefl : forall A (R : relation A), well_founded R -> Irreflexive R.

Proof. intros A R wf x. induction (wf x). intro n. eapply H0. apply n. hyp. Qed.
