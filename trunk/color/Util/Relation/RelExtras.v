(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2004-09-06
- William Delobel, 2005-10-07

This file provides some basic results concerning relations that were
missing in the standard library.
*)

Set Implicit Arguments.

Require Export Relations.
Require Import RelUtil.
Require Import LogicUtil.
Require Import Max.
Require Import Arith.
Require Import Setoid.

Section StrictOrder.

  Variable A : Type.
  Variable R : relation A.

  Definition transitive := forall x y z:A, R x y -> R y z -> R x z.
  Definition irreflexive := forall x:A, ~ R x x.

  Record strict_order : Prop := {
    sord_trans : transitive;
    sord_irrefl : irreflexive 
  }.

  Variable so : strict_order.

  Lemma so_not_symmetric : forall a b, R a b -> R b a -> False.

  Proof.
    unfold not; intros a b Rab Rba.
    exact (sord_irrefl so (sord_trans so Rab Rba)).
  Qed.

  Variable eq : relation A.
  Variable Req_compat : forall x x' y y',
    eq x x' -> eq y y' -> R x y -> R x' y'.
  Variable eq_setoid : Setoid_Theory A eq.

  Lemma so_strict : forall x y, eq x y -> R x y -> False.

  Proof.
    intros.
    assert (R y x).
    apply Req_compat with x y; auto.
    apply (Seq_sym A eq eq_setoid); trivial.
    absurd (R x x).
    unfold not; intro xx; exact (sord_irrefl so xx).
    exact (sord_trans so H0 H1).
  Qed.

End StrictOrder.

Module Type Eqset.

  Parameter A : Type.
  Parameter eqA : A -> A -> Prop.

  Notation "X =A= Y" := (eqA X Y) (at level 70) : sets_scope.
  Open Scope sets_scope.

  Parameter sid_theoryA : Setoid_Theory A eqA.

  Hint Resolve (Seq_refl  A eqA sid_theoryA) : sets.
  Hint Resolve (Seq_trans A eqA sid_theoryA) : sets.
  Hint Resolve (Seq_sym   A eqA sid_theoryA) : sets.

End Eqset.

Module Type Eqset_dec.

  Declare Module Eq : Eqset.
  Export Eq.

  Parameter eqA_dec : forall x y, {eqA x y} + {~eqA x y}.

End Eqset_dec.

Module Type SetA.
  Parameter A : Type.
End SetA.

Module Eqset_def (A : SetA) <: Eqset.

  Definition A := A.A.
  Definition eqA := eq (A:=A).
  Definition sid_theoryA := Build_Setoid_Theory _ eqA 
     (refl_equal (A:=A)) (sym_eq (A:=A)) (trans_eq (A:=A)).

  Hint Resolve (Seq_refl  A eqA sid_theoryA) : sets.
  Hint Resolve (Seq_trans A eqA sid_theoryA) : sets.
  Hint Resolve (Seq_sym   A eqA sid_theoryA) : sets.

End Eqset_def.

Section Eqset_def_gtA_eqA_compat.

  Variable A : Type.
  Variable gtA : A -> A -> Prop.

  Lemma Eqset_def_gtA_eqA_compat : forall x x' y y',
    x = x' -> y = y' -> gtA x y -> gtA x' y'.

  Proof.
    intros x x' y y' x_x' y_y' x_y.
    rewrite <- x_x'; rewrite <- y_y'; trivial.
  Qed.

End Eqset_def_gtA_eqA_compat.

Module Type Ord.

  Parameter A : Type.

  Declare Module S : Eqset with Definition A := A.
  Export S.

  Parameter gtA : A -> A -> Prop.

  Notation "X > Y" := (gtA X Y) : sets_scope.

  Parameter gtA_eqA_compat : forall x x' y y',
    x =A= x' -> y =A= y' -> x > y -> x' > y'.

  Hint Resolve gtA_eqA_compat : sets.

End Ord.

Module OrdLemmas (P : Ord).

  Export P.

  Definition ltA := transp gtA.
  Definition geA x y := ~ ltA x y.
  Definition leA x y := ~ gtA x y.
  Definition AccA := Acc ltA.

  Notation "X < Y" := (ltA X Y) : sets_scope.
  Notation "X >= Y" := (geA X Y) : sets_scope.
  Notation "X <= Y" := (leA X Y) : sets_scope.

  Hint Unfold ltA geA leA AccA : sets.

  Add Setoid A eqA sid_theoryA as sidA.

  Add Morphism gtA
    with signature eqA ==> eqA ==> iff
      as gtA_morph.

  Proof.
    split; eauto with sets.
  Qed.

  Add Morphism ltA
    with signature eqA ==> eqA ==> iff
      as ltA_morph.

  Proof.
    split. eauto with sets.
    cut (y0 =A= x0). intro. eauto with sets.
    apply (Seq_sym _ _ sid_theoryA). assumption.
  Qed.

  Add Morphism AccA
    with signature eqA ==> iff
      as AccA_morph.

  Proof.
    intros a b eq_ab. split.
    intro acc_a. inversion acc_a. constructor. intros.
    apply H. rewrite eq_ab. assumption.
    intros acc_b. inversion acc_b. constructor. intros.
    apply H. rewrite <- eq_ab. assumption.
  Qed.

End OrdLemmas.

Module Type Poset.

  Parameter A : Type.

  Declare Module O : Ord with Definition A := A.
  Export O.

  Parameter gtA_so : strict_order gtA.

  Hint Resolve (sord_trans gtA_so) : sets.
  Hint Resolve (sord_irrefl gtA_so) : sets.
  Hint Resolve (so_not_symmetric gtA_so) : sets.
  Hint Resolve (so_strict gtA_so gtA_eqA_compat sid_theoryA) : sets.

End Poset.

Module nat_ord <: Ord.

  Module natSet <: SetA.
    Definition A := nat.
    Definition eqA_dec := eq_nat_dec.
  End natSet.

  Module S := Eqset_def natSet.

  Definition A := nat.
  Definition gtA := gt.

  Lemma gtA_eqA_compat : forall x x' y y', 
    x = x' -> y = y' -> x > y -> x' > y'.

  Proof.
    intros x x' y y' xx' yy'.
    rewrite <- xx'; rewrite <- yy'; trivial.
  Qed.

End nat_ord.

Section Transitive_Closure.

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Let R_tclos := clos_trans R.

  Lemma trans_clos_step_l : forall x y, 
    R_tclos x y -> R x y \/ (exists2 z, R x z & R_tclos z y).

  Proof.
    intros x y; compute; intro xy; induction xy.
    left; trivial.
    inversion IHxy1; inversion IHxy2; right; solve [eauto |
      inversion H; try inversion H0; exists x0; 
      [trivial | constructor 2 with y; auto]].
  Qed.

  Lemma trans_clos_step_r : forall x y, 
    R_tclos x y -> R x y \/ (exists2 z, R_tclos x z & R z y).

  Proof.
    intros x y; compute; intro xy; induction xy.
    left; trivial.
    inversion_clear IHxy1; inversion_clear IHxy2; right;
      solve [eauto | inversion H0; exists x0; 
      [constructor 2 with y; auto | trivial]].
  Qed.

  Variable eqA : A -> A -> Prop.

  Parameter sid_theoryA : Setoid_Theory A eqA.
  Parameter R_eqA_comp : forall x y x' y',
    eqA x x' -> eqA y y' -> R x y -> R x' y'.
  Parameter R_so : strict_order R.

  Hint Resolve R_eqA_comp.

  Lemma trans_clos_mirror : forall x y x' y',
    eqA x x' -> eqA y y' -> R_tclos x y -> R_tclos x' y'.

  Proof.
    intros x y x' y' eq_xx' eq_yy' R_xy. 
    case (trans_clos_step_l R_xy).
    intro Rxy; constructor 1; eauto.
    intro R_xzy; destruct R_xzy as [w Rxw R_wy].
    case (trans_clos_step_r R_wy).
    intro Rwy; constructor 1; apply R_eqA_comp with x y;
      solve [trivial | apply (sord_trans R_so) with w; trivial].
    intro R_wpy; destruct R_wpy as [p Rwp R_py].
    constructor 2 with w.
    constructor 1; apply R_eqA_comp with x w; 
      solve [trivial | apply (Seq_refl A eqA sid_theoryA)].
    constructor 2 with p.
    trivial.
    constructor 1; apply R_eqA_comp with p y;
      solve [trivial | apply (Seq_refl A eqA sid_theoryA)].
  Qed.

  Lemma trans_clos_transp : forall x y, 
    transp (clos_trans R) x y <-> clos_trans (transp R) x y.

  Proof.
    intros; split; compute.
    induction 1.
    constructor; trivial.
    constructor 2 with y; auto.
    induction 1.
    constructor; trivial.
    constructor 2 with y; auto.
  Qed.

  Variable R' : A -> A -> Prop.
  Variable R'sub : inclusion R' R.
  
  Lemma trans_clos_inclusion : forall a b,
    clos_trans R' a b -> clos_trans R a b.

  Proof.
    intros a b a_b.
    induction a_b as [a b ab | a b c ab IHab bc IHbc].
    constructor; exact (R'sub ab).
    constructor 2 with b; trivial.
  Qed.

End Transitive_Closure.

Section Accessibility.

  Variable A : Type.
  Variable B : Type.
  Variables R S : relation A.

  Definition mimic (P: relation A) :=
    forall x x',
      P x x' ->
      (forall y', R y' x' ->
	exists2 y, R y x & P y y').

  Lemma Acc_mimic : forall x (P: relation A),
    Acc R x -> mimic P ->
    forall x', P x x' -> Acc R x'.
      
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
	  morphism x' x -> T y x ->
	  exists2 y': A, R y' x' & morphism y' y.

    Lemma Acc_homo : 
      forall x, Acc R x ->
      forall x', morphism x x' -> Acc T x'.
      
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

    Proof. (* William Delobel *)
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


  Lemma Acc_eq_rel : (forall a b, R a b <-> S a b) -> Acc R x -> Acc S x.

  Proof.
    induction 2.
    constructor.
    intros z Szx; apply H1.
    exact (proj2 (H z x) Szx).
  Qed.

  Lemma Acc_step_acc : Acc R x -> R y x -> Acc R y.

  Proof.
    intros AccX Rxy.
    inversion AccX.
    apply H; trivial.
  Qed.

End Accessibility.

Section Transposition.

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Lemma transp_transp_R_eq_R : forall x y, R x y <-> transp (transp R) x y.

  Proof.
    split; auto.
  Qed.
    
  Lemma transp_transp_wf :
    well_founded R -> well_founded (transp (transp R)).

  Proof.
    intros R_wf x.
    apply Acc_eq_rel with R.
    exact transp_transp_R_eq_R.
    auto.
  Qed.

End Transposition.

Section Specif.

  Inductive sigPS2 (A : Type) (P: A -> Prop) (Q: A -> Set) : Type :=
    existPS2: forall x:A, P x -> Q x -> sigPS2 (A:=A) P Q.

  Notation "{ x : A # P & Q }"
    := (sigPS2 (fun x:A => P) (fun x:A => Q)) : type_scope.

  Variable A : Type.
  Variables P Q : A -> Prop.

  Definition proj1_sig2 (e: sig2 P Q) :=
    match e with
    | exist2 a p q => a
    end.

  Lemma option_dec : forall (el: option A),
    el = None \/ exists w: A, el = Some w.
    
  Proof.
    intros.
    destruct el.
    right; exists a; trivial.
    left; trivial.
  Qed.

End Specif.

Ltac pair_destruct t0 t1 :=
  first [destruct t0 | intros until t0; destruct t0];
  first [destruct t1 | intros until t1; destruct t1];
  try contradiction; simpl.

Ltac rewrite_lr term := apply (proj1 term).
Ltac rewrite_rl term := apply (proj2 term).

Ltac try_solve := 
   simpl in *; try (intros; solve 
     [ contradiction 
     | discriminate 
     | auto with terms
     | tauto
     | congruence
     ]
).
