From CoLoR Require Import closure. 
From Stdlib Require Import Relation_Operators.

Section S.

  Variable A : Type.
  Variable R: Relation_Definitions.relation A.
  

  Lemma refl_trans_clos_ind2 : 
    forall  x (P:A -> Prop),
      (P x) -> 
      (forall y, P y -> forall z, R y z -> P z) ->
      forall a, refl_trans_clos R x a -> P a.
  Proof.
    intros x P H H0 a H1.
    induction H1.
    exact H.
    induction H1.
    apply H0 with (y:=x);assumption.
    eauto.
  Qed.


  Lemma refl_trans_clos_R : 
    forall x y z, refl_trans_clos R x y -> R y z -> 
      refl_trans_clos R x z.
  Proof.
    intros x y z Rs_x_y R_y_z.
    apply refl_trans_clos_is_trans with y. 
    assumption.
    do 2 constructor;assumption.
  Qed.

  Lemma refl_trans_clos_with_R : 
    forall x y, R x y -> refl_trans_clos R x y.
  Proof.
    intros.
    constructor;constructor;assumption.
  Qed.

  Lemma trans_clos_left : 
    forall R' x y, trans_clos  R x y -> trans_clos (union _ R R') x y.
  Proof.
    intros R' x y H.
    induction H.
    constructor. left; assumption.
    constructor 2 with y.
    left;assumption.
    assumption.
  Qed.


  Lemma trans_clos_right : 
    forall R' x y, trans_clos R x y -> trans_clos (union _ R' R) x y.
  Proof.
    intros R' x y H.
    induction H.
    constructor. right; assumption.
    constructor 2 with y.
    right;assumption.
    assumption.
  Qed.

End S.
