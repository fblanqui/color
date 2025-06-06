From Stdlib Require Lia.
From Stdlib Require Import Relations Wellfounded.
Set Implicit Arguments.

Section star.
Unset Implicit Arguments.
Variable A:Type.
Variable R : A -> A -> Prop.
Inductive star (x:A) : A -> Prop := 
| star_refl : star x x
| star_step : forall y, star x y -> forall z, R y z -> star x z
.


Lemma star_trans: forall x y z, star x y -> star y z -> star x z.
Proof. 
intros x y z H H1;revert x H; 
induction H1.

tauto.
intros.
econstructor 2 with y0;auto.
Qed.

Lemma star_R : forall x y, R x y -> star x y.
Proof.
intros x y H;constructor 2 with x;[constructor|assumption].
Qed.

Lemma star_ind2 : forall  x (P:A -> Prop),
  (P x) -> 
  (forall y, P y -> forall z, R y z -> P z) ->
  forall a, star x a -> P a.
Proof.
  intros x P H H0 a H1.
  induction H1.
  exact H.
  apply H0 with (y:=y);assumption.
Qed.

End star.

Ltac prove_star := 
  match goal with 
    | |- star _ _ ?t ?t => exact rt_refl
    | H:star _ _ ?t' ?t |- star _ _ ?t' ?t =>  assumption
    | H:star _ _ ?t'' ?t |- star _ _ ?t' ?t =>  
      (apply star_trans with t'';[prove_star|exact H]) || 
        (clear H;prove_star)
    | H:star _ _ ?t' ?t'' |- star _ _ ?t' ?t =>  
      (apply star_trans with t'';[exact H|prove_star]) || 
        (clear H;prove_star)
    | H:?R ?t' ?t |- star _ _ ?t' ?t =>  apply star_R;exact H
    | H:?R ?t'' ?t |- star _ _ ?t' ?t =>  
      (apply star_trans with t'';[prove_star|apply star_R;exact H]) || 
        (clear H;prove_star)
    | H:?R ?t' ?t'' |- star _ _ ?t' ?t =>  
      (apply star_trans with t'';[apply star_R;exact H|prove_star]) || 
        (clear H;prove_star)
    | _ => solve [eauto]
  end.


