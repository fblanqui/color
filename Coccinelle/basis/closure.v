(**************************************************************************)
(*           *                                                            *)
(*     _     *   The Coccinelle Library / Evelyne Contejean               *)
(*    <o>    *          CNRS-LRI-Universite Paris Sud                     *)
(*  -/@|@\-  *                   A3PAT Project                            *)
(*  -@ | @-  *                                                            *)
(*  -\@|@/-  *      This file is distributed under the terms of the       *)
(*    -v-    *      CeCILL-C licence                                      *)
(*           *                                                            *)
(**************************************************************************)

Set Implicit Arguments. 

From Stdlib Require Import Setoid Relations List Wellfounded.
From CoLoR Require Export TransClosure.

Lemma acc_trans :
 forall A (R : relation A) a, Acc R a -> Acc (trans_clos R) a.
Proof.
intros A R a Acc_R_a.
induction Acc_R_a as [a Acc_R_a IH].
apply Acc_intro.
intros b b_Rp_a; induction b_Rp_a.
apply IH; trivial.
apply Acc_inv with y.
apply IHb_Rp_a; trivial.
apply t_step; trivial.
Defined.

Lemma wf_trans :
  forall A (R : relation A) , well_founded R -> well_founded (trans_clos R).
Proof.
unfold well_founded; intros A R WR.
intro; apply acc_trans; apply WR; trivial.
Defined.


Lemma trans_incl :
  forall A (R1 R2 : relation A), inclusion _ R1 R2 -> inclusion _ (trans_clos R1) (trans_clos R2).
Proof.
intros A R1 R2 R1_in_R2 a b H; induction H as [a' b' H | a' b' c' H1 H2].
apply t_step; apply R1_in_R2; trivial.
apply t_trans with b'; trivial.
apply R1_in_R2; trivial.
Qed.

Lemma refl_trans_incl :
  forall A (R1 R2 : relation A), inclusion _ R1 R2 -> inclusion _ (refl_trans_clos R1) (refl_trans_clos R2).
Proof.
intros A R1 R2 R1_in_R2 a b [a' | a' b' H].
left.
apply t_clos; apply trans_incl with R1; assumption.
Qed.

Lemma trans_incl2 :
  forall A B (f : A -> B) (R1 : relation A) (R2 : relation B), 
  (forall a1 a2, R1 a1 a2 -> R2 (f a1) (f a2)) -> 
	forall a1 a2, trans_clos R1 a1 a2 ->  trans_clos R2 (f a1) (f a2).
Proof.
intros A B f R1 R2 R1_in_R2 a b H; induction H as [a' b' H | a' b' c' H1 H2].
apply t_step; apply R1_in_R2; trivial.
apply t_trans with (f b'); trivial.
apply R1_in_R2; trivial.
Qed.

Lemma trans_with_eq : 
  forall A (R : relation A) a1 a2, 
  trans_clos (union A (@eq _) R) a1 a2 <-> refl_trans_clos R a1 a2.
Proof.
intros A R a1 a2; split.
intro H; induction H as [b1 b2 H | b1 b2 b3 H1 H2]. 
destruct H as [H | H].
subst b2; apply r_step; assumption.
apply t_clos; apply t_step; assumption.
destruct H1 as [H1 | H1].
subst b2; assumption.
destruct IHH2 as [b2 | b2 b3 H3].
apply t_clos; apply t_step; assumption.
apply t_clos; apply t_trans with b2; assumption.

intro H; destruct H as [a1 | a1 a2 H].
apply t_step; left; apply eq_refl.
apply (@trans_incl _ R); trivial.
right; assumption.
Qed.

Lemma acc_star : 
   forall A (R : relation A) a, Acc R a -> forall b,  refl_trans_clos  R b a -> Acc R b.
Proof.
intros A R a Acc_a b H; destruct H as [a1 | a1 a2 H].
assumption.
apply Acc_incl with (trans_clos R).
intros b1 b2 H'; apply t_step; assumption.
apply Acc_inv with a2; trivial.
apply acc_trans; trivial.
Qed.

Inductive compose_rel A (R1 R2 : relation A) : relation A :=
  Comp : forall a1 a2 a3, R1 a1 a2 -> R2 a2 a3 -> compose_rel R1 R2 a1 a3.

Section Compose.
Variable A : Type.
Variable R1 : relation A.
Variable R2 : relation A.

Lemma trans_union :
  forall a b,
  trans_clos (union _ R1 R2) a b <-> 
  union _ (trans_clos R1) 
            (compose_rel (refl_trans_clos R1) (trans_clos (compose_rel R2 (refl_trans_clos R1)))) a b.
Proof.
intros a b; split.
(* 1/2 -> *)
intro H; induction H as [x y H1 | x y z H1 Hn].
destruct H1 as [H1 | H1].
left; apply t_step; assumption.
right; apply Comp with x.
apply r_step.
apply t_step.
apply Comp with y; trivial.
apply r_step.
destruct H1 as [H1 | H2]; destruct IHHn as [IHHn | IHHn].
left; apply t_trans with y; trivial.
right; inversion IHHn as [x' y' z' K1 K2]; subst x' z'; clear IHHn.
apply Comp with y'.
inversion K1 as [y1 | y1 y2 K1']; clear K1.
subst y1 y'; apply t_clos; apply t_step; trivial.
subst y1 y2; apply t_clos; apply t_trans with y; trivial.
trivial.
right.
apply Comp with x.
apply r_step.
apply t_step; apply Comp with y; trivial.
apply t_clos; trivial.
right; inversion IHHn as [x' y' z' K1 K2]; subst x' z'; clear IHHn.
apply Comp with x.
apply r_step.
apply t_trans with y'; trivial.
apply Comp with y; trivial.
(* 1/1 <- *)
intros [H | H].
apply trans_incl with R1; trivial.
intros; left; trivial.
inversion H as [x' y' z' K1 K2]; clear H; subst x' z'.
inversion K1 as [y1 | y1 y2 K1']; clear K1.
subst y1 y'.
apply trans_clos_is_clos.
apply trans_incl with (compose_rel R2 (refl_trans_clos R1)); trivial.
clear a b K2; intros a b K2.
inversion K2 as [x' y' z' K1 K2']; clear K2; subst x' z'.
inversion K2' as [y1 | y1 y2 K2'']; clear K2'.
subst y1 y'; apply t_step; right; trivial.
subst y1 y2.
apply t_trans with y'.
right; trivial.
apply trans_incl with R1; trivial.
intros; left; trivial.
subst y1 y2.
apply trans_clos_is_trans with y'.
apply trans_incl with R1; trivial.
intros; left; trivial.
apply trans_clos_is_clos.
apply trans_incl with (compose_rel R2 (refl_trans_clos R1)); trivial.
clear a b y' K1' K2; intros a b K2.
inversion K2 as [x' y' z' K1 K2']; clear K2; subst x' z'.
inversion K2' as [y1 | y1 y2 K2'']; clear K2'.
subst y' y1.
left; right; trivial.
subst y1 y2.
right with y'.
right; trivial.
apply trans_incl with R1; trivial.
intros; left; trivial.
Qed.

Lemma trans_union_alt :
  forall a b,
  trans_clos (union _ R1 R2) a b <-> 
  union _ (trans_clos R1) 
             (compose_rel (trans_clos (compose_rel (refl_trans_clos R1) R2)) 
                                  (refl_trans_clos R1)) a b.
Proof.
intros a b; split.
(* 1/2 -> *)
rewrite trans_clos_trans_clos_alt in *; intro H; induction H as [x y H1 | x y z H1 IHH1 Hn].
(* 1/3 one step *)
destruct H1 as [H1 | H1].
left; left; assumption.
right; apply Comp with y.
left; apply Comp with x; trivial.
left.
left.
(* 1/2 several steps *)
destruct IHH1 as [IHH1 | IHH1]; destruct Hn as [Hn | Hn].
(* 1/5 *)
left; rewrite trans_clos_trans_clos_alt in *; right with y; trivial.
(* 1/4 *)
right; apply Comp with z.
left; apply Comp with y; trivial.
right; trivial.
left.
(* 1/3 *)
inversion IHH1 as [x' y' z' K1 K2]; subst x' z'; clear IHH1.
right; apply Comp with y'; trivial.
inversion K2 as [y'' | a a' K2' K2''].
subst y' y''.
right; left; trivial.
subst a a'; right; apply trans_clos_is_trans with y; trivial.
left; trivial.
(* 1/2 *)
inversion IHH1 as [x' y' z' K1 K2]; subst x' z'; clear IHH1.
right.
apply Comp with z.
apply trans_clos_is_trans with y'; trivial.
left; apply Comp with y; trivial.
left.
(* 1/1 <- *)
intros [H | H].
apply trans_incl with R1; trivial.
intros; left; trivial.
inversion H as [x' y' z' K1 K2]; clear H; subst x' z'.
inversion K2 as [y1 | y1 y2 K2']; clear K2.
subst y1 y'.
apply trans_clos_is_clos.
apply trans_incl with (compose_rel (refl_trans_clos R1) R2); trivial.
clear a b K1; intros a b H.
inversion H as [x' y' z' K1 K2]; subst x' z'; clear H.
inversion K1 as [y1 | y1 y2 K1']; clear K1.
subst y1 y'; apply t_step; right; trivial.
subst y1 y2.
apply trans_clos_is_trans with y'.
apply trans_incl with R1; trivial.
intros; left; trivial.
left; right; trivial.
subst y1 y2.
apply trans_clos_is_trans with y'.
apply trans_clos_is_clos.
apply trans_incl with (compose_rel (refl_trans_clos R1) R2); trivial.
clear a b y' K1 K2'; intros a b H.
inversion H as [x' y' z' K1 K2]; subst x' z'; clear H.
inversion K1 as [y1 | y1 y2 K1']; clear K1.
subst y1 y'; apply t_step; right; trivial.
subst y1 y2.
apply trans_clos_is_trans with y'.
apply trans_incl with R1; trivial.
intros; left; trivial.
left; right; trivial.
apply trans_incl with R1; trivial.
intros; left; trivial.
Qed.

Lemma acc_union :
  well_founded R1 ->
  forall a, Acc (compose_rel R2 (refl_trans_clos R1)) a <-> Acc (union _ R1 R2) a.
Proof.
intros W1'.
assert (W1 := wf_trans W1'); clear W1'.
intros a; split.
intro Acc_a; induction Acc_a as [a Acc_a' IH2].
assert (Acc_a : Acc (compose_rel R2 (refl_trans_clos R1)) a).
apply Acc_intro; trivial.
clear Acc_a'.
revert IH2 Acc_a.
pattern a; apply (well_founded_ind W1); clear a.
intros a IH1 IH2 Acc_a.
apply Acc_intro.
intros b [H1 | H2].
apply IH1.
apply t_step; trivial.
intros c H2; apply IH2.
inversion H2 as [c' d' b' H H']; subst.
apply Comp with d'; trivial.
apply refl_trans_clos_is_trans with b; trivial.
right; left; trivial.
apply Acc_intro; intros c H2.
apply Acc_inv with a; trivial.
inversion H2 as [c' d' b' H H']; subst.
apply Comp with d'; trivial.
apply refl_trans_clos_is_trans with b; trivial.
right; left; trivial.
apply IH2.
apply Comp with a; trivial.
apply r_step.

intro Acc_a; apply Acc_incl with (trans_clos (union _ R1 R2)).
intros a1 a3 H; inversion H as [b1 b2 b3 H1 H2]; clear H; subst a1 a3.
inversion H2 as [b | a2 a3 K2]; clear H2; subst.
left; right; assumption.
apply t_trans with b2.
right; assumption.
apply trans_incl with R1; trivial.
intros x y H; left; assumption.
apply acc_trans; assumption.
Qed.

Lemma acc_union_weak :
  forall a, Acc (compose_rel R2 (refl_trans_clos R1)) a -> 
              (forall b, refl_trans_clos (compose_rel R2 (refl_trans_clos R1)) b a -> Acc R1 b) -> 
              Acc (union _ R1 R2) a.
Proof.
intros a Acc_a H; 
induction Acc_a as [a Acc_a' IH2].
assert (Acc_a : Acc (compose_rel R2 (refl_trans_clos R1)) a).
apply Acc_intro; trivial.
clear Acc_a'.
assert (Acc1_a : Acc R1 a).
apply H; left.
revert IH2 H Acc_a.
induction Acc1_a as [a Acc1_a IH1].
intros IH2 H Acc_a.
apply Acc_intro.
intros b [H1 | H2].
apply IH1; trivial.
intros c H2; apply IH2.
inversion H2 as [c' d' b' h H']; subst.
apply Comp with d'; trivial.
apply refl_trans_clos_is_trans with b; trivial.
right; left; trivial.
intros c K; inversion K; clear K; subst.
apply Acc1_a; assumption.
apply H.
rewrite trans_clos_trans_clos_alt in H0.
inversion H0; clear H0; subst.
right; left.
inversion H2; clear H2; subst.
apply Comp with a2; trivial.
apply refl_trans_clos_is_trans with b; trivial.
right; left; exact H1.
inversion H3; clear H3; subst.
apply refl_trans_clos_is_trans with y; trivial.
right; rewrite trans_clos_trans_clos_alt; assumption.
right; left.
apply Comp with a2; trivial.
apply refl_trans_clos_is_trans with b; trivial.
right; left; exact H1.
apply Acc_intro; intros c K.
apply Acc_inv with a; trivial.
inversion K; clear K; subst.
apply Comp with a2; trivial.
apply refl_trans_clos_is_trans with b; trivial.
right; left; exact H1.

apply IH2.
apply Comp with a; [assumption | left].
intros c K; apply H.
apply refl_trans_clos_is_trans with b; trivial.
right; left; apply Comp with a; [assumption | left].
Qed.

Lemma acc_union_alt :
  well_founded R1 ->
  forall a, (forall b, refl_trans_clos R1 b a -> Acc (compose_rel (refl_trans_clos R1) R2) b) <-> Acc (union _ R1 R2) a.
Proof.
intros W1'; split.
intro Ha; apply acc_union_weak; trivial.
apply Acc_intro; intros b4 H.
inversion H as [a4 b2 a1 H' H21]; clear H; subst.
assert (Acc_b2 := Ha b2 H21).
revert a Ha b4 H' H21; induction Acc_b2 as [b2 Acc_b2 IH].
intros a Ha b4 H' H21.
apply Acc_intro.
intros b6 H.
inversion H as [a6 b5 a4 H65 H54]; clear H; subst.
apply IH with b5 b4; trivial.
apply Comp with b4; trivial.
intros b7 H7.
apply Acc_b2.
apply Comp with b4; trivial.

intros Acc_a b H; apply Acc_incl with (trans_clos (union _ R1 R2)).
clear b H; intros a1 a3 H; inversion H as [b1 b2 b3 H1 H2]; clear H; subst a1 a3.
inversion H1 as [b | a2 a3 K1]; clear H1; subst.
left; right; assumption.
apply trans_clos_is_trans with b2.
apply trans_incl with R1; trivial.
intros x y H; left; assumption.
left; right; assumption.
inversion H as [a' | b' a' K]; clear H.
apply acc_trans; assumption.
subst; apply Acc_inv with a.
apply acc_trans; assumption.
apply trans_incl with R1; trivial.
intros x y H; left; assumption.
Qed.

Lemma acc_union_alt_weak :
  forall a, (forall b, refl_trans_clos (compose_rel R2 (refl_trans_clos R1)) b a -> Acc R1 b) ->
               (forall b, refl_trans_clos R1 b a -> Acc (compose_rel (refl_trans_clos R1) R2) b) -> 
              Acc (union _ R1 R2) a.
Proof.
intros a H1a H2a.
apply acc_union_weak; trivial.
clear H1a.
apply Acc_intro; intros b4 H.
inversion H as [a4 b2 a1 H' H21]; clear H; subst.
assert (Acc_b2 := H2a b2 H21).
revert a H2a b4 H' H21; induction Acc_b2 as [b2 Acc_b2 IH].
intros a Ha b4 H' H21.
apply Acc_intro.
intros b6 H.
inversion H as [a6 b5 a4 H65 H54]; clear H; subst.
apply IH with b5 b4; trivial.
apply Comp with b4; trivial.
intros b7 H7.
apply Acc_b2.
apply Comp with b4; trivial.
Qed.

Lemma wf_union_alt :
  well_founded R1 ->
  (well_founded (compose_rel (refl_trans_clos R1) R2) <-> well_founded (union _ R1 R2)).
Proof.
intros W1'; split.
intro W; intro a; rewrite <- acc_union; trivial.
assert (W1 := wf_trans W1'); clear W1'.
apply Acc_intro.
intros b4 H.
inversion H as [a4 b2 a1 H' H21]; clear H; subst.
clear a H21.
revert b4 H'.
pattern b2; apply (well_founded_ind (wf_trans W)); clear b2.
intros a IH b H.
apply Acc_intro; intros c K.
inversion K as [d' c' b' H1 H2];clear K; subst.
apply IH with c'; trivial.
left; apply Comp with b; trivial.

intros W a; apply Acc_incl with (trans_clos (union _ R1 R2)).
intros a1 a3 H; inversion H as [b1 b2 b3 H1 H2]; clear H; subst a1 a3.
inversion H1 as [b | a2 a3 K1]; clear H1; subst.
left; right; assumption.
apply trans_clos_is_trans with b2.
apply trans_incl with R1; trivial.
intros x y H; left; assumption.
left; right; assumption.
apply acc_trans; apply W.
Qed.

Lemma acc_comp_incl :
  forall R, (forall a, Acc R a -> Acc (union _ R1 R2) a) -> 
  forall a, Acc R a -> Acc (compose_rel (refl_trans_clos R1) R2) a.
Proof.
intros R H a Acc_a.
apply Acc_incl with (trans_clos (union _ R1 R2)).
clear; intros a b H.
inversion H as [c1 c2 c3 K1 K2]; clear H; subst.
inversion K1 as [c | b1 b2 K3 K4]; clear K1; subst.
left; right; assumption.
apply trans_clos_is_trans with c2.
apply trans_incl with R1; trivial.
clear; intros a b H; left; assumption.
left; right; assumption.
apply acc_trans.
apply H; assumption.
Qed.

End Compose.

Definition rest A P R := fun (a b : A) => R a b /\ P a /\ P b.

Lemma rest_union : forall A P (R1 R2 : relation A) a b, rest P (union _ R1 R2) a b <-> union _ (rest P R1) (rest P R2) a b.
intros A P R1 R2 a b; split.
intros [[H1 | H2] [Pa Pb]]; [left | right]; repeat split; assumption.
intros [[H1 [Pa Pb]] | [H2 [Pa Pb]]]; repeat split; trivial.
left; assumption.
right; assumption.
Qed.

Lemma rest_trans : 
   forall A (P : A -> Prop) (R : relation A), (forall a b, P a -> R b a -> P b) -> 
	forall a, P a -> forall b, trans_clos (rest P R) b a <-> trans_clos R b a.
Proof.
intros A P R Inv a Pa b; split.
apply trans_incl; intros x y [H _]; assumption.
intro H; rewrite trans_clos_trans_clos_alt in H; rewrite trans_clos_trans_clos_alt.
induction H as [x y K | x y z K1 K2].
left; repeat split; trivial.
apply Inv with y; assumption.
assert (Py := Inv _ _ Pa H).
right with y.
exact (K2 Py).
repeat split; assumption.
Qed.

Lemma acc_rest : 
  forall A (R : relation A) (P : A -> Prop),
  (forall (a b : A), P a -> R b a -> P b) -> 
  (forall a, (P a -> Acc R a) <-> Acc (rest P R) a).
Proof.
intros A R P Inv a; split.
intro K; apply Acc_intro; intros b [H [Wb Wa]].
apply Acc_inv with a; trivial.
apply Acc_incl with R.
clear; intros a b [H _]; assumption.
apply K; assumption.
repeat split; assumption.
intro Acc_a; induction Acc_a as [a Acc_a IH].
intro Pa; apply Acc_intro; intros b H.
apply IH.
repeat split; trivial.
apply Inv with a; assumption.
apply Inv with a; assumption.
Qed.

Lemma wf_rest : 
  forall A (R : relation A) (P : A -> Prop),
  (forall (a b : A), P a -> R b a -> P b) -> 
  ((forall a, P a -> Acc R a) <->  well_founded (rest P R)).
Proof.
intros A R P Inv; split.
intros W a; rewrite <- acc_rest; trivial.
apply W.
intros W a; rewrite acc_rest; trivial.
Qed.

Lemma acc_union_rest :
  forall A (R1 R2 : relation A) (P : A -> Prop),
  (forall (a b : A), P a -> R1 b a -> P b) -> 
  (forall (a b : A), P a -> R2 b a -> P b) -> 
  (forall a, P a -> Acc R1 a) ->
  forall a, P a -> Acc (compose_rel R2 (refl_trans_clos R1)) a -> Acc (union _ R1 R2) a.
Proof.
intros A R1 R2 P Inv1 Inv2 W1' a Wa Acc_a.
rewrite wf_rest in W1'.
set (R1' := fun a b => R1 a b /\ P a /\ P b) in *.
assert (W1 := wf_trans W1'); clear W1'.
revert Wa; induction Acc_a as [a Acc_a' IH2].
assert (Acc_a : Acc (compose_rel R2 (refl_trans_clos R1)) a).
apply Acc_intro; trivial.
clear Acc_a'.
revert IH2 Acc_a.
pattern a; apply (well_founded_ind W1); clear a.
intros a IH1 IH2 Acc_a Wa.
apply Acc_intro.
intros b [H1 | H2].
apply IH1.
apply t_step; repeat split; trivial.
apply Inv1 with a; trivial.
intros c H2; apply IH2.
inversion H2 as [c' d' b' H H']; subst.
apply Comp with d'; trivial.
apply refl_trans_clos_is_trans with b; trivial.
right; left; trivial.
apply Acc_intro; intros c H2.
apply Acc_inv with a; trivial.
inversion H2 as [c' d' b' H H']; subst.
apply Comp with d'; trivial.
apply refl_trans_clos_is_trans with b; trivial.
right; left; trivial.
apply Inv1 with a; trivial.
apply IH2.
apply Comp with a; trivial.
apply r_step.
apply Inv2 with a; trivial.
trivial.
Qed.

Lemma acc_union_rest_alt :
  forall A (R1 R2 : relation A) (P : A -> Prop),
  (forall (a b : A), P a -> R1 b a -> P b) -> 
  (forall (a b : A), P a -> R2 b a -> P b) -> 
  (forall a, P a -> Acc R1 a) ->
  (forall a, (forall b, refl_trans_clos R1 b a -> Acc (compose_rel (refl_trans_clos R1) R2) b) -> P a -> Acc (union _ R1 R2) a).
Proof.
intros A R1 R2 P Inv1 Inv2 W1' a W Pa.
assert (H : Acc (union _ (rest P R1) (rest P R2)) a).
rewrite <- acc_union_alt.
intros b H; apply Acc_incl with (compose_rel (refl_trans_clos R1) R2).
clear; intros a1 a2 H; inversion H as [c1 a c2 H1 [H2 _]]; subst.
apply Comp with a; [idtac | assumption].
apply refl_trans_incl with (rest P R1); [idtac | assumption].
clear; intros a1 a2 [H _]; assumption.
apply W.
apply refl_trans_incl with (rest P R1); [idtac | assumption].
clear; intros a1 a2 [H _]; assumption.
rewrite wf_rest in W1'; assumption.
clear W; revert Pa; induction H as [a Acc_a IH].
intro Pa; apply Acc_intro; intros a1 [H1 | H2]; apply IH.
left; repeat split; trivial.
apply Inv1 with a; assumption.
apply Inv1 with a; assumption.
right; repeat split; trivial.
apply Inv2 with a; assumption.
apply Inv2 with a; assumption.
Qed.

Lemma acc_union_rest_alt_weak :
  forall A (R1 R2 : relation A) (P : A -> Prop),
  (forall (a b : A), P a -> R1 b a -> P b) -> 
  (forall (a b : A), P a -> R2 b a -> P b) -> 
  forall a, (forall b, refl_trans_clos (compose_rel R2 (refl_trans_clos R1)) b a -> Acc R1 b) ->
               (forall b, refl_trans_clos R1 b a -> Acc (compose_rel (refl_trans_clos R1) R2) b) -> 
               P a -> Acc (union _ R1 R2) a.
Proof.
intros A R1 R2 P Inv1 Inv2 a H1a H2a Pa.
assert (H : Acc (union _ (rest P R1) (rest P R2)) a).
apply acc_union_alt_weak.
intros b H; apply Acc_incl with R1.
clear; intros a1 a2 [H _]; assumption.
apply H1a.
apply refl_trans_incl with (compose_rel (rest P R2) (refl_trans_clos (rest P R1))); trivial.
clear; intros a1 a2 H; inversion H as [c1 a c2 H1 H2]; subst.
apply Comp with a.
inversion H1; trivial.
apply refl_trans_incl with (rest P R1); [idtac | assumption].
clear; intros a1 a2 [H _]; assumption.

intros b H; apply Acc_incl with (compose_rel (refl_trans_clos R1) R2).
clear; intros a1 a2 H; inversion H as [c1 a c2 H1 [H2 _]]; subst.
apply Comp with a; [idtac | assumption].
apply refl_trans_incl with (rest P R1); [idtac | assumption].
clear; intros a1 a2 [H _]; assumption.
apply H2a.
apply refl_trans_incl with (rest P R1); [idtac | assumption].
clear; intros a1 a2 [H _]; assumption.
clear H1a H2a; revert Pa; induction H as [a Acc_a IH].
intro Pa; apply Acc_intro; intros a1 [H1 | H2]; apply IH.
left; repeat split; trivial.
apply Inv1 with a; assumption.
apply Inv1 with a; assumption.
right; repeat split; trivial.
apply Inv2 with a; assumption.
apply Inv2 with a; assumption.
Qed.

Lemma accR2 : forall A (R : relation A) a, Acc R a <-> Acc (compose_rel R R) a.
Proof.
intros A R a; split.
intro Acc_a; apply Acc_incl with (trans_clos R).
intros x z H; inversion H as [x' y z' H1 H2]; clear H; subst; apply t_trans with y; trivial.
apply t_step; trivial.
apply acc_trans; trivial.
intros Acc_a; induction Acc_a as [a Acc_a IH].
apply Acc_intro; intros b H; apply Acc_intro; intros c H'.
apply IH; apply Comp with b; trivial.
Qed.

Lemma acc_inv_im : 
	forall A B (R1 : relation A) (R2 : relation B) (f : A -> B),
	(forall a1 a2, R1 a1 a2 -> R2 (f a1) (f a2)) ->
	forall a, Acc R2 (f a) -> Acc R1 a.
Proof.
intros A B R1 R2 f H a.
set (b := f a) in *.
assert (b_eq_fa := eq_refl b).
unfold b at 2 in b_eq_fa; clearbody b.
intro Acc_b; revert a b_eq_fa; induction Acc_b as [b Acc_b IH].
intros a b_eq_fa; apply Acc_intro; intros a' H'.
apply IH with (f a'); trivial.
subst b; apply H; trivial.
Qed.

Lemma acc_inv_im2 :
   forall A B (R1 : relation A) (R2 : relation B) (f : A -> B),
  forall a, (forall a1 a2 a3, R1 a3 a2 -> R1 a2 a1 -> refl_trans_clos R1 a1 a -> R2 (f a2) (f a1)) ->
  Acc R2 (f a) -> Acc R1 a.
Proof.
intros A B R1 R2 f a Hinv Acc_b.
set (b := f a) in *.
assert (b_eq_fa := eq_refl b).
unfold b at 2 in b_eq_fa; clearbody b.
revert a b_eq_fa Hinv; induction Acc_b as [b Acc_b IH].
intros a b_eq_fa Hinv.
apply Acc_intro; intros a2 H2.
apply Acc_intro; intros a3 H3.
apply Acc_inv with a2; trivial.
apply IH with (f a2); trivial.
subst b; apply Hinv with a3; trivial.
left.
revert Hinv H2; clear; intros Hinv H2.
intros b1 b2 b3 K3 K2 K1.
apply Hinv with b3; trivial.
inversion K1 as [b | b' a' K1'].
right; left; assumption.
right; apply trans_clos_is_trans with a2; trivial.
left; assumption.
Qed.

Lemma acc_inv_im3 :
   forall A B (R1 : relation A) (R2 : relation B) (f : A -> B),
  forall a, (forall a1 a2, R1 a2 a1 -> refl_trans_clos R1 a1 a -> R2 (f a2) (f a1)) ->
  Acc R2 (f a) -> Acc R1 a.
Proof.
intros A B R1 R2 f a Hinv Acc_b.
set (b := f a) in *.
assert (b_eq_fa := eq_refl b).
unfold b at 2 in b_eq_fa; clearbody b.
revert a b_eq_fa Hinv; induction Acc_b as [b Acc_b IH].
intros a b_eq_fa Hinv.
apply Acc_intro; intros a2 H2.
apply IH with (f a2); trivial.
subst b; apply Hinv; trivial.
left.
revert Hinv H2; clear; intros Hinv H2.
intros b1 b2 K2 K1.
apply Hinv; trivial.
inversion K1 as [b | b' a' K1'].
right; left; assumption.
right; apply trans_clos_is_trans with a2; trivial.
left; assumption.
Qed.

Lemma union_equiv : 
forall A R1 R2 R3 R4 (R1_equiv_R3: forall x y, R1 x y <-> R3 x y)
(R2_equiv_R4: forall x y, R2 x y <-> R4 x y) x y,
(union A R1 R2 x y <-> union _ R3 R4 x y).
Proof.
  intros A R1 R2 R3 R4 R1_equiv_R3 R2_equiv_R4 x y.
  split;intro H;case H.
  rewrite R1_equiv_R3;intro H';left;exact H'.
  rewrite R2_equiv_R4;intro H';right;exact H'.
  rewrite <- R1_equiv_R3;intro H';left;exact H'.
  rewrite <- R2_equiv_R4;intro H';right;exact H'.
Qed.

Lemma union_sym : forall A R1 R2 x y, union A R1 R2 x y <-> union A R2 R1 x y.
Proof. 
  intros A R1 R2 x y.
  split;  (inversion_clear 1;[right|left];assumption).
Qed.

Lemma union_assoc : 
  forall A R1 R2 R3 x y, union A (union A R1 R2) R3 x y <-> union A R1 (union A R2 R3) x y.
Proof.
  intros A R1 R2 R3 x y.
  split.
  intro H.
  case H;clear H;intro H.
  case H;clear H;intro H.
  left;assumption.
  right;left;assumption.
  right;right;assumption.
  intro H.
  case H;clear H;intro H.
  left;left;assumption.
  case H;clear H;intro H.
  left;right;assumption.
  right;assumption.
Qed.

Lemma union_idem : forall A R x y, union A R R x y <-> R x y.
Proof.
  intros A R x y.
  split.
  inversion_clear 1;assumption.
  intro H;left;assumption.
Qed.

Lemma union_idem_strong : forall A (R R': A -> A -> Prop) (H:forall x y, R x y -> R' x y) x y, (union A R R' x y <-> R' x y).
Proof.
  intros A R R' H x y.
  split.
  inversion_clear 1. apply H;assumption.
  assumption.
  intro H';right;assumption.
Qed.


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

Lemma star_equiv :  forall A (R1 R2: A -> A -> Prop), (forall l r, R1 r l <-> R2 r l) -> 
  forall l r, star _ R1 r l <-> star _ R2 r l.
Proof.
  intros A R1 R2 H l r.
  split;induction 1;try constructor.
  constructor 2 with y;auto.
  rewrite H in H1;assumption.
  constructor 2 with y;auto.
  rewrite H;assumption.
Qed.

Set Implicit Arguments.

Inductive product_o A B (R1 : relation A) (R2 : relation B) : relation (A*B)%type :=
	| CaseA : forall a a' b, R1 a a' -> product_o R1 R2 (a,b) (a',b)
	| CaseB : forall a b b', R2 b b' -> product_o R1 R2 (a,b) (a,b').

Lemma acc_and :
   forall A B (R1 : relation A) (R2 : relation B),
   forall a b, Acc R1 a -> Acc R2 b -> Acc (product_o R1 R2) (a,b). 
Proof. 
intros A B R1 R2 a b Acc_a; generalize b; clear b;
induction Acc_a as [a Acc_a IHa].
intros b Acc_b; generalize a Acc_a IHa; clear a Acc_a IHa;
induction Acc_b as [b Acc_b IHb]; intros a Acc_a IHa;
apply Acc_intro; intros [a' b'] H; inversion H; clear H; subst.
apply IHa; trivial.
apply Acc_intro; trivial.
apply IHb; trivial.
Defined.

Definition nf A (R : relation A) t := forall s, R s t -> False.

Lemma acc_nf : forall A (R : relation A) FB, (forall t s, In s (FB t) <-> R s t) ->
                          forall t, Acc R t -> { s : A | nf R s /\ (s = t \/ trans_clos R s t)}.
Proof.
intros A R FB red_dec t Acc_t; induction Acc_t as [t Acc_t IH].
case_eq (FB t).
intro H; exists t; split.
intros s H'; rewrite <- red_dec in H';  rewrite H in H'; trivial.
left; trivial.
intros a l H; destruct (IH a) as [a' [nf_a'  H']].
rewrite <- red_dec; rewrite H; left; trivial.
exists a'; split; trivial.
destruct H' as [a'_eq_a | H'].
subst; right; apply t_step; rewrite <- red_dec; rewrite H; left; trivial.
right; apply trans_clos_is_trans with a; trivial.
apply t_step; rewrite <- red_dec; rewrite H; left; trivial.
Defined.

Lemma dec_nf : forall A (R : relation A) FB, (forall t s, In s (FB t) <-> R s t) ->
                          forall t, {nf R t}+{~nf R t}.
Proof.
intros A R FB red_dec t.
case_eq (FB t).
intro H; left; unfold nf; intros s H'; rewrite <- red_dec in H'; rewrite H in H'; contradiction.
intros a l H.
right; intro H'; apply H' with a.
rewrite <- red_dec; rewrite H; left; trivial.
Defined.

Lemma cycle_not_acc : forall A (R : relation A) (a : A), R a a -> ~Acc R a.
Proof.
intros A R a H Acc_a; generalize H; clear H; 
induction Acc_a as [a Acc_a IH].
intro H; apply (IH a); trivial.
Qed.

