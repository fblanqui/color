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

From Stdlib Require Import Setoid Relations List Utf8.

Inductive trans_clos (A : Type) (R : relation A) : relation A:=
  | t_step : forall x y, R x y -> trans_clos R x y
  | t_trans : forall x y z, R x y -> trans_clos R y z -> trans_clos R x z.

Lemma trans_clos_is_trans :
  forall A  (R : relation A) a b c, trans_clos R a b -> trans_clos R b c -> trans_clos R a c.
Proof.
intros A R a b c Hab; revert c; induction Hab as [a b Hab | a b c Hab Hbc].
intros c Hbc; apply t_trans with b; trivial.
intros d Hcd; apply t_trans with b; trivial.
apply IHHbc; trivial.
Qed.

Lemma trans_clos_is_clos :
  forall A  (R : relation A) a b, trans_clos (trans_clos R) a b -> trans_clos R a b.
Proof.
intros A R a b Hab; induction Hab as [a b Hab | a b c Hab Hbc]; trivial.
apply trans_clos_is_trans with b; trivial.
Qed.


Lemma trans_inversion :
  forall A (R : relation A) a b, trans_clos R a b -> (R a b \/ (exists c, trans_clos R a c /\ R c b)).
Proof.
intros A R a b H; induction H as [ a b H | a b c H H' [IH | IH]].
left; trivial.
right; exists b; split; trivial; apply t_step; trivial.
destruct IH as [d [H'' H''']]; right; exists d; split; trivial.
apply trans_clos_is_trans with b; trivial; apply t_step; trivial.
Qed.

Lemma inv_trans :
  forall A (R : relation A) (P : A -> Prop),
  (forall a b, P a -> R a b -> P b) -> 
  forall a b, P a -> trans_clos R a b -> P b.
Proof.
intros A R P Inv a b Pa a_Rp_b; induction a_Rp_b.
apply Inv with x; trivial.
apply IHa_Rp_b; apply Inv with x; trivial.
Qed.

Lemma trans_incl :
  forall A (R1 R2 : relation A), inclusion _ R1 R2 -> inclusion _ (trans_clos R1) (trans_clos R2).
Proof.
intros A R1 R2 R1_in_R2 a b H; induction H as [a' b' H | a' b' c' H1 H2].
apply t_step; apply R1_in_R2; trivial.
apply t_trans with b'; trivial.
apply R1_in_R2; trivial.
Qed.

Inductive refl_trans_clos (A : Type) (R : relation A) : relation A:=
  | r_step : forall x, refl_trans_clos R x x
  | t_clos : forall x y, trans_clos R x y -> refl_trans_clos R x y.

Lemma refl_trans_clos_is_trans :
  forall A  (R : relation A) a b c, 
  refl_trans_clos R a b -> refl_trans_clos R b c -> refl_trans_clos R a c.
Proof.
intros A R a b c [a' | a' b' Hab]; subst; trivial.
intro Hbc; revert Hbc Hab; intros [b'' | b'' c' Hbc] Hab; subst; trivial.
apply t_clos; assumption.
apply t_clos; apply trans_clos_is_trans with b''; assumption.
Qed.

Lemma refl_trans_clos_is_refl_trans_clos :
  forall A (R : relation A) a b, refl_trans_clos R a b <-> a = b \/ trans_clos R a b.
Proof.
intros A R a b; split; intro H.
inversion H as [a' | a' b'].
left; apply eq_refl.
right; assumption.
destruct H as [H | H].
subst b; apply r_step.
apply t_clos; assumption.
Qed.

Inductive trans_clos_alt (A : Type) (R : relation A) : relation A:=
  | t_step_alt : forall x y, R x y -> trans_clos_alt R x y
  | t_trans_lat : forall x y z, trans_clos_alt R x y -> R y z -> trans_clos_alt R x z.

Lemma trans_clos_alt_is_trans :
  forall A  (R : relation A) a b c, 
  trans_clos_alt R a b -> trans_clos_alt R b c -> trans_clos_alt R a c.
Proof.
intros A R a b c Hab Hbc; revert a Hab.
induction Hbc as [b c Hbc | b c d Hbc Hcd]; intros a Hab.
right with b; trivial.
right with c; trivial.
apply Hcd; trivial.
Qed.

Lemma trans_clos_trans_clos_alt : 
  forall A (R : relation A) x y, trans_clos R x y <-> trans_clos_alt R x y.
Proof.
intros A R; split; intro H; induction H.
left; assumption.
apply trans_clos_alt_is_trans with y; trivial.
left; assumption.
left; assumption.
apply trans_clos_is_trans with y; trivial.
left; assumption.
Qed.

Lemma trans_clos_dec :
  forall (A : Type) eq_bool, (forall a b : A, match eq_bool a b with true => a = b | false => a <> b end) ->
  forall (R : relation A) Rlist, (forall a b, R a b <-> In (a,b) Rlist) ->
   forall a b, {trans_clos R a b}+{~trans_clos R a b}.
Proof.
intros A eq_bool eq_bool_ok R Rlist; revert R; induction Rlist as [ | [u v] Rlist]; intros R Rlist_ok a b.
right; intro H; inversion H as [x y K | x y z K1 K2]; subst.
rewrite Rlist_ok in K; contradiction.
rewrite Rlist_ok in K1; contradiction.
revert a b; set (R' := fun a b => R a b /\ In (a,b) Rlist).
assert (Rlist_ok' : forall a b, R' a b <-> In (a,b) Rlist).
intros a b; split; intro H.
destruct H as [_ H]; assumption.
split; [rewrite Rlist_ok; right | ]; assumption.
assert (H := IHRlist _ Rlist_ok').

assert (split_case : forall a b, trans_clos R a b <-> (trans_clos R' a b \/ 
                                                                               (refl_trans_clos R' a u /\ refl_trans_clos R' v b))).
assert (R'_in_R : inclusion _ R' R).
intros x y [K _]; assumption.
assert (Ruv : R u v).
rewrite Rlist_ok; left; apply eq_refl.
intros a b; split; [intro H1 | intros [H1 | [H1 H2]]].
induction H1 as [a b H1 | a b c H1 H2];
rewrite Rlist_ok in H1; simpl in H1; destruct H1 as [H1 | H1].
injection H1; intros; subst; right; split; left.
do 2 left; rewrite Rlist_ok'; assumption.
injection H1; clear H1; intros; subst.
destruct IHH2 as [H3 | H3].
right; split; [left | right; assumption].
destruct H3 as [_ H3]; right; split; [left | assumption].
rewrite <- Rlist_ok' in H1.
destruct IHH2 as [H3 | [H3 H3']].
left; right with b; assumption.
right; split; [ apply refl_trans_clos_is_trans with b; [right; left | ] | ]; assumption.
apply trans_incl with R'; [apply R'_in_R | ]; assumption.
inversion H1 as [x | x y K1]; clear H1; subst.
inversion H2 as [x' | x' y' K2]; clear H2; subst.
left; apply Ruv.
right with v; [rewrite Rlist_ok; left; apply eq_refl | apply trans_incl with R'; [apply R'_in_R | ]; assumption].
apply trans_clos_is_trans with u; [apply trans_incl with R'; [apply R'_in_R | assumption] | ].
inversion H2 as [x' | x' y' K2]; clear H2; subst.
left; assumption.
right with v; [rewrite Rlist_ok; left; apply eq_refl | apply trans_incl with R'; [apply R'_in_R | ]; assumption].

assert (Hrefl : forall a b, {refl_trans_clos R' a b}+{~refl_trans_clos R' a b}).
intros a b; generalize (eq_bool_ok a b); destruct (eq_bool a b); [intro a_eq_b; subst; do 2 left | intro a_diff_b].
destruct (H a b) as [Hab | Hab].
left; right; assumption.
right; intro K; inversion K; subst; [apply a_diff_b; apply eq_refl | apply Hab; assumption].
intros a b; destruct (H a b) as [Hab | Hab].
left; apply trans_incl with R'; [intros x y [K _] | ]; assumption.
destruct (Hrefl a u) as [Hau | Hau].
destruct (Hrefl v b) as [Hvb | Hvb].
left; rewrite split_case; right; split; assumption.
right; intro K; rewrite split_case in K; destruct K as [K | [H1 H2]].
apply Hab; assumption.
apply Hvb; assumption.
right; intro K; rewrite split_case in K; destruct K as [K | [H1 H2]].
apply Hab; assumption.
apply Hau; assumption.
Defined.


Lemma refl_trans_clos_dec :
  forall (A : Type) eq_bool, (forall a b : A, match eq_bool a b with true => a = b | false => a <> b end) ->
  forall (R : relation A) Rlist, (forall a b, R a b <-> In (a,b) Rlist) ->
   forall a b, {refl_trans_clos R a b}+{~refl_trans_clos R a b}.
Proof.
intros A eq_bool eq_bool_ok R Rlist Rlist_ok a b.
generalize (eq_bool_ok a b); destruct (eq_bool a b); [intro a_eq_b; subst; do 2 left | intro a_diff_b].
destruct (trans_clos_dec _ eq_bool_ok _ _ Rlist_ok a b) as [Hab | Hab].
left; right; assumption.
right; intro K; inversion K; subst; [apply a_diff_b; apply eq_refl | apply Hab; assumption].
Defined.



