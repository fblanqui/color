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


(** * Termination of rewriting *)

From Coq Require Import List Relations Wellfounded Arith Recdef Setoid.
From CoLoR Require Import closure more_list weaved_relation term_spec
     equational_theory_spec.
From CoLoR Require Export dp.

Module MakeIGDP (E : EqTh).

  Import E.
  Import T.
  Module Dp := dp.MakeDP (E).
  Import Dp.


Inductive hide_in_context R : relation term :=
  Hide_in_context : forall f l1 l2, (one_step_list (one_step R)) l1 l2 -> hide_in_context R (Term f l1) (Term f l2).

Lemma expand_dp : forall dpR R t f l, 
   rdp_step dpR R t (Term f l) <-> compose_rel dpR (refl_trans_clos (hide_in_context R)) t (Term f l).
Proof.
intros dpR R t f l; split.
intro H; inversion H as [g l1 l2 H1 H2 H3]; subst.
constructor 1 with (Term f l2); trivial.
inversion H2 as [k | k1 k2 K2]; subst.
left.
right; clear -K2; induction K2 as [l1 l2 H | l1 l2 l3 H1 H2].
left; constructor; assumption.
right with (Term f l2); [ constructor | ]; assumption.
intro H; inversion H as [u1 u2 u3 H1 H2]; subst.
assert (K : exists l2, u2 = Term f l2 /\ refl_trans_clos (one_step_list (one_step R)) l2 l).
clear -H2; inversion H2 as [u | u1 v2 K2]; clear H2; subst.
exists l; split; [apply eq_refl | left].
set (s := Term f l) in *.
assert (s_eq_fl := eq_refl s).
unfold s at 2 in s_eq_fl; clearbody s.
revert f l s_eq_fl; induction K2 as [t1 t2 K | t1 t2 t3 K1 K2]; intros f l s_eq_fl.
inversion K as [f' l1 l2]; clear K; subst.
injection H1; clear H1; intros; subst f' l2.
exists l1; split; [apply eq_refl | right; left; assumption].
inversion K1 as [f' l1 l2]; clear K1; subst.
destruct (IHK2 _ _ (eq_refl _)) as [l3 [J1 J2]].
injection J1; clear J1; intros; subst f' l3.
exists l1; split; [apply eq_refl | apply refl_trans_clos_is_trans with l2; [right; left | ]; assumption].
destruct K as [l2 [J1 J2]].
subst u2; constructor 1 with l2; assumption.
Qed.

(* Definition dpi comp i (v u : term) := comp (u,v) = i /\ i <> 0. *)

Lemma split_rel :
  forall dpR R (comp : (term * term) -> nat -> Prop) 
  (comp_approx : forall uv uv', are_connected dpR R uv uv' -> forall n n', comp uv n -> comp uv' n' -> n <= n') 
  (comp_def_on_dps : forall u v, (exists n, comp (u,v) n) <-> dpR v u) 
  (split_graph : 
    exists n0,  forall uv n, comp uv n -> n <= n0),
   forall P,  well_founded (rest P (rdp_step (axiom dpR) R))  <-> 
  (forall n, well_founded (rest P (rdp_step (axiom (fun v u => comp (u,v) n)) R))).
Proof.
intros dpR R comp comp_approx comp_def_on_dps split_graph P.
split; intro W.
intros n; revert W; apply wf_incl; intros s t [K [As At]].
inversion K as [f l1 l2 s' H1 H2]; subst.
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst.
split; [ | split; assumption].
constructor 1 with l2; trivial.
rewrite <- H5; constructor.
rewrite <- comp_def_on_dps; exists n; assumption.

destruct split_graph as [n G].
revert comp comp_approx comp_def_on_dps G W.
induction n as [ | n]; intros  comp comp_approx comp_def_on_dps G W.
(* 1/2 there is only one component *)
apply wf_incl with (rest P (rdp_step (axiom (fun v u : term => comp (u, v) 0)) R)).
intros s t [K [As At]]; split; [ | split; assumption].
inversion K as [f l1 l2 s' H1 H2]; subst.
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst.
constructor 1 with l2.
assumption.
rewrite <- H5; apply instance.
rewrite <- comp_def_on_dps in H3.
destruct H3 as [n H3].
assert (H6 := G _ _ H3); inversion H6; subst n; assumption.
apply (W 0).

(* 1/1, there are at least two components, apply the induction hypothesis by merging the components 1 and 2 *)
set (comp' := fun uv m => match m with 0 => comp uv 0 \/ comp uv 1 | S n => comp uv (S m) end).
apply (IHn comp'); clear IHn.
(* 1/4 *)
intros uv uv' H; assert (K := comp_approx _ _ H); unfold comp'.
intros [ | c] [ | c'].
intros _ _; apply le_n.
intros _ _; apply Nat.le_0_l.
intros J [J' | J'].
assert (J'' := K _ _ J J'); inversion J''.
apply (le_S_n _ _ (K _ _ J J')).
intros J J'; apply (le_S_n _ _ (K _ _ J J')).
(* 1/3 *)
intros u v; rewrite <- (comp_def_on_dps u v).
unfold comp'; split.
intros [[ | n0] H].
destruct H as [H | H]; [exists 0 | exists 1]; assumption.
exists (S (S n0)); assumption.
intros [[ | [ | n0]] H].
exists 0; left; assumption.
exists 0; right; assumption.
exists (S n0); assumption.
(* 1/2 *)
unfold comp'; intros [u v] [ | n0].
intros _; apply Nat.le_0_l.
intro K; apply le_S_n; apply (G _ _ K).

(* 1/1 *)
intros [ | n0].
(* 1/2 The new component 0 (i.e. the union of old components 0 and 1) is well founded *)
apply wf_incl with (union _ (rest P (rdp_step (axiom (fun v u : term => comp (u, v) 1)) R))
                                   (rest P (rdp_step (axiom (fun v u : term => comp (u, v) 0)) R))).
intros s t [K [As At]];
inversion K as [f l1 l2 s' H1 H2]; subst;
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst.
unfold comp' in H3; destruct H3 as [H3 | H3].
right; split; [ | split; assumption].
constructor 1 with l2.
assumption.
rewrite <- H5; constructor; assumption.
left; split; [ | split; assumption].
constructor 1 with l2.
assumption.
rewrite <- H5; constructor; assumption.
clear comp'.
intro a; rewrite <- (acc_union_alt _ (W 1)).
intros t _; clear a.
pattern t; apply (well_founded_ind (W 0)); clear t; intro t.
set (R0 := rest P (rdp_step (axiom (fun v u : term => comp (u, v) 0)) R)) in *.
set (R1 := rest P (rdp_step (axiom (fun v u : term => comp (u, v) 1)) R)) in *.
intros IH0.
rewrite accR2; apply Acc_intro; intros s H; rewrite <- accR2.
inversion H as [a1 a3 a5 H13 H35]; clear H; subst s t.
inversion H35 as [a3' a4 a5' H34 H45]; subst a3' a5'.
inversion H34 as [a34 | a3' a4' K34]; clear H34.
subst a3 a4.
apply Acc_inv with a34; [ apply IH0 | ]; assumption.
subst a3' a4'.
assert (H : exists a, R1 a a4).
rewrite trans_clos_trans_clos_alt in K34; inversion K34 as [a3' a4' H34 | a3' a a4' H3 H4]; clear K34; subst a3' a4'.
exists a3; assumption.
exists a; assumption.
destruct H as [a H]; apply False_rect.
destruct H45 as [H45 _]; destruct H as [H _].
inversion H45 as [f l5 l4 t4 H5 H4]; subst a4 a5; inversion H4 as [v4 u4 sigma4]; subst t4.
inversion H as [g k4 l t K4 K]; subst a; inversion K as [v u sigma]; subst t.
assert (C : are_connected dpR R (u,v) (u4,v4)).
exists sigma4; exists sigma.
split.
rewrite <- comp_def_on_dps; exists 0; assumption.
split.
rewrite <- comp_def_on_dps; exists 1; assumption.
rewrite H7; rewrite <- H3; split; trivial.
assert (Abs := comp_approx _ _ C _ _ H1 H0); inversion Abs.
(* 1/1 The new component n+1 (i.e. the old component n+2) is well founded *)
apply wf_incl with (rest P (rdp_step (axiom (fun v u : term => comp (u, v) (S (S n0)))) R)).
intros s t [K [As At]]; split; [ | split; assumption].
inversion K as [f l1 l2 s' H1 H2]; subst.
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst.
constructor 1 with l2; trivial.
apply W.
Qed.

Inductive lex o1 lo1 o2 : relation term :=
  | Comp1 : forall s t, o1 s t -> lex o1 lo1 o2 s t
  | Comp2 : forall s t, lo1 s t -> o2 s t -> lex o1 lo1 o2 s t.

Lemma wf_lex : 
  forall (o1 lo1 o2 : relation term), (forall t1 t2 t3, o1 t1 t2 -> lo1 t2 t3 -> o1 t1 t3) ->
  well_founded o1 -> well_founded o2 -> well_founded (lex o1 lo1 o2).
Proof.
intros o1 lo1 o2 Transo W1 W2.
intro t; apply (well_founded_ind W1); clear t.
intro t; pattern t; apply (well_founded_ind W2); clear t.
intros t IH2 IH1; apply Acc_intro.
intros s H; inversion H as [u1 u2 K | u1 u2 K1 K2]; subst.
apply IH1; assumption.
apply IH2.
assumption.
intros u K3; apply IH1; apply Transo with s; assumption.
Defined.

Lemma remove_edge :
  forall (dpR R : relation term) P u0 v0 (lo so : relation term), 
  (forall t, lo t t) ->
  (forall t1 t2 t3, lo t1 t2 -> lo t2 t3 -> lo t1 t3) ->
  (forall t1 t2 t3, so t1 t2 -> lo t2 t3 -> so t1 t3) ->
  well_founded so ->
  (forall s t, one_step R s t -> lo s t) ->
  (forall u v, dpR v u -> forall sigma, lo (apply_subst sigma v) (apply_subst sigma u)) ->
  (forall sigma, so  (apply_subst sigma v0) (apply_subst sigma u0)) ->
  well_founded  (rest P (rdp_step (axiom dpR) R)) -> 
  well_founded  (rest P (rdp_step (axiom (union _ (fun s t => (s,t) = (v0,u0)) dpR)) R)).
Proof.
intros dpR R P u0 v0 lo so lo_refl lo_trans Transo Wo Hlo Hlo' Hso W.
assert (WW := wf_lex _ _ _ Transo Wo W).
intro t; apply (well_founded_ind WW); clear t.
intros t IH; apply Acc_intro; intros s H; apply IH; clear WW IH.
destruct H as [H [Ps Pt]].
inversion H as [f l1 l2 v K1 K2]; clear H; subst.
inversion K2 as [v u sigma [K3 | K3]]; clear K2; subst.
injection K3; clear K3; intros; subst u v.
left; apply Transo with (Term f l2).
rewrite <- H0; apply Hso.
inversion K1 as [l | k1 k2 K]; clear K1; subst.
apply lo_refl.
clear Pt H0; induction K as [k1 k2 K | k1 k2 k3 K1 K2].
apply Hlo; apply in_context; assumption.
apply lo_trans with (Term f k2); [apply Hlo; apply in_context | ]; assumption.
right.
apply lo_trans with (Term f l2).
rewrite <- H0; apply Hlo'; assumption.
inversion K1 as [l | k1 k2 K]; clear K1; subst.
apply lo_refl.
clear Pt H0; induction K as [k1 k2 K | k1 k2 k3 K1 K2].
apply Hlo; apply in_context; assumption.
apply lo_trans with (Term f k2); [apply Hlo; apply in_context | ]; assumption.
split; [ constructor 1 with l2; [ | rewrite <- H0; apply instance] | split]; assumption.
Qed.


End MakeIGDP.
