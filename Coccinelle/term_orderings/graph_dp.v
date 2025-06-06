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

From Stdlib Require Import List Relations Wellfounded Arith Recdef Setoid.
From CoLoR Require Import closure more_list weaved_relation term_spec
     equational_theory_spec.
From CoLoR Require Export dp.

Module MakeGDP (E : EqTh).

  Import E.
  Import T.

  Module Dp := dp.MakeDP (E).
  Import Dp.

Definition dpi comp i (v u : term) := comp (u,v) = i /\ i <> 0.


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

Lemma split_rel :
  forall dpR R (comp : term * term -> nat) 
  (comp_approx : forall uv uv', are_connected dpR R uv uv' -> comp uv <= comp uv') 
  (comp_def_on_dps : forall u v, comp (u,v) <> 0 <-> dpR v u) 
  (split_graph : 
    exists n0,  forall u v, (dpR v u) <-> (exists i, i <= n0 /\ dpi comp i v u)),
   forall P,  well_founded (rest P (rdp_step (axiom dpR) R))  <-> 
  (forall n, well_founded (rest P (rdp_step (axiom (dpi comp n)) R))).
Proof.
intros dpR R comp comp_approx comp_def_on_dps split_graph P.
split.
intros W n; revert W; apply wf_incl; intros s t [K [As At]].
inversion K as [f l1 l2 s' H1 H2]; subst.
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst.
split; [ | split; assumption].
constructor 1 with l2; trivial.
rewrite <- H5; constructor.
rewrite <- comp_def_on_dps.
destruct n as [ | n].
destruct H3 as [ _ H3]; apply False_rect; apply H3; apply eq_refl.
destruct H3 as [H3 _]; rewrite H3; discriminate.

destruct split_graph as [n G].
revert comp comp_approx comp_def_on_dps G.
induction n as [ | n]; intros  comp comp_approx comp_def_on_dps G.
intros _ t; apply Acc_intro.
intros s [K [As At]].
inversion K as [f l1 l2 s' H1 H2]; subst.
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst.
rewrite G in H3.
destruct H3 as [ [ | i] [i_le_0 Hi]].
destruct Hi as [_ Hi]; apply False_rect; apply Hi; apply eq_refl.
inversion i_le_0.
intros W.
destruct n as [ | n].
(* 1/2 there is only one component *)
apply wf_incl with (rest P (rdp_step (axiom (dpi comp 1)) R)).
intros s t [K [As At]]; split; [ | split; assumption].
inversion K as [f l1 l2 s' H1 H2]; subst.
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst.
rewrite G in H3; destruct H3 as [[ | [ | i]] [i_le_1 [H3 i_diff_0]]].
apply False_rect; apply i_diff_0; apply eq_refl.
constructor 1 with l2; trivial.
rewrite <- H5; constructor.
split; trivial.
assert (H := le_S_n _ _ i_le_1); inversion H.
apply (W 1).
(* 1/1, there are at least two components, apply the induction hypothesis by merging the components 1 and 2 *)
set (comp' := fun uv => match comp uv with 0 => 0 | S 0 => S 0 | S (S n) => S n end).
apply (IHn comp'); clear IHn.
(* 1/4 *)
intros uv uv' H; generalize (comp_approx _ _ H); unfold comp'.
destruct (comp uv) as [ | [ | c]];
destruct (comp uv') as [ | [ | c']]; auto with arith.
(* 1/3 *)
intros u v; rewrite <- (comp_def_on_dps u v).
unfold comp'; destruct (comp (u,v)) as [ | [ | i]]; split; intro; (trivial || discriminate).
(* 1/2 *)
intros u v; rewrite G; split.
intros [[ | [ | i]] [i_le_n Hi]].
destruct Hi as [_ Hi]; apply False_rect; apply Hi; apply eq_refl.
destruct Hi as [Hi _]; exists 1; split.
apply le_n_S; apply Nat.le_0_l.
split; [unfold comp'; rewrite Hi; apply eq_refl | discriminate].
exists (S i); split.
apply le_S_n; assumption.
split; [destruct Hi as [Hi _] | discriminate].
unfold comp'; rewrite Hi; apply eq_refl.

intros [[ | i] [i_le_Sn Hi]].
destruct Hi as [_ Hi]; apply False_rect; apply Hi; apply eq_refl.
destruct Hi as [Hi _]; exists (comp (u,v)); split.
unfold comp' in Hi; destruct (comp (u,v)) as [ | [ | c]]; 
[ discriminate 
| apply le_n_S; apply Nat.le_0_l 
| injection Hi; intros; subst; apply le_n_S; assumption].
split; [apply eq_refl | unfold comp' in Hi; destruct (comp (u,v)); discriminate].

(* 1/1 *)
intros [ | [ | n0]].
(* 1/3 The component 0 is well founded *)
apply wf_incl with (rest P (rdp_step (axiom (dpi comp 0)) R)).
intros s t [K [As At]]; split; [ | split; assumption].
inversion K as [f l1 l2 s' H1 H2]; subst.
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst.
destruct H3 as [_ i_diff_0]; apply False_rect; apply i_diff_0; apply eq_refl.
apply W.
(* 1/2 The new component 1 (i.e. the union of old components 1 and 2) is well founded *)
apply wf_incl with (union _ (rest P (rdp_step (axiom (dpi comp 2)) R))
                                   (rest P (rdp_step (axiom (dpi comp 1)) R))).
intros s t [K [As At]];
inversion K as [f l1 l2 s' H1 H2]; subst;
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst;
destruct H3 as [H3 _]; unfold comp' in H3.
case_eq (comp (t2,t1)).
intro c_eq_0; rewrite c_eq_0 in H3; discriminate.
intros [ | [ | i]] c_eq_i; rewrite c_eq_i in H3.
right; split; [ | split; assumption].
constructor 1 with l2; trivial.
rewrite <- H5; constructor.
split; [assumption | discriminate].
left; split; [ | split; assumption].
constructor 1 with l2; trivial.
rewrite <- H5; constructor.
split; [assumption | discriminate].
discriminate H3.
clear comp'.
intro a; rewrite <- (acc_union_alt _ (W 2)).
intros t _; clear a.
pattern t; apply (well_founded_ind (W 1)); clear t; intro t.
set (R1 := rest P (rdp_step (axiom (dpi comp 1)) R)) in *.
set (R2 := rest P (rdp_step (axiom (dpi comp 2)) R)) in *.
intros IH1.
rewrite accR2; apply Acc_intro; intros s H; rewrite <- accR2.
inversion H as [a1 a3 a5 H13 H35]; clear H; subst s t.
inversion H35 as [a3' a4 a5' H34 H45]; subst a3' a5'.
inversion H34 as [a34 | a3' a4' K34]; clear H34.
subst a3 a4.
apply Acc_inv with a34; [ apply IH1 | ]; assumption.
subst a3' a4'.
assert (H : exists a, R2 a a4).
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
rewrite <- comp_def_on_dps; destruct H0 as [e _]; rewrite e; discriminate.
split.
rewrite <- comp_def_on_dps; destruct H1 as [e _]; rewrite e; discriminate.
rewrite H7; rewrite <- H3; split; trivial.
generalize (comp_approx _ _ C).
destruct H0 as [e _]; rewrite e.
destruct H1 as [e' _]; rewrite e'.
intro Abs; generalize (le_S_n _ _ Abs); clear Abs; intro Abs; inversion Abs.
(* 1/1 The new component n+2 (i.e. the old component n+1) is well founded *)
apply wf_incl with (rest P (rdp_step (axiom (dpi comp (S (S (S n0))))) R)).
intros s t [K [As At]]; split; [ | split; assumption].
inversion K as [f l1 l2 s' H1 H2]; subst.
inversion H2 as [t1 t2 sigma H3 H4 H5]; subst.
constructor 1 with l2; trivial.
rewrite <- H5; constructor.
split; [ | discriminate].
destruct H3 as [H3 _]; unfold comp' in H3; destruct (comp (t2,t1)) as [ | [ | c]].
discriminate H3.
discriminate H3.
injection H3; intros; subst; apply eq_refl.
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


End MakeGDP.
