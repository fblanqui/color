(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-01-22

dependancy pairs graph

a more general development is given in AGraph.
*)

Set Implicit Arguments.

From Coq Require Import Lia.
From CoLoR Require ACompat.
From CoLoR Require Import LogicUtil ATrs ListUtil RelUtil RelSub Path ARelation
     SN ListOccur ListNodup AShift VecUtil ASubstitution Iter Cycle.
From CoLoR Require Export ADP.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (list rule).
Notation lhs := (@lhs Sig). Notation rhs := (@rhs Sig).

Variable R : rules.

Variable hyp : rules_preserve_vars R.

Notation DP := (dp R). Notation Chain := (chain R).

Lemma hyp' : rules_preserve_vars DP.

Proof.
apply dp_preserve_vars. exact hyp.
Qed.

(***********************************************************************)
(** dependancy pairs graph *)

Definition dp_graph a1 a2 := In a1 DP /\ In a2 DP
  /\ exists p, exists s,
    int_red R # (sub s (rhs a1)) (sub s (shift p (lhs a2))).

Lemma restricted_dp_graph : is_restricted dp_graph DP.

Proof.
unfold is_restricted, dp_graph, inclusion. intros. intuition.
Qed.

(***********************************************************************)
(** chain relation for a given dependency pair *)

Definition chain_dp a t u := In a DP /\
  exists s, int_red R # t (sub s (lhs a)) /\ u = sub s (rhs a).

Lemma chain_dp_chain : forall a, chain_dp a << Chain.

Proof.
unfold inclusion. intros. destruct H. do 2 destruct H0.
exists (sub x0 (lhs a)). intuition.
subst y. destruct a. simpl. apply hd_red_rule. exact H.
Qed.

Lemma chain_chain_dp : forall t u, Chain t u -> exists a, chain_dp a t u.

Proof.
intros. do 2 destruct H. redtac. subst x. subst u. exists (mkRule l r).
unfold chain_dp. simpl. intuition. exists s. intuition.
Qed.

(***********************************************************************)
(** iteration of chain steps given a list of dependency pairs *)

Fixpoint chain_dps (a : rule) (l : rules) : relation term :=
  match l with
    | nil => chain_dp a
    | b :: m => chain_dp a @ chain_dps b m
  end.

Lemma chain_dps_app : forall l a b m,
  chain_dps a (l ++ b :: m) << chain_dps a l @ chain_dps b m.

Proof. induction l; simpl; intros. refl. assoc. comp. apply IHl. Qed.

Arguments chain_dps_app [l a b m] _ _ _.

Lemma chain_dps_app' : forall a l m b p, a :: l = m ++ b :: p ->
  chain_dps a l << chain_dps a (tail m) % @ chain_dps b p.

Proof.
intros. destruct m; simpl in H; injection H; unfold inclusion; intros.
subst p. subst b. exists x. unfold clos_refl. intuition.
subst r. subst l. simpl. ded (chain_dps_app _ _ H2). do 2 destruct H0.
exists x0. unfold clos_refl. intuition.
Qed.

Arguments chain_dps_app' [a l m b p] _ [x y] _.

Lemma chain_dps_iter_chain :
  forall l a, chain_dps a l << iter Chain (length l).

Proof.
induction l; simpl; intros. apply chain_dp_chain.
comp. apply chain_dp_chain. apply IHl.
Qed.

Lemma iter_chain_chain_dps : forall n t u, iter Chain n t u ->
  exists a, exists l, length l = n /\ chain_dps a l t u.

Proof.
induction n; simpl; intros. ded (chain_chain_dp H). destruct H0.
exists x. exists nil. intuition.
do 2 destruct H. ded (chain_chain_dp H). destruct H1. exists x0.
ded (IHn _ _ H0). do 3 destruct H2. exists (x1 :: x2). simpl. intuition.
exists x. intuition.
Qed.

Arguments iter_chain_chain_dps [n t u] _.

(***********************************************************************)
(** two consecutive chain steps provide a dp_graph step *)

Lemma chain_dp2_dp_graph : forall a1 a2 t u v,
  chain_dp a1 t u -> chain_dp a2 u v -> dp_graph a1 a2.

Proof.
intros. destruct a1 as [l0 r0]. destruct a2 as [l1 r1].
destruct H. simpl in H1. do 2 destruct H1. subst u. rename x into s0.
destruct H0. simpl in H2. do 2 destruct H2. subst v. rename x into s1.
(* [maxvar l0 + 1] for shift *)
unfold dp_graph. intuition. simpl. set (p := maxvar l0 + 1). exists p.
(* take the union of s0 (restricted to [vars l0])
and [comp s1 (shift_inv_sub p l1)] (restricted to [vars (shift p l1)] *)
set (s0' := restrict s0 (vars l0)).
set (s1' := restrict (sub_comp s1 (shift_inv_sub p l1)) (vars (shift p l1))).
set (s := ASubstitution.union s0' s1'). exists s.
(* compatibility *)
assert (compat s0' s1' (vars l0) (vars (shift p l1))). unfold compat. intros.
ded (vars_max H3). ded (in_vars_shift_min H4). unfold p in H6.
absurd (x <= maxvar l0). lia. hyp.
(* domains of substitutions *)
assert (dom_incl s0' (vars l0)). unfold s0'. apply dom_incl_restrict.
assert (dom_incl s1' (vars (shift p l1))). unfold s1'. apply dom_incl_restrict.
(* inclusion in the dp_graph *)
assert (sub s r0 = sub s0' r0). unfold s. eapply sub_union1. apply H5.
apply H3. apply hyp'. hyp. rewrite H6.
assert (sub s0' r0 = sub s0 r0). unfold s0'. sym.
apply sub_restrict_incl. apply hyp'. hyp. rewrite H7.
assert (sub s (shift p l1) = sub s1' (shift p l1)).
unfold s. eapply sub_union2. apply H4. apply H3. refl.
rewrite H8.
assert (sub s1' (shift p l1) = sub s1 l1). unfold s1'.
rewrite <- sub_restrict, <- sub_shift.
refl. rewrite H9. hyp.
Qed.

Lemma chain_dps_path_dp_graph : forall l a b t u,
  chain_dps a (l ++ b :: nil) t u -> path dp_graph a b l.

Proof.
induction l; simpl; intros; do 2 destruct H.
eapply chain_dp2_dp_graph. apply H. apply H0.
ded (IHl _ _ _ _ H0). intuition.
destruct l; simpl in H0; do 2 destruct H0.
eapply chain_dp2_dp_graph. apply H. apply H0.
eapply chain_dp2_dp_graph. apply H. apply H0.
Qed.

Arguments chain_dps_path_dp_graph [l a b t u] _.

(***********************************************************************)
(** hypotheses of the criterion based on cycles
using the same reduction pair for every cycle *)

Import ACompat.

Variables (succ succ_eq : relation term)
  (Hredord : weak_rewrite_ordering succ succ_eq)
  (Hreword : rewrite_ordering succ_eq)
  (Habsorb : absorbs_left succ succ_eq)
  (HcompR : compat succ_eq R)
  (HcompDP : compat succ_eq (dp R))
  (Hwf : WF succ)
  (Hcycle : forall a l, length l < length DP -> cycle_min dp_graph a l ->
    exists b, In b (a :: l) /\ succ (lhs b) (rhs b)).

Notation eq_dec := (@eq_rule_dec Sig).
Notation occur := (occur eq_dec).

(***********************************************************************)
(** compatibility properties of chains *)

Lemma chain_dp_hd_red_mod : forall a, chain_dp a << hd_red_mod R (a::nil).

Proof.
unfold inclusion. intros. destruct H. do 2 destruct H0. subst y.
destruct a. simpl. simpl in H0. exists (sub x0 lhs). split.
apply incl_elim with (R := int_red R #). apply rtc_incl.
apply int_red_incl_red. exact H0. apply hd_red_rule. simpl. auto.
Qed.

Lemma compat_chain_dp : forall a, chain_dp a << succ_eq#.

Proof.
intros. incl_trans (red_mod R DP).
apply incl_trans with Chain; try incl_refl.
apply chain_dp_chain.
incl_trans (hd_red_mod R DP). apply chain_hd_red_mod.
apply hd_red_mod_incl_red_mod. incl_trans (succ_eq!).
apply compat_red_mod_tc; hyp. apply tc_incl_rtc.
Qed.

Lemma compat_chain_dps : forall l a, chain_dps a l << succ_eq#.

Proof.
induction l; simpl; intros. apply compat_chain_dp.
incl_trans (succ_eq# @ succ_eq#).
comp. apply compat_chain_dp. apply IHl. apply comp_rtc_idem.
Qed.

Lemma compat_chain_dp_strict : forall a,
  succ (lhs a) (rhs a) -> chain_dp a << succ.

Proof.
unfold inclusion. intros. destruct H0. do 2 destruct H1. subst y.
apply (absorbs_left_rtc Habsorb). exists (sub x0 (lhs a)). split.
apply incl_elim with (R := int_red R #). 2: exact H1.
apply rtc_incl.
incl_trans (red R). apply int_red_incl_red. apply compat_red; hyp.
destruct Hredord. apply H2. exact H.
Qed.

(***********************************************************************)
(** proof of the criterion based on cycles *)

Lemma WF_cycles : WF (chain R).

Proof.
(* we prove it by looking at paths of length n+3, where n = length DP *)
set (n := length DP). apply WF_iter with (S n). intro.
(* we proceed by induction on succ @ succ_eq# *)
assert (Hwf' : WF (succ @ succ_eq#)). apply absorb_WF_modulo_r; hyp.
gen (Hwf' x). induction 1. apply SN_intro; intros. apply H0.
(* path in the dp_graph corresponding to the chains *)
ded (iter_chain_chain_dps H1). do 3 destruct H2.
assert (length x1 > 0). lia. ded (last_intro H4). do 3 destruct H5.
clear H4. rewrite H5 in H3. ded (chain_dps_path_dp_graph H3).
(* pigeon-hole principle: there is a dp visited twice *)
set (l' := x0 :: x2 ++ x3 :: nil). assert (exists z, occur z l' >= 2).
unfold l'. eapply long_path_occur. apply restricted_dp_graph. apply H4.
rewrite H6, H2. unfold n. lia.
(* we prove (A): in this cycle, a dp is included in succ *)
assert (exists l, exists a, exists m,
  l' = l ++ a :: m /\ succ (lhs a) (rhs a)).
destruct H7. set (p := occur x4 l' - 2). assert (occur x4 l' = S (S p)).
unfold p. lia. ded (occur_S eq_dec H8). do 3 destruct H9. destruct H10.
clear H8. rewrite H9. ded (occur_S eq_dec H11). do 3 destruct H8.
destruct H12. clear H11. clear H13. clear p. rewrite H8. rewrite H8 in H9.
clear H8. clear H10.
(* cycle min *)
assert (cycle dp_graph x4 x7). unfold cycle. eapply sub_path. unfold l' in H9.
apply H9. exact H4. ded (cycle_min_intro eq_dec H8). decomp H10.
(* length x11 < length DP *)
assert (length l' = n+2). unfold l'. simpl. rewrite <- H5. lia.
rewrite H9 in H10. change (length (x5++(x4::x7)++x4::x8) = n+2) in H10.
rewrite H11 in H10. repeat (rewrite length_app in H10; simpl in H10).
unfold n in H10. assert (h : length x11 < length DP).
unfold cycle_min in H14. destruct H14. assert (length (x10::x11) <= length DP).
apply nodup_incl_length. apply eq_dec. exact H14.
apply incl_appr_incl with (x10::nil). simpl. eapply restricted_path_incl.
apply restricted_dp_graph. exact H13. simpl in H15. lia. clear H10.
(* end of the proof of (A) *)
ded (Hcycle h H14). do 2 destruct H10. ded (in_elim H10).
do 2 destruct H15. exists (x5++x9++x14). exists x13. exists (x15++x12++x4::x8).
intuition. rewrite !app_ass. trans (x5++(x4::x7)++x4::x8). refl.
rewrite H11, app_ass. trans (x5++x9++(x10::x11)++x12++x4::x8).
simpl. rewrite app_ass. refl. rewrite H15, app_ass. refl.
(* consequence of (A) *)
do 4 destruct H8. unfold l' in H8. ded (chain_dps_app' H8 H3).
do 2 destruct H10.
(* succ_eq# x x7 *)
assert (succ_eq# x x7). destruct H10. subst x7. intuition.
eapply incl_elim. eapply compat_chain_dps. apply H10.
(* (succ @ succ_eq#) x7 y *)
assert ((succ @ succ_eq#) x7 y). destruct x6; simpl in H11.
ded (compat_chain_dp_strict H9 H11). exists y. intuition.
do 2 destruct H11. exists x8. split. eapply incl_elim.
apply (compat_chain_dp_strict H9). exact H11.
eapply incl_elim. eapply compat_chain_dps. apply H13.
(* (succ @ succ_eq#) x y *)
do 2 destruct H13. exists x8. intuition.
eapply incl_elim with (R := succ_eq# @ succ). apply absorbs_left_rtc.
intuition. exists x7. intuition.
Qed.

End S.
