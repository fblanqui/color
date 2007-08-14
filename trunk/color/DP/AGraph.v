(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- DucasLeo, 2007-01-22

Agraph
*)
(** head rules graph, generalisation of ADPGraph to S @ (hd_red R)
instead of (int_red R #) @ (dp R) *)

Set Implicit Arguments.

Require Export LogicUtil.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).

Require Export ATrs.

Notation rule := (rule Sig).
Notation rules := (list rule).
Notation lhs := (@lhs Sig).
Notation rhs := (@rhs Sig).

Section S1.
Variable S : relation term.
Variable R : rules.
Variable hyp : rules_preserv_vars R.


(***********************************************************************)

Require Export ARename.

Definition hd_red_Mod :=  S @ (hd_red R).



Definition hd_rules_graph a1 a2 := In a1 R /\ In a2 R
  /\ exists p, exists s,
    S (app s (rhs a1)) (app s (shift p (lhs a2))).

Lemma restricted_dp_graph : is_restricted hd_rules_graph R.

Proof.
unfold is_restricted, hd_rules_graph, inclusion. intros. intuition.
Qed.

(***********************************************************************)

Definition hd_red_Mod_rule a t u := In a R /\
  exists s, S t (app s (lhs a)) /\ u = app s (rhs a).

Lemma chain_hd_rules_hd_red_Mod : forall a, hd_red_Mod_rule a << hd_red_Mod.
Proof.
unfold inclusion. intros. destruct H. do 2 destruct H0.
exists (app x0 (lhs a)). split;auto. 
subst y. destruct a. simpl in *. unfold hd_red. exists lhs;exists rhs;exists x0. auto.
Qed.


Lemma hd_red_Mod_chain_hd_rules : forall t u, hd_red_Mod t u-> exists a, hd_red_Mod_rule a t u.
Proof.
intros. do 2 destruct H. do 3 destruct H0.  exists (mkRule x0 x1).
unfold hd_red_Mod_rule. simpl. intuition. exists x2. intuition.
subst. auto.
Qed.

Lemma hd_red_Mod_rule2_hd_rules_graph : forall a1 a2 t u v,
  hd_red_Mod_rule a1 t u -> hd_red_Mod_rule a2 u v -> hd_rules_graph a1 a2.

Proof.
intros. destruct a1 as [l0 r0]. destruct a2 as [l1 r1].
destruct H. simpl in H1. do 2 destruct H1. subst u. rename x into s0.
destruct H0. simpl in H2. do 2 destruct H2. subst v. rename x into s1.
(* [maxvar l0 + 1] for shift *)
unfold hd_rules_graph. intuition. simpl. set (p := maxvar l0 + 1). exists p.
(* take the union of s0 (restricted to [vars l0])
and [comp s1 (shift_inv_sub p l1)] (restricted to [vars (shift p l1)] *)
set (s0' := restrict s0 (vars l0)).
set (s1' := restrict (comp s1 (shift_inv_sub p l1)) (vars (shift p l1))).
set (s := ASubstitution.union s0' s1'). exists s.
(* compatibility *)
assert (compat s0' s1' (vars l0) (vars (shift p l1))). unfold compat. intros.
deduce (vars_max H3). deduce (in_vars_shift_min H4). unfold p in H6.
absurd (x <= maxvar l0). omega. assumption.
(* domains of substitutions *)
assert (dom_incl s0' (vars l0)). unfold s0'. apply dom_incl_restrict.
assert (dom_incl s1' (vars (shift p l1))). unfold s1'. apply dom_incl_restrict.
(* inclusion in the dp_graph *)
assert (app s r0 = app s0' r0). unfold s. eapply app_union1. apply H5. apply H3.
apply hyp. assumption. rewrite H6.
assert (app s0' r0 = app s0 r0). unfold s0'. symmetry.
apply app_restrict_incl. apply hyp. assumption. rewrite H7.
assert (app s (shift p l1) = app s1' (shift p l1)).
unfold s. eapply app_union2. apply H4. apply H3. apply List.incl_refl.
rewrite H8.
assert (app s1' (shift p l1) = app s1 l1). unfold s1'.
rewrite <- app_restrict. rewrite <- app_shift.
refl. rewrite H9. assumption.
Qed.
End S1.

Section S2.
Variable E R : rules.
Variable hyp : rules_preserv_vars R.

Lemma hd_red_mod_of_hd_red_Mod  :  hd_red_Mod (int_red E #) R << hd_red_mod E R.
Proof.
unfold hd_red_Mod,hd_red_mod.
apply incl_comp. assert (int_red E # << ATrs.red E #).
apply incl_rtc. apply int_red_incl_red. eauto.
apply inclusion_refl.
Qed.

End S2.

Section S3.
Require Export ADPGraph.
Variable R : rules.
Variable hyp : rules_preserv_vars R.

Lemma hd_red_Mod_of_chain : chain R << hd_red_Mod  (int_red R #) (dp R).
Proof.
unfold chain, hd_red_Mod.
apply inclusion_refl.
Qed.

End S3.

End S.




