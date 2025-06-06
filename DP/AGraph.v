(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

head rules graph: generalisation of ADPGraph
to S @ (hd_red R) instead of (int_red R ##) @ (dp R)
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil ATrs RelUtil RelSub SN AShift ADPGraph
     VecUtil ASubstitution.
From CoLoR Require Export ADP.
From Stdlib Require Import List Lia.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).

  Notation rule := (rule Sig). Notation rules := (list rule).
  Notation lhs := (@lhs Sig). Notation rhs := (@rhs Sig).

  Section hd_red_Mod.

    Variable S : relation term.
    Variable D : rules.

(***********************************************************************)
(** head rules graph *)

    Definition hd_rules_graph a1 a2 := In a1 D /\ In a2 D
      /\ exists p, exists s, S (sub s (rhs a1)) (sub s (shift p (lhs a2))).

    Lemma restricted_dp_graph : is_restricted hd_rules_graph D.

    Proof.
      unfold is_restricted, hd_rules_graph, inclusion. intros. intuition.
    Qed.

(***********************************************************************)
(** corresponding chain relation *)

    Definition hd_red_Mod_rule a t u := In a D /\
      exists s, S t (sub s (lhs a)) /\ u = sub s (rhs a).

    Lemma chain_hd_rules_hd_red_Mod : forall a,
      hd_red_Mod_rule a << hd_red_Mod S D.

    Proof.
      unfold inclusion. intros. destruct H. do 2 destruct H0.
      exists (sub x0 (lhs a)). split;auto. 
      subst y. destruct a. simpl in *. unfold hd_red.
      exists lhs; exists rhs; exists x0. auto.
    Qed.

    Lemma hd_red_Mod_chain_hd_rules : forall t u,
      hd_red_Mod S D t u -> exists a, hd_red_Mod_rule a t u.

    Proof.
      intros. do 2 destruct H. do 3 destruct H0. exists (mkRule x0 x1).
      unfold hd_red_Mod_rule. simpl. intuition. exists x2. intuition.
      subst. auto.
    Qed.

    Variable hyp : rules_preserve_vars D.

    Lemma hd_red_Mod_rule2_hd_rules_graph : forall a1 a2 t u v,
      hd_red_Mod_rule a1 t u -> hd_red_Mod_rule a2 u v -> hd_rules_graph a1 a2.

    Proof.
      intros. destruct a1 as [l0 r0]. destruct a2 as [l1 r1].
      destruct H. simpl in H1. do 2 destruct H1. subst u. rename x into s0.
      destruct H0. simpl in H2. do 2 destruct H2. subst v. rename x into s1.
      (* [maxvar l0 + 1] for shift *)
      unfold hd_rules_graph. intuition. simpl. set (p := maxvar l0 + 1).
      exists p.
      (* take the union of s0 (restricted to [vars l0]) and
         [comp s1 (shift_inv_sub p l1)] (restricted to [vars (shift p l1)] *)
      set (s0' := restrict s0 (vars l0)).
      set (s1' :=
        restrict (sub_comp s1 (shift_inv_sub p l1)) (vars (shift p l1))).
      set (s := ASubstitution.union s0' s1'). exists s.
      (* compatibility *)
      assert (compat s0' s1' (vars l0) (vars (shift p l1))).
      unfold compat. intros.
      ded (vars_max H3). ded (in_vars_shift_min H4). unfold p in H6.
      absurd (x <= maxvar l0). lia. hyp.
      (* domains of substitutions *)
      assert (dom_incl s0' (vars l0)). unfold s0'. apply dom_incl_restrict.
      assert (dom_incl s1' (vars (shift p l1))).
      unfold s1'. apply dom_incl_restrict.
      (* inclusion in the dp_graph *)
      assert (sub s r0 = sub s0' r0). unfold s. eapply sub_union1. apply H5.
      apply H3. apply hyp. hyp. rewrite H6.
      assert (sub s0' r0 = sub s0 r0). unfold s0'. sym.
      apply sub_restrict_incl. apply hyp. hyp. rewrite H7.
      assert (sub s (shift p l1) = sub s1' (shift p l1)).
      unfold s. eapply sub_union2. apply H4. apply H3. refl.
      rewrite H8.
      assert (sub s1' (shift p l1) = sub s1 l1). unfold s1'.
      rewrite <- sub_restrict, <- sub_shift.
      refl. rewrite H9. hyp.
    Qed.

    Lemma hd_red_Mod2_hd_rules_graph : forall t u v,
      hd_red_Mod S D t u -> hd_red_Mod S D u v ->
      exists a1, exists a2, hd_rules_graph a1 a2.

    Proof.
      intros. ded (hd_red_Mod_chain_hd_rules H).
      ded (hd_red_Mod_chain_hd_rules H0).
      destruct H1. destruct H2. exists x. exists x0.
      eapply hd_red_Mod_rule2_hd_rules_graph. apply H1. apply H2.
    Qed.

  End hd_red_Mod.

  Lemma hd_rules_graph_incl : forall S D D', incl D D' ->
    hd_rules_graph S D << hd_rules_graph S D'.

  Proof.
    intros. intros a b h. destruct h. decomp H1. unfold hd_rules_graph.
    intuition. exists x. exists x0. hyp.
  Qed.

(***********************************************************************)
(** relation between hd_red_Mod and chain *)

  Lemma hd_red_Mod_of_chain : forall R : rules,
    chain R << hd_red_Mod (int_red R #) (dp R).

  Proof. intros. unfold chain, hd_red_Mod. refl. Qed.

End S.

(***********************************************************************)
(** tactics *)

Ltac dp_trans := chain; eapply WF_incl; [apply hd_red_Mod_of_chain | idtac].
