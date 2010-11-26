(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-11-02

violation of variable condition
*)

Set Implicit Arguments.

Require Import LogicUtil ATrs AVariables BoolUtil EqUtil ListUtil RelUtil
  NatUtil APosition.

Section S.

Variable Sig : Signature.

Notation term := (term Sig).
Notation rule := (rule Sig). Notation rules := (list rule).

Lemma var_cond_mod : forall E R : rules,
  ~rules_preserv_vars R -> non_terminating (red_mod E R).

Proof.
intros E R. rewrite <- brules_preserv_vars_ok. rewrite <- false_not_true.
unfold brules_preserv_vars. rewrite (forallb_neg (@brule_preserv_vars_ok Sig)).
intros [[l r] [h1 h2]]. simpl in *. rewrite not_incl in h2. 2: apply eq_nat_dec.
destruct h2. destruct H. destruct (in_vars_subterm H). rename x0 into p.
destruct (subterm_pos_elim H1). rename x0 into c. destruct a.
set (s := single x l). set (f := fun n => iter (fill (subc s c)) n l).
exists f. unfold IS. induction i; simpl in *. exists (f 0). split.
apply rt_refl. exists l. exists r. exists Hole. simpl. exists s.
repeat split. hyp. unfold s. rewrite sub_single_not_var. refl. hyp.
rewrite H3. rewrite sub_fill. unfold s, single. simpl.
rewrite (beq_refl beq_nat_ok). refl.
unfold f. simpl. repeat rewrite iter_com. apply red_mod_fill.
rewrite <- iter_com. hyp.
Qed.

Lemma var_cond : forall R : rules,
  ~rules_preserv_vars R -> non_terminating (red R).

Proof.
intros. rewrite <- red_mod_empty. apply var_cond_mod. hyp.
Qed.

End S.

Ltac var_cond Sig :=
  (apply var_cond_mod || apply var_cond);
    rewrite <- (ko (@brules_preserv_vars_ok Sig));
      (check_eq || fail 10 "variable condition satisfied").
