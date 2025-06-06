(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-10-08

over graph based on unification
*)

Set Implicit Arguments.

From Stdlib Require Import Lia Compare_dec.
From CoLoR Require Import ADecomp AUnif ARenCap ATrs ListUtil RelUtil AGraph
     LogicUtil AShift ACalls BoolUtil ADuplicateSymb ListDec EqUtil AHDE.

Section S.

  Variable N : nat. (* maximum number of unification steps *)

(***********************************************************************)
(** over graph based on unification *)

  Section unif.

    Variable Sig : Signature.

    Notation rule := (rule Sig). Notation rules := (rules Sig).

    Variables R D : rules.

    Definition connectable u v := unifiable (ren_cap R (S (maxvar v)) u) v.

    Definition dpg_unif (r1 r2 : rule) :=
      In r1 D /\ In r2 D /\ connectable (rhs r1) (lhs r2).

    Variable hypR : forallb (@is_notvar_lhs Sig) R = true.

    Lemma dpg_unif_correct : hd_rules_graph (red R #) D << dpg_unif.

    Proof.
      intros x y h. destruct h. decomp H0. unfold dpg_unif. intuition.
      destruct x as [l1 r1]. destruct y as [l2 r2]. simpl in *.
      unfold connectable. set (k := S (maxvar l2)).
      destruct (rtc_red_sub_ren_cap hypR k H2).
      destruct (ren_cap_sub R x1 r1 k).
      destruct H3. revert H0. rewrite H3. unfold shift. rewrite !sub_sub.
      intro. assert (forall x, In x (vars (ren_cap R k r1))
        -> In x (vars l2) -> False).
      intros. ded (vars_ren_cap H5). ded (vars_max H6). subst k. lia.
      unfold unifiable. eapply sub_eq_is_sol. hyp. symmetry in H0. apply H0.
    Qed.

(***********************************************************************)
(** over graph using a finite number of unification steps *)

    Definition ren_cap (r1 r2 : rule) :=
      ren_cap R (S (maxvar (lhs r2))) (rhs r1).

    Definition unifiable_N r1 r2 :=
      iter_step N (mk_problem (ren_cap r1 r2) (lhs r2)).

    Definition connectable_N r1 r2 :=
      match unifiable_N r1 r2 with
        | None => false
        | Some (_, nil) => true
        | _ => hd_eq (rhs r1) (lhs r2)
      end.

    Notation mem := (mem (@beq_rule Sig)).
    Notation mem_ok := (mem_ok (@beq_rule_ok Sig)).

    Definition dpg_unif_N r1 r2 := mem r1 D && mem r2 D && connectable_N r1 r2.

    Variable hypD : forallb (undefined_rhs R) D = true.

    Lemma successfull_hd_eq : forall x r1 r2, In r1 D -> In r2 D ->
      successfull (iter_step x (mk_problem (ren_cap r1 r2) (lhs r2))) = true ->
      hd_eq (rhs r1) (lhs r2) = true.

    Proof.
      intros x r1 r2 h1 h2 H.
      set (p := mk_problem (ren_cap r1 r2) (lhs r2)) in H.
      assert (problem_wf p). apply wf_mk_problem.
      destruct (successfull_is_sol H0 H).
      revert H1. unfold p, mk_problem, ren_cap. simpl. intuition. revert H1.
      rewrite forallb_forall in hypD. ded (hypD _ h1). ded (hypD _ h2).
      destruct r1 as [l1 r1]. destruct r2 as [l2 r2]. simpl. destruct r1. refl.
      destruct l2. refl. set (k := S (maxvar (Fun f0 t0))). rewrite ren_cap_fun.
      revert H1. unfold undefined_rhs, undefined. simpl. rewrite negb_lr. simpl.
      intro. rewrite H1. unfold is_sol_eqn. unfold fst, snd.
      rewrite !sub_fun. intro. Funeqtac.
      rewrite (beq_refl (@beq_symb_ok Sig)). refl.
    Qed.

    Lemma dpg_unif_N_correct : hd_rules_graph (red R #) D << Graph dpg_unif_N.

    Proof.
      incl_trans dpg_unif. apply dpg_unif_correct. intros r1 r2 h. destruct h.
      destruct H0. unfold Graph, dpg_unif_N. rewrite <- mem_ok in H.
      rewrite <- mem_ok in H0. rewrite H, H0. bool.
      destruct (iter_step_complete (wf_mk_problem (ren_cap r1 r2) (lhs r2)) H1).
      unfold connectable_N, unifiable_N. case (lt_eq_lt_dec x N); intro.
      destruct s. ded (successfull_preserved H2 l).
      destruct (successfull_elim H3). rewrite H4.
      refl. subst. destruct (successfull_elim H2). rewrite H3. refl.
      ded (successfull_inv H2 l).
      destruct (iter_step N (mk_problem (ren_cap r1 r2) (lhs r2))). 2: cong.
      destruct p. destruct e. refl. eapply successfull_hd_eq.
      rewrite <- mem_ok. hyp. rewrite <- mem_ok. hyp. apply H2.
    Qed.

  End unif.

(***********************************************************************)
(** with marked symbols *)

  Section mark.

    Variable Sig : Signature.

    Notation Sig' := (dup_sig Sig).

    Lemma undefined_hd_symb_dup_int_rules : forall f R,
      @defined Sig' (hd_symb Sig f) (dup_int_rules R) = false.

    Proof.
      induction R; intros. refl. simpl dup_int_rules. destruct a as [l r].
      destruct l; hyp.
    Qed.

    Variables R D : rules Sig.

    Notation R' := (dup_int_rules R). Notation D' := (dup_hd_rules D).

    Variable hypR : forallb (@is_notvar_lhs Sig') R' = true.
    Variable hypD : forallb (@is_notvar_rhs Sig') D' = true.

    Lemma dpg_unif_N_mark_correct :
      hd_rules_graph (red R' #) D' << Graph (dpg_unif_N R' D').

    Proof.
      apply dpg_unif_N_correct. hyp. rewrite forallb_forall. intros.
      unfold undefined_rhs. destruct (in_map_elim H). destruct H0. subst.
      destruct x0 as [l r]. simpl. unfold undefined. destruct r.
      rewrite forallb_forall in hypD. ded (hypD _ H). discr. simpl.
      rewrite negb_lr. apply undefined_hd_symb_dup_int_rules.
    Qed.

  End mark.

End S.

(***********************************************************************)
(** tactics *)

Ltac dpg_unif_N_correct :=
  (apply dpg_unif_N_mark_correct || apply dpg_unif_N_correct);
  (check_eq || fail 10 "a LHS is a variable").
