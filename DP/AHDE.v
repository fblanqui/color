(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-09-25
- Leo Ducas, 2007-08-06

a simple over graph of the DP graph based on the equality of head symbols
("hde" stands for head equality)
*)

Set Implicit Arguments.

From CoLoR Require Import ADecomp ADuplicateSymb ATrs ListUtil RelSub RelUtil
     AGraph LogicUtil BoolUtil AShift EqUtil ListDec.
From Stdlib Require Btauto.

(***********************************************************************)
(** definition of the hde over graph *)

Section prop_def.

Variable Sig : Signature.

Variable D : rules Sig.

(* REMARK: [In _ D] can be optimized when D is sorted. *)

Definition hde r1 r2 := In r1 D /\ In r2 D /\
  match rhs r1 with 
    | Var _ => True
    | Fun f _ =>
      match lhs r2 with
        | Var _ => True
        | Fun g _ => f=g
      end
  end.

Lemma hde_restricted : is_restricted hde D.

Proof.
unfold is_restricted. intros. unfold hde in H; tauto.
Qed.

Notation eq_rule_dec := (@eq_rule_dec Sig).
Notation eq_symb_dec := (@eq_symb_dec Sig).

Lemma hde_dec : forall r1 r2, {hde r1 r2} + {~hde r1 r2}.

Proof.
intros. unfold hde.
destruct (In_dec eq_rule_dec r1 D); try tauto.
destruct (In_dec eq_rule_dec r2 D); try tauto.
destruct (rhs r1). left; auto. destruct (lhs r2); auto.
destruct (eq_symb_dec f f0); try tauto.
Defined.

End prop_def.

(***********************************************************************)
(** correctness *)

Section prop_correct.

Variable Sig : Signature.

Variables R D : rules Sig.

Lemma int_red_hd_rules_graph_incl_hde :
  hd_rules_graph (int_red R #) D << hde D.

Proof.
unfold inclusion. intros. destruct x. destruct y. destruct H. destruct H0.
do 2 destruct H1. unfold hde. destruct lhs0; destruct rhs; simpl; auto.
intuition; auto.
ded (int_red_rtc_preserve_hd H1). destruct H2. simpl in H2. inversion H2; auto.
do 4 destruct H2. inversion H2. inversion H3. congruence.
Qed.

End prop_correct.

(***********************************************************************)
(** correctness with marked symbols *)

Section prop_mark_correct.

Variable Sig : Signature.

Notation Sig' := (dup_sig Sig).

Variable R D : rules Sig'.

Variable int_hyp : forallb (@is_int_symb_lhs Sig) R = true.
Variable hd_hyp : forallb (@is_hd_symb_rhs Sig) D = true.

Lemma dup_hd_rules_graph_incl_hde : hd_rules_graph (red R #) D << hde D.

Proof.
unfold inclusion. intros. apply (@int_red_hd_rules_graph_incl_hde _ R D x y).
destruct H. decomp H0. rewrite forallb_forall in hd_hyp. ded (hd_hyp _ H).
compute in H0. destruct x. destruct rhs. discr. destruct f.
unfold hd_rules_graph. intuition. exists x0. exists x1. simpl rhs.
rewrite sub_fun. apply dup_int_rules_int_red_rtc; hyp. discr.
Qed.

End prop_mark_correct.

(***********************************************************************)
(** definition of hde as a boolean function *)

Section bool_def.

Variable Sig : Signature.

Variables D : rules Sig.

Definition hd_eq (u v : term Sig) :=
  match u with
  | Var _ => true
  | Fun f _ =>
    match v with
    | Var _ => true
    | Fun g _ => beq_symb f g
    end
  end.

(* REMARK: [Inb _ D] can be optimized when D is sorted. *)

Notation mem := (mem (@beq_rule Sig)).
Notation mem_ok := (mem_ok (@beq_rule_ok Sig)).

Definition hde_bool r1 r2 :=
  mem r1 D && mem r2 D && hd_eq (rhs r1) (lhs r2).

Lemma hde_bool_correct_aux : forall x y, hde D x y <-> Graph hde_bool x y.

Proof.
intros x y. unfold hde, hde_bool, hd_eq, Graph; simpl.
pose proof (fun s x y => proj1 (@beq_symb_ok s x y)).
pose proof (fun s x y => proj2 (@beq_symb_ok s x y)).
rewrite <- !mem_ok. destruct (rhs x); bool; intuition auto with core;
repeat match goal with
| H : _ && _ = true |- _ => apply andb_elim in H; case H as []
| H : _ = true |- _ => rewrite H; cbn [andb]
| H : match ?x in term _ return _ with _ => _ end |- _ => case x eqn:? in *; subst
| H : match ?x in term _ return _ with _ => _ end = true |- _ => case x eqn:? in *; subst
end; auto.
Qed.

End bool_def.

(***********************************************************************)
(** correctness *)

Section bool_correct.

Variable Sig : Signature.

Variables R D : rules Sig.

Lemma hde_bool_correct : hd_rules_graph (int_red R #) D << Graph (hde_bool D).

Proof.
incl_trans (hde D). apply int_red_hd_rules_graph_incl_hde.
intros x y. rewrite hde_bool_correct_aux. auto.
Qed.

(***********************************************************************)
(** correctness with marked symbols *)

Notation Sig' := (dup_sig Sig).

Notation R' := (dup_int_rules R).

Variable hyp : forallb (@is_notvar_lhs Sig') R' = true.

Lemma hde_bool_mark_correct :
  hd_rules_graph (red (dup_int_rules R) #) (dup_hd_rules D)
  << Graph (hde_bool (dup_hd_rules D)).

Proof.
incl_trans (hde (dup_hd_rules D)).
2:{ intros x y. rewrite hde_bool_correct_aux. auto. }
intros x y h. destruct h. decomp H0. unfold hde. intuition.
destruct (in_map_elim H). destruct H0. destruct x2. unfold dup_hd_rule in H3.
simpl in H3. subst x. simpl in *.
destruct (in_map_elim H1). destruct H3. destruct x. unfold dup_hd_rule in H4.
simpl in H4. subst y. simpl in *.
destruct rhs; simpl. trivial. destruct lhs0; simpl. trivial.
simpl dup_hd_term in H2. unfold shift in H2. rewrite !sub_fun in H2.
destruct (rtc_red_dup_int_hd_symb hyp H2). Funeqtac. auto.
Qed.

End bool_correct.

(***********************************************************************)
(** tactics *)

Ltac hde_bool_correct :=
  (apply hde_bool_mark_correct || apply hde_bool_correct);
  (check_eq || fail 10 "a LHS is a variable").
