(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-09-25
- Leo Ducas, 2007-08-06

a simple over graph of the DP graph based on the equality of head symbols
("hde" stands for head equality)
*)

Set Implicit Arguments.

Require Export ADecomp.
Require Export ADuplicateSymb.

(***********************************************************************)
(** definition of the hde over graph *)

Section prop_def.

Variable Sig : Signature.

Notation rule := (rule Sig). Notation rules := (list rule).

Variable D : rules.

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

Lemma hde_dec : forall r1 r2, {hde r1 r2} + {~hde r1 r2}.

Proof.
intros. unfold hde.
destruct (In_dec (@eq_rule_dec Sig) r1 D); try tauto.
destruct (In_dec (@eq_rule_dec Sig) r2 D); try tauto.
destruct (rhs r1). left; auto. destruct (lhs r2); auto.
destruct (@eq_symbol_dec Sig f f0); try tauto.
Defined.

End prop_def.

(***********************************************************************)
(** correctness *)

Section prop_correct.

Variable Sig : Signature.

Notation rule := (rule Sig). Notation rules := (list rule).

Variables R D : rules.

Lemma int_red_hd_rules_graph_incl_hde :
  hd_rules_graph (int_red R #) D << hde D.

Proof.
unfold inclusion. intros. destruct x. destruct y. destruct H. destruct H0.
do 2 destruct H1. unfold hde. destruct lhs0; destruct rhs; simpl; auto.
intuition; auto.
ded (int_red_rtc_preserv_hd H1). destruct H2. simpl in H2. inversion H2; auto.
do 4 destruct H2. inversion H2. inversion H3. congruence.
Qed.

End prop_correct.

(***********************************************************************)
(** correctness with marked symbols *)

Section prop_mark_correct.

Variable Sig : Signature. Notation Sig' := (dup_sig Sig).
Notation rule' := (ATrs.rule Sig'). Notation rules' := (list rule').

Variable R D : rules'.

Variable int_hyp : forallb (@is_lhs_int_symb_headed Sig) R = true.

Definition is_rhs_hd_symb_headed (a : rule') :=
  match rhs a with
    | Fun (hd_symb _) _ => true
    | _ => false
  end.

Variable hd_hyp : forallb is_rhs_hd_symb_headed D = true.

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

Notation rule := (rule Sig). Notation rules := (list rule).

Variables D : rules.

Notation eq_symbol_dec := (@eq_symbol_dec Sig).
Notation eq_rule_dec := (@eq_rule_dec Sig).

Notation Inb := (Inb eq_rule_dec).

(* REMARK: [Inb _ D] can be optimized when D is sorted. *)

Definition hde_bool (r1 r2 : rule) := Inb r1 D && Inb r2 D &&
  match rhs r1 with
  | Var _ => true
  | Fun f _ =>
    match lhs r2 with
    | Var _ => true
    | Fun g _ =>
      match eq_symbol_dec f g with
      | left _ => true
      | right _ => false
      end
    end
  end.

Lemma hde_bool_correct_aux : forall x y, hde D x y <-> Graph hde_bool x y.

Proof.
intros x y. unfold hde, hde_bool, Graph; simpl.
destruct (rhs x); autorewrite with bool; intuition.
apply andb_intro; apply Inb_intro; hyp.
destruct (andb_elim H). rewrite <- Inb_correct in H0. hyp.
destruct (andb_elim H). rewrite <- Inb_correct in H1. hyp.
gen H2. destruct (lhs y); autorewrite with bool; intro.
apply andb_intro; apply Inb_intro; hyp.
subst f0. case (eq_symbol_dec f f); intro. autorewrite with bool.
apply andb_intro; apply Inb_intro; hyp. irrefl.
destruct (andb_elim H). destruct (andb_elim H0).
rewrite <- Inb_correct in H2. hyp.
destruct (andb_elim H). destruct (andb_elim H0).
rewrite <- Inb_correct in H3. hyp.
gen H. destruct (lhs y); autorewrite with bool; intro. trivial.
gen H. case (eq_symbol_dec f f0). auto. autorewrite with bool. discr.
Qed.

End bool_def.

(***********************************************************************)
(** correctness *)

Section bool_correct.

Variable Sig : Signature.

Notation hd := (hd_symb Sig).
Notation rule := (rule Sig). Notation rules := (list rule).

Variables R D : rules.

Lemma hde_bool_correct : hd_rules_graph (int_red R #) D << Graph (hde_bool D).

Proof.
trans (hde D). apply int_red_hd_rules_graph_incl_hde.
intros x y. rewrite hde_bool_correct_aux. auto.
Qed.

(***********************************************************************)
(** correctness with marked symbols *)

Notation Sig' := (dup_sig Sig). Notation Fun' := (@Fun Sig').

Notation R' := (dup_int_rules R).

Variable hyp : forallb (@is_notvar_lhs Sig') R' = true.

Lemma red_dup_int_hd_symb :
  forall f us v, red R' (Fun' (hd f) us) v -> exists vs, v = Fun' (hd f) vs.

Proof.
intros. redtac. destruct (in_map_elim H). destruct H2. destruct x.
inversion H3. subst. destruct c; simpl in *.
(* Hole *)
rewrite forallb_forall in hyp. ded (hyp _ H). destruct lhs. discr.
simpl dup_int_term in H0. rewrite sub_fun in H0. Funeqtac. discr.
(* Cont *)
Funeqtac.
exists (Vcast (Vapp v (Vcons (fill c (sub s (dup_int_term rhs))) v0)) e).
refl.
Qed.

Lemma rtc_red_dup_int_hd_symb_aux : forall f u v, red R' # u v ->
  forall us, u = Fun' (hd f) us -> exists vs, v = Fun' (hd f) vs.

Proof.
induction 1; intros. eapply red_dup_int_hd_symb. subst. apply H. eauto.
destruct (IHclos_refl_trans1 _ H1). eapply IHclos_refl_trans2. apply H2.
Qed.

Lemma rtc_red_dup_int_hd_symb : forall f us v,
  red R' # (Fun' (hd f) us) v -> exists vs, v = Fun' (hd f) vs.

Proof.
intros. eapply rtc_red_dup_int_hd_symb_aux. apply H. refl.
Qed.

Lemma hde_bool_mark_correct :
  hd_rules_graph (red (dup_int_rules R) #) (dup_hd_rules D)
  << Graph (hde_bool (dup_hd_rules D)).

Proof.
trans (hde (dup_hd_rules D)).
Focus 2. intros x y. rewrite hde_bool_correct_aux. auto.
intros x y h. destruct h. decomp H0. unfold hde. intuition.
destruct (in_map_elim H). destruct H0. destruct x2. unfold dup_hd_rule in H3.
simpl in H3. subst x. simpl in *.
destruct (in_map_elim H1). destruct H3. destruct x. unfold dup_hd_rule in H4.
simpl in H4. subst y. simpl in *.
destruct rhs; simpl. trivial. destruct lhs0; simpl. trivial.
simpl dup_hd_term in H2. unfold shift in H2. repeat rewrite sub_fun in H2.
destruct (rtc_red_dup_int_hd_symb H2). Funeqtac. auto.
Qed.

End bool_correct.

(***********************************************************************)
(** tactics *)

Ltac hde_bool_correct :=
  (apply hde_bool_correct || apply hde_bool_mark_correct); vm_compute; refl.
