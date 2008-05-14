(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

a simple over graph of the DP graph based on the equality of head symbols
(hde stands for head equality)
*)

Require Export AGraph.

Set Implicit Arguments.

Section S.

Variable Sig : Signature.

Notation rule := (rule Sig).
Notation rules := (list rule).
Notation lhs := (@lhs Sig).
Notation rhs := (@rhs Sig).

Variables E R : rules.

(***********************************************************************)
(** definition of the hde over graph *)

Definition hde (r1 r2 : rule) := In r1 R /\ In r2 R /\
  match rhs r1 with 
    | Var n => True
    | Fun f v =>
      match lhs r2 with
        | Var m => True
        | Fun g w => f=g
      end
  end.

(***********************************************************************)
(** properties of hde *)

Lemma hde_restricted : is_restricted hde R.

Proof.
unfold is_restricted. intros. unfold hde in H; tauto.
Qed.

Lemma hde_dec : forall r1 r2, {hde r1 r2} + {~hde r1 r2}.

Proof.
intros. unfold hde.
destruct (In_dec (@eq_rule_dec Sig) r1 R); try tauto.
destruct (In_dec (@eq_rule_dec Sig) r2 R); try tauto.
destruct (rhs r1). left; auto. destruct (lhs r2); auto.
destruct (@eq_symbol_dec Sig f f0); try tauto.
Defined.

Lemma int_red_hd_rules_graph_incl_hde : hd_rules_graph (int_red E #) R << hde.

Proof.
unfold inclusion. intros. destruct x. destruct y. destruct H. destruct H0.
do 2 destruct H1. unfold hde. destruct lhs0; destruct rhs; simpl; auto.
intuition; auto.
ded (int_red_rtc_preserv_hd H1). destruct H2. simpl in H2. inversion H2; auto.
do 4 destruct H2. inversion H2. inversion H3. congruence.
Qed.

End S.

(***********************************************************************)
(** properties wrt marked symbols *)

Section S'.

Variable Sig : Signature.

Require Export ADuplicateSymb.

Notation Sig' := (dup_sig Sig).
Notation rule' := (ATrs.rule Sig').
Notation rules' := (list rule').
Notation Fun' := (@Fun Sig').

Variable E' R' : rules'.

Definition int_lhs_rules_only := forall l r, In (mkRule l r) E' ->
  exists f, exists v, l = Fun' (int_symb Sig f) v.

Variable int_hyp : int_lhs_rules_only.

Lemma dup_int_rules_int_red : forall f v t,
  red E' (Fun' (hd_symb _ f) v) t -> int_red E' (Fun' (hd_symb _ f) v) t.

Proof.
intros.
redtac.
exists l; exists r;exists c;exists s.
split.
destruct c. simpl in *.
ded (int_hyp _ _ H).
do 2 destruct H2; subst.
rewrite app_fun in H0.
inversion H0.
congruence.
tauto.
Qed.

Lemma dup_int_rules_int_red_rtc_aux : forall u t, red E' # u t ->
  forall f v, u = Fun' (hd_symb _ f) v -> 
    int_red E' # u t /\ exists w, t = Fun' (hd_symb _ f) w.

Proof.
intros u t H.
induction H; intros.
assert (int_red E' # x y).
apply rt_step.
rewrite H0.
apply dup_int_rules_int_red. subst;auto.
split. auto.
clear H.
ded (int_red_rtc_preserv_hd H1).
destruct H.
exists v. subst. rewrite H; auto.
do 3 destruct H; subst.
destruct H. inversion H. subst.
exists x2. apply refl_equal.

split. apply rt_refl.
exists v; auto.
ded (IHclos_refl_trans1 _ _ H1).
clear IHclos_refl_trans1.
destruct H2.
destruct H3 as [w].
ded (IHclos_refl_trans2 _ _ H3).
destruct H4. destruct H5.
split.
eapply rt_trans; eauto.
exists x0. auto.
Qed.

Lemma dup_int_rules_int_red_rtc : forall f v t,
  red E' # (Fun' (hd_symb _ f) v) t -> int_red E' # (Fun' (hd_symb _ f) v) t.

Proof.
intros. ded (dup_int_rules_int_red_rtc_aux H (refl_equal _)). tauto.
Qed. 

Definition hd_rhs_rules_only := forall l r, In (mkRule l r) R' ->
  exists f, exists v, r = Fun' (hd_symb Sig f) v.

Variable hd_hyp : hd_rhs_rules_only.

Lemma dup_hd_rules_graph_incl_hde : hd_rules_graph (red E' #) R' << hde R'.

Proof.
unfold inclusion. intros.
destruct H. intuition. destruct H2. destruct H0. destruct x as [l r].
ded (hd_hyp _ _ H). do 2 destruct H2. simpl in *. subst.
rewrite app_fun in H0.
apply (@int_red_hd_rules_graph_incl_hde _ E' R'
  (mkRule l (Fun' (hd_symb Sig x) x2)) y).
unfold hd_rules_graph. split. tauto. split. tauto. exists x0. exists x1.
norm (rhs (mkRule l (Fun' (hd_symb Sig x) x2))). rewrite app_fun.
change (int_red E' #
  (Fun' (hd_symb Sig x) (Vmap (ASubstitution.app x1) x2))
  (ASubstitution.app x1 (shift x0 (lhs y)))).
apply dup_int_rules_int_red_rtc. auto.
Qed.

End S'.

(***********************************************************************)
(** tactics *)

Ltac prove_int_lhs_rules_only :=
  match goal with
    | |- int_lhs_rules_only ?L =>
      unfold int_lhs_rules_only; norm L;
        let aux l r H0 :=
          match type of H0 with
            | In ?X nil => simpl in H0; tauto
            | In ?Y (mkRule ?L ?R :: ?Q) =>
              rewrite In_cons in H0; destruct H0; [inversion H0; subst l;
	        (match L with 
                   | Fun (int_symb ?i ?f) ?v => exists f; exists v; auto
                 end)
                | idtac]
          end in
          let l:=fresh in let r:=fresh in let H:=fresh in
            intros l r H; repeat aux l r H
  end.

Ltac prove_hd_rhs_rules_only :=
  match goal with
    | |- hd_rhs_rules_only ?L =>
      unfold hd_rhs_rules_only; norm L;
        let aux l r H0 :=
          match type of H0 with
            | In ?X nil => simpl in H0; tauto
            | In ?Y (mkRule ?L ?R :: ?Q) =>
              rewrite In_cons in H0; destruct H0; [inversion H0; subst l;
	        (match R with
                   | Fun (hd_symb ?i ?f) ?v => exists f; exists v; auto
                 end)
                | idtac] end in
          let l:=fresh in let r:=fresh in let H:=fresh in
            intros l r H; repeat aux l r H
  end.
