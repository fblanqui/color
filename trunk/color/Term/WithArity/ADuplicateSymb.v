(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

Duplicate/mark symbols to distinguish internal reductions from head reductions
*)

Set Implicit Arguments.

Require Export ATrs.

Section S.

Variable Sig : Signature.

Notation symb := (symbol Sig).
Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** signature of symbols marked as head or internal *)

Inductive dup_symb : Type :=
| hd_symb : symb -> dup_symb
| int_symb : symb -> dup_symb.

Definition dup_ar s :=
  match s with
    | hd_symb s' => arity s'
    | int_symb s' => arity s'
  end.

Lemma eq_dup_symb_dec : forall f g : dup_symb, {f=g}+{~f=g}.

Proof.
decide equality; apply eq_symbol_dec.
Defined.

Definition dup_sig := mkSignature dup_ar eq_dup_symb_dec.

Notation Sig' := dup_sig. Notation Fun' := (@Fun Sig').

(***********************************************************************)
(** function marking all symbols as internal *)

Fixpoint dup_int_term t :=
  match t with
    | Var x => Var x
    | Fun f v => Fun' (int_symb f) (Vmap dup_int_term v)
  end.

Lemma dup_int_term_fun : forall f v,
  dup_int_term (Fun f v) = Fun' (int_symb f) (Vmap dup_int_term v).

Proof.
intros. trivial.
Qed.

(***********************************************************************)
(** function marking all symbols as internal except the head symbol *)

Definition dup_hd_term t :=
  match t with
    | Var x => Var x
    | Fun f v => Fun' (hd_symb f) (Vmap dup_int_term v)
  end.

Lemma dup_hd_term_fun : forall f v,
  dup_hd_term (Fun f v) = Fun' (hd_symb f) (Vmap dup_int_term v).

Proof.
intros. trivial.
Qed.

(***********************************************************************)
(** function marking substitutions *)

Definition dup_int_subst (s : substitution Sig) n := dup_int_term (s n).

Require Export ASubstitution.

Lemma dup_int_subst_spec : forall s t,
  sub (dup_int_subst s) (dup_int_term t) = dup_int_term (sub s t).

Proof.
intros.
pattern t.
set (Q := Vforall (fun t0 =>
  sub (dup_int_subst s) (dup_int_term t0) = dup_int_term (sub s t0))).
apply term_ind with (Q:=Q).
(* Var *)
intro; unfold dup_int_subst; simpl. apply refl_equal.
(* Fun *)
intros. rewrite dup_int_term_fun.
do 2 rewrite sub_fun. rewrite dup_int_term_fun.
unfold Q in H.
cut (Vmap (sub (dup_int_subst s)) (Vmap dup_int_term v) =
  Vmap dup_int_term (Vmap (sub s) v)).
intros. rewrite <- H0. auto.
do 2 rewrite Vmap_map.
apply Vmap_eq. apply H.
(* Vnil *)
unfold Q; simpl; auto.
(* Vcons *)
unfold Q; simpl; auto.
Qed.

Lemma dup_int_subst_hd_dup : forall s f v,
  sub (dup_int_subst s) (dup_hd_term (Fun f v))
  = dup_hd_term (sub s (Fun f v)).

Proof.
intros.
rewrite dup_hd_term_fun. do 2 rewrite sub_fun. rewrite dup_hd_term_fun.
cut ((Vmap (sub (dup_int_subst s)) (Vmap dup_int_term v)) =
 (Vmap dup_int_term (Vmap (sub s) v)) ).
intro. rewrite <- H. apply refl_equal.
do 2 rewrite Vmap_map.
apply Vmap_eq_ext. 
apply dup_int_subst_spec.
Qed. 

(***********************************************************************)
(** function marking contexts *)

Notation Cont' := (@Cont Sig').

Fixpoint dup_int_context c :=
  match c with
    | Hole => Hole
    | Cont f _ _ H v c' w => Cont' (int_symb f) _ _ H 
      (Vmap dup_int_term v) (dup_int_context c') (Vmap dup_int_term w)
  end.

Lemma dup_int_context_spec : forall c s l,
  dup_int_term (fill c (sub s l)) =
  fill (dup_int_context c) (sub (dup_int_subst s) (dup_int_term l)).

Proof.
induction c; intros.
simpl.
rewrite dup_int_subst_spec. apply refl_equal.
simpl.
cut (Vmap dup_int_term (Vcast (Vapp v (Vcons (fill c (sub s l)) v0)) e) =
  (Vcast (Vapp (Vmap dup_int_term v)
    (Vcons
      (fill (dup_int_context c) (sub (dup_int_subst s) (dup_int_term l)))
      (Vmap dup_int_term v0))) e)).
intro. rewrite H; auto.
rewrite Vmap_cast.
rewrite Vmap_app.
simpl.
rewrite IHc.
auto.
Qed.

Definition dup_hd_context c :=
  match c with
    | Hole => Hole
    | Cont f _ _ H v c' w => Cont' (hd_symb f) _ _ H 
      (Vmap dup_int_term v) (dup_int_context c') (Vmap dup_int_term w)
  end.

(***********************************************************************)
(** function marking rules *)

Definition dup_int_rule r :=
  mkRule (dup_int_term (lhs r)) (dup_int_term (rhs r)).

Definition dup_hd_rule r :=
  mkRule (dup_hd_term (lhs r)) (dup_hd_term (rhs r)).

Definition dup_int_rules := map dup_int_rule.

Definition dup_hd_rules := map dup_hd_rule.

Section red.

Variable R : rules.

Variable hyp : forallb (@is_notvar_lhs Sig) R = true.
Variable hyp' : forallb (@is_notvar_rhs Sig) R = true.

Lemma hd_red_dup_hd_red : forall  t u, hd_red R t u -> 
  hd_red (dup_hd_rules R) (dup_hd_term t) (dup_hd_term u).

Proof.
intros. redtac. subst. unfold hd_red.
exists (dup_hd_term l). exists (dup_hd_term r). exists (dup_int_subst s).
ded (is_notvar_lhs_elim hyp H). decomp H0.
ded (is_notvar_rhs_elim hyp' H). decomp H0. subst.
do 2 rewrite dup_int_subst_hd_dup. intuition. unfold dup_hd_rules.
change (In (dup_hd_rule (mkRule (Fun x x0) (Fun x1 x2))) (map dup_hd_rule R)).
apply in_map. hyp.
Qed.

Lemma red_dup_int_red : forall t u,
  red R t u -> red (dup_int_rules R) (dup_int_term t) (dup_int_term u).

Proof.
intros. redtac.
exists (dup_int_term l). exists (dup_int_term r).
exists (dup_int_context c). exists (dup_int_subst s).
split.
change (In (dup_int_rule (mkRule l r)) (map dup_int_rule R)).
apply in_map. auto.
do 2 rewrite <- dup_int_context_spec.
split; subst; refl.
Qed.

Lemma int_red_dup_int_red : forall t u,
  int_red R t u -> red (dup_int_rules R) (dup_hd_term t) (dup_hd_term u).

Proof.
intros. redtac.
exists (dup_int_term l). exists (dup_int_term r).
exists (dup_hd_context c). exists (dup_int_subst s).
destruct c. tauto.
split.
change (In (dup_int_rule (mkRule l r)) (map dup_int_rule R)).
apply in_map. auto.
subst; simpl.
split; rewrite Vmap_cast; rewrite Vmap_app;
simpl; rewrite <- dup_int_context_spec; auto.
Qed.

End red.

(***********************************************************************)
(** preservation of termination by marking *)

Variables E R : rules.

Variable no_lhs_var : forallb (@is_notvar_lhs Sig) R = true.
Variable no_rhs_var : forallb (@is_notvar_rhs Sig) R = true.

Lemma WF_duplicate_hd_int_red :
  WF (hd_red_mod (dup_int_rules E) (dup_hd_rules R))
  -> WF (hd_red_Mod (int_red E #) R).

Proof.
intros. set (rel := hd_red_mod (dup_int_rules E) (dup_hd_rules R)).
set (rel' := Rof rel (dup_hd_term)).
apply (@WF_incl _ (hd_red_Mod (int_red E #) R) rel').
unfold rel', rel, hd_red_Mod, hd_red_mod. unfold inclusion; intros.
destruct H0 as [z]; exists (dup_hd_term z). destruct H0; split.
clear H1. induction H0. apply rt_step. apply int_red_dup_int_red. hyp.
apply rt_refl. eapply rt_trans. apply IHclos_refl_trans1. hyp.
apply  hd_red_dup_hd_red; auto. subst rel rel'. apply WF_inverse; auto.
Qed.

(***********************************************************************)
(** relation between (@int_red Sig) and (@red Sig') *)

Section int_red.

Notation rule' := (ATrs.rule Sig'). Notation rules' := (list rule').

Variable E' R' : rules'.

Definition is_lhs_int_symb_headed (a : rule') :=
  match lhs a with
    | Fun (int_symb _) _ => true
    | _ => false
  end.

Variable int_hyp : forallb is_lhs_int_symb_headed E' = true.

Lemma dup_int_rules_int_red : forall f v t,
  red E' (Fun' (hd_symb f) v) t -> int_red E' (Fun' (hd_symb f) v) t.

Proof.
intros. redtac. exists l. exists r. exists c. exists s. split.
destruct c. simpl in *. rewrite forallb_forall in int_hyp. ded (int_hyp _ H).
gen H2. compute. case_eq l. discr. gen H3. gen H2. gen v0. case_eq f0. discr.
subst l. rewrite sub_fun in H0. discr. congruence. tauto.
Qed.

Lemma dup_int_rules_int_red_rtc_aux : forall u t, red E' # u t ->
  forall f v, u = Fun' (hd_symb f) v -> 
    int_red E' # u t /\ exists w, t = Fun' (hd_symb f) w.

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
  red E' # (Fun' (hd_symb f) v) t -> int_red E' # (Fun' (hd_symb f) v) t.

Proof.
intros. ded (dup_int_rules_int_red_rtc_aux H (refl_equal _)). tauto.
Qed. 

End int_red.

End S.

(***********************************************************************)
(** tactics *)

Ltac mark := apply WF_duplicate_hd_int_red; [refl | refl | idtac].
