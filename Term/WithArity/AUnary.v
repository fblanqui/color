(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

properties of systems with unary symbols only
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs VecUtil LogicUtil ListUtil NatUtil VecMax EqUtil
     RelUtil SN ListMax.

(***********************************************************************)
(** tactics *)

Ltac arity1 hyp :=
  match goal with
    | e : ?i + S ?j = arity ?f |- _ =>
      ded (hyp f); assert (i=0); [lia | subst i; assert (j=0);
        [lia | subst j; VOtac]]
  end.

(***********************************************************************)
(** we assume a signature with unary symbols only *)

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation context := (context Sig).
Notation substitution := (substitution Sig).
Notation rule := (rule Sig). Notation rules := (list rule).

Definition is_unary := forall f : Sig, 1 = arity f.

Variable is_unary_sig : is_unary.

Ltac arity := arity1 is_unary_sig.

(***********************************************************************)
(** boolean function checking is_unary *)

Definition bis_unary Fs := forallb (fun f : Sig => beq_nat 1 (arity f)) Fs.

Lemma bis_unary_ok : forall (Fs : list Sig) (Fs_ok : forall f, In f Fs),
  bis_unary Fs = true <-> is_unary.

Proof.
intros. apply forallb_ok_fintype. intro. rewrite beq_nat_ok. refl. hyp.
Qed.  

(***********************************************************************)
(** unary function application *)

Definition Fun1 f (t : term) :=
  @Fun Sig f (Vcast (Vcons t Vnil) (is_unary_sig f)).

Lemma sub_fun1 : forall s f u, sub s (Fun1 f u) = Fun1 f (sub s u).

Proof.
intros. unfold Fun1. rewrite sub_fun, Vmap_cast. simpl Vmap. refl.
Qed.

Lemma vars_fun1 : forall f u, vars (Fun1 f u) = vars u.

Proof.
intros. unfold Fun1. rewrite vars_fun, vars_vec_cast. simpl.
rewrite app_nil_r. refl.
Qed.

Lemma maxvar_fun1 : forall f t, maxvar (Fun1 f t) = maxvar t.

Proof.
intros. unfold Fun1. rewrite maxvar_fun, maxvars_cast.
unfold maxvars. simpl Vmap. simpl VecMax.Vmax. rewrite max_0_r. refl.
Qed.

(***********************************************************************)
(** specific induction principle *)

Section term_ind.

Variables (P : term -> Prop)
  (Hvar : forall x, P (Var x))
  (Hfun : forall f t, P t -> P (Fun1 f t)).

Lemma term_ind_forall : forall t, P t.

Proof.
apply term_ind_forall_cast. hyp. intro f. ded (is_unary_sig f). destruct ts.
intro. lia. destruct ts.
simpl Vforall. split_all. assert (h0 = is_unary_sig f). apply eq_unique.
subst h0. apply Hfun. hyp.
intro. lia.
Qed.

End term_ind.

(***********************************************************************)
(** unique variable of a term *)

Fixpoint var (t : term) : variable :=
  match t with
    | Var x => x
    | Fun _ ts => Vmap_first 0 var ts
  end.

Lemma var_fun1 : forall f u, var (Fun1 f u) = var u.

Proof.
intros. unfold Fun1, var; fold var. rewrite Vmap_first_cast. refl.
Qed.

Lemma var_fill : forall c t, var (fill c t) = var t.

Proof.
induction c; simpl; intros. refl. rewrite Vmap_first_cast. arity. simpl.
apply IHc.
Qed.

Lemma var_sub : forall s t, var (sub s t) = var (s (var t)).

Proof.
intro s. apply term_ind_forall. refl. intros. rewrite sub_fun1, !var_fun1. hyp.
Qed.

Lemma vars_var : forall t, vars t = var t :: nil.

Proof.
apply term_ind_forall. refl. intros. rewrite vars_fun1, var_fun1. hyp.
Qed.

Lemma maxvar_var : forall t, maxvar t = var t.

Proof.
intro t; pattern t; apply term_ind_forall; clear t; intros. refl.
rewrite maxvar_fun1, var_fun1. hyp.
Qed.

(***********************************************************************)
(** unary context application *)

Lemma cont_aux : forall f : Sig, 0 + S 0 = arity f.

Proof. intro. rewrite <- is_unary_sig. refl. Qed.

Lemma cont_aux_eq : forall f, cont_aux f = is_unary_sig f.

Proof. intro. apply eq_unique. Qed.

Definition Cont1 f c := Cont f (cont_aux f) Vnil c Vnil.

Lemma fill_cont1 : forall f c t, fill (Cont1 f c) t = Fun1 f (fill c t).

Proof.
intros. unfold Cont1. unfold fill. fold (fill c t). simpl Vapp. unfold Fun1.
apply args_eq. apply Vcast_pi.
Qed.

(***********************************************************************)
(** biggest context of a term *)
 
Fixpoint cont (t : term) : context :=
  match t with
    | Var _ => Hole
    | Fun f ts => Cont1 f (Vmap_first Hole cont ts)
  end.

Lemma cont_fun1 : forall f t, cont (Fun1 f t) = Cont1 f (cont t).

Proof.
intros. unfold Fun1, cont. fold cont. rewrite Vmap_first_cast. refl.
Qed.

Lemma subc_cont : forall s (c : context), subc s c = c.

Proof. induction c; simpl; intros. refl. arity. simpl. rewrite IHc. refl. Qed.

Lemma term_cont_var : forall t, t = fill (cont t) (Var (var t)).

Proof.
apply term_ind_forall. refl.
intros. rewrite cont_fun1, fill_cont1, var_fun1, <- H. refl.
Qed.

Lemma sub_cont : forall s t, sub s t = fill (cont t) (s (var t)).

Proof.
intro. apply term_ind_forall. refl. intros.
rewrite sub_fun1, cont_fun1, var_fun1, fill_cont1, <- H. refl.
Qed.

Lemma term_sub_cont : forall x t,
  t = sub (single x (Var (var t))) (fill (cont t) (Var x)).

Proof.
intros. rewrite sub_fill, subc_cont. unfold single. simpl.
rewrite (beq_refl beq_nat_ok). apply term_cont_var.
Qed.

Lemma fill_var_elim : forall x c d (u : term), fill c (Var x) = fill d u ->
  exists e, c = comp d e.

Proof.
induction c. simpl. intros. destruct (var_eq_fill H). subst. exists Hole. refl.
simpl. intros. destruct (fun_eq_fill H). subst. exists (Cont f e t c t0). refl.
decomp H0. subst. simpl in *. Funeqtac. arity. arity. simpl Vapp in *.
assert (x2=e). apply eq_unique. subst x2. rewrite Vcast_eq in H0.
inversion H0. destruct (IHc _ _ H3). subst. exists x0. refl.
Qed.

Arguments fill_var_elim [x c d u] _.

Lemma fill_eq_cont : forall (t : term) c d, fill c t = fill d t <-> c = d.

Proof.
split. 2:{ intro. subst. refl. }
revert d. revert c. induction c.
(* c=Hole *)
simpl. intro. sym. apply (wf_term H).
(* c=Cont *)
destruct d; simpl.
(* d=Hole *)
intro. change (fill (Cont f e t0 c t1) t = t) in H. symmetry in H.
ded (wf_term H). hyp.
(* d=Cont *)
intro. Funeqtac. arity. arity. assert (e0=e). apply eq_unique. subst.
rewrite Vcast_eq, Vapp_eq in H0. destruct H0. inversion H2.
rewrite (IHc _ H4). refl.
Qed.

Lemma maxvar_fill : forall (t : term) c, maxvar (fill c t) = maxvar t.

Proof.
induction c. refl. simpl fill. rewrite maxvar_fun. unfold maxvars.
rewrite Vmap_cast, Vmax_cast. arity. simpl. rewrite IHc. apply max_0_r.
Qed.

(***********************************************************************)
(** equivalent definition of rewriting (when rules preserve variables) *)

Section red.

Variables (R : rules) (hR : rules_preserve_vars R).

Lemma rules_preserve_vars_var : forall l r, In (mkRule l r) R -> var r = var l.

Proof.
intros. ded (hR _ _ H). rewrite !vars_var in H0. unfold incl in H0.
ded (H0 (var r)). simpl in H1. fo.
Qed.

Arguments rules_preserve_vars_var [l r] _.

Definition red1 t u := exists l, exists r, exists c, exists d,
  In (mkRule l r) R /\ t = fill (comp c (comp (cont l) d)) (Var (var t))
  /\ u = fill (comp c (comp (cont r) d)) (Var (var t)).

Lemma red1_ok : forall t u, red R t u <-> red1 t u.

Proof.
intros t u; split; intro H.
(* red -> red1 *)
redtac. ex l r c (cont (s (var l))).
subst. rewrite !sub_cont, !fill_fill, !var_fill. split_all.
rewrite (term_cont_var (s (var l))) at 1. rewrite fill_fill, comp_comp. refl.
rewrite (term_cont_var (s (var r))) at 1.
rewrite fill_fill, comp_comp, (rules_preserve_vars_var lr). refl.
(* red1 -> red *)
destruct H as [l]. destruct H as [r]. destruct H as [c]. destruct H as [d].
decomp H.
set (s := fun x => if beq_nat x (var l) then fill d (Var (var t)) else Var x).
ex l r c s. rewrite H2, H3, !sub_cont. unfold s.
rewrite (rules_preserve_vars_var H0), (beq_refl beq_nat_ok),
  !fill_fill, !comp_comp. tauto.
Qed.

Lemma red1_eq : red R == red1.

Proof. rewrite rel_eq. apply red1_ok. Qed.

End red.

Arguments rules_preserve_vars_var [R] _ [l r] _.

(***********************************************************************)
(** equivalent definition of rewriting modulo (when rules preserve variables) *)

Section red_mod.

Variables (E R : rules)
  (hE : rules_preserve_vars E) (hR : rules_preserve_vars R).

Definition red_mod1 := red1 E # @ red1 R.

Lemma red_mod1_eq : red_mod E R == red_mod1.

Proof. unfold red_mod, red_mod1. rewrite !red1_eq; auto. refl. Qed.

End red_mod.

(***********************************************************************)
(** some properties of renamings *)

Definition is_renaming (s : substitution) := forall x, exists y, s x = Var y.

Lemma is_ren_single_var : forall x y, is_renaming (single x (Var y)).

Proof.
unfold is_renaming, single. intros. case_beq_nat x x0. exists y. refl.
exists x0. refl.
Qed.

Section renaming.

Variables (s : substitution) (hs : is_renaming s).

Lemma size_sub : forall t, size (sub s t) = size t.

Proof.
intro t; pattern t; apply term_ind with (Q := fun n (ts : terms n) =>
  size_terms (Vmap (sub s) ts) = size_terms ts); clear t.
(* Var *)
simpl. intro. destruct (hs x). rewrite H. refl.
(* Fun *)
intros. rewrite sub_fun, !size_fun, H. refl.
(* Vnil *)
refl.
(* Vcons *)
intros. simpl. rewrite H, H0. refl.
Qed.

Section red.

Variables (R : rules) (hR : rules_preserve_vars R).

(*REMARK: instance of a more general lemma on left-linear TRSs *)
Lemma red_ren : forall t u,
  red R (sub s t) u -> exists v, red R t v /\ sub s v = u.

Proof.
intros t u. rewrite red1_ok. 2: hyp. intro h. destruct h as [l].
destruct H as[r]. destruct H as [c]. destruct H as [d]. decomp H.
exists (fill (comp c (comp (cont r) d)) (Var (var t))). rewrite red1_ok.
2: hyp. split.
(* left *)
ex l r c d. split_all.
revert H2. rewrite (term_cont_var t), sub_fill, !var_fill.
simpl. rewrite subc_cont. destruct (hs (var t)). rewrite H. simpl. intro.
destruct (fill_var_elim H2) as [e]. revert H2. rewrite H1, !comp_comp.
intro. rewrite fill_eq_cont, !comp_eq in H2. rewrite H2. refl.
(* right *)
rewrite sub_fill, subc_cont, H3, fill_eq.
simpl. rewrite var_sub. destruct (hs (var t)). rewrite H. refl.
Qed.

Arguments red_ren [t u] _.

Lemma rtc_red_ren : forall t u,
  red R # (sub s t) u -> exists v, red R # t v /\ sub s v = u.

Proof.
cut (forall t' u, red R # t' u -> forall t, t' = sub s t -> exists v,
  red R # t v /\ sub s v = u). intros. apply H with (t':=sub s t). hyp. refl.
induction 1; intros; subst.
destruct (red_ren H). exists x. intuition auto with *.
exists t. intuition auto with *.
destruct (IHclos_refl_trans1 t (eq_refl (sub s t))). destruct H1.
symmetry in H2. destruct (IHclos_refl_trans2 x H2). exists x0. split_all.
apply rtc_trans with x; hyp.
Qed.

Lemma SN_red_ren : forall t : term, SN (red R) t -> SN (red R) (sub s t).

Proof.
induction 1. apply SN_intro. intros. destruct (red_ren H1). destruct H2.
subst. apply H0. hyp.
Qed.

End red.

Arguments red_ren [R] _ [t u] _.
Arguments rtc_red_ren [R] _ [t u] _.

Section red_mod.

Variables (E R : rules)
  (hE : rules_preserve_vars E) (hR : rules_preserve_vars R).

Lemma red_mod_ren : forall t u, red_mod E R (sub s t) u ->
  exists v, red_mod E R t v /\ sub s v = u.

Proof.
intros. do 2 destruct H. destruct (rtc_red_ren hE H). destruct H1. subst.
destruct (red_ren hR H0). exists x. split_all. exists x0. intuition.
Qed.

Arguments red_mod_ren [t u] _.

Lemma SN_red_mod_ren : forall t : term,
  SN (red_mod E R) t -> SN (red_mod E R) (sub s t).

Proof.
induction 1. apply SN_intro. intros. destruct (red_mod_ren H1). destruct H2.
subst. apply H0. hyp.
Qed.

End red_mod.

End renaming.

Arguments red_ren [s] _ [R] _ [t u] _.
Arguments red_mod_ren [s] _ [E R] _ _ [t u] _.

(***********************************************************************)
(** equivalence with rewriting on terms with at most 0 as variable *)

Definition red0 (R : rules) t u := red R t u /\ maxvar t = 0.

Lemma red0_incl_red : forall R, red0 R << red R.

Proof. intros R t u. unfold red0. tauto. Qed.

Section red0.

Variables (R : rules) (hR : rules_preserve_vars R).

Lemma red0_maxvar : forall t u, red0 R t u -> maxvar u = 0.

Proof.
unfold red0. split_all. cut (maxvar u <= maxvar t). lia.
apply (red_maxvar hR H).
Qed.

Lemma WF_red0 : WF (red R) <-> WF (red0 R).

Proof.
split; intro.
(* -> *)
apply (WF_incl (red R)). intros t u. unfold red0. intuition. hyp.
(* <- *)
cut (forall t, SN (red0 R) t -> maxvar t = 0 -> forall x,
  SN (red R) (sub (single 0 (@Var Sig x)) t)).
(* cut correctness *)
intro. intro u. rewrite (term_sub_cont 0 u). apply H0. apply H.
rewrite maxvar_fill. refl.
(* proof with cut *)
induction 1. intros h v. apply SN_intro; intros.
destruct (red_ren (is_ren_single_var 0 v) hR H2). destruct H3.
subst. assert (red0 R x x0). unfold red0. intuition.
apply H1. hyp. eapply red0_maxvar. apply H4.
Qed.

End red0.

Definition red_mod0 (E R : rules) t u := red_mod E R t u /\ maxvar t = 0.

Lemma red_mod0_incl_red_mod : forall E R, red_mod0 E R << red_mod E R.

Proof. intros E R t u. unfold red_mod0. tauto. Qed.

Section red_mod0.

Variables (E R : rules)
  (hE : rules_preserve_vars E) (hR : rules_preserve_vars R).

Lemma red_mod0_maxvar : forall t u, red_mod0 E R t u -> maxvar u = 0.

Proof.
intros. destruct H. cut (maxvar u <= maxvar t). lia.
apply (red_mod_maxvar hE hR H).
Qed.

Lemma WF_red_mod0 : WF (red_mod E R) <-> WF (red_mod0 E R).

Proof.
split; intro.
(* -> *)
apply (WF_incl (red_mod E R)). intros t u. unfold red_mod0. intuition.
hyp.
(* <- *)
cut (forall t, SN (red_mod0 E R) t -> maxvar t = 0 -> forall x,
  SN (red_mod E R) (sub (single 0 (@Var Sig x)) t)).
(* cut correctness *)
intro. intro u. rewrite (term_sub_cont 0 u). apply H0. apply H.
rewrite maxvar_fill. refl.
(* proof with cut *)
induction 1. intros h v. apply SN_intro; intros.
destruct (red_mod_ren (is_ren_single_var 0 v) hE hR H2). destruct H3.
subst. assert (red_mod0 E R x x0). unfold red_mod0. split_all.
apply H1. hyp. eapply red_mod0_maxvar. apply H4.
Qed.

End red_mod0.

(***********************************************************************)
(** equivalence with rewriting on rules with at most 0 as variable *)

Section reset.

Definition reset t := sub (swap (var t) 0) t.

Definition reset_rule (a : rule) := mkRule (reset (lhs a)) (reset (rhs a)).

Definition reset_rules := map reset_rule.

Lemma reset_fun1 : forall f t, reset (Fun1 f t) = Fun1 f (reset t).

Proof. intros. unfold reset. rewrite var_fun1, sub_fun1. refl. Qed.

Lemma var_reset : forall t, var (reset t) = 0.

Proof.
intro t; pattern t; apply term_ind_forall; clear t; intros.
unfold reset, swap, single. simpl. rewrite (beq_refl beq_nat_ok). refl.
unfold reset. rewrite sub_fun1, !var_fun1. fold (reset t). hyp.
Qed.

Lemma maxvar_reset : forall t, maxvar (reset t) = 0.

Proof. intro. rewrite maxvar_var, var_reset. refl. Qed.

Lemma maxvar_reset_rules : forall R a, In a (reset_rules R) ->
  maxvar (lhs a) = 0 /\ maxvar (rhs a) = 0.

Proof.
intros. unfold reset_rules in H. destruct (in_map_elim H). destruct H0. subst.
destruct x as [l r]. unfold reset_rule. simpl. rewrite !maxvar_reset. auto.
Qed.

Section red.

Variable R : rules.
Variable hR : rules_preserve_vars R.

Lemma rules_preserve_vars_reset : rules_preserve_vars (reset_rules R).

Proof.
intros l0 r0 h. destruct (in_map_elim h). destruct H. destruct x as [l r].
unfold reset_rule in H0. simpl in H0. inversion H0.
rewrite !vars_var, !var_reset. refl.
Qed.

Lemma red_reset : forall t u, red R t u <-> red (reset_rules R) t u.

Proof.
split; intro.
(* -> *)
redtac. subst. ded (rules_preserve_vars_var hR lr).
case (In_dec eq_nat_dec 0 (vars l)); intro.
(* In 0 (vars l) *)
rewrite vars_var in i. simpl in i. split_all.
apply red_rule. assert (mkRule l r = reset_rule (mkRule l r)).
unfold reset_rule. simpl. unfold reset. rewrite H, !H0, !swap_id. refl.
rewrite H1. apply in_map. hyp.
(* ~In 0 (vars l) *)
rewrite swap_intro with (x:=var l)(y:=0). 2: hyp.
rewrite swap_intro with (t:=r)(x:=var r)(y:=0).
2:{ rewrite vars_var. rewrite vars_var in n. rewrite H. hyp. }
(*VERY SLOW*)rewrite H at -2. apply red_rule.
change (In (reset_rule (mkRule l r)) (reset_rules R)). apply in_map. hyp.
(* <- *)
redtac. rename l into l0. rename r into r0. subst. destruct (in_map_elim lr).
destruct H. destruct x as [l r]. unfold reset_rule in H0. simpl in H0.
inversion H0. unfold reset. rewrite !sub_sub.
ded (rules_preserve_vars_var hR H). rewrite H1. apply red_rule. hyp.
Qed.

Lemma red_reset_eq : red R == red (reset_rules R).

Proof. split; intros t u; rewrite <- red_reset; auto. Qed.

Lemma hd_red_reset : forall t u, hd_red R t u <-> hd_red (reset_rules R) t u.

Proof.
split; intro.
(* -> *)
redtac. subst. ded (rules_preserve_vars_var hR lr).
case (In_dec eq_nat_dec 0 (vars l)); intro.
(* In 0 (vars l) *)
rewrite vars_var in i. simpl in i. split_all.
apply hd_red_rule. assert (mkRule l r = reset_rule (mkRule l r)).
unfold reset_rule. simpl. unfold reset. rewrite H, !H0, !swap_id. refl.
rewrite H1. apply in_map. hyp.
(* ~In 0 (vars l) *)
rewrite swap_intro with (x:=var l)(y:=0). 2: hyp.
rewrite swap_intro with (t:=r)(x:=var r)(y:=0).
2:{ rewrite vars_var. rewrite vars_var in n. rewrite H. hyp. }
(*VERY SLOW*)rewrite H at -2. apply hd_red_rule.
change (In (reset_rule (mkRule l r)) (reset_rules R)). apply in_map. hyp.
(* <- *)
redtac. rename l into l0. rename r into r0. subst. destruct (in_map_elim lr).
destruct H. destruct x as [l r]. unfold reset_rule in H0. simpl in H0.
inversion H0. unfold reset. rewrite !sub_sub.
ded (rules_preserve_vars_var hR H). rewrite H1. apply hd_red_rule. hyp.
Qed.

Lemma hd_red_reset_eq : hd_red R == hd_red (reset_rules R).

Proof. split; intros t u; rewrite <- hd_red_reset; auto. Qed.

End red.

Variable E R : rules.
Variable hE : rules_preserve_vars E.
Variable hR : rules_preserve_vars R.

Lemma red_mod_reset_eq : red_mod E R == red_mod (reset_rules E) (reset_rules R).

Proof. unfold red_mod. rewrite <- !red_reset_eq; try hyp. refl. Qed.

Lemma hd_red_mod_reset_eq :
  hd_red_mod E R == hd_red_mod (reset_rules E) (reset_rules R).

Proof.
unfold hd_red_mod. rewrite <- hd_red_reset_eq; try hyp.
rewrite <- red_reset_eq; try hyp. refl.
Qed.

Lemma red_mod_reset : forall t u,
  red_mod E R t u <-> red_mod (reset_rules E) (reset_rules R) t u.

Proof. rewrite <- rel_eq. apply red_mod_reset_eq. Qed.

Lemma hd_red_mod_reset : forall t u,
  hd_red_mod E R t u <-> hd_red_mod (reset_rules E) (reset_rules R) t u.

Proof. rewrite <- rel_eq. apply hd_red_mod_reset_eq. Qed.

End reset.

End S.

Arguments rules_preserve_vars_var [Sig] _ [R] _ [l r] _.
Arguments bis_unary_ok [Sig Fs] _.

(***********************************************************************)
(** tactics for Rainbow *)

Ltac is_unary Fs_ok := rewrite <- (bis_unary_ok Fs_ok); check_eq.
