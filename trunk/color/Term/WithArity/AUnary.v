(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

properties of systems with unary symbols only
*)

Set Implicit Arguments.

Require Import ATrs.
Require Import VecUtil.
Require Import LogicUtil.
Require Import List.

(***********************************************************************)
(** tactics *)

Ltac arity1 hyp :=
  match goal with
    | e : ?i + S ?j = arity ?f |- _ =>
      ded (hyp f); assert (i=0); [omega | subst i; assert (j=0);
        [omega | subst j; VOtac]]
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

Variable hyp : is_unary.

Ltac arity := arity1 hyp.

(***********************************************************************)
(** specific induction principle *)

Section term_ind.

Variables (P : term -> Prop)
  (Hvar : forall x, P (Var x))
  (Hfun : forall f t, P t -> P (Fun f (Vcast (Vcons t Vnil) (hyp f)))).

Require Import NatUtil.

Lemma term_ind_forall : forall t, P t.

Proof.
apply term_ind_forall_cast. hyp. intro f. ded (hyp f). destruct ts.
intro. absurd_arith. destruct ts.
simpl Vforall. intuition. assert (h = hyp f). apply eq_unique. subst h.
apply Hfun. hyp.
intro. absurd_arith.
Qed.

End term_ind.

(***********************************************************************)
(** unique variable of a term *)

Fixpoint var (t : term) : variable :=
  match t with
    | Var x => x
    | Fun _ ts => Vmap_first 0 var ts
  end.

Lemma var_fun : forall f u (h : 1 = arity f),
  var (Fun f (Vcast (Vcons u Vnil) h)) = var u.

Proof.
intros. unfold var; fold var. rewrite Vmap_first_cast. refl.
Qed.

Lemma var_fill : forall c t, var (fill c t) = var t.

Proof.
induction c; simpl; intros. refl. rewrite Vmap_first_cast. arity. simpl.
apply IHc.
Qed.

Lemma var_sub : forall s t, var (sub s t) = var (s (var t)).

Proof.
intro s. apply term_ind_forall. refl. intros. rewrite sub_fun.
rewrite Vmap_cast. simpl Vmap. repeat rewrite var_fun. hyp.
Qed.

Lemma vars_var : forall t, vars t = var t :: nil.

Proof.
apply term_ind_forall. refl. intros. rewrite vars_fun. rewrite vars_vec_cast.
rewrite var_fun. simpl. rewrite <- app_nil_end. hyp.
Qed.

(***********************************************************************)
(** biggest context of a term *)

Lemma cont_aux : forall f : Sig, 0 + S 0 = arity f.

Proof.
intro. rewrite <- hyp. refl.
Qed.

Fixpoint cont (t : term) : context :=
  match t with
    | Var _ => Hole
    | Fun f ts => Cont f (cont_aux f) Vnil (Vmap_first Hole cont ts) Vnil
  end.

Lemma cont_aux_eq : forall f, cont_aux f = hyp f.

Proof.
intro. apply eq_unique.
Qed.

Ltac simpl_cont := unfold cont, var; repeat rewrite Vmap_first_cast;
  fold cont; fold var; simpl Vmap_first; unfold fill;
    repeat rewrite cont_aux_eq.

Lemma subc_cont : forall s (c : context), subc s c = c.

Proof.
induction c; simpl; intros. refl. arity. simpl. rewrite IHc. refl.
Qed.

Lemma term_cont_var : forall t, t = fill (cont t) (Var (var t)).

Proof.
apply term_ind_forall. refl. intros. simpl_cont. apply args_eq. simpl Vapp.
apply Vcast_eq_intro. apply Vcons_eq_intro. hyp. refl.
Qed.

Lemma sub_cont : forall s t, sub s t = fill (cont t) (s (var t)).

Proof.
intro. apply term_ind_forall. refl. intros. simpl_cont. rewrite sub_fun.
apply args_eq. rewrite Vmap_cast. apply Vcast_eq_intro. simpl. rewrite H. refl.
Qed.

Require Import EqUtil.

Lemma term_sub_cont : forall x t,
  t = sub (single x (Var (var t))) (fill (cont t) (Var x)).

Proof.
intros. rewrite sub_fill. rewrite subc_cont. unfold single. simpl.
rewrite (beq_refl beq_nat_ok). apply term_cont_var.
Qed.

Lemma fill_var_elim : forall x c d (u : term), fill c (Var x) = fill d u ->
  exists e, c = comp d e.

Proof.
induction c. simpl. intros. destruct (var_eq_fill H). subst. exists Hole. refl.
simpl. intros. destruct (fun_eq_fill H). subst. exists (Cont f e v c v0). refl.
decomp H0. subst. simpl in *. Funeqtac. arity. arity. simpl Vapp in *.
assert (x2=e). apply eq_unique. subst x2. rewrite Vcast_eq in H0.
inversion H0. destruct (IHc _ _ H3). subst. exists x0. refl.
Qed.

Implicit Arguments fill_var_elim [x c d u].

Lemma fill_eq_cont : forall (t : term) c d, fill c t = fill d t <-> c = d.

Proof.
split. Focus 2. intro. subst. refl.
gen d. gen c. induction c.
(* c=Hole *)
simpl. intro. symmetry. apply (wf_term H).
(* c=Cont *)
destruct d; simpl.
(* d=Hole *)
intro. change (fill (Cont f e v c v0) t = t) in H. symmetry in H.
ded (wf_term H). hyp.
(* d=Cont *)
intro. Funeqtac. arity. arity. assert (e0=e). apply eq_unique. subst.
rewrite Vcast_eq in H0. rewrite Vapp_eq in H0. destruct H0. inversion H2.
rewrite (IHc _ H4). refl.
Qed.

Require Import VecMax.

Lemma maxvar_fill : forall (t : term) c, maxvar (fill c t) = maxvar t.

Proof.
induction c. refl. simpl fill. rewrite maxvar_fun. unfold maxvars.
rewrite Vmap_cast. rewrite Vmax_cast. arity. simpl. rewrite IHc.
apply max_0_r.
Qed.

(***********************************************************************)
(** equivalent definition of rewriting (when rules preserve variables) *)

Section red.

Variables (R : rules) (hR : rules_preserv_vars R).

Lemma rules_preserv_vars_var : forall l r, In (mkRule l r) R -> var r = var l.

Proof.
intros. ded (hR _ _ H). repeat rewrite vars_var in H0. unfold incl in H0.
ded (H0 (var r)). simpl in H1. intuition.
Qed.

Implicit Arguments rules_preserv_vars_var [l r].

Definition red1 t u := exists l, exists r, exists c, exists d,
  In (mkRule l r) R /\ t = fill (comp c (comp (cont l) d)) (Var (var t))
  /\ u = fill (comp c (comp (cont r) d)) (Var (var t)).

Require Import EqUtil.

Lemma red1_ok : forall t u, red R t u <-> red1 t u.

Proof.
intros t u; split; intro H.
(* red -> red1 *)
redtac. exists l. exists r. exists c. exists (cont (s (var l))).
subst. repeat rewrite sub_cont. repeat rewrite fill_fill.
repeat rewrite var_fill. intuition.
rewrite (term_cont_var (s (var l))) at 1. rewrite fill_fill.
rewrite comp_comp. refl.
rewrite (term_cont_var (s (var r))) at 1. rewrite fill_fill.
rewrite comp_comp. rewrite (rules_preserv_vars_var lr). refl.
(* red1 -> red *)
destruct H as [l]. destruct H as [r]. destruct H as [c]. destruct H as [d].
decomp H. exists l. exists r. exists c.
set (s := fun x => if beq_nat x (var l) then fill d (Var (var t)) else Var x).
exists s. rewrite H2. rewrite H3. repeat rewrite sub_cont. unfold s.
rewrite (rules_preserv_vars_var H0). rewrite (beq_refl beq_nat_ok).
repeat rewrite fill_fill. repeat rewrite comp_comp. intuition.
Qed.

Require Import RelUtil.

Lemma red1_eq : red R == red1.

Proof.
rewrite rel_eq. apply red1_ok.
Qed.

End red.

(***********************************************************************)
(** equivalent definition of rewriting modulo (when rules preserve variables) *)

Section red_mod.

Variables (E R : rules)
  (hE : rules_preserv_vars E) (hR : rules_preserv_vars R).

Require Import RelUtil.

Definition red_mod1 := red1 E # @ red1 R.

Lemma red_mod1_eq : red_mod E R == red_mod1.

Proof.
unfold red_mod, red_mod1. repeat (rewrite red1_eq; [idtac|hyp]). refl.
Qed.

End red_mod.

(***********************************************************************)
(** some properties of renamings *)

Definition is_renaming (s : substitution) := forall x, exists y, s x = Var y.

Lemma is_ren_single_var : forall x y, is_renaming (single x (Var y)).

Proof.
unfold is_renaming, single. intros. case_nat_eq x x0. exists y. refl.
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
intros. rewrite sub_fun. repeat rewrite size_fun. rewrite H. refl.
(* Vnil *)
refl.
(* Vcons *)
intros. simpl. rewrite H. rewrite H0. refl.
Qed.

Section red.

Variables (R : rules) (hR : rules_preserv_vars R).

(*FIXME: instance of a more general lemma on left-linear TRSs *)
Lemma red_ren : forall t u,
  red R (sub s t) u -> exists v, red R t v /\ sub s v = u.

Proof.
intros t u. rewrite red1_ok. 2: hyp. intro h. destruct h as [l].
destruct H as[r]. destruct H as [c]. destruct H as [d]. decomp H.
exists (fill (comp c (comp (cont r) d)) (Var (var t))). rewrite red1_ok.
2: hyp. split.
(* left *)
exists l. exists r. exists c. exists d. intuition.
gen H2. rewrite (term_cont_var t). rewrite sub_fill. repeat rewrite var_fill.
simpl. rewrite subc_cont. destruct (hs (var t)). rewrite H. simpl. intro.
destruct (fill_var_elim H2) as [e]. gen H2. rewrite H1.
repeat rewrite comp_comp. intro. rewrite fill_eq_cont in H2.
repeat rewrite comp_eq in H2. rewrite H2. refl.
(* right *)
rewrite sub_fill. rewrite subc_cont. rewrite H3. rewrite fill_eq.
simpl. rewrite var_sub. destruct (hs (var t)). rewrite H. refl.
Qed.

Implicit Arguments red_ren [t u].

Lemma rtc_red_ren : forall t u,
  red R # (sub s t) u -> exists v, red R # t v /\ sub s v = u.

Proof.
cut (forall t' u, red R # t' u -> forall t, t' = sub s t -> exists v,
  red R # t v /\ sub s v = u). intros. apply H with (t':=sub s t). hyp. refl.
induction 1; intros; subst.
destruct (red_ren H). exists x. intuition.
exists t. intuition.
destruct (IHclos_refl_trans1 t (refl_equal (sub s t))). destruct H1.
symmetry in H2. destruct (IHclos_refl_trans2 x H2). exists x0. intuition.
apply rtc_trans with x; hyp.
Qed.

Require Import SN.

Lemma SN_red_ren : forall t : term, SN (red R) t -> SN (red R) (sub s t).

Proof.
induction 1. apply SN_intro. intros. destruct (red_ren H1). destruct H2.
subst. apply H0. hyp.
Qed.

End red.

Implicit Arguments red_ren [R t u].
Implicit Arguments rtc_red_ren [R t u].

Section red_mod.

Variables (E R : rules)
  (hE : rules_preserv_vars E) (hR : rules_preserv_vars R).

Lemma red_mod_ren : forall t u, red_mod E R (sub s t) u ->
  exists v, red_mod E R t v /\ sub s v = u.

Proof.
intros. do 2 destruct H. destruct (rtc_red_ren hE H). destruct H1. subst.
destruct (red_ren hR H0). exists x. intuition. exists x0. intuition.
Qed.

Implicit Arguments red_mod_ren [t u].

Require Import SN.

Lemma SN_red_mod_ren : forall t : term,
  SN (red_mod E R) t -> SN (red_mod E R) (sub s t).

Proof.
induction 1. apply SN_intro. intros. destruct (red_mod_ren H1). destruct H2.
subst. apply H0. hyp.
Qed.

End red_mod.

End renaming.

Implicit Arguments red_ren [s R t u].
Implicit Arguments red_mod_ren [s E R t u].

(***********************************************************************)
(** equivalence with rewriting on terms with one variable only *)

Definition red0 (R : rules) t u := red R t u /\ maxvar t = 0.

Section red0.

Require Import ListMax.

Variables (R : rules) (hR : rules_preserv_vars R).

Lemma red0_maxvar : forall t u, red0 R t u -> maxvar u = 0.

Proof.
unfold red0. intuition. cut (maxvar u <= maxvar t). intro. omega.
apply (red_maxvar hR H0).
Qed.

Lemma WF_red0 : WF (red R) <-> WF (red0 R).

Proof.
split; intro.
(* -> *)
apply WF_incl with (S := red R). intros t u. unfold red0. intuition. hyp.
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

Section red_mod0.

Variables (E R : rules)
  (hE : rules_preserv_vars E) (hR : rules_preserv_vars R).

Lemma red_mod0_maxvar : forall t u, red_mod0 E R t u -> maxvar u = 0.

Proof.
intros. destruct H. cut (maxvar u <= maxvar t). intro. omega.
apply (red_mod_maxvar hE hR H).
Qed.

Lemma WF_red_mod0 : WF (red_mod E R) <-> WF (red_mod0 E R).

Proof.
split; intro.
(* -> *)
apply WF_incl with (S := red_mod E R). intros t u. unfold red_mod0. intuition.
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
subst. assert (red_mod0 E R x x0). unfold red_mod0. intuition.
apply H1. hyp. eapply red_mod0_maxvar. apply H4.
Qed.

End red_mod0.

End S.

Implicit Arguments rules_preserv_vars_var [Sig R l r].
