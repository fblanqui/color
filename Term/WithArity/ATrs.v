(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Adam Koprowski and Hans Zantema, 2007-03-20

rewriting
*)

Set Implicit Arguments.

Require Import ARelation.
Require Export AContext.
Require Export ASubstitution.
Require Import ListUtil.
Require Import ListRepeatFree.
Require Import LogicUtil.
Require Import VecUtil.
Require Import RelUtil.
Require Import ListForall.
Require Import SN.

Section basic_definitions.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).

(***********************************************************************)
(** rule *)

Record rule : Type := mkRule { lhs : term; rhs : term }.

Lemma eq_rule_dec : forall a b : rule, {a=b}+{~a=b}.

Proof.
decide equality; apply eq_term_dec.
Defined.

Definition rules := (list rule).

(***********************************************************************)
(** basic definitions and properties on rules *)

Definition is_notvar_lhs a :=
  match lhs a with
    | Var _ => false
    | _ => true
  end.

Lemma is_notvar_lhs_elim : forall R, forallb is_notvar_lhs R = true ->
  forall l r, In (mkRule l r) R -> exists f, exists ts, l = Fun f ts.

Proof.
intros. rewrite forallb_forall in H. ded (H _ H0). destruct l. discr.
exists f. exists v. refl.
Qed.

Lemma is_notvar_lhs_false : forall R, forallb is_notvar_lhs R = true ->
  forall x r, In (mkRule (Var x) r) R -> False.

Proof.
intros. rewrite forallb_forall in H. ded (H _ H0). discr.
Qed.

Definition is_notvar_rhs a :=
  match rhs a with
    | Var _ => false
    | _ => true
  end.

Lemma is_notvar_rhs_elim : forall R, forallb is_notvar_rhs R = true ->
  forall l r, In (mkRule l r) R -> exists f, exists ts, r = Fun f ts.

Proof.
intros. rewrite forallb_forall in H. ded (H _ H0). destruct r. discr.
exists f. exists v. refl.
Qed.

Lemma is_notvar_rhs_false : forall R, forallb is_notvar_rhs R = true ->
  forall x l, In (mkRule l (Var x)) R -> False.

Proof.
intros. rewrite forallb_forall in H. ded (H _ H0). discr.
Qed.

(***********************************************************************)
(** rewrite steps *)

Section rewriting.

Variable R : rules.

Definition red u v := exists l, exists r, exists c, exists s,
  In (mkRule l r) R /\ u = fill c (sub s l) /\ v = fill c (sub s r).

Definition hd_red u v := exists l, exists r, exists s,
  In (mkRule l r) R /\ u = sub s l /\ v = sub s r.

Definition int_red u v := exists l, exists r, exists c, exists s,
  c <> Hole
  /\ In (mkRule l r) R /\ u = fill c (sub s l) /\ v = fill c (sub s r).

Definition NF u := forall v, ~red u v.

(***********************************************************************)
(** innermost rewriting *)

Definition innermost u := forall f us, u = Fun f us -> Vforall NF us.

Definition in_red u v := exists l, exists r, exists c, exists s,
  In (mkRule l r) R /\ u = fill c (sub s l) /\ v = fill c (sub s r)
  /\ innermost (sub s l).

Definition in_hd_red u v := exists l, exists r, exists s,
  In (mkRule l r) R /\ u = sub s l /\ v = sub s r
  /\ innermost u.

Definition in_int_red u v := exists l, exists r, exists c, exists s,
  c <> Hole
  /\ In (mkRule l r) R /\ u = fill c (sub s l) /\ v = fill c (sub s r)
  /\ innermost (sub s l).

End rewriting.

(***********************************************************************)
(** rewrite modulo steps *)

Section rewriting_modulo.

Variables (S : relation term) (E R: rules).

Definition hd_red_Mod := S @ hd_red R.

Definition red_mod := red E # @ red R.

Definition hd_red_mod := red E # @ hd_red R.

Definition hd_red_mod_min s t := hd_red_mod s t 
  /\ lforall (SN (red E)) (direct_subterms s)
  /\ lforall (SN (red E)) (direct_subterms t).

End rewriting_modulo.

End basic_definitions.

Implicit Arguments is_notvar_lhs_elim [Sig R l r].
Implicit Arguments is_notvar_rhs_elim [Sig R l r].

(***********************************************************************)
(** tactics *)

Ltac redtac := repeat
  match goal with
    | H : red _ _ _ |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r];
       destruct H as [c]; destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (red _) _ _ |- _ => unfold transp in H; redtac
    | H : hd_red _ _ _ |- _ =>
      let l := fresh "l" in let r := fresh "r" in
      let s := fresh "s" in let h1 := fresh in
      (unfold hd_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (hd_red _) _ _ |- _ => unfold transp in H; redtac
    | H : int_red _ _ _ |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in let h2 := fresh in
      (unfold int_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [c]; destruct H as [s]; destruct H as [H h1];
      destruct h1 as [h1 h2]; destruct h2)
    | H : transp (int_red _) _ _ |- _ => unfold transp in H; redtac
    | H : red_mod _ _ _ _ |- _ =>
      let t := fresh "t" in let h := fresh in
        (destruct H as [t h]; destruct h; redtac)
    | H : hd_red_mod _ _ _ _ |- _ =>
      let t := fresh "t" in let h := fresh in
        (destruct H as [t h]; destruct h; redtac)
    | H : hd_red_Mod _ _ _ _ |- _ =>
      let t := fresh "t" in let h := fresh in
        (destruct H as [t h]; destruct h; redtac)
  end.

Ltac is_var_lhs := cut False;
  [tauto | eapply is_notvar_lhs_false; eassumption].

Ltac is_var_rhs := cut False;
  [tauto | eapply is_notvar_rhs_false; eassumption].

(***********************************************************************)
(** properties *)

Section S.

Variable Sig : Signature.

Notation term := (term Sig).
Notation terms := (vector term).
Notation rule := (rule Sig).
Notation rules := (list rule).

Notation empty_trs := (nil (A:=rule)).

(***********************************************************************)
(** basic properties of rewriting *)

Section rewriting.

Variable R R' : rules.

Lemma red_rule : forall l r c s, In (mkRule l r) R ->
  red R (fill c (sub s l)) (fill c (sub s r)).

Proof.
intros. unfold red. exists l. exists r. exists c. exists s. auto.
Qed.

Lemma red_empty : forall t u : term, (red empty_trs #) t u -> t = u.

Proof.
intros. induction H. redtac. contradiction. refl. congruence.
Qed.

Lemma red_rule_top : forall l r s, In (mkRule l r) R ->
  red R (sub s l) (sub s r).

Proof.
intros. unfold red. exists l. exists r. exists (@Hole Sig). exists s. auto.
Qed.

Lemma hd_red_rule : forall l r s, In (mkRule l r) R ->
  hd_red R (sub s l) (sub s r).

Proof.
intros. unfold hd_red. exists l. exists r. exists s. auto.
Qed.

Lemma red_fill : forall c t u, red R t u -> red R (fill c t) (fill c u).

Proof.
intros. redtac. unfold red.
exists l. exists r. exists (AContext.comp c c0). exists s. split. assumption.
subst t. subst u. do 2 rewrite fill_comp. auto.
Qed.

Lemma red_subterm : forall u u' t, red R u u' -> subterm_eq u t
  -> exists t', red R t t' /\ subterm_eq u' t'.

Proof.
unfold subterm_eq. intros. destruct H0 as [d]. subst t. redtac. subst u.
subst u'. exists (fill (AContext.comp d c) (sub s r)). split.
exists l. exists r. exists (AContext.comp d c). exists s. split. assumption.
rewrite fill_comp. auto. exists d. rewrite fill_comp. refl.
Qed.

Lemma int_red_fun : forall f ts v, int_red R (Fun f ts) v
  -> exists i, exists vi : terms i, exists t, exists j, exists vj : terms j,
    exists h, exists t', ts = Vcast (Vapp vi (Vcons t vj)) h
    /\ v = Fun f (Vcast (Vapp vi (Vcons t' vj)) h) /\ red R t t'.

Proof.
intros. redtac. destruct c. absurd (@Hole Sig = Hole); auto. clear H.
simpl in H1.
Funeqtac. exists i. exists v0. exists (fill c (sub s l)). exists j. exists v1.
exists e. exists (fill c (sub s r)). split. assumption. split. assumption.
unfold red. exists l. exists r. exists c. exists s. auto.
Qed.

Lemma red_swap : red (R ++ R') << red (R' ++ R).

Proof.
intros x y RR'xy. redtac.
exists l. exists r. exists c. exists s. repeat split; auto.
destruct (in_app_or RR'xy); apply in_or_app; auto.
Qed.

Lemma hd_red_swap : hd_red (R ++ R') << hd_red (R' ++ R).

Proof.
intros x y RR'xy. redtac.
exists l. exists r. exists s. repeat split; auto.
destruct (in_app_or RR'xy); apply in_or_app; auto.
Qed.

Lemma int_red_incl_red : int_red R << red R.

Proof.
unfold inclusion, int_red. intros. decomp H. subst x. subst y. apply red_rule.
assumption.
Qed.

Lemma hd_red_incl_red : hd_red R << red R.

Proof.
unfold inclusion. intros. redtac. subst x. subst y. apply red_rule_top. hyp.
Qed.

Lemma WF_red_empty : WF (red empty_trs).

Proof.
intro x. apply SN_intro. intros y Exy. redtac. contradiction.
Qed.

Lemma hd_red_mod_incl_red_mod : forall E, hd_red_mod E R << red_mod E R.

Proof.
intro. unfold hd_red_mod, red_mod. comp. apply hd_red_incl_red.
Qed.

Lemma int_red_preserv_hd : forall u v, int_red R u v ->
  exists f, exists us,exists vs, u = Fun f us /\ v = Fun f vs.

Proof.
intros. do 5 destruct H. intuition. destruct x1. congruence.
simpl in *. exists f.
exists (Vcast (Vapp v0 (Vcons (fill x1 (sub x2 x)) v1)) e).
exists (Vcast (Vapp v0 (Vcons (fill x1 (sub x2 x0)) v1)) e).
tauto.
Qed.

Lemma int_red_rtc_preserv_hd : forall u v, int_red R # u v ->
  u=v \/ exists f, exists us, exists vs, u = Fun f us /\ v = Fun f vs.

Proof.
intros. induction H; auto.
right. apply int_red_preserv_hd. auto.
destruct IHclos_refl_trans1; destruct IHclos_refl_trans2; subst; auto.
right. do 3 destruct H1. do 3 destruct H2. intuition; subst; auto.
inversion H1. subst. exists x3; exists x1; exists x5. auto.
Qed.

End rewriting.

(***********************************************************************)
(** preservation of variables under reduction *)

Section vars.

Variable R : rules.

Definition rules_preserv_vars :=
  forall l r, In (mkRule l r) R -> incl (vars r) (vars l).

Variable hyp : rules_preserv_vars.

Lemma red_preserv_vars : preserv_vars (red R).

Proof.
unfold preserv_vars. intros. redtac. subst t. subst u.
apply incl_tran with (cvars c ++ vars (sub s r)). apply vars_fill_elim.
apply incl_tran with (cvars c ++ vars (sub s l)). apply appl_incl.
apply incl_vars_sub. apply hyp. exact H.
apply vars_fill_intro.
Qed.

Lemma tred_preserv_vars : preserv_vars (red R !).

Proof.
unfold preserv_vars. induction 1. apply red_preserv_vars. exact H.
apply incl_tran with (vars y); assumption.
Qed.

Lemma rtred_preserv_vars : preserv_vars (red R #).

Proof.
unfold preserv_vars. induction 1. apply red_preserv_vars. exact H.
apply List.incl_refl. apply incl_tran with (vars y); assumption.
Qed.

End vars.

Lemma rules_preserv_vars_incl : forall R S : rules,
  incl R S -> rules_preserv_vars S -> rules_preserv_vars R.

Proof.
unfold rules_preserv_vars, incl. intuition. eapply H0. apply H. apply H1. hyp.
Qed.

(***********************************************************************)
(** rewriting vectors of terms *)

Section vector.

Require Import VecOrd.

Variable R : rules.

Definition terms_gt := Vgt_prod (red R).

Lemma Vgt_prod_fun : forall f ts ts',
  Vgt_prod (red R) ts ts' -> int_red R (Fun f ts) (Fun f ts').

Proof.
intros. ded (Vgt_prod_gt H). do 8 destruct H0. destruct H1. redtac.
subst x1. subst x5. unfold transp, int_red. rewrite H0. rewrite H1.
exists l. exists r. exists (Cont f x4 x0 c x3). exists s. split. discriminate.
auto.
Qed.

End vector.

(***********************************************************************)
(** union of rewrite rules *)

Section union.

Variables R R' : rules.

Lemma red_union : red (R ++ R') << red R U red R'.

Proof.
unfold inclusion. intros. redtac. subst x. subst y.
ded (in_app_or H). destruct H0.
left. apply red_rule. exact H0. right. apply red_rule. exact H0.
Qed.

Lemma red_union_inv : red R U red R' << red (R ++ R').

Proof.
intros x y RR'xy.
destruct RR'xy as [Rxy | Rxy]; destruct Rxy as [rl [rr [c [s [Rr [dx dy]]]]]]; 
  subst x; subst y; exists rl; exists rr; exists c; exists s; intuition.
Qed.

Lemma red_incl : incl R R' -> red R << red R'.

Proof.
  intros RR' u v Rst. redtac.
  exists l. exists r. exists c. exists s. repeat split; try assumption.
  apply RR'. assumption.
Qed.

Lemma hd_red_incl : incl R R' -> hd_red R << hd_red R'.

Proof.
  intros RR' u v Rst. redtac.
  exists l. exists r. exists s. repeat split; try assumption.
  apply RR'. assumption.
Qed.

Lemma hd_red_union : hd_red (R ++ R') << hd_red R U hd_red R'.

Proof.
unfold inclusion. intros. redtac. subst x. subst y.
ded (in_app_or H). destruct H0.
left. apply hd_red_rule. exact H0. right. apply hd_red_rule. exact H0.
Qed.

Lemma hd_red_union_inv : hd_red R U hd_red R' << hd_red (R ++ R').

Proof.
intros x y RR'xy.
destruct RR'xy as [Rxy | Rxy]; destruct Rxy as [rl [rr [s [Rr [dx dy]]]]]; 
  subst x; subst y; exists rl; exists rr; exists s; intuition.
Qed.

End union.

(***********************************************************************)
(** properties of rewriting modulo *)

Section rewriting_modulo_results.

Variables (S S' : relation term) (E E' R R' : rules).

Lemma hd_red_Mod_incl :
  S << S' -> incl R R' -> hd_red_Mod S R << hd_red_Mod S' R'.

Proof.
intros. unfold hd_red_Mod. comp. hyp. apply hd_red_incl. hyp.
Qed.

Lemma hd_red_mod_of_hd_red_Mod_int :
  hd_red_Mod (int_red E #) R << hd_red_mod E R.

Proof.
unfold hd_red_Mod, hd_red_mod.
apply incl_comp. assert (int_red E # << red E #).
apply incl_rtc. apply int_red_incl_red. eauto.
apply inclusion_refl.
Qed.

Lemma hd_red_mod_of_hd_red_Mod : hd_red_Mod (red E #) R << hd_red_mod E R.

Proof.
unfold hd_red_Mod, hd_red_mod. apply inclusion_refl.
Qed.

Lemma hd_red_Mod_make_repeat_free :
  hd_red_Mod S R << hd_red_Mod S (make_repeat_free (@eq_rule_dec Sig) R).

Proof.
intros. unfold hd_red_Mod. comp. unfold inclusion. intros. redtac.
exists l; exists r; exists s. intuition. apply incl_make_repeat_free. auto.
Qed.

Lemma hd_red_mod_make_repeat_free :
  hd_red_mod E R << hd_red_mod E (make_repeat_free (@eq_rule_dec Sig) R).

Proof.
intros. unfold hd_red_mod. comp. unfold inclusion. intros. redtac.
exists l; exists r; exists s. intuition. apply incl_make_repeat_free. auto.
Qed.

Lemma red_mod_empty_incl_red : red_mod empty_trs R << red R.

Proof.
intros u v Ruv. destruct Ruv as [s' [ss' Ruv]].
rewrite (red_empty ss'). assumption.
Qed.

Lemma hd_red_mod_empty_incl_hd_red : hd_red_mod empty_trs R << hd_red R.

Proof.
unfold inclusion. intros. do 2 destruct H. ded (red_empty H). subst x0.
exact H0.
Qed.

Lemma red_mod_incl : incl R R' -> incl E E' -> red_mod E R << red_mod E' R'.

Proof.
intros. unfold red_mod. comp. apply incl_rtc.
apply red_incl. assumption. apply red_incl. assumption.
Qed.

Lemma WF_red_mod_empty : WF (red_mod E empty_trs).

Proof.
intro x. apply SN_intro. intros y Exy. destruct Exy as [z [xz zy]]. redtac.
contradiction.
Qed.

Lemma WF_hd_red_mod_empty : WF (hd_red_mod E empty_trs).

Proof.
apply WF_incl with (red_mod E empty_trs).
apply hd_red_mod_incl_red_mod. apply WF_red_mod_empty.
Qed.

Lemma WF_hd_red_Mod_empty : WF (hd_red_Mod S empty_trs).

Proof.
apply WF_incl with (@empty_rel term). intros x y h. redtac. contradiction.
apply WF_empty_rel.
Qed.

Lemma hd_red_mod_min_incl : hd_red_mod_min E R << hd_red_mod E R.

Proof.
unfold hd_red_mod_min. intros s t [hrm _]. trivial. 
Qed.

End rewriting_modulo_results.

(***********************************************************************)
(** termination as special case of relative termination *)

Section termination_as_relative_term.

Variable R R' : rules.

Lemma red_incl_red_mod : red R << red_mod empty_trs R.

Proof.
intros u v Ruv. exists u. split. constructor 2. assumption.
Qed.

Lemma hd_red_incl_hd_red_mod : hd_red R << hd_red_mod empty_trs R.

Proof.
intros u v Ruv. exists u. split. constructor 2. assumption.
Qed.

End termination_as_relative_term.

(***********************************************************************)
(** union of rewrite rules modulo *)

Section union_modulo.

Variable S : relation term.
Variables E R R' : rules.

Lemma red_mod_union : red_mod E (R ++ R') << red_mod E R U red_mod E R'.

Proof.
unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
ded (in_app_or H0). destruct H1.
left. exists (fill c (sub s l)); split. assumption. apply red_rule. exact H1.
right. exists (fill c (sub s l)); split. assumption. apply red_rule. exact H1.
Qed.

Lemma hd_red_Mod_union :
  hd_red_Mod S (R ++ R') << hd_red_Mod S R U hd_red_Mod S R'.

Proof.
unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
ded (in_app_or H0). destruct H1.
left. exists (sub s l); split. assumption. apply hd_red_rule. exact H1.
right. exists (sub s l); split. assumption. apply hd_red_rule. exact H1.
Qed.

Lemma hd_red_mod_union :
  hd_red_mod E (R ++ R') << hd_red_mod E R U hd_red_mod E R'.

Proof.
unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
ded (in_app_or H0). destruct H1.
left. exists (sub s l); split. assumption. apply hd_red_rule. exact H1.
right. exists (sub s l); split. assumption. apply hd_red_rule. exact H1.
Qed.

Lemma hd_red_mod_min_union :
  hd_red_mod_min E (R ++ R') << hd_red_mod_min E R U hd_red_mod_min E R'.

Proof.
unfold inclusion. intros. destruct H. do 2 destruct H. redtac. subst x0. subst y.
ded (in_app_or H1). destruct H2.
left. split. exists (sub s l); split. assumption. apply hd_red_rule. exact H2. exact H0.
right. split. exists (sub s l); split. assumption. apply hd_red_rule. exact H2. exact H0.
Qed.

End union_modulo.

(***********************************************************************)
(** declarations of implicit arguments *)

End S.

Implicit Arguments int_red_fun [Sig R f ts v].

(***********************************************************************)
(** tactics *)

Ltac set_Sig_to x :=
  match goal with
  | |- WF (@hd_red_Mod ?S _ _) => set (x := S)
  | |- WF (@hd_red_mod ?S _ _) => set (x := S)
  end.

Ltac set_rules_to x :=
  match goal with
  | |- WF (hd_red_Mod _ ?R) => set (x := R)
  | |- WF (hd_red_mod _ ?R) => set (x := R)
  | |- WF (red_mod _ ?R) => set (x := R)
  | |- WF (red ?R) => set (x := R)
  end.

Ltac set_mod_rules_to x :=
  match goal with
  | |- WF (hd_red_mod ?E _) => set (x := E)
  end.

Ltac set_Mod_to x :=
  match goal with
  | |- WF (hd_red_Mod ?S _) => set (x := S)
  | |- WF (hd_red_mod ?E _) => set (x := red E #)
  end.

Ltac hd_red_mod :=
  match goal with
  | |- WF (hd_red_Mod _ _) =>
    eapply WF_incl;
    [(apply hd_red_mod_of_hd_red_Mod || apply hd_red_mod_of_hd_red_Mod_int)
      | idtac]
  | |- WF (hd_red_mod _ _) => idtac
  end.

Ltac termination_trivial :=
  let R := fresh in set_rules_to R; norm R;
  (apply WF_hd_red_mod_empty || apply WF_red_mod_empty || apply WF_red_empty).

Ltac no_relative_rules :=
  match goal with
    |- WF (red_mod ?E _) =>
      norm E; eapply WF_incl; [apply red_mod_empty_incl_red | idtac]
    | _ => idtac
  end.

Ltac rules_preserv_vars :=
  (*rewrite rules_preserv_vars_dec; refl.*)
  (* computation is not faster than tactic in this case! *)
  match goal with
    | |- rules_preserv_vars ?R =>
      unfold rules_preserv_vars; let H := fresh in
      assert (H :
        lforall (fun a => incl (ATerm.vars (rhs a)) (ATerm.vars (lhs a))) R);
        [unfold incl; simpl; intuition
        | let H0 := fresh in do 2 intro; intro H0; apply (lforall_in H H0)]
  end.
