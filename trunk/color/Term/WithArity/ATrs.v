(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Adam Koprowski and Hans Zantema, 2007-03-20

rewriting
*)

(* $Id: ATrs.v,v 1.19 2007-04-20 13:56:36 koper Exp $ *)

Set Implicit Arguments.

Require Export ARelation.

Section basic_definitions.

Variable Sig : Signature.

Notation term := (term Sig).
Notation terms := (vector term).

(***********************************************************************)
(** rule *)

Record rule : Set := mkRule {
  lhs : term;
  rhs : term
}.

Lemma eq_rule_dec : forall a b : rule, {a=b}+{~a=b}.

Proof.
decide equality; apply eq_term_dec.
Qed.

Notation rules := (list rule).

(***********************************************************************)
(** rewrite steps *)

Variable R : rules.

Definition red (t1 t2 : term) :=
  exists l, exists r, exists c, exists s,
  In (mkRule l r) R /\ t1 = fill c (app s l) /\ t2 = fill c (app s r).

Definition hd_red (t1 t2 : term) :=
  exists l, exists r, exists s,
  In (mkRule l r) R /\ t1 = app s l /\ t2 = app s r.

Definition int_red (t1 t2 : term) :=
  exists l, exists r, exists c, exists s, c <> Hole
  /\ In (mkRule l r) R /\ t1 = fill c (app s l) /\ t2 = fill c (app s r).

End basic_definitions.

(***********************************************************************)
(** tactics *)

Ltac redtac := repeat
  match goal with
    | H : red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in
      (unfold red in H; destruct H as [l]; destruct H as [r]; destruct H as [c];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (red _) _ _ |- _ =>
      unfold transp in H; redtac
    | H : hd_red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in
      let s := fresh "s" in let h1 := fresh in
      (unfold hd_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [s]; destruct H as [H h1]; destruct h1)
    | H : transp (hd_red _) _ _ |- _ =>
      unfold transp in H; redtac
    | H : int_red ?R ?t ?u |- _ =>
      let l := fresh "l" in let r := fresh "r" in let c := fresh "c" in
      let s := fresh "s" in let h1 := fresh in let h2 := fresh in
      (unfold int_red in H; destruct H as [l]; destruct H as [r];
      destruct H as [c]; destruct H as [s]; destruct H as [H h1];
      destruct h1 as [h1 h2]; destruct h2)
    | H : transp (int_red _) _ _ |- _ =>
      unfold transp in H; redtac
  end.

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
  red R (fill c (app s l)) (fill c (app s r)).

Proof.
intros. unfold red. exists l. exists r. exists c. exists s. auto.
Qed.

Lemma red_empty : forall t u : term, (red empty_trs #) t u -> t = u.

Proof.
intros. induction H. redtac. contradiction. refl. congruence.
Qed.

Lemma red_rule_top : forall l r s, In (mkRule l r) R ->
  red R (app s l) (app s r).

Proof.
intros. unfold red. exists l. exists r. exists (@Hole Sig). exists s. auto.
Qed.

Lemma hd_red_rule : forall l r s, In (mkRule l r) R ->
  hd_red R (app s l) (app s r).

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
subst u'. exists (fill (AContext.comp d c) (app s r)). split.
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
Funeqtac. exists i. exists v0. exists (fill c (app s l)). exists j. exists v1.
exists e. exists (fill c (app s r)). split. assumption. split. assumption.
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
unfold inclusion. intros. redtac. subst x. subst y. apply red_rule_top. exact H.
Qed.

Lemma WF_red_empty : WF (red empty_trs).

Proof.
  intro x. apply SN_intro. intros y Exy. redtac. contradiction.
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
apply incl_tran with (cvars c ++ vars (app s r)). apply vars_fill_elim.
apply incl_tran with (cvars c ++ vars (app s l)). apply appl_incl.
apply incl_vars_app. apply hyp. exact H.
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

(***********************************************************************)
(** rewriting vectors of terms *)

Section vector.

Require Export VecOrd.

Variable R : rules.

Definition terms_gt := Vgt_prod (red R).

Lemma Vgt_prod_fun : forall f ts ts',
  Vgt_prod (red R) ts ts' -> int_red R (Fun f ts) (Fun f ts').

Proof.
intros. deduce (Vgt_prod_gt H). do 8 destruct H0. destruct H1. redtac.
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
deduce (in_app_or H). destruct H0.
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

Lemma hd_red_union : hd_red (R ++ R') << hd_red R U hd_red R'.

Proof.
unfold inclusion. intros. redtac. subst x. subst y.
deduce (in_app_or H). destruct H0.
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
(** rewriting modulo *)

Section rewriting_modulo.

Variable E R : rules.

Definition red_mod := red E # @ red R.

Definition hd_red_mod := red E # @ hd_red R.

Lemma hd_red_mod_incl_red_mod : hd_red_mod << red_mod.

Proof.
unfold hd_red_mod, red_mod. comp. apply hd_red_incl_red.
Qed.

End rewriting_modulo.

Section rewriting_modulo_results.

Variables R R' E E' : rules.

Lemma red_mod_empty_incl_red : red_mod empty_trs R << red R.

Proof.
intros s t Rst. destruct Rst as [s' [ss' Rst]].
rewrite (red_empty ss'). assumption.
Qed.

Lemma hd_red_mod_empty_incl_hd_red : hd_red_mod empty_trs R << hd_red R.

Proof.
unfold inclusion. intros. do 2 destruct H. deduce (red_empty H). subst x0.
exact H0.
Qed.

Lemma red_mod_sub : incl R R' -> incl E E' -> red_mod E R << red_mod E' R'.

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
  apply hd_red_mod_incl_red_mod.
  apply WF_red_mod_empty.
Qed.

End rewriting_modulo_results.

(***********************************************************************)
(** termination as special case of relative termination *)

Section termination_as_relative_term.

Variable R R' : rules.

Lemma red_incl_red_mod : red R << red_mod empty_trs R.

Proof.
intros s t Rst. exists s. split. constructor 2. assumption.
Qed.

Lemma hd_red_incl_hd_red_mod : hd_red R << hd_red_mod empty_trs R.

Proof.
intros s t Rst. exists s. split. constructor 2. assumption.
Qed.

End termination_as_relative_term.

(***********************************************************************)
(** union of rewrite rules modulo *)

Section union_modulo.

Variables E E' R R' : rules.

Lemma red_mod_union : red_mod E (R ++ R') << red_mod E R U red_mod E R'.

Proof.
unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
deduce (in_app_or H0). destruct H1.
left. exists (fill c (app s l)); split. assumption. apply red_rule. exact H1.
right. exists (fill c (app s l)); split. assumption. apply red_rule. exact H1.
Qed.

Lemma hd_red_mod_union :
  hd_red_mod E (R ++ R') << hd_red_mod E R U hd_red_mod E R'.

Proof.
unfold inclusion. intros. do 2 destruct H. redtac. subst x0. subst y.
deduce (in_app_or H0). destruct H1.
left. exists (app s l); split. assumption. apply hd_red_rule. exact H1.
right. exists (app s l); split. assumption. apply hd_red_rule. exact H1.
Qed.

End union_modulo.

(***********************************************************************)
(** declarations of implicit arguments *)

End S.

Implicit Arguments int_red_fun [Sig R f ts v].

(***********************************************************************)
(** declarations of tactics *)

Ltac solve_termination R lemma :=
  match type of R with
  | list ?rule => first 
    [ solve [replace R with (nil (A:=rule)); [apply lemma | vm_compute; trivial]]
    | fail "The termination problem is non-trivial"]
  | _ => fail "Unrecognized TRS type"
  end.

Ltac termination_trivial := 
  match goal with
  | |- WF (red ?R) => solve_termination R WF_red_empty
  | |- WF (red_mod ?E ?R) => solve_termination R WF_red_mod_empty
  | |- WF (hd_red_mod ?E ?R) => solve_termination R WF_hd_red_mod_empty
  | _ => fail "The goal does not seem to be a termination problem"
  end.
