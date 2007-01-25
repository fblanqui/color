(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-01-22

rule renaming
*)

(* $Id: ARename.v,v 1.1 2007-01-25 14:52:01 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).
Notation vars := (@vars Sig).

Require Export ATrs.

Notation rule := (rule Sig).
Notation rules := (list rule).
Notation lhs := (@lhs Sig).

(***********************************************************************)
(** shift variable indices *)

Section shift.

Variable p : nat.

Require Export ASubstitution.

Definition shift_sub x := @Var Sig (x+p).
Definition shift := app shift_sub.

Lemma in_vars_shift_min : forall x t, In x (vars (shift t)) -> p <= x.

Proof.
intros x t. pattern t. apply term_ind_forall; clear t.
simpl. intros. destruct H. omega. contradiction.
intros. unfold shift in H0. rewrite app_fun in H0. rewrite vars_fun in H0.
deduce (in_vars_vec_elim H0). do 2 destruct H1.
deduce (Vin_map H1). do 2 destruct H3. subst x0.
deduce (Vforall_in H H3). auto.
Qed.

Lemma in_vars_shift_max : forall x t,
  In x (vars (shift t)) -> x <= maxvar t + p.

Proof.
intros x t. pattern t. apply term_ind_forall; clear t.
simpl. intros. destruct H. omega. contradiction.
intros. unfold shift in H0. rewrite app_fun in H0. rewrite vars_fun in H0.
deduce (in_vars_vec_elim H0). do 2 destruct H1.
deduce (Vin_map H1). do 2 destruct H3. subst x0.
deduce (Vforall_in H H3). deduce (H4 H2).
rewrite maxvar_fun. deduce (Vin_map_intro (@maxvar Sig) H3).
deduce (Vmax_in H6). omega.
Qed.
 
Definition shift_inv_sub x := @Var Sig (x-p).
Definition shift_inv := app shift_inv_sub.

Lemma shift_inv_shift : forall t, shift_inv (shift t) = t.

Proof.
apply term_ind_forall. simpl. unfold shift_inv_sub. intro. rewrite plus_minus.
refl. intros. unfold shift_inv, shift. repeat rewrite app_fun.
apply (f_equal (@Fun _ f)). rewrite Vmap_map. apply Vmap_eq_id. exact H.
Qed.

Lemma app_shift : forall s t, app s t = app (comp s shift_inv_sub) (shift t).

Proof.
intros. unfold shift. rewrite app_app. unfold app. apply term_int_eq.
intro. rewrite comp_assoc. unfold comp. simpl. rewrite plus_minus. refl.
Qed.

Definition shift_rule (rho : rule) :=
  let (l,r) := rho in mkRule (shift l) (shift r).

Definition shift_rule_inv (rho : rule) :=
  let (l,r) := rho in mkRule (shift_inv l) (shift_inv r).

End shift.

Implicit Arguments in_vars_shift_min [p x t].
Implicit Arguments in_vars_shift_max [p x t].

(***********************************************************************)
(** red included in shifted red *)

Section red_incl_shift_red.

Variables R R' : rules.

Variable hyp : forall a, In a R -> exists p, In (shift_rule p a) R'.

Implicit Arguments hyp [a].

Lemma red_incl_shift_red : red R << red R'.

Proof.
unfold inclusion. intros. redtac. deduce (hyp H). destruct H2.
rewrite (app_shift x0) in H0. subst x. rewrite (app_shift x0) in H1. subst y.
apply red_rule. auto.
Qed.

End red_incl_shift_red.

(***********************************************************************)
(** shifted red included in red *)

Section shift_red_incl_red.

Variables R R' : rules.

Variable hyp : forall a', In a' R' ->
  exists p, exists a, In a R /\ a' = shift_rule p a.

Implicit Arguments hyp [a'].

Lemma shift_red_incl_red : red R' << red R.

Proof.
unfold inclusion. intros. redtac. rename l into l'. rename r into r'.
subst x. subst y. deduce (hyp H). do 3 destruct H0. destruct x0 as [l r].
simpl in H1. inversion H1. subst l'. subst r'. unfold shift.
repeat rewrite app_app. apply red_rule. exact H0.
Qed.

End shift_red_incl_red.

(***********************************************************************)
(** terms with disjoint vars *)

Definition disjoint_vars t u :=
  forall x, In x (vars t) -> In x (vars u) -> t = u.

Lemma disjoint_vars_refl : forall t, disjoint_vars t t.

Proof.
unfold disjoint_vars. auto.
Qed.

Lemma disjoint_vars_com : forall t u, disjoint_vars t u -> disjoint_vars u t.

Proof.
unfold disjoint_vars. intros. apply sym_eq. apply (H x); assumption.
Qed.

Definition pw_disjoint_vars l :=
  forall t u, In t l -> In u l -> disjoint_vars t u.

Lemma pw_disjoint_vars_cons : forall t l, pw_disjoint_vars l ->
  (forall u, In u l -> disjoint_vars t u) -> pw_disjoint_vars (t :: l).

Proof.
intros. unfold pw_disjoint_vars. simpl. intros. destruct H1; destruct H2.
subst t0. subst u. apply disjoint_vars_refl.
subst t0. auto.
subst u. apply disjoint_vars_com. apply H0. exact H1.
apply H; assumption.
Qed.

(***********************************************************************)
(** shift terms *)

Fixpoint shift_terms (p : nat) (l : list term) {struct l} : list term :=
  match l with
    | nil => nil
    | cons t l' => shift p t :: shift_terms (maxvar t + p + 1) l'
  end.

Lemma in_vars_shift_terms : forall t l p, In t (shift_terms p l) ->
  exists u, exists q, In u l /\ t = shift q u /\ p <= q.

Proof.
induction l; simpl; intros. contradiction. destruct H.
exists a. exists p. auto.
deduce (IHl _ H). do 3 destruct H0. destruct H1. subst t. exists x. exists x0.
intuition.
Qed.

Implicit Arguments in_vars_shift_terms [t l p].

Lemma in_vars_shift_terms_min : forall p t l x,
  In t (shift_terms p l) -> In x (vars t) -> p <= x.

Proof.
intros. deduce (in_vars_shift_terms H). do 3 destruct H1. destruct H2. subst t.
deduce (in_vars_shift_min H0). omega.
Qed.

Implicit Arguments in_vars_shift_terms_min [p t l x].

Lemma shift_terms_correct : forall l p, pw_disjoint_vars (shift_terms p l).

Proof.
induction l. unfold pw_disjoint_vars. intros. contradiction.
intro. simpl. apply pw_disjoint_vars_cons. apply IHl.
unfold disjoint_vars. intros. deduce (in_vars_shift_max H0).
deduce (in_vars_shift_terms_min H H1). absurd (x <= maxvar a + p); omega.
Qed.

(***********************************************************************)
(** shift rules *)

Fixpoint shift_rules (p : nat) (R : rules) {struct R} : rules :=
  match R with
    | nil => nil
    | cons a R' => shift_rule p a :: shift_rules (maxvar(lhs a)+p+1) R'
  end.

Lemma shift_rules_lhs : forall R p,
  map lhs (shift_rules p R) = shift_terms p (map lhs R).

Proof.
induction R; simpl; intros. refl. destruct a. simpl.
apply (f_equal (cons (shift p lhs))). apply IHR.
Qed.

End S.
