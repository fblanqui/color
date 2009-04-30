(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22

set of variables occuring in a term
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import ASubstitution.
Require Import FSetUtil.
Require Import OrderedTypeEx.
Require Import NatUtil.
Require Import BoolUtil.
Require Import EqUtil.
Require Import ATrs.
Require Import ListUtil.
Require Import VecUtil.

(***********************************************************************)
(** sets of variables *)

Module VarSetUtil := FSetUtil.Make (Nat_as_OT).
Export VarSetUtil.

Lemma eqb_beq_nat : forall x y, eqb x y = beq_nat x y.

Proof.
intros. unfold eqb. case (eq_dec x y); intro.
change (x=y) in e. rewrite <- beq_nat_ok in e. rewrite e. refl.
change (x<>y) in n. rewrite <- beq_nat_ok in n.
ded (not_true_is_false _ n). rewrite H. refl.
Qed.

Hint Rewrite eqb_beq_nat : mem.
Hint Rewrite beq_nat_ok : mem.
Hint Rewrite (beq_refl beq_nat_ok) : mem.

(***********************************************************************)
(** variables in a term *)

Section S.

Variable Sig : Signature.

Notation term := (term Sig).
Notation terms := (vector term).

Fixpoint vars t :=
  match t with
    | Var x => singleton x
    | Fun f ts =>
      let fix vars_vec n (ts : terms n) {struct ts} :=
        match ts with
          | Vnil => empty
          | Vcons u _ ts => union (vars u) (vars_vec _ ts)
        end
        in vars_vec _ ts
  end.

Definition vars_vec :=
  fix vars_vec n (ts : terms n) {struct ts} :=
  match ts with
    | Vnil => empty
    | Vcons u _ ts => union (vars u) (vars_vec _ ts)
  end.

Lemma vars_fun : forall f ts, vars (Fun f ts) = vars_vec ts.

Proof.
refl.
Qed.

Fixpoint vars_list ts :=
  match ts with
    | nil => empty
    | t :: ts' => union (vars t) (vars_list ts')
  end.

Lemma in_vars_mem : forall x (u : term),
  List.In x (ATerm.vars u) <-> mem x (vars u) = true.

Proof.
intros. pattern u. apply term_ind with (Q := fun n (us : terms n) =>
  List.In x (ATerm.vars_vec us) <-> mem x (vars_vec us) = true); clear u.
intro. simpl. mem. intuition.
intros f us H. rewrite ATerm.vars_fun. rewrite vars_fun. hyp.
simpl. mem. intuition.
intros. simpl. mem. intuition. destruct (in_app_or H0).
ded (H1 H4). rewrite H5. refl. ded (H H4). rewrite H5. bool.
refl. case (orb_true_elim H0); intro.
ded (H2 e). apply in_appl. hyp. ded (H3 e). apply in_appr. hyp.
Qed.

Lemma mem_vars_vec : forall x n (ts : terms n),
  mem x (vars_vec ts) = true -> exists t, Vin t ts /\ mem x (vars t) = true.

Proof.
induction ts; simpl; mem; intuition. discriminate.
destruct (orb_true_elim H). exists a. auto.
destruct (IHts e). exists x0. intuition.
Qed.

Implicit Arguments mem_vars_vec [x n ts].

Local Open Scope nat_scope.

Lemma mem_vars_size_sub_ge : forall s x u,
  mem x (vars u) = true -> size (sub s u) >= size (s x). 

Proof.
intros s x u. pattern u. apply term_ind with (Q := fun n (ts : terms n) =>
  mem x (vars_vec ts) = true -> size_terms (Vmap (sub s) ts) >= size (s x));
  clear u.
intro. simpl. mem. intro. subst x0. omega.
intros f v. rewrite vars_fun. rewrite sub_fun. rewrite size_fun. intros.
ded (H H0). omega. simpl. mem. intros. discriminate.
intros until v. simpl. mem. intros. destruct (orb_true_elim H1).
ded (H e). omega. ded (H0 e). omega.
Qed.

Implicit Arguments mem_vars_size_sub_ge [x u].

Lemma mem_vars_size_sub_gt : forall s x u,
  mem x (vars u) = true -> u <> Var x -> size (sub s u) > size (s x).

Proof.
intros. destruct u.
simpl in H. autorewrite with mem in H. subst n. irrefl.
clear H0. rewrite sub_fun. rewrite size_fun. rewrite vars_fun in H.
destruct (mem_vars_vec H). destruct H0. ded (Vin_elim H0). decomp H2.
rewrite H3. rewrite Vmap_cast. rewrite size_terms_Vcast. rewrite Vmap_app.
rewrite size_terms_Vapp. simpl. ded (mem_vars_size_sub_ge s H1). omega.
Qed.

Implicit Arguments mem_vars_size_sub_gt [x u].

Lemma term_wf : forall s x u,
  s x = sub s u -> mem x (vars u) = true -> u = Var x.

Proof.
intros. ded (mem_vars_size_sub_gt s H0). rewrite H in H1.
case (eq_term_dec u (Var x)). auto. intro. ded (H1 n).
contradict H2; omega.
Qed.

(***********************************************************************)
(* vars of a term on which a substitution is applied *)

Lemma vars_subs_elim : forall s x (v : term), mem x (vars (sub s v)) = true ->
  exists y, mem y (vars v) = true /\ mem x (vars (s y)) = true.

Proof.
intros s x v. pattern v; apply term_ind with (Q := fun n (ts : terms n) =>
  mem x (vars_vec (Vmap (sub s) ts)) = true ->
  exists y, mem y (vars_vec ts) = true /\ mem x (vars (s y)) = true); clear v.
(* Var *)
simpl. intros. exists x0. mem. intuition.
(* Fun *)
intros f ts IH. rewrite sub_fun. repeat rewrite vars_fun. intro.
destruct (IH H). exists x0. hyp.
(* Vnil *)
simpl. mem. discr.
(* Vcons *)
simpl. intros u n us IH1 IH2. mem. intro. destruct (orb_true_elim H).
destruct (IH1 e). exists x0. mem. intuition.
destruct (IH2 e). exists x0. mem. intuition.
Qed.

Lemma vars_subs_intro : forall s x y, mem x (vars (s y)) = true ->
  forall v : term, mem y (vars v) = true -> mem x (vars (sub s v)) = true.

Proof.
intros s x y H v. pattern v; apply term_ind with (Q := fun n (ts : terms n) =>
  mem y (vars_vec ts) = true -> mem x (vars_vec (Vmap (sub s) ts)) = true);
  clear v.
(* Var *)
intro. simpl. mem. intro. subst. hyp.
(* Fun *)
intros f ts IH. rewrite sub_fun. repeat rewrite vars_fun. hyp.
(* Vnil *)
simpl. auto.
(* Vcons *)
simpl. intros u n us IH1 IH2. mem. intro. destruct (orb_true_elim H0).
rewrite (IH1 e). refl. rewrite (IH2 e). bool. refl.
Qed.

Lemma notin_vars_subs_elim : forall s x (v : term),
  mem x (vars (sub s v)) = false ->
  forall y, mem y (vars v) = true -> mem x (vars (s y)) = false.

Proof.
intros s x v. pattern v; apply term_ind with (Q := fun n (ts : terms n) =>
  mem x (vars_vec (Vmap (sub s) ts)) = false ->
  forall y, mem y (vars_vec ts) = true -> mem x (vars (s y)) = false); clear v.
(* Var *)
simpl. intros x0 H y. mem. intro. subst. hyp.
(* Fun *)
intros f ts IH. rewrite sub_fun. repeat rewrite vars_fun. hyp.
(* Vnil *)
simpl. intros H y. mem. discr.
(* Vcons *)
simpl. intros u n us IH1 IH2. mem. intros H y. mem. intro.
destruct (orb_false_elim H). destruct (orb_true_elim H0).
apply IH1; hyp. apply IH2; hyp.
Qed.

Lemma notin_vars_subs_intro : forall s x (v : term),
  (forall y, mem y (vars v) = true -> mem x (vars (s y)) = false) ->
  mem x (vars (sub s v)) = false.

Proof.
intros s x v. pattern v; apply term_ind with (Q := fun n (ts : terms n) =>
  (forall y, mem y (vars_vec ts) = true -> mem x (vars (s y)) = false) ->
  mem x (vars_vec (Vmap (sub s) ts)) = false); clear v.
(* Var *)
simpl. intros. apply H. mem. refl.
(* Fun *)
intros f ts IH. rewrite sub_fun. repeat rewrite vars_fun. hyp.
(* Vnil *)
simpl. mem. refl.
(* Vcons *)
simpl. intros u n us IH1 IH2 H. mem. apply orb_false_intro.
apply IH1. intros. apply H. mem. rewrite H0. refl.
apply IH2. intros. apply H. mem. rewrite H0. bool. refl.
Qed.

(***********************************************************************)
(* vars of a term on which a single substitution is applied *)

Lemma vars_single : forall x v u,
  vars (sub (single x v) u) [=]
  if mem x (vars u) then union (vars v) (remove x (vars u)) else vars u.

Proof.
intros x v. apply term_ind with (Q := fun n (ts : terms n) =>
  vars_vec (Vmap (sub (single x v)) ts) [=]
  if mem x (vars_vec ts) then union (vars v) (remove x (vars_vec ts))
    else vars_vec ts).
(* Var *)
intro. simpl. unfold single. case_nat_eq x x0. 
autorewrite with mem Equal. refl.
simpl. mem. rewrite (beq_com beq_nat_ok). rewrite H. refl.
(* Fun *)
intros. rewrite sub_fun.
coq_case_eq (mem x (vars (Fun f v0))); repeat rewrite vars_fun; intro;
  rewrite H0 in H; exact H.
(* Vnil *)
refl.
(* Vcons *)
intros u n us. simpl. mem. intros. rewrite H. rewrite H0.
case_eq (mem x (vars u)); simpl. gen H1. case_eq (mem x (vars_vec us)).
transitivity (union (union (vars v) (remove x (vars u)))
  (union (vars v) (remove x (vars_vec us)))). refl.
transitivity (union (vars v) (union (remove x (vars u))
  (remove x (vars_vec us)))). apply union_idem_3.
apply union_m. refl. symmetry. apply remove_union.
transitivity (union (union (vars v) (remove x (vars u))) (vars_vec us)).
apply union_m; refl.
transitivity (union (vars v) (union (remove x (vars u)) (vars_vec us))).
autorewrite with Equal. refl. apply union_m. refl.
transitivity (union (remove x (vars u)) (remove x (vars_vec us))).
apply union_m. refl. symmetry. apply remove_equal. apply mem_4. hyp.
symmetry. apply remove_union.
gen H1. case_eq (mem x (vars_vec us)).
transitivity (union (vars u) (union (vars v) (remove x (vars_vec us)))).
apply union_m; refl.
transitivity (union (vars v) (union (vars u) (remove x (vars_vec us)))).
apply union_sym_2. apply union_m. refl.
transitivity (union (remove x (vars u)) (remove x (vars_vec us))).
apply union_m. symmetry. apply remove_equal. apply mem_4. hyp.
refl. symmetry. apply remove_union.
apply union_m; refl.
Qed.

Lemma vars_singles : forall x v us,
  vars_list (map (sub (single x v)) us) [=]
  if mem x (vars_list us) then union (vars v) (remove x (vars_list us))
    else vars_list us.

Proof.
induction us; simpl; intros. refl. mem.
transitivity (union
  (if mem x (vars a) then union (vars v) (remove x (vars a)) else vars a)
  (if mem x (vars_list us)
    then union (vars v) (remove x (vars_list us)) else vars_list us)).
apply union_m. apply vars_single. exact IHus.
case_eq (mem x (vars a)); case_eq (mem x (vars_list us)); intros; bool.
transitivity
  (union (vars v) (union (remove x (vars a)) (remove x (vars_list us)))).
apply union_idem_3. apply union_m. refl. symmetry. apply remove_union.
transitivity (union (vars v) (union (remove x (vars a)) (vars_list us))).
apply union_assoc. apply union_m. refl.
transitivity (union (remove x (vars a)) (remove x (vars_list us))).
apply union_m. refl. symmetry. apply remove_equal. apply mem_4. hyp.
symmetry. apply remove_union.
transitivity (union (vars v) (union (vars a) (remove x (vars_list us)))).
apply union_sym_2. apply union_m. refl.
transitivity (union (remove x (vars a)) (remove x (vars_list us))).
apply union_m. symmetry. apply remove_equal. apply mem_4. hyp. refl.
symmetry. apply remove_union. refl.
Qed.

(***********************************************************************)
(* preservation of variables under reduction *)

Require Import ATrs.

Notation rule := (rule Sig). Notation rules := (rules Sig).

Definition rule_preserv_vars_bool (a : rule) :=
  subset (vars (rhs a)) (vars (lhs a)).

Definition rules_preserv_vars_bool := forallb rule_preserv_vars_bool.

Lemma vars_equiv : forall x (t : term),
  List.In x (ATerm.vars t) <-> In x (vars t).

Proof.
intros x t0. pattern t0. apply term_ind with (Q := fun n (ts : terms n) =>
  List.In x (ATerm.vars_vec ts) <-> In x (vars_vec ts)).
intro. simpl. set_iff. intuition.
intros. rewrite ATerm.vars_fun. rewrite vars_fun. hyp.
simpl. set_iff. intuition.
intros. simpl. set_iff. rewrite in_app. intuition.
Qed.

Lemma rule_preserv_vars_dec : forall l r : term,
  incl (ATerm.vars r) (ATerm.vars l) <->
  rule_preserv_vars_bool (mkRule l r) = true.

Proof.
unfold rule_preserv_vars_bool. intros. rewrite subset_Subset.
split; intros h x. simpl. repeat rewrite <- vars_equiv. intuition.
repeat rewrite vars_equiv. intuition.
Qed.

Lemma rule_preserv_vars_dec' : forall a : rule,
  rule_preserv_vars_bool a = true <->
  incl (ATerm.vars (rhs a)) (ATerm.vars (lhs a)).

Proof.
intro. destruct a. rewrite rule_preserv_vars_dec. tauto.
Qed.

Lemma rules_preserv_vars_dec : forall R : rules,
  rules_preserv_vars R <-> rules_preserv_vars_bool R = true.

Proof.
intro. unfold rules_preserv_vars_bool, rules_preserv_vars.
rewrite forallb_forall. intuition.
destruct x. rewrite <- rule_preserv_vars_dec. auto.
rewrite rule_preserv_vars_dec. auto.
Qed.

End S.

Implicit Arguments term_wf [Sig s x u].
Implicit Arguments mem_vars_vec [Sig x n ts].
Implicit Arguments vars_subs_elim [Sig s x v].
