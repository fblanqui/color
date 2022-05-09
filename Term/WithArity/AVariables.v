(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22

set of variables occuring in a term
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil ASubstitution FSetUtil NatUtil
     BoolUtil EqUtil ATrs ListUtil VecUtil.
From Coq Require Import OrderedTypeEx.
From Coq Require FSetAVL.

(***********************************************************************)
(** sets of variables *)

Module XSet := FSetAVL.Make Nat_as_OT.
Module Export VarSetUtil := FSetUtil.Make XSet.

Lemma eqb_beq_nat x y : eqb x y = beq_nat x y.

Proof.
  eq_dec x y. rewrite <- beq_nat_ok in e. rewrite e. refl.
  rewrite <- beq_nat_ok in n. ded (not_true_is_false _ n). rewrite H. refl.
Qed.

#[global] Hint Rewrite eqb_beq_nat : mem.
#[global] Hint Rewrite beq_nat_ok : mem.
#[global] Hint Rewrite (beq_refl beq_nat_ok) : mem.

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
      let fix vars_vec n (ts : terms n) :=
        match ts with
          | Vnil => empty
          | Vcons u ts => union (vars u) (vars_vec _ ts)
        end
        in vars_vec _ ts
  end.

Definition vars_vec :=
  fix vars_vec n (ts : terms n) :=
  match ts with
    | Vnil => empty
    | Vcons u ts => union (vars u) (vars_vec _ ts)
  end.

Lemma vars_fun : forall f ts, vars (Fun f ts) = vars_vec ts.

Proof. refl. Qed.

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
intro. simpl. mem. tauto.
intros f us H. rewrite ATerm.vars_fun, vars_fun. hyp.
simpl. mem. easy.
intros. simpl. mem. split_all. destruct (in_app_or H1).
rewrite (H H4). refl. rewrite (H0 H4). bool. refl.
case (orb_true_elim H1); intro e.
ded (H3 e). apply in_appl. hyp. ded (H2 e). apply in_appr. hyp.
Qed.

Lemma mem_vars_vec : forall x n (ts : terms n),
  mem x (vars_vec ts) = true -> exists t, Vin t ts /\ mem x (vars t) = true.

Proof.
induction ts; simpl; mem; split_all. discr.
destruct (orb_true_elim H). exists h. auto.
destruct (IHts e). exists x0. tauto.
Qed.

Arguments mem_vars_vec [x n ts] _.

Local Open Scope nat_scope.

Lemma mem_vars_size_sub_ge : forall s x u,
  mem x (vars u) = true -> size (sub s u) >= size (s x). 

Proof.
intros s x u. pattern u. apply term_ind with (Q := fun n (ts : terms n) =>
  mem x (vars_vec ts) = true -> size_terms (Vmap (sub s) ts) >= size (s x));
  clear u.
intro. simpl. mem. intro. subst x0. lia.
intros f v. rewrite vars_fun, sub_fun, size_fun. intros.
ded (H H0). lia. simpl. mem. intros. discr.
intros until v. simpl. mem. intros. destruct (orb_true_elim H1).
ded (H e). lia. ded (H0 e). lia.
Qed.

Arguments mem_vars_size_sub_ge _ [x u] _.

Lemma mem_vars_size_sub_gt : forall s x u,
  mem x (vars u) = true -> u <> Var x -> size (sub s u) > size (s x).

Proof.
intros. destruct u.
simpl in H. autorewrite with mem in H. subst n. cong.
clear H0. rewrite sub_fun, size_fun. rewrite vars_fun in H.
destruct (mem_vars_vec H). destruct H0. ded (Vin_elim H0). decomp H2.
rewrite H3, Vmap_cast, size_terms_cast, Vmap_app, size_terms_app. simpl.
ded (mem_vars_size_sub_ge s H1). lia.
Qed.

Arguments mem_vars_size_sub_gt _ [x u] _ _.

Lemma wf_term_var : forall s x u,
  s x = sub s u -> mem x (vars u) = true -> u = Var x.

Proof.
intros. ded (mem_vars_size_sub_gt s H0). rewrite H in H1.
case (eq_term_dec u (Var x)). auto. intro. ded (H1 n). lia.
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
simpl. intros. exists x0. mem. tauto.
(* Fun *)
intros f ts IH. rewrite sub_fun, !vars_fun. intro.
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
intros f ts IH. rewrite sub_fun, !vars_fun. hyp.
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
intros f ts IH. rewrite sub_fun, !vars_fun. hyp.
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
intros f ts IH. rewrite sub_fun, !vars_fun. hyp.
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
intro. simpl. unfold single. case_beq_nat x x0. 
autorewrite with mem Equal. refl.
simpl. mem. rewrite (beq_com beq_nat_ok), H. refl.
(* Fun *)
intros. rewrite sub_fun.
case_eq (mem x (vars (Fun f v0))); rewrite !vars_fun; intro;
  rewrite H0 in H; exact H.
(* Vnil *)
refl.
(* Vcons *)
intros u n us. simpl. mem. intros. rewrite H, H0.
case_eq (mem x (vars u)); intro H1; simpl.
revert H1. case_eq (mem x (vars_vec us)); intro H2.
trans (union (union (vars v) (remove x (vars u)))
  (union (vars v) (remove x (vars_vec us)))). refl.
trans (union (vars v) (union (remove x (vars u))
  (remove x (vars_vec us)))). apply union_idem_3.
apply union_m. refl. sym. apply remove_union.
trans (union (union (vars v) (remove x (vars u))) (vars_vec us)).
apply union_m; refl.
trans (union (vars v) (union (remove x (vars u)) (vars_vec us))).
autorewrite with Equal. refl. apply union_m. refl.
trans (union (remove x (vars u)) (remove x (vars_vec us))).
apply union_m. refl. sym. apply remove_equal. apply mem_4. hyp.
sym. apply remove_union.
revert H1. case_eq (mem x (vars_vec us)); intros H2 H1.
trans (union (vars u) (union (vars v) (remove x (vars_vec us)))).
apply union_m; refl.
trans (union (vars v) (union (vars u) (remove x (vars_vec us)))).
apply union_sym_2. apply union_m. refl.
trans (union (remove x (vars u)) (remove x (vars_vec us))).
apply union_m. sym. apply remove_equal. apply mem_4. hyp.
refl. sym. apply remove_union.
apply union_m; refl.
Qed.

Lemma vars_singles : forall x v us,
  vars_list (map (sub (single x v)) us) [=]
  if mem x (vars_list us) then union (vars v) (remove x (vars_list us))
    else vars_list us.

Proof.
induction us; simpl; intros. refl. mem.
trans (union
  (if mem x (vars a) then union (vars v) (remove x (vars a)) else vars a)
  (if mem x (vars_list us)
    then union (vars v) (remove x (vars_list us)) else vars_list us)).
apply union_m. apply vars_single. exact IHus.
case_eq (mem x (vars a)); case_eq (mem x (vars_list us)); intros; bool.
trans
  (union (vars v) (union (remove x (vars a)) (remove x (vars_list us)))).
apply union_idem_3. apply union_m. refl. sym. apply remove_union.
trans (union (vars v) (union (remove x (vars a)) (vars_list us))).
apply union_assoc. apply union_m. refl.
trans (union (remove x (vars a)) (remove x (vars_list us))).
apply union_m. refl. sym. apply remove_equal. apply mem_4. hyp.
sym. apply remove_union.
trans (union (vars v) (union (vars a) (remove x (vars_list us)))).
apply union_sym_2. apply union_m. refl.
trans (union (remove x (vars a)) (remove x (vars_list us))).
apply union_m. sym. apply remove_equal. apply mem_4. hyp. refl.
sym. apply remove_union. refl.
Qed.

(***********************************************************************)
(* preservation of variables under reduction *)

Notation rule := (rule Sig). Notation rules := (rules Sig).

Definition brule_preserve_vars (a : rule) :=
  subset (vars (rhs a)) (vars (lhs a)).

Definition brules_preserve_vars := forallb brule_preserve_vars.

Lemma vars_equiv : forall x (t : term),
  List.In x (ATerm.vars t) <-> In x (vars t).

Proof.
intros x t0. pattern t0. apply term_ind with (Q := fun n (ts : terms n) =>
  List.In x (ATerm.vars_vec ts) <-> In x (vars_vec ts)).
intro. simpl. set_iff. tauto.
intros. rewrite ATerm.vars_fun, vars_fun. hyp.
simpl. set_iff. refl.
intros. simpl. set_iff. rewrite in_app. tauto.
Qed.

Lemma brule_preserve_vars_ok' : forall l r,
  brule_preserve_vars (mkRule l r) = true
  <-> incl (ATerm.vars r) (ATerm.vars l).

Proof.
unfold brule_preserve_vars. intros l r. rewrite subset_Subset.
split; intros h x; simpl. rewrite !vars_equiv. intuition.
rewrite <- !vars_equiv. intuition.
Qed.

Lemma brule_preserve_vars_ok : forall a : rule,
  brule_preserve_vars a = true <->
  incl (ATerm.vars (rhs a)) (ATerm.vars (lhs a)).

Proof. intro. destruct a. rewrite brule_preserve_vars_ok'. tauto. Qed.

Lemma brules_preserve_vars_ok : forall R : rules,
  brules_preserve_vars R = true <-> rules_preserve_vars R.

Proof.
intro. unfold brules_preserve_vars, rules_preserve_vars.
rewrite forallb_forall. split_all.
rewrite <- brule_preserve_vars_ok'. auto.
rewrite brule_preserve_vars_ok. destruct x. auto.
Qed.

End S.

Arguments wf_term_var [Sig s x u] _ _.
Arguments mem_vars_vec [Sig x n ts] _.
Arguments vars_subs_elim [Sig s x v] _.

Ltac rules_preserve_vars := rewrite <- brules_preserve_vars_ok;
  (check_eq || fail 10 "some rule does not preserve variables").
