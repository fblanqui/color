(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22

set of variables occuring in a term
*)

(* $Id: AVariables.v,v 1.3 2008-05-29 15:04:34 blanqui Exp $ *)

Set Implicit Arguments.

Require Export ASubstitution.

(***********************************************************************)
(** sets of variables *)

Require Export FSetUtil.
Require Import OrderedTypeEx.

Module VarSetUtil := FSetUtil.Make (Nat_as_OT). Export VarSetUtil.

Require Export NatUtil.

Lemma eqb_beq_nat : forall x y, ME.eqb x y = beq_nat x y.

Proof.
intros. unfold ME.eqb. case (ME.eq_dec x y); intro.
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
      let fix vars_terms n (ts : terms n) {struct ts} :=
        match ts with
          | Vnil => empty
          | Vcons u _ ts => union (vars u) (vars_terms _ ts)
        end
        in vars_terms _ ts
  end.

Definition vars_terms :=
  fix vars_terms n (ts : terms n) {struct ts} :=
  match ts with
    | Vnil => empty
    | Vcons u _ ts => union (vars u) (vars_terms _ ts)
  end.

Lemma vars_fun : forall f ts, vars (Fun f ts) = vars_terms ts.

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
  List.In x (ATerm.vars_vec us) <-> mem x (vars_terms us) = true); clear u.
intro. simpl. mem. intuition.
intros f us H. rewrite ATerm.vars_fun. rewrite vars_fun. hyp.
simpl. mem. intuition.
intros. simpl. mem. intuition. destruct (in_app_or H0).
ded (H1 H4). rewrite H5. refl. ded (H H4). rewrite H5. bool.
refl. case (orb_true_elim H0); intro.
ded (H2 e). apply in_appl. hyp. ded (H3 e). apply in_appr. hyp.
Qed.

Lemma mem_vars_terms : forall x n (ts : terms n),
  mem x (vars_terms ts) = true -> exists t, Vin t ts /\ mem x (vars t) = true.

Proof.
induction ts; simpl; mem; intuition. discriminate.
destruct (orb_true_elim H). exists a. auto.
destruct (IHts e). exists x0. intuition.
Qed.

Implicit Arguments mem_vars_terms [x n ts].

Open Scope nat_scope.

Lemma mem_vars_size_app_ge : forall s x u,
  mem x (vars u) = true -> size (app s u) >= size (s x). 

Proof.
intros s x u. pattern u. apply term_ind with (Q := fun n (ts : terms n) =>
  mem x (vars_terms ts) = true -> size_terms (Vmap (app s) ts) >= size (s x));
  clear u.
intro. simpl. mem. intro. subst x0. omega.
intros f v. rewrite vars_fun. rewrite app_fun. rewrite size_fun. intros.
ded (H H0). omega. simpl. mem. intros. discriminate.
intros until v. simpl. mem. intros. destruct (orb_true_elim H1).
ded (H e). omega. ded (H0 e). omega.
Qed.

Implicit Arguments mem_vars_size_app_ge [x u].

Lemma mem_vars_size_app_gt : forall s x u,
  mem x (vars u) = true -> u <> Var x -> size (app s u) > size (s x).

Proof.
intros. destruct u.
simpl in H. autorewrite with mem in H. subst n. irrefl.
clear H0. rewrite app_fun. rewrite size_fun. rewrite vars_fun in H.
destruct (mem_vars_terms H). destruct H0. ded (Vin_elim H0). decomp H2.
rewrite H3. rewrite Vmap_cast. rewrite size_terms_Vcast. rewrite Vmap_app.
rewrite size_terms_Vapp. simpl. ded (mem_vars_size_app_ge s H1). omega.
Qed.

Implicit Arguments mem_vars_size_app_gt [x u].

Lemma term_wf : forall s x u,
  s x = app s u -> mem x (vars u) = true -> u = Var x.

Proof.
intros. ded (mem_vars_size_app_gt s H0). rewrite H in H1.
case (eq_term_dec u (Var x)). auto. intro. ded (H1 n).
absurd_hyp H2. omega. hyp.
Qed.

(***********************************************************************)
(* vars of a term on which a substitution is applied *)

Lemma vars_subs : forall x v u,
  vars (app (single x v) u) [=]
  if mem x (vars u) then union (vars v) (remove x (vars u)) else vars u.

Proof.
intros x v. apply term_ind with (Q := fun n (ts : terms n) =>
  vars_terms (Vmap (app (single x v)) ts) [=]
  if mem x (vars_terms ts) then union (vars v) (remove x (vars_terms ts))
    else vars_terms ts).
(* Var *)
intro. simpl. unfold single. case_nat_eq x x0. autorewrite with mem Equal.
transitivity (union (vars v) empty). symmetry. apply union_empty_right.
apply union_m. refl. symmetry. apply remove_singleton.
simpl. mem. rewrite (beq_com beq_nat_ok). rewrite H. refl.
(* Fun *)
intros. rewrite app_fun.
coq_case_eq (mem x (vars (Fun f v0))); repeat rewrite vars_fun; intro;
  rewrite H0 in H; exact H.
(* Vnil *)
refl.
(* Vcons *)
intros u n us. simpl. mem. (*FIXME: rewrite H. rewrite H0.*)
case_eq (mem x (vars u)); simpl. gen H1. case_eq (mem x (vars_terms us)).
transitivity (union (union (vars v) (remove x (vars u)))
  (union (vars v) (remove x (vars_terms us)))). apply union_m; hyp.
transitivity (union (vars v) (union (remove x (vars u))
  (remove x (vars_terms us)))). apply union_idem_3.
apply union_m. refl. symmetry. apply remove_union.
transitivity (union (union (vars v) (remove x (vars u))) (vars_terms us)).
apply union_m; hyp.
transitivity (union (vars v) (union (remove x (vars u)) (vars_terms us))).
apply union_assoc. apply union_m. refl.
transitivity (union (remove x (vars u)) (remove x (vars_terms us))).
apply union_m. refl. symmetry. apply remove_equal. apply mem_4. hyp.
symmetry. apply remove_union.
gen H1. case_eq (mem x (vars_terms us)).
transitivity (union (vars u) (union (vars v) (remove x (vars_terms us)))).
apply union_m; hyp.
transitivity (union (vars v) (union (vars u) (remove x (vars_terms us)))).
apply union_sym_2. apply union_m. refl.
transitivity (union (remove x (vars u)) (remove x (vars_terms us))).
apply union_m. symmetry. apply remove_equal. apply mem_4. hyp.
refl. symmetry. apply remove_union.
apply union_m; hyp.
Qed.

Lemma vars_subs_list : forall x v us,
  vars_list (map (app (single x v)) us) [=]
  if mem x (vars_list us) then union (vars v) (remove x (vars_list us))
    else vars_list us.

Proof.
induction us; simpl; intros. refl. mem.
transitivity (union (if mem x (vars a) then union (vars v) (remove x (vars a)) else vars a) (if mem x (vars_list us)
          then union (vars v) (remove x (vars_list us))
          else vars_list us)). apply union_m. apply vars_subs. exact IHus.
case_eq (mem x (vars a)); case_eq (mem x (vars_list us)); intros; bool.
transitivity (union (vars v) (union (remove x (vars a)) (remove x (vars_list us)))). apply union_idem_3. apply union_m. refl. symmetry. apply remove_union.
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

End S.

Implicit Arguments term_wf [Sig s x u].