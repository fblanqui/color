(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09
- Frederic Blanqui, 2005-02-17

one-hole contexts
*)

(* $Id: AContext.v,v 1.9 2008-05-14 12:26:54 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).
Notation "'args' f" := (terms (arity f)) (at level 70).

(***********************************************************************)
(** contexts and replacement of the hole *)

Inductive context : Set :=
  | Hole : context
  | Cont : forall f : Sig, forall i j : nat, i + S j = arity f ->
    terms i -> context -> terms j -> context.

Implicit Arguments Cont [f i j].

Fixpoint fill (c : context) (t : term) {struct c} : term :=
  match c with
    | Hole => t
    | Cont f i j H v1 c' v2 => Fun f (Vcast (Vapp v1 (Vcons (fill c' t) v2)) H)
  end.

(***********************************************************************)
(** properties of fill *)

Lemma var_eq_fill : forall x c t, Var x = fill c t -> c = Hole /\ t = Var x.

Proof.
intros. destruct c; simpl in H. auto. discriminate.
Qed.

Lemma fun_eq_fill : forall f ts c u, Fun f ts = fill c u ->
  c = Hole \/ exists i, exists j, exists H : i + S j = arity f,
    exists ti, exists d, exists tj, c = Cont H ti d tj.

Proof.
intros. destruct c. auto. right.
simpl in H. injection H. intros. subst f0.
exists i. exists j. exists e. exists v. exists c. exists v0.
refl.
Qed.

(***********************************************************************)
(** subterm ordering *)

Definition subterm_eq u t := exists C, t = fill C u.

Definition subterm u t := exists C, C <> Hole /\ t = fill C u.

Lemma subterm_eq_refl : forall t, subterm_eq t t.

Proof.
intro. exists Hole. refl.
Qed.

Lemma subterm_eq_var : forall u x, subterm_eq u (Var x) -> u = Var x.

Proof.
intros. unfold subterm_eq in H. destruct H as [C].
assert (C = Hole /\ u = Var x).
apply var_eq_fill. exact H. destruct H0. exact H1.
Qed.

Lemma subterm_fun_elim : forall u f (ts : args f),
  subterm u (Fun f ts) -> exists t, Vin t ts /\ subterm_eq u t.

Proof.
intros. unfold subterm in H. destruct H as [C]. destruct H.
destruct C. absurd (Hole = Hole); auto.
clear H. simpl in H0. Funeqtac. subst ts. exists (fill C u). split.
apply Vin_cast_intro. apply Vin_app_cons. unfold subterm_eq. exists C. refl.
Qed.

Lemma subterm_fun : forall f (ts : args f) u, Vin u ts -> subterm u (Fun f ts).

Proof.
intros. unfold subterm.
assert (exists n1, exists v1 : terms n1, exists n2, exists v2 : terms n2,
  exists H : n1 + S n2 = arity f, ts = Vcast (Vapp v1 (Vcons u v2)) H).
apply Vin_elim. assumption.
destruct H0 as [n1]. destruct H0 as [ts1].
destruct H0 as [n2]. destruct H0 as [ts2]. destruct H0 as [H1].
exists (Cont H1 ts1 Hole ts2). split. discriminate.
rewrite H0. refl.
Qed.

Lemma subterm_strict : forall u t, subterm u t -> subterm_eq u t.

Proof.
unfold subterm_eq, subterm. intros. destruct H. destruct H. exists x. assumption.
Qed.

Lemma subterm_noteq : forall u t, subterm_eq u t -> u <> t -> subterm u t.

Proof.
unfold subterm_eq, subterm. intros. destruct H as [C]. destruct C.
subst t. simpl in H0. absurd (u<>u); auto.
exists (Cont e v C v0). split. discriminate. subst t. refl.
Qed.

(***********************************************************************)
(** context composition *)

Fixpoint comp (C : context) : context -> context :=
  match C with
    | Hole => fun E => E
    | Cont _ _ _ H ts1 D ts2 => fun E => Cont H ts1 (comp D E) ts2
  end.

Lemma fill_comp : forall C D u, fill C (fill D u) = fill (comp C D) u.

Proof.
induction C; simpl; intros. refl.
rewrite (IHC D u). refl.
Qed.

(***********************************************************************)
(** transitivity of the subterm ordering *)

Lemma subterm_trans_eq1 : forall t u v,
  subterm_eq t u -> subterm u v -> subterm t v.

Proof.
unfold subterm, subterm_eq. intros. destruct H. destruct H0. destruct H0.
subst u. subst v. rewrite (fill_comp x0 x t). exists (comp x0 x).
split. destruct x0. absurd (Hole = Hole); auto. simpl. discriminate. refl.
Qed.

Lemma subterm_trans_eq2 : forall t u v,
  subterm t u -> subterm_eq u v -> subterm t v.

Proof.
unfold subterm, subterm_eq. intros. destruct H. destruct H. destruct H0.
subst u. subst v. rewrite (fill_comp x0 x t). exists (comp x0 x).
split. destruct x. absurd (Hole = Hole); auto.
destruct x0; simpl; discriminate. refl.
Qed.

Lemma subterm_trans : forall t u v,
  subterm t u -> subterm u v -> subterm t v.

Proof.
unfold subterm. intros. do 2 destruct H. do 2 destruct H0.
subst u. subst v. rewrite (fill_comp x0 x t). exists (comp x0 x).
split. destruct x. absurd (Hole = Hole); auto.
destruct x0; simpl; discriminate. refl.
Qed.

(***********************************************************************)
(** subterms and variables *)

Lemma subterm_eq_vars : forall u t x,
  subterm_eq u t -> In x (vars u) -> In x (vars t).

Proof.
unfold subterm_eq. intros. destruct H as [C]. subst t. elim C; clear C.
simpl. assumption. intros. simpl fill. rewrite vars_fun.
rewrite vars_vec_cast. rewrite vars_vec_app. rewrite vars_vec_cons.
apply in_appr. apply in_appl. assumption.
Qed.

Lemma in_vars_subterm_eq : forall x t, In x (vars t) -> subterm_eq (Var x) t.

Proof.
intros x t. pattern t. apply term_ind_forall; clear t; simpl; intros.
intuition. rewrite H0. apply subterm_eq_refl.
generalize (in_vars_vec_elim H0). intro.
destruct H1 as [t]. destruct H1. generalize (Vforall_in H H1). intro.
generalize (H3 H2). intro. apply subterm_strict. eapply subterm_trans_eq1.
apply H4.
apply subterm_fun. assumption.
Qed.

Lemma in_vars_fun : forall x f ts,
  In x (vars (Fun f ts)) -> exists t, Vin t ts /\ subterm_eq (Var x) t.

Proof.
intros. apply subterm_fun_elim. ded (in_vars_subterm_eq _ _ H).
apply subterm_noteq. assumption. discriminate.
Qed.

(***********************************************************************)
(** subterm-based induction principle *)

Lemma forall_subterm_eq : forall (P : term -> Prop) t,
  (forall u, subterm_eq u t -> P u) -> P t.

Proof.
intros. apply H. unfold subterm. exists Hole. auto.
Qed.

Lemma subterm_ind_sub : forall (P : term -> Prop)
  (IH : forall t, (forall u, subterm u t -> P u) -> P t),
  forall t u, subterm_eq u t -> P u.

Proof.
intros P IH. set (P' := fun t => forall u, subterm_eq u t -> P u).
change (forall t, P' t). apply term_ind_forall.
(* var *)
unfold P'. intros. assert (u = Var v). apply subterm_eq_var. assumption.
subst u. apply IH. unfold subterm. intros. destruct H0. destruct H0.
destruct x. absurd (Hole = Hole); auto. discriminate.
(* fun *)
intros. unfold P'. intros. apply IH. intros.
assert (subterm u0 (Fun f v)). eapply subterm_trans_eq2. apply H1. assumption.
assert (exists t, Vin t v /\ subterm_eq u0 t). apply subterm_fun_elim.
assumption.
destruct H3. destruct H3.
assert (P' x). eapply Vforall_in with (n := arity f). apply H. assumption.
apply H5. assumption.
Qed.

Lemma subterm_ind : forall (P : term -> Prop)
  (IH : forall t, (forall u, subterm u t -> P u) -> P t),
  forall t, P t.

Proof.
intros. apply forall_subterm_eq. apply subterm_ind_sub. assumption.
Qed.

(***********************************************************************)
(** variables of a context *)

Fixpoint cvars (c : context) : variables :=
  match c with
    | Hole => nil
    | Cont f i j H v1 c' v2 => vars_vec v1 ++ cvars c' ++ vars_vec v2
  end.

Lemma vars_fill_elim : forall t c, incl (vars (fill c t)) (cvars c ++ vars t).

Proof.
induction c. simpl. apply incl_refl. simpl fill. rewrite vars_fun. simpl.
unfold incl. intros. ded (in_vars_vec_elim H). do 2 destruct H0.
ded (Vin_cast_elim H0). ded (Vin_app H2). destruct H3.
repeat apply in_appl. apply (in_vars_vec_intro H1 H3).
simpl in H3. destruct H3. subst x. ded (IHc _ H1).
rewrite app_ass. apply in_appr. apply in_app_com. apply in_appl. exact H3.
apply in_appl. repeat apply in_appr. apply (in_vars_vec_intro H1 H3).
Qed.

Lemma vars_fill_intro : forall t c, incl (cvars c ++ vars t) (vars (fill c t)).

Proof.
induction c. simpl. apply incl_refl. simpl cvars. simpl fill. rewrite vars_fun.
rewrite vars_vec_cast. rewrite vars_vec_app. rewrite vars_vec_cons.
rewrite app_ass. apply appl_incl. apply app_com_incl. apply appr_incl. exact IHc.
Qed.

End S.

(***********************************************************************)
(** declarations of implicit arguments *)

Implicit Arguments Hole [Sig].
Implicit Arguments in_vars_subterm_eq [Sig x t].
Implicit Arguments in_vars_fun [Sig x f ts].
Implicit Arguments vars_fill_elim [Sig t c].
