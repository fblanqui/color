(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-12-05

one-hole contexts
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil.
From CoLoR Require Import ListUtil.
From CoLoR Require Export VTerm.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (list term).

(***********************************************************************)
(** contexts and replacement of the hole *)

  Inductive context : Type :=
  | Hole : context
  | Cont : forall f : Sig, terms -> context -> terms -> context.

  Fixpoint fill (c : context) (t : term) : term :=
    match c with
      | Hole => t
      | Cont f v1 c' v2 => Fun f (v1 ++ fill c' t :: v2)
    end.

  Lemma var_eq_fill : forall x c t, Var x = fill c t -> c = Hole /\ t = Var x.

  Proof. intros. destruct c; simpl in H. auto. discr. Qed.

(***********************************************************************)
(** context composition *)

  Fixpoint comp (C : context) : context -> context :=
    match C with
      | Hole => fun E => E
      | Cont f ts1 D ts2 => fun E => Cont f ts1 (comp D E) ts2
    end.

  Lemma fill_fill : forall C D u, fill C (fill D u) = fill (comp C D) u.

  Proof. induction C; simpl; intros. refl. rewrite (IHC D u). refl. Qed.

(***********************************************************************)
(** subterm ordering *)

  Definition subterm_eq u t := exists C, t = fill C u.

  Definition subterm u t := exists C, C <> Hole /\ t = fill C u.

  Lemma subterm_eq_var : forall u x, subterm_eq u (Var x) -> u = Var x.

  Proof.
    intros. unfold subterm_eq in H. destruct H as [C].
    assert (C = Hole /\ u = Var x).
    apply var_eq_fill. exact H. destruct H0. exact H1.
  Qed.

  Lemma subterm_trans_eq2 : forall t u v,
    subterm t u -> subterm_eq u v -> subterm t v.

  Proof.
    unfold subterm, subterm_eq. intros. destruct H. destruct H. destruct H0.
    subst u. subst v. rewrite (fill_fill x0 x t). exists (comp x0 x).
    split. destruct x. cong.
    destruct x0; simpl; discr. refl.
  Qed.

  Lemma subterm_fun_elim : forall u f ts,
    subterm u (Fun f ts) -> exists t, In t ts /\ subterm_eq u t.

  Proof.
    intros. destruct H as [C [CH fC]]. 
    destruct C. intuition.
    simpl in fC. injection fC. intros. subst ts.
    exists (fill C u). split. auto with datatypes.
    unfold subterm_eq. exists C. refl.
  Qed.

  Lemma subterm_immediate : forall f v a, In a v -> subterm a (Fun f v).

  Proof.
    intros. destruct (In_split a v) as [l1 [l2 dec]]. hyp.
    exists (Cont f l1 Hole l2). split. discr. simpl. congruence.
  Qed.

(***********************************************************************)
(** subterm-based induction principle *)

  Lemma subterm_eq_rect : forall (P : term -> Type) t,
    (forall u, subterm_eq u t -> P u) -> P t.

  Proof. intros. apply X. unfold subterm_eq. exists Hole. auto. Qed.

  Lemma subterm_sub_ind : forall (P : term -> Prop)
    (IH : forall t, (forall u, subterm u t -> P u) -> P t),
    forall t u, subterm_eq u t -> P u.

  Proof.
    intros P IH. set (P' := fun t => forall u, subterm_eq u t -> P u).
    change (forall t, P' t). apply term_ind_forall.
    (* var *)
    unfold P'. intros. assert (u = Var x). apply subterm_eq_var. hyp.
    subst u. apply IH. unfold subterm. intros. destruct H0. destruct H0.
    destruct x0. cong. discr.
    (* fun *)
    intros. unfold P'. intros. apply IH. intros.
    assert (subterm u0 (Fun f v)). eapply subterm_trans_eq2. apply H1. hyp.
    assert (exists t, In t v /\ subterm_eq u0 t). apply subterm_fun_elim with f.
    hyp.
    destruct H3. destruct H3.
    assert (P' x). apply lforall_in with term v. hyp. hyp.
    apply H5. hyp.
  Qed.

  Lemma subterm_ind : forall (P : term -> Prop)
    (IH : forall t, (forall u, subterm u t -> P u) -> P t),
    forall t, P t.

  Proof. intros. apply subterm_eq_rect. apply subterm_sub_ind. hyp. Qed.

  Lemma subterm_wf : well_founded subterm.

  Proof.
    intro t. induction t using subterm_ind. constructor. intros.
    apply H. hyp.
  Qed.

End S.

Arguments Hole [Sig].
