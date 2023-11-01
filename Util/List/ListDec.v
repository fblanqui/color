(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-08-08

boolean functions on lists
*)

Set Implicit Arguments.

From Coq Require Import Arith Lia.
From CoLoR Require Import ListUtil BoolUtil EqUtil LogicUtil.

Section S.

  Variables (A : Type) (beq : A -> A -> bool)
            (beq_ok : forall x y, beq x y = true <-> x = y).

  Ltac case_beq := EqUtil.case_beq beq beq_ok.

(***********************************************************************)
(** boolean decidability of equality *)

  Fixpoint beq_list (l m : list A) :=
    match l, m with
    | nil, nil => true
    | x :: l', y :: m' => beq x y && beq_list l' m'
    | _, _ => false
    end.

  Lemma beq_list_refl : forall l, beq_list l l = true.

  Proof. induction l; simpl. refl. rewrite IHl, (beq_refl beq_ok). refl. Qed.

  Lemma beq_list_ok : forall l m, beq_list l m = true <-> l = m.

  Proof.
    induction l; destruct m; simpl; split; intro; try (refl || discr).
    destruct (andb_elim H). rewrite beq_ok in H0. subst a0.
    rewrite IHl in H1. subst m. refl.
    inversion H. subst a0. subst m. apply andb_intro.
    rewrite beq_ok. refl. rewrite IHl. refl.
  Qed.

  (*REMARK: this lemma does not use beq_ok *)
  Lemma beq_list_ok_in : forall l,
      forall hyp : forall x, In x l -> forall y, beq x y = true <-> x = y,
        forall m, beq_list l m = true <-> l = m.

  Proof.
    induction l; destruct m; split; intro; try (refl || discr).
    inversion H. destruct (andb_elim H1).
    assert (h : In a (a::l)). simpl. auto.
    ded (hyp _ h a0). rewrite H3 in H0. subst a0.
    apply tail_eq.
    assert (hyp' : forall x, In x l -> forall y, beq x y = true <-> x=y).
    intros x hx. apply hyp. simpl. auto.
    destruct (andb_elim H1). ded (IHl hyp' m). rewrite H5 in H4. exact H4.
    rewrite <- H. simpl. apply andb_intro.
    assert (h : In a (a::l)). simpl. auto.
    ded (hyp _ h a). rewrite H0. refl.
    assert (hyp' : forall x, In x l -> forall y, beq x y = true <-> x=y).
    intros x hx. apply hyp. simpl. auto.
    ded (IHl hyp' l). rewrite H0. refl.
  Qed.

(***********************************************************************)
(** membership *)

  Fixpoint mem (x : A) (l : list A) : bool :=
    match l with
    | nil => false
    | y :: m => beq x y || mem x m
    end.

  Lemma mem_ok x : forall l, mem x l = true <-> In x l.

  Proof.
    induction l; simpl; intros; auto. intuition. split; intro.
    destruct (orb_true_elim H). rewrite beq_ok in e. subst. auto. intuition.
    destruct H. subst. rewrite (beq_refl beq_ok). refl. intuition.
  Qed.

(***********************************************************************)
(** inclusion *)

  Fixpoint incl (l l' : list A) : bool :=
    match l with
    | nil => true
    | y :: m => mem y l' && incl m l'
    end.

  Lemma incl_ok : forall l l', incl l l' = true <-> l [= l'.

  Proof.
    induction l; simpl; intros; auto. intuition. apply incl_nil. split; intro.
    destruct (andb_elim H). rewrite mem_ok in H0. rewrite IHl in H1. intuition.
    destruct (incl_cons_l H). rewrite <- mem_ok in H0. rewrite <- IHl in H1.
    rewrite H0, H1. refl.
  Qed.

(***********************************************************************)
(** position of an element in a list *)

  Fixpoint position_aux (i : nat) (x : A) (l : list A) : option nat :=
    match l with
    | nil => None
    | y :: m => if beq x y then Some i else position_aux (S i) x m
    end.

  Definition position := position_aux 0.

  Lemma position_ko : forall x l, position x l = None <-> ~In x l.

  Proof.
    unfold position. cut (forall x l i, position_aux i x l = None <-> ~In x l).
    auto. induction l; simpl; intros. intuition. case_beq x a.
    intuition; discr. rewrite (beq_ko beq_ok) in H. ded (IHl (S i)). intuition.
  Qed.

  Lemma position_aux_plus x j k : forall l i,
      position_aux i x l = Some k -> position_aux (i+j) x l = Some (k+j).

  Proof.
    induction l; simpl. discr. case_beq x a; intros. inversion H.
    refl. assert (S(i+j) = S i+j). refl. rewrite H1. apply IHl. hyp.
  Qed.

  Lemma position_aux_S x k : forall l i,
      position_aux i x l = Some k -> position_aux (S i) x l = Some (S k).

  Proof.
    induction l; simpl. discr. case_beq x a; intros. inversion H.
    refl. apply IHl. hyp.
  Qed.

  Lemma position_aux_ok1 k x : forall l i,
      position_aux i x l = Some k -> k >= i /\ element_at l (k-i) = Some x.

  Proof.
    induction l; simpl. discr. case_beq x a. intros. inversion H.
    rewrite Nat.sub_diag. intuition. destruct l. simpl. discr. intros.
    ded (IHl _ H0). assert (exists p', k - i = S p'). exists (k-i-1). lia.
    destruct H2. rewrite H2. assert (k - S i = x0). lia. rewrite <- H3.
    intuition.
  Qed.

  Lemma position_aux_ok2 i x : forall l k, element_at l k = Some x ->
    exists k', k' <= k /\ position_aux i x l = Some (i+k').

  Proof.
    induction l; simpl; intros. discr. case_beq x a.
    exists 0. intuition. rewrite (beq_ko beq_ok) in H0. destruct k.
    inversion H. subst. cong. destruct (IHl _ H). exists (S x0). intuition.
    rewrite Nat.add_succ_r. simpl. apply position_aux_S. hyp.
  Qed.

End S.

Arguments mem_ok [A beq] _ _ _.
Arguments beq_list_ok [A beq] _ _ _.
Arguments beq_list_ok_in [A beq l] _ _.
Arguments incl_ok [A beq] _ _ _.

(***********************************************************************)
(** tactics *)

Ltac incl beq_ok :=
  rewrite <- (incl_ok beq_ok); check_eq
    || fail 10 "list inclusion not satisfied".
