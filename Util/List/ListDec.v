(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-08-08

boolean functions on lists
*)

Set Implicit Arguments.

Require Import ListUtil.
Require Import BoolUtil.
Require Import EqUtil.
Require Import LogicUtil.
Require Import Arith.

Section S.

Variable A : Type.
Variable beq : A -> A -> bool.
Variable beq_ok : forall x y, beq x y = true <-> x = y.

Ltac case_beq := EqUtil.case_beq beq beq_ok.

(***********************************************************************)
(** membership *)

Fixpoint mem (x : A) (l : list A) {struct l} : bool :=
  match l with
    | nil => false
    | y :: m => beq x y || mem x m
  end.

Lemma mem_ok : forall x l, mem x l = true <-> In x l.

Proof.
induction l; simpl; intros; auto. intuition. split; intro.
destruct (orb_true_elim H). rewrite beq_ok in e. subst. auto. intuition.
destruct H. subst. rewrite (beq_refl beq_ok). refl. intuition.
Qed.

(***********************************************************************)
(** inclusion *)

Fixpoint incl (l l' : list A) {struct l} : bool :=
  match l with
    | nil => true
    | y :: m => mem y l' && incl m l'
  end.

Lemma incl_ok : forall l l', incl l l' = true <-> List.incl l l'.

Proof.
induction l; simpl; intros; auto. intuition. apply incl_nil. split; intro.
destruct (andb_elim H). rewrite mem_ok in H0. rewrite IHl in H1. intuition.
destruct (incl_cons_l H). rewrite <- mem_ok in H0. rewrite <- IHl in H1.
rewrite H0. rewrite H1. refl.
Qed.

(***********************************************************************)
(** position of an element in a list *)

Section position.

Fixpoint position_aux (i : nat) (x : A) (l : list A) {struct l} : option nat :=
  match l with
    | nil => None
    | y :: m => if beq x y then Some i else position_aux (S i) x m
  end.

Definition position := position_aux 0.

Lemma position_ko :
  forall x l, position x l = None <-> ~In x l.

Proof.
unfold position. cut (forall x l i, position_aux i x l = None <-> ~In x l).
auto. induction l; simpl; intros. intuition. case_beq x a.
intuition; discr. rewrite (beq_ko beq_ok) in H. ded (IHl (S i)). intuition.
Qed.

Lemma position_aux_plus : forall x j k l i,
  position_aux i x l = Some k -> position_aux (i+j) x l = Some (k+j).

Proof.
induction l; simpl. discr. case_beq x a; intros. inversion H.
refl. assert (S(i+j) = S i+j). refl. rewrite H1. apply IHl. hyp.
Qed.

Lemma position_aux_S : forall x k l i,
  position_aux i x l = Some k -> position_aux (S i) x l = Some (S k).

Proof.
induction l; simpl. discr. case_beq x a; intros. inversion H.
refl. apply IHl. hyp.
Qed.

Lemma position_aux_ok1 : forall k x l i,
  position_aux i x l = Some k -> k >= i /\ element_at l (k-i) = Some x.

Proof.
induction l; simpl. discr. case_beq x a. intros. inversion H.
rewrite <- minus_n_n. intuition. destruct l. simpl. discr. intros.
ded (IHl _ H0). assert (exists p', k - i = S p'). exists (k-i-1). omega.
destruct H2. rewrite H2. assert (k - S i = x0). omega. rewrite <- H3.
intuition.
Qed.

Lemma position_aux_ok2 : forall i x l k, element_at l k = Some x ->
  exists k', k' <= k /\ position_aux i x l = Some (i+k').

Proof.
induction l; simpl; intros. discr. case_beq x a.
exists 0. intuition. rewrite (beq_ko beq_ok) in H0. destruct k.
inversion H. subst. irrefl. destruct (IHl _ H). exists (S x0). intuition.
rewrite <- plus_Snm_nSm. simpl. apply position_aux_S. hyp.
Qed.

End position.

End S.

Implicit Arguments mem_ok [A beq].
