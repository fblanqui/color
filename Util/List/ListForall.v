(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-12

forall predicate
*)

(* $Id: ListForall.v,v 1.4 2007-04-27 19:13:36 koper Exp $ *)

Set Implicit Arguments.

Require Export List.

Section S.

Variables (A : Set) (P : A->Prop).

Fixpoint lforall (l : list A) { struct l} : Prop :=
  match l with
    | nil => True
    | cons h t => P h /\ lforall t
  end.

Lemma lforall_nil : lforall nil.

Proof.
simpl. auto.
Qed.

Lemma lforall_cons : forall (a : A) (l : list A),
  lforall (cons a l) -> P a /\ lforall l.

Proof.
intro a. simpl. auto.
Qed.

Lemma lforall_app : forall l1 l2 : list A,
  lforall (l1 ++ l2) -> lforall l1 /\ lforall l2.

Proof.
intros l1 l2.
elim l1.
 simpl. auto.
 intros a' l' Hrec. simpl. tauto.
Qed.

Lemma lforall_app_inv : forall l1 l2 : list A,
  lforall l1 -> lforall l2 -> lforall (l1 ++ l2).

Proof.
intros l1 l2. elim l1.
 intros. simpl. assumption.
 intros h t Hrec. simpl. intros (H1, H2) H3. split.
  assumption.
  apply (Hrec H2 H3).
Qed.

Lemma lforall_in : forall (a : A) (l : list A), lforall l -> In a l -> P a.

Proof.
intros a l. elim l.
 intros H1 H2. absurd (In a nil); [apply in_nil | assumption].
 intros b l' Hrec H1 H2. elim (in_inv H2).
  intro H3. subst a. unfold lforall in H1. intuition.
  clear H2. intro H2. generalize (lforall_cons H1).
  intros (H3, H4). apply (Hrec H4 H2).
Qed.

Lemma lforall_intro : forall l, (forall x, In x l -> P x) -> lforall l.

Proof.
induction l; simpl; intros. exact I. split. apply H. auto.
apply IHl. intros. apply H. auto.
Qed.

Lemma lforall_incl : forall l1 l2, incl l1 l2 -> lforall l2 -> lforall l1.

Proof.
intros. apply lforall_intro. intros. eapply lforall_in. apply H0.
apply H. assumption.
Qed.

Require Import LogicUtil.
Variable P_dec : prop_dec P.

Lemma lforall_dec : forall l, {lforall l} + {~lforall l}.

Proof.
  induction l.
  left. simpl. trivial.
  simpl. destruct (P_dec a). 
  destruct IHl.
  left; auto.
  right; intuition.
  right; intuition.
Defined.

End S.

Implicit Arguments lforall_app [A P l1 l2].
Implicit Arguments lforall_app_inv [A P l1 l2].
Implicit Arguments lforall_in [A P a l].

Lemma lforall_imp : forall (A : Set) (P1 P2 : A->Prop),
  (forall x, P1 x -> P2 x) -> forall (l : list A), lforall P1 l -> lforall P2 l.

Proof.
intros A P1 P2 H l. elim l.
 intuition.
 intros a' l' Hrec. simpl. intros (H1, H2). split.
  apply H. assumption.
  apply Hrec. assumption.
Qed.
