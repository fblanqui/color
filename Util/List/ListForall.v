(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-12

forall predicate
*)

Set Implicit Arguments.

Require Import LogicUtil List.

Section S.

Variables (A : Type) (P : A->Prop).

Fixpoint lforall (l : list A) : Prop :=
  match l with
    | nil => True
    | cons h t => P h /\ lforall t
  end.

Lemma lforall_eq : forall l, lforall l <-> (forall x, In x l -> P x).

Proof.
induction l; simpl; intuition. subst. hyp.
Qed.

Lemma lforall_nil : lforall nil.

Proof.
simpl. auto.
Qed.

Lemma lforall_cons : forall a l, lforall (cons a l) -> P a /\ lforall l.

Proof.
intro a. simpl. auto.
Qed.

Lemma lforall_app : forall l2 l1 : list A,
  lforall (l1 ++ l2) <-> lforall l1 /\ lforall l2.

Proof.
induction l1; simpl; intuition.
Qed.

Lemma lforall_in : forall a l, lforall l -> In a l -> P a.

Proof.
intros a l. elim l.
 intros H1 H2. absurd (In a nil); [apply in_nil | hyp].
 intros b l' Hrec H1 H2. elim (in_inv H2).
  intro H3. subst a. unfold lforall in H1. intuition.
  clear H2. intro H2. gen (lforall_cons H1).
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
apply H. hyp.
Qed.

Lemma forallb_imp_lforall : forall f l,
  (forall x, f x = true -> P x) -> forallb f l = true -> lforall l.

Proof with auto.
induction l; simpl; intros...
split.
apply H. destruct (f a)...
destruct (f a)... discr.
Qed.

Require Import BoolUtil.
Require Setoid.

Lemma forallb_lforall : forall f, (forall x, f x = true <-> P x) ->
  forall l, forallb f l = true <-> lforall l.

Proof.
intros f fok. induction l; simpl. tauto. rewrite andb_eq, fok. intuition.
Qed.

Variable P_dec : forall x, {P x}+{~P x}.

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

Implicit Arguments lforall_in [A P a l].

Lemma lforall_imp : forall (A : Type) (P1 P2 : A->Prop),
  (forall x, P1 x -> P2 x) -> forall l, lforall P1 l -> lforall P2 l.

Proof.
intros A P1 P2 H l. elim l.
 intuition.
 intros a' l' Hrec. simpl. intros (H1, H2). split.
  apply H. hyp.
  apply Hrec. hyp.
Qed.
