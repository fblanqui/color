(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-01-22
- Sebastien Hinderer, 2004-04-02

greatest/smallest component of a list of natural numbers
*)

Set Implicit Arguments.

From CoLoR Require Import ListUtil LogicUtil NatUtil.

Notation nats := (list nat).

(***********************************************************************)
(** max *)

Fixpoint lmax (l : nats) : nat :=
  match l with
    | nil => 0
    | a :: l' => max a (lmax l')
  end.

Lemma in_lmax : forall x l, In x l -> x <= lmax l.

Proof.
induction l; simpl; intro. contr.
destruct H. subst a. apply Nat.le_max_l.
ded (IHl H). apply le_max_intro_r. exact H0.
Qed.

Arguments in_lmax [x l] _.

Lemma incl_lmax : forall l1 l2, incl l1 l2 -> lmax l1 <= lmax l2.

Proof.
intros l1 l2. induction l1 as [| a' l' Hrec].
 auto with arith.
 intro H. gen (incl_cons_l H). clear H. intros (H1, H2). simpl.
 apply (Nat.max_case a' (lmax l') (fun n : nat => n <= lmax l2)).
  apply in_lmax. hyp.
  apply Hrec. hyp.
Qed.

Lemma lmax_app m : forall l, lmax (l ++ m) = max (lmax l) (lmax m).

Proof.
  induction l as [| a l Hrec]. auto. simpl. rewrite Hrec, max_assoc. refl.
Qed.

Lemma lmax_in : forall l, length l > 0 -> exists x, In x l /\ lmax l = x.

Proof.
induction l; simpl; intros. contradict H; lia. destruct l.
exists a. intuition. set (l' := n::l) in *. assert (length l'>0). simpl. lia.
ded (IHl H0). do 2 destruct H1. case (Nat.max_dec a (lmax l')); intro.
exists a. intuition. exists x. intuition.
Qed.

(***********************************************************************)
(** min *)

Fixpoint lmin (l : nats) : nat :=
  match l with
    | nil => 0
    | a :: l' => min a (lmin l')
  end.

Lemma in_lmin : forall x l, In x l -> lmin l <= x.

Proof.
induction l; simpl; intro. contr.
destruct H. subst a. apply Nat.le_min_l.
ded (IHl H). apply elim_min_r. exact H0.
Qed.

Arguments in_lmin [x l] _.
