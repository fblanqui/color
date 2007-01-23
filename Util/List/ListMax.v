(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-01-22
- Sebastien Hinderer, 2004-04-02

greatest/smallest component of a list of natural numbers
*)

(* $Id: ListMax.v,v 1.3 2007-01-23 16:42:56 blanqui Exp $ *)

Set Implicit Arguments.

Require Export List.

Notation nats := (list nat).

(***********************************************************************)
(** max *)

Require Export Max.

Fixpoint lmax (l : nats) : nat :=
  match l with
    | nil => 0
    | a :: l' => max a (lmax l')
  end.

Require Export NatUtil.

Lemma in_le_lmax : forall x l, In x l -> x <= lmax l.

Proof.
induction l; simpl; intro. contradiction.
destruct H. subst a. apply le_max_l.
deduce (IHl H). apply elim_max_r. exact H0.
Qed.

Implicit Arguments in_le_lmax [x l].

Require Export ListUtil.

Lemma incl_le_lmax : forall l1 l2, incl l1 l2 -> lmax l1 <= lmax l2.

Proof.
intros l1 l2. induction l1 as [| a' l' Hrec].
 auto with arith.
 intro H. generalize (incl_cons H). clear H. intros (H1, H2). simpl.
 apply (max_case2 a' (lmax l') (fun n : nat => n <= lmax l2)).
  apply in_le_lmax. assumption.
  apply Hrec. assumption.
Qed.

Require Export NatUtil.

Lemma lmax_app : forall l m, lmax (l ++ m) = max (lmax l) (lmax m).

Proof.
intros. induction l as [| a l Hrec].
 auto.
 simpl. rewrite Hrec. rewrite max_assoc. reflexivity.
Qed.

(***********************************************************************)
(** min *)

Require Export Min.

Fixpoint lmin (l : nats) : nat :=
  match l with
    | nil => 0
    | a :: l' => min a (lmin l')
  end.

Lemma in_lmin_le : forall x l, In x l -> lmin l <= x.

Proof.
induction l; simpl; intro. contradiction.
destruct H. subst a. apply le_min_l.
deduce (IHl H). apply elim_min_r. exact H0.
Qed.

Implicit Arguments in_lmin_le [x l].
