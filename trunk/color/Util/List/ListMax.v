(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02

greatest component of a list of natural numbers
*)

(* $Id: ListMax.v,v 1.2 2007-01-19 17:22:40 blanqui Exp $ *)

Set Implicit Arguments.

Require Export List.
Require Export Arith.
Require Export Max.

Notation nats := (list nat).

Fixpoint lmax (l : nats) : nat :=
  match l with
    | nil => 0
    | a :: l' => max a (lmax l')
  end.

Lemma lmax_in_ineq :
  forall (x : nat) (l : nats), In x l -> x <= lmax l.

Proof.
intros x l. induction l as [|a l Hrec].
 intro H. elimtype False. apply (in_nil H).
 simpl. intro H. inversion_clear H as [| H0].
  subst x. apply le_max_l.
  eapply le_trans.
   apply (Hrec H0).
   apply le_max_r.
Qed.

Require Export ListUtil.

Lemma lmax_incl_ineq : forall l1 l2, incl l1 l2 -> lmax l1 <= lmax l2.

Proof.
intros l1 l2. induction l1 as [| a' l' Hrec].
 auto with arith.
 intro H. generalize (incl_cons H). clear H. intros (H1, H2). simpl.
 apply (max_case2 a' (lmax l') (fun n : nat => n <= lmax l2)).
  apply lmax_in_ineq. assumption.
  apply Hrec. assumption.
Qed.

Require Export NatUtil.

Lemma lmax_app : forall l m, lmax (l ++ m) = max (lmax l) (lmax m).

Proof.
intros. induction l as [| a l Hrec].
 auto.
 simpl. rewrite Hrec. rewrite max_assoc. reflexivity.
Qed.
