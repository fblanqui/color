(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-02
- Sebastien Hinderer, 2004-04-29

greatest/smallest component of a vector of natural numbers
*)

Set Implicit Arguments.

From CoLoR Require Import VecUtil NatUtil LogicUtil.

Notation nats := (vector nat).

(***********************************************************************)
(** max *)

Fixpoint Vmax n (v : nats n) : nat :=
  match v with
    | Vnil => O
    | Vcons a w => max a (Vmax w)
  end.

Lemma Vmax_in : forall x n (v : nats n), Vin x v -> x <= Vmax v.

Proof.
induction v; simpl; intros. contr. destruct H. subst h.
apply le_max_intro_l. apply Nat.le_refl. apply le_max_intro_r. auto.
Qed.

Arguments Vmax_in [x n v] _.

Lemma Vmax_head : forall n (v : nats (S n)), Vhead v <= Vmax v.

Proof. intros n v. rewrite (VSn_eq v). simpl. auto with arith. Qed.

Lemma Vmax_tail : forall n (v : nats (S n)), Vmax (Vtail v) <= Vmax v.

Proof. intros n v. rewrite (VSn_eq v). simpl. auto with arith. Qed.

Lemma Vmax_app_cons : forall n1 (v1 : nats n1) p n2 (v2 : nats n2),
  p <= Vmax (Vapp v1 (Vcons p v2)).

Proof.
intros. elim v1. simpl. auto with arith.
intros a n' w H. simpl. eapply Nat.le_trans. apply H. auto with arith.
Qed.

Lemma Vmax_forall : forall n (v : nats n) p,
  Vmax v <= p -> Vforall (fun n => n <= p) v.

Proof.
intros n v p. elim v. intro. simpl. auto.
simpl. intros h n' t Hrec H. split.
eapply Nat.le_trans. apply (Nat.le_max_l h (Vmax t)). hyp.
apply (Hrec (Nat.le_trans (Nat.le_max_r h (Vmax t)) H)).
Qed.

Arguments Vmax_forall [n v p] _.

Lemma Vmax_cast : forall n (v : nats n) p (e : n=p), Vmax (Vcast v e) = Vmax v.

Proof.
induction v; destruct p; intros; try lia.
rewrite Vcast_refl. refl. rewrite Vcast_cons. simpl. rewrite IHv. refl.
Qed.

(***********************************************************************)
(** min *)

Fixpoint Vmin n (v : nats n) : nat :=
  match v with
    | Vnil => O
    | Vcons a w => min a (Vmin w)
  end.
