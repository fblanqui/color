(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-08

useful definitions and lemmas on boolean vectors
*)

Set Implicit Arguments.

From CoLoR Require Import VecUtil LogicUtil.

Notation bools := (vector bool).

Fixpoint Vtrue n (bs : bools n) : nat :=
  match bs with
    | Vnil => 0
    | Vcons true bs' => S (Vtrue bs')
    | Vcons false bs' => Vtrue bs'
  end.

Lemma Vtrue_app : forall n1 (bs1 : bools n1) n2 (bs2 : bools n2),
  Vtrue (Vapp bs1 bs2) = Vtrue bs1 + Vtrue bs2.

Proof.
induction bs1; simpl. auto. intros. ded (IHbs1 n2 bs2). rewrite H.
case h; refl.
Qed.

Lemma Vtrue_break : forall n1 n2 (bs : bools (n1+n2)),
  Vtrue (fst (Vbreak bs)) + Vtrue (snd (Vbreak bs)) = Vtrue bs.

Proof.
induction n1; simpl; intros. refl. VSntac bs. simpl. case (Vhead bs); simpl.
f_equal. apply IHn1. apply IHn1.
Qed.

Arguments Vtrue_break [n1 n2] _.

Lemma Vtrue_cast : forall n (bs : bools n) p (h:n=p),
  Vtrue (Vcast bs h) = Vtrue bs.

Proof.
induction bs; induction p; intros. rewrite Vcast_refl. refl.
discr. discr. rewrite Vcast_cons. simpl. case h.
f_equal. apply IHbs. apply IHbs.
Qed.

Definition Vtrue_cons_if (b : bool) n (bs : bools (S n)) :=
  if b then S (Vtrue (Vtail bs)) else Vtrue (Vtail bs).

Definition Vtrue_cons n (bs : bools (S n)) := Vtrue_cons_if (Vhead bs) bs.

Lemma Vtrue_cons_eq : forall n (bs : bools (S n)), Vtrue_cons bs = Vtrue bs.

Proof. intros. VSntac bs. unfold Vtrue_cons, Vtrue_cons_if. simpl. refl. Qed.

Lemma Vtrue_cons_true : forall b n (bs : bools n),
  b = true -> S (Vtrue bs) = Vtrue (Vcons b bs).

Proof. intros. subst b. refl. Qed.

Lemma Vtrue_cons_false : forall b n (bs : bools n),
  b = false -> Vtrue bs = Vtrue (Vcons b bs).

Proof. intros. subst b. refl. Qed.

Lemma Vtrue_Sn_true : forall n (bs : bools (S n)),
  Vhead bs = true -> S (Vtrue (Vtail bs)) = Vtrue bs.

Proof. intros. VSntac bs. apply Vtrue_cons_true. hyp. Qed.

Lemma Vtrue_Sn_false : forall n (bs : bools (S n)),
  Vhead bs = false -> Vtrue (Vtail bs) = Vtrue bs.

Proof. intros. VSntac bs. apply Vtrue_cons_false. hyp. Qed.

Lemma Vtrue_Sn : forall n (bs : bools (S n)),
  Vtrue (Vcons (Vhead bs) (Vtail bs)) = Vtrue bs.

Proof. intros. rewrite <- VSn_eq. refl. Qed.
