(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-08

vector filtering
*)

Set Implicit Arguments.

From Stdlib Require Export Vector.
From CoLoR Require Export VecBool.
From Stdlib Require Import Arith.
From CoLoR Require Import VecUtil LogicUtil EqUtil.

Section S.

Variable A : Type.

Notation vec := (vector A).

Fixpoint Vfilter n (bs : bools n) : vec n -> vec (Vtrue bs) :=
  match bs as bs in vector _ n return vec n -> vec (Vtrue bs) with
  | Vnil => fun _ => Vnil
  | Vcons true bs' => fun v => Vcons (Vhead v) (Vfilter bs' (Vtail v))
  | Vcons false bs' => fun v => Vfilter bs' (Vtail v)
  end.

Lemma Vfilter_in : forall n bs (v : vec n) x, Vin x (Vfilter bs v) -> Vin x v.

Proof.
induction v. VOtac. simpl. auto. VSntac bs. simpl.
case (Vhead bs); simpl; intros.
decomp H0. subst x. auto. right. eapply IHv. apply H1. right. eapply IHv.
apply H0.
Qed.

Lemma Vfilter_app_eq : forall n (bs : bools n) n1 (v1 : vec n1)
  n2 (v2 : vec n2) (h : n=n1+n2) (h' : Vtrue (fst (Vbreak (Vcast bs h)))
    + Vtrue (snd (Vbreak (Vcast bs h))) = Vtrue (Vcast bs h)),
  Vfilter (Vcast bs h) (Vapp v1 v2)
  = Vcast (Vapp (Vfilter (fst (Vbreak (Vcast bs h))) v1)
    (Vfilter (snd (Vbreak (Vcast bs h))) v2)) h'.

Proof.
  induction bs; intros.
  destruct n1; destruct n2; repeat rewrite Vcast_refl; solve [discr | refl].
  destruct n1; try VOtac; repeat rewrite Vcast_refl; try solve [discr | refl].
  revert h'; rewrite (Vcast_cons h0); simpl; intro h'.
  VSntac v1. destruct h; simpl; try apply IHbs.
  rewrite Vcast_cons; f_equal; apply IHbs.
Qed.

Lemma Vfilter_app : forall n (bs : bools n) n1 (v1 : vec n1) n2 (v2 : vec n2)
  (h : n=n1+n2), Vfilter (Vcast bs h) (Vapp v1 v2)
  = Vcast (Vapp (Vfilter (fst (Vbreak (Vcast bs h))) v1)
    (Vfilter (snd (Vbreak (Vcast bs h))) v2)) (Vtrue_break (Vcast bs h)).

Proof.
intros. apply Vfilter_app_eq.
Qed.

Lemma Vfilter_cons_eq : forall n (bs : bools (S n)) x (v : vec n)
  (h' : Vtrue_cons bs = Vtrue bs),
  Vfilter bs (Vcons x v) = Vcast (
    if Vhead bs as b return vec (Vtrue_cons_if b bs)
    then Vcons x (Vfilter (Vtail bs) v)
    else Vfilter (Vtail bs) v) h'.

Proof.
intros n bs. VSntac bs. unfold Vtrue_cons. case (Vhead bs); simpl; intros.
rewrite Vcast_refl. refl. rewrite Vcast_refl. refl.
Qed.

Lemma Vfilter_cons : forall n (bs : bools (S n)) x (v : vec n),
  Vfilter bs (Vcons x v) = Vcast (
    if Vhead bs as b return vec (Vtrue_cons_if b bs)
    then Vcons x (Vfilter (Vtail bs) v)
    else Vfilter (Vtail bs) v) (Vtrue_cons_eq bs).

Proof.
intros. apply Vfilter_cons_eq.
Qed.

Lemma Vfilter_cons_true_eq : forall n b (bs : bools n) x (v : vec n), b = true
  -> forall h : S (Vtrue bs) = Vtrue (Vcons b bs),
  Vfilter (Vcons b bs) (Vcons x v) = Vcast (Vcons x (Vfilter bs v)) h.

Proof.
intros n b bs x v H. subst b. simpl Vtrue. intro. rewrite Vcast_refl. refl.
Qed.

Lemma Vfilter_cons_true : forall n b (bs : bools n) x (v : vec n)
  (h : b = true), Vfilter (Vcons b bs) (Vcons x v)
  = Vcast (Vcons x (Vfilter bs v)) (Vtrue_cons_true bs h).

Proof.
intros. apply Vfilter_cons_true_eq. hyp.
Qed.

Lemma Vfilter_head_true_eq : forall n (bs : bools (S n)) x (v : vec n),
  Vhead bs = true -> forall h : S (Vtrue (Vtail bs)) = Vtrue bs,
  Vfilter bs (Vcons x v) = Vcast (Vcons x (Vfilter (Vtail bs) v)) h.

Proof.
intros n bs x v H. VSntac bs. rewrite H. simpl Vtrue. intro.
rewrite Vcast_refl. refl.
Qed.

Lemma Vfilter_head_true : forall n (bs : bools (S n)) x (v : vec n)
  (h : Vhead bs = true), Vfilter bs (Vcons x v)
  = Vcast (Vcons x (Vfilter (Vtail bs) v)) (Vtrue_Sn_true bs h).

Proof.
intros. apply Vfilter_head_true_eq. hyp.
Qed.

Lemma Vfilter_cons_false_eq : forall n b (bs : bools n) x (v : vec n),
  b = false -> forall h : Vtrue bs = Vtrue (Vcons b bs),
  Vfilter (Vcons b bs) (Vcons x v) = Vcast (Vfilter bs v) h.

Proof.
intros n b bs x v H. subst b. simpl Vtrue. intro. rewrite Vcast_refl. refl.
Qed.

Lemma Vfilter_cons_false : forall n b (bs : bools n) x (v : vec n)
  (h : b = false), Vfilter (Vcons b bs) (Vcons x v)
  = Vcast (Vfilter bs v) (Vtrue_cons_false bs h).

Proof.
intros. apply Vfilter_cons_false_eq. hyp.
Qed.

Lemma Vfilter_head_false_eq : forall n (bs : bools (S n)) x (v : vec n),
  Vhead bs = false -> forall h : Vtrue (Vtail bs) = Vtrue bs,
  Vfilter bs (Vcons x v) = Vcast (Vfilter (Vtail bs) v) h.

Proof.
intros n bs x v H. VSntac bs. rewrite H. simpl Vtrue. intro.
rewrite Vcast_refl. refl.
Qed.

Lemma Vfilter_head_false : forall n (bs : bools (S n)) x (v : vec n)
  (h : Vhead bs = false), Vfilter bs (Vcons x v)
  = Vcast (Vfilter (Vtail bs) v) (Vtrue_Sn_false bs h).

Proof.
intros. apply Vfilter_head_false_eq. hyp.
Qed.

Lemma Vfilter_app2_eq : forall n1 (bs1 : bools n1) (v1 : vec n1)
  n2 (bs2 : bools n2) (v2 : vec n2)
  (h : Vtrue bs1 + Vtrue bs2 = Vtrue (Vapp bs1 bs2)),
  Vfilter (Vapp bs1 bs2) (Vapp v1 v2)
  = Vcast (Vapp (Vfilter bs1 v1) (Vfilter bs2 v2)) h.

Proof.
induction bs1; simpl. intros. VOtac. simpl. rewrite Vcast_refl. refl.
case h; simpl; intros; VSntac v1; simpl. rewrite Vcast_cons. f_equal.
apply IHbs1. apply IHbs1.
Qed.

Lemma Vfilter_app2 : forall n1 (bs1 : bools n1) (v1 : vec n1)
  n2 (bs2 : bools n2) (v2 : vec n2),
  Vfilter (Vapp bs1 bs2) (Vapp v1 v2) =
  Vcast (Vapp (Vfilter bs1 v1) (Vfilter bs2 v2)) (sym_eq (Vtrue_app bs1 bs2)).

Proof.
intros. apply Vfilter_app2_eq.
Qed.

Lemma Vfilter_break_eq : forall n1 n2 (bs : bools (n1+n2)) (v : vec (n1+n2))
  (h : Vtrue (fst (Vbreak bs)) + Vtrue (snd (Vbreak bs)) = Vtrue bs),
  Vfilter bs v = Vcast (Vapp (Vfilter (fst (Vbreak bs)) (fst (Vbreak v)))
    (Vfilter (snd (Vbreak bs)) (snd (Vbreak v)))) h.

Proof.
induction n1; simpl. intros. rewrite Vcast_refl. refl.
intros n2 bs v. VSntac bs. VSntac v. simpl. case (Vhead bs); simpl; intros.
rewrite Vcast_cons. f_equal. apply IHn1. apply IHn1.
Qed.

Lemma Vfilter_break : forall n1 n2 (bs : bools (n1+n2)) (v : vec (n1+n2)),
  Vfilter bs v = Vcast (Vapp (Vfilter (fst (Vbreak bs)) (fst (Vbreak v)))
    (Vfilter (snd (Vbreak bs)) (snd (Vbreak v)))) (Vtrue_break bs).

Proof.
intros. apply Vfilter_break_eq.
Qed.

Lemma Vfilter_cast_eq : forall n (bs : bools n) p (v : vec p)
  (hpn : p=n) (hnp: n=p) (h' : Vtrue (Vcast bs hnp) = Vtrue bs),
  Vfilter bs (Vcast v hpn) = Vcast (Vfilter (Vcast bs hnp) v) h'.

Proof.
induction bs; induction p; simpl; intros; try discr;
  revert h'; [rewrite Vcast_refl | rewrite Vcast_cons]; intros.
rewrite Vcast_refl; refl.
VSntac v. simpl. generalize h'. clear h'.
case h; simpl; intro; rewrite Vcast_cons; simpl.
rewrite Vcast_cons; f_equal; apply IHbs. apply IHbs.
Qed.

Lemma Vfilter_cast : forall n (bs : bools n) p (v : vec p) (h : p=n),
  Vfilter bs (Vcast v h)
  = Vcast (Vfilter (Vcast bs (sym_eq h)) v) (Vtrue_cast bs (sym_eq h)).

Proof.
intros. apply Vfilter_cast_eq.
Qed.

End S.

Arguments Vfilter_head_true [A n bs] _ _ _.
Arguments Vfilter_head_false [A n bs] _ _ _.

Lemma Vmap_filter : forall (A B : Type) (f : A->B) n (bs : bools n)
  (v : vector A n), Vmap f (Vfilter bs v) = Vfilter bs (Vmap f v).

Proof.
induction v; intros; simpl. VOtac. refl. ded (IHv (Vtail bs)).
VSntac bs. case (Vhead bs); simpl; rewrite H; refl.
Qed.
