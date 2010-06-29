(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-05-20
- Frederic Blanqui, 2005-02-25

polynomials with non-negative integers as coefficients
*)

Set Implicit Arguments.

Require Import Polynom.
Require Import ZUtil.
Require Import LogicUtil.
Require Import NaryFunction.
Require Import ListForall.
Require Import VecUtil.
Require Import List.
Require Import Max.

Notation vec := (vector D).
Notation vals := (@Vmap D Z val _).

Open Local Scope Z_scope.

Lemma pos_meval : forall n (m : monom n) (v : vec n), 0 <= meval m (vals v).

Proof.
induction n; intros; simpl. omega. VSntac m. VSntac v. simpl.
apply Zmult_le_0_compat. apply pos_power. destruct (Vhead v). assumption.
apply IHn.
Qed.

Lemma preserv_pos_meval : forall n (m : monom n), preserv pos (meval m).

Proof.
intros n m v Hv. rewrite (Vmap_proj1 Hv). apply pos_meval.
Qed.

Definition meval_D n (m : monom n) := restrict (preserv_pos_meval m).

Definition coef_pos n (p : poly n) := lforall (fun x => 0 <= fst x) p.

Definition bcoef_pos n (p : poly n) := forallb (fun x => is_not_neg (fst x)) p.

Lemma bcoef_pos_ok : forall n (p : poly n), bcoef_pos p = true <-> coef_pos p.

Proof.
intros n p. apply forallb_lforall. intros [z m]. apply is_not_neg_ok.
Qed.

Lemma coef_pos_coef : forall n (p : poly n) m, coef_pos p -> 0 <= coef m p.

Proof.
induction p; intros; simpl. omega. destruct a. simpl in H. destruct H.
case (monom_eq_dec m v); intro. assert (0 <= coef m p). apply IHp. assumption.
omega. apply IHp. assumption.
Qed.

Lemma coef_pos_cons : forall n c (m : monom n) (p : poly n),
  coef_pos ((c,m)::p) -> 0 <= c /\ coef_pos p.

Proof.
unfold coef_pos. intros n c m p. simpl. auto.
Qed.

Lemma coef_pos_app : forall n (p1 p2 : poly n),
  coef_pos (p1 ++ p2) -> coef_pos p1 /\ coef_pos p2.

Proof.
unfold coef_pos. intros n p1 p2. simpl. rewrite lforall_app. intuition.
Qed.

Implicit Arguments coef_pos_app [n p1 p2].

Lemma coef_pos_mpmult : forall n c (m : monom n) (p : poly n),
  0 <= c -> coef_pos p -> coef_pos (mpmult c m p).

Proof.
induction p; intros; simpl. exact I. destruct a. simpl.
simpl in H0. destruct H0. split. apply Zmult_le_0_compat; assumption.
apply IHp; assumption.
Qed.

Lemma pos_peval : forall n (p : poly n) v, coef_pos p -> 0 <= peval p (vals v).

Proof.
induction p; intros; simpl. omega. destruct a. simpl in H. destruct H.
apply Zplus_le_0_compat. apply Zmult_le_0_compat. assumption.
apply pos_meval. apply IHp. assumption.
Qed.

Lemma preserv_pos_peval : forall n (p : poly n),
  coef_pos p -> preserv pos (peval p).

Proof.
intros. unfold preserv. intros v Hv.
rewrite (Vmap_proj1 Hv). apply pos_peval. assumption.
Qed.

Definition peval_D n (p : poly n) (H : coef_pos p) :=
  restrict (preserv_pos_peval p H).

Implicit Arguments peval_D [n p].

Lemma val_peval_D : forall n (p : poly n) (H : coef_pos p) (v : vec n),
  val (peval_D H v) = peval p (vals v).

Proof.
intuition.
Qed.

Lemma coef_pos_mpplus : forall n c (m : monom n) (p : poly n),
  0 <= c -> coef_pos p -> coef_pos (mpplus c m p).

Proof.
induction p; intros; simpl. auto. destruct a. simpl in H0. destruct H0.
case (monom_eq_dec m v); simpl; intuition.
Qed.

Lemma coef_pos_plus : forall n (p1 p2 : poly n),
  coef_pos p1 -> coef_pos p2 -> coef_pos (p1 + p2).

Proof.
induction p1; intros; simpl. assumption. destruct a. simpl in H. destruct H.
apply coef_pos_mpplus. assumption. apply IHp1; assumption.
Qed.

Lemma coef_pos_mult : forall n (p1 p2 : poly n),
  coef_pos p1 -> coef_pos p2 -> coef_pos (p1 * p2).

Proof.
induction p1; intros; simpl. exact I. destruct a. simpl in H. destruct H.
apply coef_pos_plus. apply coef_pos_mpmult; assumption. apply IHp1; assumption.
Qed.

Lemma coef_pos_power : forall k n (p : poly n),
  coef_pos p -> coef_pos (ppower p k).

Proof.
induction k; intros; simpl. intuition. apply coef_pos_mult. assumption.
apply IHk. assumption.
Qed.

Lemma coef_pos_mcomp : forall k n (m : monom n) (ps : vector (poly k) n),
  Vforall (@coef_pos k) ps -> coef_pos (mcomp m ps).

Proof.
induction n; intros; simpl. intuition. VSntac ps. simpl. rewrite H0 in H.
simpl in H. destruct H. apply coef_pos_mult. apply coef_pos_power.
assumption. apply IHn. assumption.
Qed.

Lemma coef_pos_cpmult : forall n c (p : poly n),
  0 <= c -> coef_pos p -> coef_pos (cpmult c p).

Proof.
induction p; intros; simpl. exact I. destruct a. simpl. simpl in H0. intuition.
Qed.

Lemma coef_pos_pcomp : forall n k (p : poly n) (ps : vector (poly k) n),
  coef_pos p -> Vforall (@coef_pos k) ps -> coef_pos (pcomp p ps).

Proof.
induction p; intros; simpl. exact I. destruct a. simpl. simpl in H. destruct H.
apply coef_pos_plus. apply coef_pos_cpmult. assumption. apply coef_pos_mcomp.
assumption. apply IHp; assumption.
Qed.

Lemma coefPos_ge0 : forall n (p : poly n) (m : monom n),
  coef_pos p -> coef m p >= 0.

Proof with auto with zarith.
  induction p. simpl...
  intros. destruct a. simpl.
  destruct (monom_eq_dec m v).
  subst m. apply Zge_trans with (coef v p).
  destruct H. simpl in H...
  apply IHp. destruct H...
  apply IHp. destruct H...
Qed.

Lemma coefPos_geC : forall n (p : poly n) (m : monom n) c,
  coef_pos p -> In (c, m) p -> coef m p >= c.

Proof with auto with zarith.
  induction p. simpl. tauto.
  intros. destruct a. simpl.
  destruct (monom_eq_dec m v). subst m.
  destruct H0. injection H0. intros. subst z.
  destruct H. ded (coefPos_ge0 p v H1)...
  apply Zge_trans with (coef v p).
  simpl in H...
  apply IHp... destruct H...
  destruct H0. congruence.
  apply IHp... destruct H...
Qed.