(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-11-26
- Adam Koprowski & Hans Zantema, 2007-03-13, added WF_union_mod

inductive definition of strong normalization (inverse of accessibility)
*)

Set Implicit Arguments.

Require Export RelUtil.

Section sn.

Variable (A : Set) (R : relation A).

Inductive SN : A -> Prop :=
  SN_intro : forall x, (forall y, R x y -> SN y) -> SN x.

Lemma SN_inv : forall x, SN x -> forall y, R x y -> SN y.

Proof.
  destruct 1; trivial.
Qed.

Definition WF := forall x, SN x.

End sn.

(***********************************************************************)
(** accessibility *)

Section acc.

Variable (A : Set) (R : relation A).

Lemma SN_Acc : forall x, SN (transp R) x -> Acc R x.

Proof.
induction 1. apply Acc_intro. intros. apply H0. exact H1.
Qed.

Lemma Acc_SN : forall x, Acc (transp R) x -> SN R x.

Proof.
induction 1. apply SN_intro. intros. apply H0. exact H1.
Qed.

Lemma WF_wf : WF (transp R) -> well_founded R.

Proof.
unfold well_founded. intros. apply SN_Acc. apply H.
Qed.

Lemma wf_WF : well_founded (transp R) -> WF R.

Proof.
unfold WF. intros. apply Acc_SN. apply H.
Qed.

End acc.

(***********************************************************************)
(** inclusion *)

Section incl.

Variable (A : Set) (R S : relation A).

Lemma SN_incl : R << S -> forall x, SN S x -> SN R x.

Proof.
intros. elim H0; intros. apply SN_intro. intros. apply H2. apply H. exact H3.
Qed.

Lemma WF_incl : R << S -> WF S -> WF R.

Proof.
unfold WF. intros. apply SN_incl; auto.
Qed.

End incl.

(***********************************************************************)
(** inverse relation *)

Section transp.

Variables (A : Set) (R : relation A).

Lemma WF_transp : WF R -> WF (transp (transp R)).

Proof.
intro. apply WF_incl with (S := R). unfold inclusion, transp. auto. exact H.
Qed.

End transp.

(***********************************************************************)
(** compatibility *)

Section compat.

Variable (A : Set) (E R : relation A) (Hcomp : E @ R << R).

Lemma SN_compat_inv : forall x,
  SN (R @ E) x -> forall x', E x x' -> SN (R @ E) x'.

Proof.
intros. apply SN_intro. intros. do 2 destruct H1. assert (h : (R @ E) x y).
exists x0; split. apply (incl_elim Hcomp). exists x'; split; assumption.
assumption. apply (SN_inv H). exact h.
Qed.

Lemma WF_compat_inv : WF R -> WF (R @ E).

Proof.
unfold WF. intros. deduce (H x). elim H0. intros. apply SN_intro. intros.
do 2 destruct H3. deduce (H2 _ H3). apply (SN_compat_inv H5 H4).
Qed.

End compat.

(***********************************************************************)
(** functional inverse image *)

Section inverse.

Variables (A B : Set) (f : A->B) (R : relation B).

Notation Rof := (Rof R f).

Lemma SN_Rof : forall b, SN R b -> forall a, b = f a -> SN Rof a.

Proof.
induction 1. intros. apply SN_intro. intros.
apply (H0 (f y)). rewrite H1. exact H2. refl.
Qed.

Lemma SN_inverse : forall a, SN R (f a) -> SN Rof a.

Proof.
intros. apply (SN_Rof H). refl.
Qed.

Lemma WF_inverse : WF R -> WF Rof.

Proof.
unfold WF. intros. apply SN_inverse; auto.
Qed.

End inverse.

(***********************************************************************)
(** relational inverse image *)

Section rel_inverse.

Variables (A B : Set) (R : relation B) (F : A->B->Prop).

Notation RoF := (RoF R F).

Lemma SN_RoF : forall b, SN R b -> forall a, F a b -> SN RoF a.

Proof.
induction 1. rename x into b. intros a H1. apply SN_intro. intros a' H2.
destruct H2 as [b']. destruct H2. apply (H0 b'). apply H3. exact H1. exact H2.
Qed.

Lemma SN_Inverse : forall a, (exists b, F a b /\ SN R b) -> SN RoF a.

Proof.
intros. destruct H as [b]. destruct H. eapply SN_RoF. apply H0. exact H.
Qed.

Lemma WF_Inverse : WF R -> WF RoF.

Proof.
unfold WF. intros H a. apply SN_intro. intros a' H'. destruct H' as [b'].
destruct H0. apply (@SN_RoF b'). apply H. exact H0.
Qed.

End rel_inverse.

(***********************************************************************)
(** reflexive transitive closure *)

Section rtc.

Variable (A : Set) (R : relation A).

Lemma SN_rtc : forall x, SN R x -> forall x', R# x x' -> SN R x'.

Proof.
intros x H. induction 1. inversion H. auto. exact H. auto.
Qed.

End rtc.

(***********************************************************************)
(** transitive closure *)

Section tc.

Variable (A : Set) (R : relation A).

Lemma SN_tc : forall x, SN R x -> SN (R!) x.

Proof.
induction 1. apply SN_intro. intros. deduce (tc_split H1). do 2 destruct H2.
apply SN_rtc with (x := x0). apply H0. exact H2.
apply incl_elim with (R := R#). apply incl_rtc. apply tc_incl.
exact H3.
Qed.

Lemma WF_tc : WF R -> WF (R!).

Proof.
intros. unfold WF. intro. apply SN_tc. apply H.
Qed.

End tc.

(***********************************************************************)
(** symmetric product *)

Section symprod.

Variable (A B : Set) (gtA : relation A) (gtB : relation B).

Notation gt := (symprod A B gtA gtB).

Require Import Wellfounded.

Lemma SN_symprod : forall x, SN gtA x -> forall y, SN gtB y -> SN gt (x,y).

Proof.
induction 1 as [x _ IHAcc]; intros y H2.
induction H2 as [x1 H3 IHAcc1].
apply SN_intro; intros y H5.
inversion_clear H5; auto with sets.
apply IHAcc; auto.
apply SN_intro; trivial.
Qed.

Lemma WF_symprod : WF gtA -> WF gtB -> WF gt.

Proof.
red in |- *. intros. destruct x. apply SN_symprod; auto with sets.
Qed.

Lemma SN_symprod_fst : forall x, SN gt x -> SN gtA (fst x).

Proof.
induction 1. destruct x. simpl. apply SN_intro. intros. deduce (H0 (y,b)).
apply H2. apply left_sym. assumption.
Qed.

Lemma SN_symprod_snd : forall x, SN gt x -> SN gtB (snd x).

Proof.
induction 1. destruct x. simpl. apply SN_intro. intros. deduce (H0 (a,y)).
apply H2. apply right_sym. assumption.
Qed.

Lemma SN_symprod_invl : forall x y, SN gt (x,y) -> SN gtA x.

Proof.
intros. deduce (SN_symprod_fst H). assumption.
Qed.

Lemma SN_symprod_invr : forall x y, SN gt (x,y) -> SN gtB y.

Proof.
intros. deduce (SN_symprod_snd H). assumption.
Qed.

Lemma SN_symprod_inv : forall x y, SN gt (x,y) -> SN gtA x /\ SN gtB y.

Proof.
intros. split. eapply SN_symprod_invl. apply H. eapply SN_symprod_invr.
apply H.
Qed.

End symprod.

(***********************************************************************)
(** reduction modulo *)

Section modulo.

Variables (A : Set) (E R : relation A).

Lemma SN_modulo : forall x x', SN (E# @ R) x -> E# x x' -> SN (E# @ R) x'.

Proof.
intros. apply SN_intro. intros. apply (SN_inv H). do 2 destruct H1.
exists x0. intuition. apply rt_trans with x'; assumption.
Qed.

Lemma WF_union_mod : WF E -> WF (E# @ R) -> WF (R U E).

Proof.
  intros WF_E WF_ER x.
  apply SN_ind with A (E# @ R); auto. 
  clear x. intros x _ IH.
  apply SN_intro. intros y RExy.
  destruct RExy as [Rxy | Exy].
  apply IH. exists x. 
  split; [constructor rt_refl | assumption].
  cut (forall y, (E# @ R) x y -> SN (R U E) y); [idtac | assumption].
  cut (E! x y). pattern y. apply SN_ind with A E; auto.
  clear y IH Exy. intros y _ IH_out Exy IH_in.
  apply SN_intro. intros z REyz.
  destruct REyz.
  apply IH_in. exists y. split; trivial.
  apply tc_incl_rtc. assumption.
  apply IH_out; trivial.
  constructor 2 with y. trivial.
  constructor. assumption.
  constructor. assumption.
Qed.

End modulo.

(***********************************************************************)
(** S @ R << R @ S -> SN R x -> S x x' -> SN R x' *)

Section commut.

Variables (A : Set) (R S : relation A) (commut : S @ R << R @ S).

Lemma commut_SN : forall x, SN R x -> forall x', S x x' -> SN R x'.

Proof.
induction 1; intros. apply SN_intro. intros.
assert ((S @ R) x y). exists x'. intuition. deduce (commut H3).
do 2 destruct H4. apply (H0 _ H4 _ H5).
Qed.

End commut.

(***********************************************************************)
(** WF (iter R n) -> WF R *)

Require Export Iter.

Section iter.

Variables (A : Set) (R : relation A).

Lemma SN_iter_S : forall n x, SN (iter R n) x -> SN (iter R (S n)) x.

Proof.
intros. elim H. intros. apply SN_intro. intros.
assert ((iter R n @ iter R 0) x0 y). apply iter_commut. exact H2.
do 2 destruct H3. deduce (H1 _ H3).
eapply commut_SN with (S := iter R 0). apply iter_commut. apply H5. exact H4.
Qed.

Lemma SN_iter_S' : forall n x, SN (iter R (S n)) x -> SN (iter R n) x.

Proof.
intros. elim H; intros. do 2 (apply SN_intro; intros). destruct n.
simpl in *. apply H1. exists y. intuition.
assert ((iter R (S (S n)) @ iter R n) x0 y0).
apply incl_elim with (R := iter R (S n) @ iter R (S n)).
trans (iter R (S n+S n+1)). apply iter_iter.
assert (S n+S n+1 = S(S n)+n+1). omega. rewrite H4. apply iter_plus_1.
exists y. intuition. do 2 destruct H4. deduce (H1 _ H4).
eapply commut_SN with (S := iter R n). apply iter_commut. apply H6. exact H5.
Qed.

Lemma SN_iter : forall n x, SN (iter R n) x -> SN R x.

Proof.
induction n; intros. exact H. apply IHn. apply SN_iter_S'. exact H.
Qed.

Lemma WF_iter : forall n, WF (iter R n) -> WF R.

Proof.
unfold WF. intros. eapply SN_iter. apply H.
Qed.

End iter.

(***********************************************************************)
(** extension of SN_intro to paths of fixed length *)

Require Export Path.

Section path.

Variables (A : Set) (R : relation A).

Lemma SN_path : forall n x,
  (forall y l, length l = n -> is_path R x y l -> SN R y) -> SN R x.

Proof.
intros. apply SN_iter with n. apply SN_intro. intros.
apply SN_incl with (R!). apply iter_tc. apply SN_tc.
deduce (iter_path H0). do 2 destruct H1. subst n.
apply H with x0. refl. exact H2.
Qed.

End path.

(***********************************************************************)
(** R @ S << S @ R -> WF S -> WF (R# @ S) *)

Section commut_modulo.

Variables (A : Set) (R S : relation A) (commut : R @ S << S @ R).

Lemma commut_SN_modulo : forall x, SN S x -> SN (R# @ S) x.

Proof.
induction 1. apply SN_intro. intros. deduce (commut_rtc commut H1).
do 2 destruct H2. eapply SN_modulo. apply H0. apply H2. exact H3.
Qed.

Lemma commut_WF_modulo : WF S -> WF (R# @ S).

Proof.
unfold WF. intros. apply commut_SN_modulo. apply H.
Qed.

End commut_modulo.

(***********************************************************************)
(** R @ T << T -> WF T -> WF (T @ R#) *)

Section absorb.

Variables (A : Set) (R T : relation A) (absorb : R @ T << T).

Lemma SN_modulo_r : forall x x', SN (T @ R#) x -> R# x x' -> SN (T @ R#) x'.

Proof.
intros. apply SN_intro. intros. apply (SN_inv H). do 2 destruct H1. exists x0.
intuition. apply (comp_rtc_incl absorb). exists x'. intuition.
Qed.

Lemma absorb_SN_modulo_r : forall x, SN T x -> SN (T @ R#) x.

Proof.
induction 1. apply SN_intro. intros. apply SN_intro. intros.
do 2 destruct H1. do 2 destruct H2.
assert (T x0 x1). apply (comp_rtc_incl absorb). exists y. intuition.
deduce (H0 _ H1). apply (SN_inv H6). exists x1. intuition.
Qed.

Lemma absorb_WF_modulo_r : WF T -> WF (T @ R#).

Proof.
unfold WF. intros. eapply absorb_SN_modulo_r. apply H.
Qed.

End absorb.
