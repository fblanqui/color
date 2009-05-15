(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-11-26
- Adam Koprowski & Hans Zantema, 2007-03
- Joerg Endrullis, 2008-07

inductive definition of strong normalization (inverse of accessibility)
*)

Set Implicit Arguments.

Require Import RelUtil.
Require Import Setoid.
Require Import LogicUtil.
Require Import List.

Section sn.

Variable (A : Type) (R : relation A).

Inductive SN : A -> Prop :=
  SN_intro : forall x, (forall y, R x y -> SN y) -> SN x.

Lemma SN_inv : forall x, SN x -> forall y, R x y -> SN y.

Proof.
destruct 1; trivial.
Qed.

Definition WF := forall x, SN x.

End sn.

Lemma WF_empty_rel : forall A, WF (@empty_rel A).

Proof.
intros A x. apply SN_intro. intros. contradiction.
Qed.

(***********************************************************************)
(** accessibility *)

Section acc.

Variable (A : Type) (R : relation A).

Lemma SN_transp_Acc : forall x, SN (transp R) x -> Acc R x.

Proof.
induction 1. apply Acc_intro. intros. apply H0. exact H1.
Qed.

Lemma Acc_transp_SN : forall x, Acc (transp R) x -> SN R x.

Proof.
induction 1. apply SN_intro. intros. apply H0. exact H1.
Qed.

Lemma WF_transp_wf : WF (transp R) -> well_founded R.

Proof.
unfold well_founded. intros. apply SN_transp_Acc. apply H.
Qed.

Lemma wf_transp_WF : well_founded (transp R) -> WF R.

Proof.
unfold WF. intros. apply Acc_transp_SN. apply H.
Qed.

End acc.

Section acc_transp.

Variable (A : Type) (R : relation A).

Lemma SN_Acc_transp : forall x, SN R x -> Acc (transp R) x.

Proof.
induction 1. apply Acc_intro. intros. apply H0. exact H1.
Qed.

Lemma Acc_SN_transp : forall x, Acc R x -> SN (transp R) x.

Proof.
induction 1. apply SN_intro. intros. apply H0. exact H1.
Qed.

Lemma WF_wf_transp : WF R -> well_founded (transp R).

Proof.
unfold well_founded. intros. apply SN_Acc_transp. apply H.
Qed.

Lemma wf_WF_transp : well_founded R -> WF (transp R).

Proof.
unfold WF. intros. apply Acc_SN_transp. apply H.
Qed.

End acc_transp.

(***********************************************************************)
(** inclusion *)

Section incl.

Variable (A : Type) (R S : relation A).

Lemma Acc_incl : R << S -> forall x, Acc S x -> Acc R x.
  
Proof.
intros. elim H0; intros. apply Acc_intro. intros. apply H2. apply H. exact H3.
Qed.

Lemma SN_incl : R << S -> forall x, SN S x -> SN R x.

Proof.
intros. elim H0; intros. apply SN_intro. intros. apply H2. apply H. exact H3.
Qed.

Lemma WF_incl : R << S -> WF S -> WF R.

Proof.
unfold WF. intros. apply SN_incl; auto.
Qed.

End incl.

Add Parametric Morphism (A : Type) : (@WF A)
  with signature (same_relation A) ==> iff as WF_mor.

Proof.
intros x y x_eq_y. destruct x_eq_y. split; intro.
apply WF_incl with x; assumption. apply WF_incl with y; assumption.
Qed.

Add Parametric Morphism (A : Type) : (@WF A)
  with signature (@inclusion A) --> impl as WF_incl_mor.

Proof.
intros x y x_eq_y h. apply WF_incl with x; hyp.
Qed.

(***********************************************************************)
(** inverse relation *)

Section transp.

Variables (A : Type) (R : relation A).

Lemma WF_transp : WF R -> WF (transp (transp R)).

Proof.
intro. apply WF_incl with (S := R). unfold inclusion, transp. auto. exact H.
Qed.

End transp.

(***********************************************************************)
(** compatibility *)

Section compat.

Variable (A : Type) (E R : relation A) (Hcomp : E @ R << R).

Lemma SN_compat_inv : forall x,
  SN (R @ E) x -> forall x', E x x' -> SN (R @ E) x'.

Proof.
intros. apply SN_intro. intros. do 2 destruct H1. assert (h : (R @ E) x y).
exists x0; split. apply (incl_elim Hcomp). exists x'; split; assumption.
assumption. apply (SN_inv H). exact h.
Qed.

Lemma WF_compat_inv : WF R -> WF (R @ E).

Proof.
unfold WF. intros. ded (H x). elim H0. intros. apply SN_intro. intros.
do 2 destruct H3. ded (H2 _ H3). apply (SN_compat_inv H5 H4).
Qed.

End compat.

(***********************************************************************)
(** functional inverse image *)

Section inverse.

Variables (A B : Type) (f : A->B) (R : relation B).

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

Variables (A B : Type) (R : relation B) (F : A->B->Prop).

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
(** relation composition *)

Section compose.

Variable (A : Type) (R S : relation A).

Lemma WF_compose_swap : WF (R @ S) -> WF (S @ R).

Proof.
  intro WF_RS.
  assert (forall p q, R p q -> SN (S @ R) q).
  intro p. pattern p.
  apply SN_ind with A (R @ S); auto.
  intros. apply SN_intro. intros.
  destruct H2. apply H0 with x0.
  exists q; intuition.
  intuition.
  unfold WF. intro. apply SN_intro. intros.
  destruct H0 as [z [Sxz Rzy]].
  apply H with z. assumption.
Qed.

End compose.

(***********************************************************************)
(** reflexive transitive closure *)

Section rtc.

Variable (A : Type) (R : relation A).

Lemma SN_rtc : forall x, SN R x -> forall x', R# x x' -> SN R x'.

Proof.
intros x H. induction 1. inversion H. auto. exact H. auto.
Qed.

Lemma SN_rtc1 : forall x, SN R x -> forall x', R#1 x x' -> SN R x'.

Proof.
  intros x snx x' xRx'. apply SN_rtc with x.
  assumption.
  apply (proj1 (clos_refl_trans_equiv R x x')). assumption.
Qed.

End rtc.

(***********************************************************************)
(** transitive closure *)

Section tc.

Variable (A : Type) (R : relation A).

Lemma SN_tc : forall x, SN R x -> SN (R!) x.

Proof.
induction 1. apply SN_intro. intros. ded (tc_split H1). do 2 destruct H2.
apply SN_rtc with (x := x0). apply H0. exact H2.
apply incl_elim with (R := R#). apply incl_rtc. apply tc_incl.
exact H3.
Qed.

Lemma WF_tc : WF R -> WF (R!).

Proof.
intros. unfold WF. intro. apply SN_tc. apply H.
Qed.

Lemma SN_tc1 : forall x, SN R x -> SN (R!1) x.

Proof.
  intros x snx. induction snx as [x IH0 IH1].
  apply SN_intro. intros y xRty. destruct xRty.
  apply IH1. assumption.
  assert (SNy := IH1 y H). destruct SNy as [y' SNy']. apply SNy'.
  assumption.
Qed.

End tc.

(***********************************************************************)
(** symmetric product *)

Section symprod.

Variable (A B : Type) (gtA : relation A) (gtB : relation B).

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
induction 1. destruct x. simpl. apply SN_intro. intros. ded (H0 (y,b)).
apply H2. apply left_sym. assumption.
Qed.

Lemma SN_symprod_snd : forall x, SN gt x -> SN gtB (snd x).

Proof.
induction 1. destruct x. simpl. apply SN_intro. intros. ded (H0 (a,y)).
apply H2. apply right_sym. assumption.
Qed.

Lemma SN_symprod_invl : forall x y, SN gt (x,y) -> SN gtA x.

Proof.
intros. ded (SN_symprod_fst H). assumption.
Qed.

Lemma SN_symprod_invr : forall x y, SN gt (x,y) -> SN gtB y.

Proof.
intros. ded (SN_symprod_snd H). assumption.
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

Variables (A : Type) (E R : relation A).

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

Variables (A : Type) (R S : relation A) (commut : S @ R << R @ S).

Lemma SN_commut : forall x, SN R x -> forall x', S x x' -> SN R x'.

Proof.
induction 1; intros. apply SN_intro. intros.
assert ((S @ R) x y). exists x'. intuition. ded (commut H3).
do 2 destruct H4. apply (H0 _ H4 _ H5).
Qed.

End commut.

(***********************************************************************)
(** WF (iter R n) -> WF R *)

Require Import Iter.

Section iter.

Variables (A : Type) (R : relation A).

Lemma SN_iter_S : forall n x, SN (iter R n) x -> SN (iter R (S n)) x.

Proof.
intros. elim H. intros. apply SN_intro. intros.
assert ((iter R n @ iter R 0) x0 y). apply iter_commut. exact H2.
do 2 destruct H3. ded (H1 _ H3).
eapply SN_commut with (S := iter R 0). apply iter_commut. apply H5. exact H4.
Qed.

Lemma SN_iter_S' : forall n x, SN (iter R (S n)) x -> SN (iter R n) x.

Proof.
intros. elim H; intros. do 2 (apply SN_intro; intros). destruct n.
simpl in *. apply H1. exists y. intuition.
assert ((iter R (S (S n)) @ iter R n) x0 y0).
apply incl_elim with (R := iter R (S n) @ iter R (S n)).
trans (iter R (S n+S n+1)). apply iter_iter.
assert (S n+S n+1 = S(S n)+n+1). omega. rewrite H4. apply iter_plus_1.
exists y. intuition. do 2 destruct H4. ded (H1 _ H4).
eapply SN_commut with (S := iter R n). apply iter_commut. apply H6. exact H5.
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

Require Import Path.

Section path.

Variables (A : Type) (R : relation A).

Lemma SN_path : forall n x,
  (forall y l, length l = n -> is_path R x y l -> SN R y) -> SN R x.

Proof.
intros. apply SN_iter with n. apply SN_intro. intros.
apply SN_incl with (R!). apply iter_tc. apply SN_tc.
ded (iter_path H0). do 2 destruct H1. subst n.
apply H with x0. refl. exact H2.
Qed.

End path.

(***********************************************************************)
(** R @ S << S @ R -> WF S -> WF (R## @ S) *)

Section commut_modulo.

Variables (A : Type) (R S : relation A) (commut : R @ S << S @ R).

Lemma SN_commut_modulo : forall x, SN S x -> SN (R# @ S) x.

Proof.
induction 1. apply SN_intro. intros. ded (commut_rtc commut H1).
do 2 destruct H2. eapply SN_modulo. apply H0. apply H2. exact H3.
Qed.

Lemma WF_commut_modulo : WF S -> WF (R# @ S).

Proof.
unfold WF. intros. apply SN_commut_modulo. apply H.
Qed.

End commut_modulo.

(***********************************************************************)
(** R @ T << T -> WF T -> WF (T @ R##) *)

Section absorb.

Variables (A : Type) (R T : relation A) (absorb : R @ T << T).

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
ded (H0 _ H1). apply (SN_inv H6). exists x1. intuition.
Qed.

Lemma absorb_WF_modulo_r : WF T -> WF (T @ R#).

Proof.
unfold WF. intros. eapply absorb_SN_modulo_r. apply H.
Qed.

End absorb.

(***********************************************************************)
(** Modular removal of rules for relative termination *)

Section wf_mod_shift.
    
  Variable (A : Type) (R S T : relation A).

  Lemma wf_mod_shift : WF (T# @ (R U S)) -> WF ((S U T)# @ R).

  Proof.
    intro. apply WF_incl with ((T # @ (R U S)) !).
    intros x y Rxy. apply tc_split_inv. apply comp_assoc.
    destruct Rxy as [z [STxz Rzy]]. exists z. split; [idtac | intuition].
    apply rtc_union. apply incl_rtc with (S U T); trivial.
    intros s t STst. destruct STst as [Sst | Tst]; solve [intuition].
    apply WF_tc. assumption.
  Qed.
  
End wf_mod_shift.

Section wf_rel_mod.

  Variable (A : Type) (R S R' S': relation A).

  Lemma wf_rel_mod : WF (S# @ R) -> WF ((R U S)# @ (R' U S')) -> 
    WF ((S' U S)# @ (R' U R)).

  Proof.
    intros. apply WF_incl with ((S' U S)# @ (R U R')).
    comp. apply union_commut.
    apply wf_mod_shift.
    apply WF_incl with (S# @ (R' U S') U S# @ R).
    intros x y Q.
    destruct Q as [z [Sxz [[Rxz | R'xz] | S'xz]]]; 
      solve [ right; exists z; intuition | left; exists z; intuition].
    apply WF_union_mod. assumption.
    apply WF_incl with ((R U S)# @ (R' U S')); [idtac | assumption].
    intros x y Q. destruct Q as [z [Lxz [w [Szw RSwy]]]].
    exists w. split; [idtac | assumption].
    constructor 3 with z.
    apply incl_rtc_rtc with (S# @ R); [idtac | intuition].
    intros a b B. destruct B as [c [Sac Rcb]].
    constructor 3 with c; [idtac | intuition].
    apply incl_rtc with S; intuition.
    apply incl_rtc with S; intuition.
  Qed.

End wf_rel_mod.

Section wf_rel_mod_simpl.

  Variable (A : Type) (R R' S : relation A).

  Lemma wf_rel_mod_simpl : WF (S# @ R) -> WF ((R U S)# @ R') ->
    WF (S# @ (R' U R)).

  Proof.
    intros. apply WF_incl with (((@empty_rel A) U S)# @ (R' U R)).
    comp. apply incl_rtc. intuition.
    apply wf_rel_mod. assumption.
    apply WF_incl with ((R U S)# @ R'); trivial.
    comp. apply union_empty_r.
  Qed.

End wf_rel_mod_simpl.

(***********************************************************************)
(** WF of relations on nat. *)

Require Import Wf_nat.

Section wf_nat.

  Lemma WF_gt : WF gt.

  Proof.
    apply wf_transp_WF. intro n. apply Acc_incl with lt. 
    intros x y. auto.
    apply lt_wf.
  Qed.

End wf_nat.
