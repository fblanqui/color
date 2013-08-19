(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-11-26
- Adam Koprowski & Hans Zantema, 2007-03
- Joerg Endrullis, 2008-07

inductive definition of strong normalization (inverse of accessibility)
*)

Set Implicit Arguments.

Require Import RelUtil Morphisms LogicUtil List Basics.

Section sn.

  Variable (A : Type) (R : relation A).

  Inductive SN x : Prop := SN_intro : (forall y, R x y -> SN y) -> SN x.

  Lemma SN_inv : forall x, SN x -> forall y, R x y -> SN y.

  Proof. destruct 1; trivial. Qed.

  Definition WF := forall x, SN x.

End sn.

Arguments SN_inv [A R x] _ [y] _.

Global Instance SN_proper A (R E : relation A) : Equivalence E ->
  Proper (E ==> E ==> impl) R -> Proper (E ==> impl) (SN R).

Proof.
  intros hE hR x y xy hx. apply SN_intro. intros z yz. eapply SN_inv.
  apply hx. rewrite xy. hyp.
Qed.

(***********************************************************************)
(** If [x] is strongly normalizing wrt [R], then there is no infinite
[R]-sequence starting from [x]. Proof obtained after the correction of
Exercise 15.7 page 413 of the book Coq'Art by Yves Bertot and Pierre
Casteran,
http://www.labri.fr/perso/casteran/CoqArt/gen-rec/SRC/not_decreasing.v. *)

Section notIS.

  Variables (A : Type) (R : relation A).

  Lemma SN_notNT : forall x, SN R x -> ~NT R x.

  Proof.
    intros y hy [f [h0 hf]].
    cut (forall i, ~SN R (f i)). intro h. apply (h 0). rewrite h0. hyp.
    cut (forall x, SN R x -> ~(exists i, x = f i)).
    intros h i hi. eapply h. apply hi. exists i. refl.
    induction 1. intros [i hi]. subst. eapply H0. apply hf. exists (S i). refl.
  Qed.

  Lemma NT_notSN : forall x, NT R x -> ~SN R x.

  Proof. intros x h1 h2. eapply SN_notNT. apply h2. hyp. Qed.

  Lemma WF_notIS : WF R -> forall f, ~IS R f.

  Proof.
    intros wf f hf. eapply SN_notNT with (x:=f 0). apply wf. exists f. auto.
  Qed.

  Lemma WF_notEIS : WF R -> ~EIS R.

  Proof. intros wf [f hf]. eapply WF_notIS. hyp. apply hf. Qed.

End notIS.

(***********************************************************************)
(** accessibility *)

Section acc.

  Variable (A : Type) (R : relation A).

  Lemma SN_transp_Acc : forall x, SN (transp R) x -> Acc R x.

  Proof. induction 1. apply Acc_intro. intros. apply H0. hyp. Qed.

  Lemma Acc_transp_SN : forall x, Acc (transp R) x -> SN R x.

  Proof. induction 1. apply SN_intro. intros. apply H0. hyp. Qed.

  Lemma WF_transp_wf : WF (transp R) -> well_founded R.

  Proof. unfold well_founded. intros. apply SN_transp_Acc. apply H. Qed.

  Lemma wf_transp_WF : well_founded (transp R) -> WF R.

  Proof. unfold WF. intros. apply Acc_transp_SN. apply H. Qed.

End acc.

Section acc_transp.

  Variable (A : Type) (R : relation A).

  Lemma SN_Acc_transp : forall x, SN R x -> Acc (transp R) x.

  Proof. induction 1. apply Acc_intro. intros. apply H0. hyp. Qed.

  Lemma Acc_SN_transp : forall x, Acc R x -> SN (transp R) x.

  Proof. induction 1. apply SN_intro. intros. apply H0. hyp. Qed.

  Lemma WF_wf_transp : WF R -> well_founded (transp R).

  Proof. unfold well_founded. intros. apply SN_Acc_transp. apply H. Qed.

  Lemma wf_WF_transp : well_founded R -> WF (transp R).

  Proof. unfold WF. intros. apply Acc_SN_transp. apply H. Qed.

End acc_transp.

(***********************************************************************)
(** inclusion *)

Section incl.

  Variable (A : Type) (R S : relation A).

  Lemma WF_empty_rel : WF (@empty_rel A).

  Proof. intro x. apply SN_intro. intros. contr. Qed.

  Lemma Acc_incl : R << S -> forall x, Acc S x -> Acc R x.
  
  Proof.
    intros. elim H0; intros. apply Acc_intro. intros. apply H2. apply H. hyp.
  Qed.

  Lemma SN_incl : R << S -> forall x, SN S x -> SN R x.

  Proof.
    intros. elim H0; intros. apply SN_intro. intros. apply H2. apply H. hyp.
  Qed.

  Lemma WF_incl : R << S -> WF S -> WF R.

  Proof. unfold WF. intros. apply SN_incl; auto. Qed.

End incl.

Instance WF_m A : Proper (same_relation ==> iff) (@WF A).

Proof.
  intros x y x_eq_y. destruct x_eq_y. split; intro.
  apply WF_incl with x; hyp. apply WF_incl with y; hyp.
Qed.

Instance WF_m' A : Proper (inclusion --> impl) (@WF A).

Proof. intros x y x_eq_y h. apply WF_incl with x; hyp. Qed.

(***********************************************************************)
(** inverse relation *)

Section transp.

  Variables (A : Type) (R : relation A).

  Lemma WF_transp : WF R -> WF (transp (transp R)).

  Proof.
    intro. apply WF_incl with (S := R). unfold inclusion, transp. auto. hyp.
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
    exists x0; split. apply (inclusion_elim Hcomp). exists x'; split; hyp.
    hyp. apply (SN_inv H). exact h.
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
    apply (H0 (f y)). rewrite H1. hyp. refl.
  Qed.

  Lemma SN_inverse : forall a, SN R (f a) -> SN Rof a.

  Proof. intros. apply (SN_Rof H). refl. Qed.

  Lemma WF_inverse : WF R -> WF Rof.

  Proof. unfold WF. intros. apply SN_inverse; auto. Qed.

End inverse.

(***********************************************************************)
(** relational inverse image *)

Section rel_inverse.

  Variables (A B : Type) (R : relation B) (F : A->B->Prop).

  Notation RoF := (RoF R F).

  Lemma SN_RoF : forall b, SN R b -> forall a, F a b -> SN RoF a.

  Proof.
    induction 1. rename x into b. intros a H1. apply SN_intro. intros a' H2.
    destruct H2 as [b']. destruct H2. apply (H0 b'). apply H3. hyp. hyp.
  Qed.

  Lemma SN_Inverse : forall a, (exists b, F a b /\ SN R b) -> SN RoF a.

  Proof.
    intros. destruct H as [b]. destruct H. eapply SN_RoF. apply H0. hyp.
  Qed.

  Lemma WF_Inverse : WF R -> WF RoF.

  Proof.
    unfold WF. intros H a. apply SN_intro. intros a' H'. destruct H' as [b'].
    destruct H0. apply (@SN_RoF b'). apply H. hyp.
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
    apply H with z. hyp.
  Qed.

End compose.

(***********************************************************************)
(** reflexive transitive closure *)

Section rtc.

  Variable (A : Type) (R : relation A).

  Lemma SN_rtc : forall x, SN R x -> forall x', R# x x' -> SN R x'.

  Proof. intros x H. induction 1. inversion H. auto. hyp. auto. Qed.

  Lemma SN_rtc1 : forall x, SN R x -> forall x', R#1 x x' -> SN R x'.

  Proof.
    intros x snx x' xRx'. apply SN_rtc with x. hyp.
    apply (proj1 (clos_refl_trans_equiv R x x')). hyp.
  Qed.

End rtc.

(***********************************************************************)
(** transitive closure *)

Section tc.

  Variable (A : Type) (R : relation A).

  Lemma SN_tc : forall x, SN R x -> SN (R!) x.

  Proof.
    induction 1. apply SN_intro. intros. ded (tc_split H1). do 2 destruct H2.
    apply SN_rtc with (x := x0). apply H0. hyp.
    apply inclusion_elim with (R := R#). apply clos_refl_trans_inclusion.
    apply incl_tc. refl. hyp.
  Qed.

  Lemma WF_tc : WF R -> WF (R!).

  Proof. intros. unfold WF. intro. apply SN_tc. apply H. Qed.

  Lemma SN_tc1 : forall x, SN R x -> SN (R!1) x.

  Proof.
    intros x snx. induction snx as [x IH0 IH1].
    apply SN_intro. intros y xRty. destruct xRty.
    apply IH1. hyp.
    assert (SNy := IH1 y H). destruct SNy as [SNy]. apply SNy. hyp.
  Qed.

End tc.

(***********************************************************************)
(** symmetric product *)

Section symprod.

  Variable (A B : Type) (gtA : relation A) (gtB : relation B).

  Notation gt := (symprod gtA gtB).

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
    apply H2. apply left_sym. hyp.
  Qed.

  Lemma SN_symprod_snd : forall x, SN gt x -> SN gtB (snd x).

  Proof.
    induction 1. destruct x. simpl. apply SN_intro. intros. ded (H0 (a,y)).
    apply H2. apply right_sym. hyp.
  Qed.

  Lemma SN_symprod_invl : forall x y, SN gt (x,y) -> SN gtA x.

  Proof. intros. ded (SN_symprod_fst H). hyp. Qed.

  Lemma SN_symprod_invr : forall x y, SN gt (x,y) -> SN gtB y.

  Proof. intros. ded (SN_symprod_snd H). hyp. Qed.

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
    exists x0. intuition. apply rt_trans with x'; hyp.
  Qed.

  Lemma WF_union_mod : WF E -> WF (E# @ R) -> WF (R U E).

  Proof.
    intros WF_E WF_ER x.
    apply SN_ind with A (E# @ R); auto. 
    clear x. intros x _ IH.
    apply SN_intro. intros y RExy.
    destruct RExy as [Rxy | Exy].
    apply IH. exists x. 
    split; [apply rt_refl | hyp].
    cut (forall y, (E# @ R) x y -> SN (R U E) y); [idtac | hyp].
    cut (E! x y). pattern y. apply SN_ind with A E; auto.
    clear y IH Exy. intros y _ IH_out Exy IH_in.
    apply SN_intro. intros z REyz.
    destruct REyz.
    apply IH_in. exists y. split; trivial.
    apply tc_incl_rtc. hyp.
    apply IH_out; trivial.
    constructor 2 with y. trivial.
    constructor. hyp.
    constructor. hyp.
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
    assert ((iter R n @ iter R 0) x0 y). apply iter_commut. hyp.
    do 2 destruct H3. ded (H1 _ H3).
    eapply SN_commut with (S := iter R 0). apply iter_commut. apply H5. hyp.
  Qed.

  Lemma SN_iter_S' : forall n x, SN (iter R (S n)) x -> SN (iter R n) x.

  Proof.
    intros. elim H; intros. do 2 (apply SN_intro; intros). destruct n.
    simpl in *. apply H1. exists y. intuition.
    assert ((iter R (S (S n)) @ iter R n) x0 y0).
    apply inclusion_elim with (R := iter R (S n) @ iter R (S n)).
    incl_trans (iter R (S n+S n+1)). apply iter_iter.
    assert (S n+S n+1 = S(S n)+n+1). omega. rewrite H4. apply iter_plus_1.
    exists y. intuition. do 2 destruct H4. ded (H1 _ H4).
    eapply SN_commut with (S := iter R n). apply iter_commut. apply H6. hyp.
  Qed.

  Lemma SN_iter : forall n x, SN (iter R n) x -> SN R x.

  Proof. induction n; intros. hyp. apply IHn. apply SN_iter_S'. hyp. Qed.

  Lemma WF_iter : forall n, WF (iter R n) -> WF R.

  Proof. unfold WF. intros. eapply SN_iter. apply H. Qed.

End iter.

(***********************************************************************)
(** extension of SN_intro to paths of fixed length *)

Require Import Path.

Section path.

  Variables (A : Type) (R : relation A).

  Lemma SN_path : forall n x,
    (forall y l, length l = n -> path R x y l -> SN R y) -> SN R x.

  Proof.
    intros. apply SN_iter with n. apply SN_intro. intros.
    apply SN_incl with (R!). apply iter_tc. apply SN_tc.
    ded (iter_path H0). do 2 destruct H1. subst n.
    apply H with x0. refl. hyp.
  Qed.

End path.

(***********************************************************************)
(** R @ S << S @ R -> WF S -> WF (R## @ S) *)

Section commut_modulo.

  Variables (A : Type) (R S : relation A) (commut : R @ S << S @ R).

  Lemma SN_commut_modulo : forall x, SN S x -> SN (R# @ S) x.

  Proof.
    induction 1. apply SN_intro. intros. ded (commut_rtc commut H1).
    do 2 destruct H2. eapply SN_modulo. apply H0. apply H2. hyp.
  Qed.

  Lemma WF_commut_modulo : WF S -> WF (R# @ S).

  Proof. unfold WF. intros. apply SN_commut_modulo. apply H. Qed.

End commut_modulo.

(***********************************************************************)
(** R @ T << T -> WF T -> WF (T @ R##) *)

Section absorb.

  Variables (A : Type) (R T : relation A) (absorb : R @ T << T).

  Lemma SN_modulo_r : forall x x', SN (T @ R#) x -> R# x x' -> SN (T @ R#) x'.

  Proof.
    intros. apply SN_intro. intros. apply (SN_inv H). do 2 destruct H1.
    exists x0. intuition. apply (incl_rtc_comp absorb). exists x'. intuition.
  Qed.

  Lemma absorb_SN_modulo_r : forall x, SN T x -> SN (T @ R#) x.

  Proof.
    induction 1. apply SN_intro. intros. apply SN_intro. intros.
    do 2 destruct H1. do 2 destruct H2.
    assert (T x0 x1). apply (incl_rtc_comp absorb). exists y. intuition.
    ded (H0 _ H1). apply (SN_inv H6). exists x1. intuition.
  Qed.

  Lemma absorb_WF_modulo_r : WF T -> WF (T @ R#).

  Proof. unfold WF. intros. eapply absorb_SN_modulo_r. apply H. Qed.

End absorb.

Section WF_mod_rev.

  Variables (A : Type) (E S : relation A).

  Lemma WF_mod_rev : WF (E# @ S) -> WF (S @ E#).

  Proof.
    intro wf. cut (WF (E# @ S @ E#)). intro wf'.
    eapply WF_incl. 2: apply wf'.
    intros x z [y [xy yz]]. exists y. intuition. exists x. intuition.
    apply absorb_WF_modulo_r. 2: hyp.
    intros x z [y [xy yz]]. destruct yz as [t [yt tz]].
    exists t. intuition. apply rt_trans with y. apply rt_step. hyp. hyp.
  Qed.

End WF_mod_rev.

(***********************************************************************)
(** Modular removal of rules for relative termination *)

Section wf_mod_shift.
    
  Variable (A : Type) (R S T : relation A).

  Lemma wf_mod_shift : WF (T# @ (R U S)) -> WF ((S U T)# @ R).

  Proof.
    intro. apply WF_incl with ((T # @ (R U S)) !).
    intros x y Rxy. apply tc_split_inv. apply comp_assoc.
    destruct Rxy as [z [STxz Rzy]]. exists z. split; [idtac | intuition].
    apply rtc_union. apply clos_refl_trans_inclusion with (S U T); trivial.
    intros s t STst. destruct STst as [Sst | Tst]; solve [intuition].
    apply WF_tc. hyp.
  Qed.
  
End wf_mod_shift.

Section wf_rel_mod.

  Variable (A : Type) (R S R' S': relation A).

  Lemma wf_rel_mod :
    WF (S# @ R) -> WF ((R U S)# @ (R' U S')) -> WF ((S' U S)# @ (R' U R)).

  Proof.
    intros. apply WF_incl with ((S' U S)# @ (R U R')).
    comp. apply union_commut.
    apply wf_mod_shift.
    apply WF_incl with (S# @ (R' U S') U S# @ R).
    intros x y Q.
    destruct Q as [z [Sxz [[Rxz | R'xz] | S'xz]]]; 
      solve [ right; exists z; intuition | left; exists z; intuition].
    apply WF_union_mod. hyp.
    apply WF_incl with ((R U S)# @ (R' U S')); [idtac | hyp].
    intros x y Q. destruct Q as [z [Lxz [w [Szw RSwy]]]].
    exists w. split; [idtac | hyp].
    constructor 3 with z.
    apply incl_rtc_rtc with (S# @ R); [idtac | intuition].
    intros a b B. destruct B as [c [Sac Rcb]].
    constructor 3 with c; [idtac | intuition].
    apply clos_refl_trans_inclusion with S; intuition.
    apply clos_refl_trans_inclusion with S; intuition.
  Qed.

End wf_rel_mod.

Section wf_rel_mod_simpl.

  Variable (A : Type) (R R' S : relation A).

  Lemma wf_rel_mod_simpl :
    WF (S# @ R) -> WF ((R U S)# @ R') -> WF (S# @ (R' U R)).

  Proof.
    intros. apply WF_incl with ((empty_rel U S)# @ (R' U R)).
    comp. apply clos_refl_trans_inclusion. intuition.
    apply wf_rel_mod. hyp.
    apply WF_incl with ((R U S)# @ R'); trivial.
    comp. apply union_empty_r.
  Qed.

End wf_rel_mod_simpl.

(***********************************************************************)
(** WF of relations on nat. *)

Require Export Wf_nat.

Arguments ltof [A] _ _ _.
Arguments induction_ltof1 [A] _ _ _ _.
Arguments well_founded_ltof [A] _ _.

Section ltof.

  Variables (A : Type) (f : A -> nat).

  Global Instance ltof_trans : Transitive (ltof f).

  Proof. intros x y z. unfold ltof. omega. Qed.

  Lemma transp_ltof_wf : WF (transp (ltof f)).

  Proof. apply wf_WF_transp. apply well_founded_ltof. Qed.

End ltof.

Lemma WF_gt : WF gt.

Proof.
  apply wf_transp_WF. intro n. apply Acc_incl with lt. fo. apply lt_wf.
Qed.

(***********************************************************************)
(** Restriction of a relation to some set. *)

Require Import SetUtil.

Section restrict.

  Variables (A : Type) (P : set A) (R : relation A).

  Definition restrict : relation A := fun x y => P x /\ R x y.

  Lemma restrict_wf : P [= SN R -> WF restrict.

  Proof.
    intros h x. apply SN_intro; intros y [hx xy]. gen (SN_inv (h _ hx) xy).
    clear x hx xy. revert y; induction 1. apply SN_intro. fo.
  Qed.

  Global Instance restrict_proper E :
    Proper (E ==> impl) P -> Proper (E ==> E ==> impl) R ->
    Proper (E ==> E ==> impl) restrict.

  Proof.
    intros PE RE x x' xx' y y' yy' [hxy xy]. split.
    rewrite <- xx'. hyp.
    (*COQ:rewrite <- xx', <- yy'.*)
    eapply RE. apply xx'. apply yy'. hyp.
  Qed.

End restrict.

Lemma restrict_union A (P : set A) R S :
  restrict P (R U S) == restrict P R U restrict P S.

Proof. fo. Qed.

(****************************************************************************)
(** Extension of a relation on [A] to [option A]. *)

Section opt.

  Variables (A : Type) (R : relation A).

  Inductive opt : relation (option A) :=
  | opt_intro : forall x y, R x y -> opt (Some x) (Some y).

  Lemma opt_wf : WF R -> WF opt.

  Proof.
    intros h p. destruct p.
    gen (h a); revert a; induction 1.
    apply SN_intro; intros [y|] hy; inversion hy; clear hy; subst. fo.
    apply SN_intro; intros [y|] hy; inversion hy.
  Qed.

  Global Instance opt_eq_opt E : Proper (E ==> E ==> impl) R ->
    Proper (eq_opt E ==> eq_opt E ==> impl) opt.

  Proof.
    intros R_E x x' xx' y y' yy' xy.
    inversion xy; inversion xx'; inversion yy'; clear xy xx' yy'; subst;
      try discr. inversion H6; inversion H3; clear H6 H3; subst.
    apply opt_intro. eapply R_E. apply H2. apply H5. hyp.
  Qed.

  Lemma opt_eq_opt_r E : R @ E << R -> opt @ eq_opt E << opt.

  Proof.
    intros RE x z [y [xy yz]].
    inversion xy; clear xy; subst. inversion yz; clear yz; subst.
    apply opt_intro. apply RE. exists y0. fo.
  Qed.

  Lemma opt_eq_opt_l E : E @ R << R -> eq_opt E @ opt << opt.

  Proof.
    intros ER x z [y [xy yz]].
    inversion yz; clear yz; subst. inversion xy; clear xy; subst.
    apply opt_intro. apply ER. exists x0. fo.
  Qed.

  Global Instance opt_trans : Transitive R -> Transitive opt.

  Proof.
    intros R_trans x y z xy yz. inversion xy; inversion yz; clear xy yz; subst.
    inversion H3; clear H3; subst. apply opt_intro. trans y0; hyp.
  Qed.

End opt.

Instance opt_incl A : Proper (inclusion ==> inclusion) (@opt A).

Proof.
  intros R S RS x y xy. inversion xy; clear xy; subst. apply opt_intro. fo.
Qed.
