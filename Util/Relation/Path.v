(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17
- Frederic Blanqui, 2007-01-22
- Sidi Ould-Biha, 2010-04-27

paths
*)

Set Implicit Arguments.

From Coq Require Arith.
From CoLoR Require Import RelSub ListUtil ListNodup RelUtil LogicUtil
  ListShrink NatUtil ListOccur.

(***********************************************************************)
(** in the following, we assume given a type A and a relation R on A *)

Section S.

  Variables (A : Type) (R : relation A).

(***********************************************************************)
(** (path x y [z1;..;zn]) if x R z1 R .. R zn R y *)

  (*FIXME: put y after l! *)

  Fixpoint path (x y : A) (l : list A) : Prop :=
    match l with
      | nil => R x y
      | z::l' => R x z /\ path z y l'
    end.

  Lemma path_clos_trans : forall y l x, path x y l -> R! x y.

  Proof.
    induction l; simpl; intros. constructor. hyp.
    constructor 2 with a. constructor. tauto. apply IHl. tauto.
  Qed.

  Lemma path_app : forall y z l' l x,
    path x y l -> path y z l' -> path x z (l++y::l'). 

  Proof.
    induction l; simpl; intros. tauto. split. tauto. apply IHl; tauto.
  Qed.

  Lemma clos_trans_path : forall x y, R! x y -> exists l, path x y l.

  Proof.
    intros. induction H. exists (nil : list A). simpl. hyp.
    destruct IHclos_trans1. destruct IHclos_trans2. exists (x0++y::x1). 
    apply path_app; hyp.
  Qed.

  Lemma path_app_elim_right : forall y z l l' x, 
    path x z (l++y::l') -> path y z l'.

  Proof. induction l; simpl; intros. tauto. apply IHl with a. tauto. Qed.

  Lemma path_nodup_length : 
    eq_midex A -> forall y l x,  path x y l -> 
      exists l', ~In x l' /\ ~In y l' /\ nodup l'
        /\ length l'<= length l /\ l' [= l /\ path x y l'.

  Proof.
    induction l; intros; simpl in H0. exists (nil : list A). simpl.
    pose (incl_nil (nil : list A)). pose (Nat.le_0_l 0). tauto. 
    destruct (IHl a). tauto.
    destruct (H y a). exists (nil : list A). simpl.
    pose (Nat.le_0_l (S (length l))). pose (incl_nil (a::l)). rewrite H2. tauto. 
    destruct (In_midex H x x0). destruct (In_elim_right H x x0). hyp. 
    destruct H4. exists x2. split. tauto. split.
    intro. absurd (In y x0). tauto. 
    rewrite (proj1 H4). apply in_or_app. simpl. tauto. rewrite (proj1 H4) in H1.
    split.
    destruct (nodup_app_elim_right x1 (x::x2)). tauto. tauto.   
    split. rewrite (length_app x1 (x::x2)) in H1. simpl in H1|-* . lia. split.
    trans (x::x2). apply incl_tl. refl.
    trans (x1++(x::x2)). apply incl_appr. refl.
    trans l.
    tauto. apply incl_tl. refl. apply path_app_elim_right with x1 a.
    tauto.
    destruct (H x a). exists x0. rewrite H4. simpl.
    assert (length x0 <= S (length l)). lia. 
    assert (x0 [= a :: l). apply incl_tl. tauto.
    tauto. exists (a::x0). simpl.
    assert (S (length x0) <= S (length l)). lia. 
    assert (a :: x0 [= a :: l). apply cons_incl. refl. tauto.
    assert (a<>x). intro. rewrite H7 in H4. tauto.
    assert (a<>y). intro. rewrite H8 in H2. tauto. tauto.
  Qed.

  Lemma path_restricted_incl : forall y l l' x,
    is_restricted R l -> path x y l' -> l' [= l.

  Proof.
    unfold is_restricted. induction l'; simpl; intros. intro. simpl. tauto.
    apply incl_cons. pose (H x a). tauto. apply IHl' with a; tauto.
  Qed.

  Lemma path_nth_inP : forall l x y k,
    path x y l -> S k < length l -> R (nth k l y) (nth (S k) l y).

  Proof.
    induction l.
    intros. simpl in H0. lia.
    intros. simpl in H. simpl in H0. gen (lt_n_Sm_le H0); intro.
    simpl. induction k. induction l. simpl. simpl in H. intuition.
    simpl. simpl in H. intuition.
    clear IHk. apply (IHl a y k). intuition. lia.
  Qed.

  Lemma path_lastP : forall k x y l,
    path x y l -> S k = length l -> R (nth k l y) y.

  Proof.
    induction k.
    intros. destruct l. simpl in H0. lia.
    destruct l. simpl. simpl in H. intuition.
    simpl in H0. lia.
    intros. destruct l. simpl in H0. lia.
    simpl. simpl in H. simpl in H0. apply (IHk a y l); intuition.
  Qed.

  Lemma path_headP : forall l x y, path x y l -> R x (nth 0 l y).

  Proof.
    induction l.
    intros. simpl. simpl in H. auto.
    intros. simpl. simpl in H. intuition.
  Qed.

(***********************************************************************)
(** paths of bounded length *)

  Inductive bpath n : relation A :=
  | bp_intro : forall x y l, length l <= n -> path x y l -> bpath n x y.

  Lemma bpath_clos_trans : forall n, bpath n << R!.

  Proof. repeat intro. inversion H. apply path_clos_trans with l. hyp. Qed.

  Lemma clos_trans_bpath : eq_midex A -> forall l,
    is_restricted R l -> R! << bpath (length l).

  Proof.
    do 6 intro. destruct (clos_trans_path H1).
    destruct (path_nodup_length H y x0 x H2). apply bp_intro with x1. 
    apply nodup_midex_incl_length. hyp. tauto. 
    apply path_restricted_incl with y x;tauto. tauto. 
  Qed.

  Lemma bpath_n_Sn : forall n x y, bpath n x y -> bpath (S n) x y.

  Proof.
    intros. inversion H. apply bp_intro with l. apply Nat.le_trans with n. hyp. 
    apply Nat.le_succ_diag_r. hyp.
  Qed.

  Lemma bpath_Sn_n_or_Rn : forall n x y,
    bpath (S n) x y -> bpath n x y \/ exists z : A, R x z /\ bpath n z y.

  Proof.
    intros. inversion H. destruct (le_le_S_dec (length l) n). 
    constructor. apply bp_intro with l; hyp. constructor 2. 
    destruct l. simpl in l0. pose (Nat.nle_succ_0 n l0). tauto. exists a.
    simpl in H0, H1.
    split. tauto. apply bp_intro with l. apply le_S_n. hyp. tauto.
  Qed.

  Lemma R_bpath_n_Sn : forall x y z n,
    R x y -> bpath n y z -> bpath (S n) x z.

  Proof.
    intros. inversion H0. apply bp_intro with (y::l). simpl. apply le_n_S.
    hyp. simpl. tauto. 
  Qed.

(***********************************************************************)
(** properties when the equality is decidable *)

  Variables eqdec : eq_dec A.

  Lemma path_app_elim : forall l x y z m,
    path x y (l++z::m) -> path x z l /\ path z y m.

  Proof.
    induction l; simpl; intros. exact H. destruct H. ded (IHl _ _ _ _ H0).
    intuition.
  Qed.

  Lemma sub_path : forall l x y x' y' l' m p,
    x::l++y::nil = m++x'::l'++y'::p -> path x y l -> path x' y' l'.

  Proof.
    induction l; simpl; intros.
    (* case l=nil *)
    destruct m; simpl in H.
    (* case m=nil *)
    injection H; intros. subst x'. destruct l'; simpl in H1.
    (* case l'=nil *)
    injection H1; intros. subst y'. exact H0.
    (* case l'=a::l' *)
    injection H1; intros. destruct l'; discr.
    (* case m=a::m *)
    injection H; intros. destruct m; simpl in H1.
    (* case m=nil *)
    injection H1; intros. destruct l'; discr.
    (* case m=a0::m *)
    injection H1; intros. destruct m; discr.
    (* case l=a::l *)
    destruct H0. destruct m; simpl in H.
    (* case m=nil *)
    injection H; intros. subst x'. destruct l'; simpl in H2; simpl in H.
    (* case l'=nil *)
    injection H2; intros. subst a. exact H0.
    (* case l'=a0::l' *)
    simpl. injection H2; intros. subst a0. intuition.
    apply (IHl a y a y' l' nil p). simpl. exact H2. exact H1.
    (* case m=a0::m *)
    injection H; intros. subst a0. eapply IHl. apply H2. exact H1.
  Qed.

  Lemma path_suffix : forall y z l' l'' x,
    path x y l' -> suffix (z::l'') l' -> path z y l''.

  Proof.
    induction l'; intros. assert (rev (z :: l'')=nil). apply prefix_nil. hyp.
    simpl in H1. symmetry in H1. pose (app_cons_not_nil (rev l'') nil z H1).
    tauto.
    destruct (list_eq_dec eqdec (z :: l'')(a :: l')). inversion e. simpl in H.
    tauto. simpl in H. 
    apply IHl' with a. tauto. apply suffix_smaller with a; hyp.
  Qed.

  Lemma path_cut : forall y l' x,
    In x l' -> path x y l' -> path x y (tail(cut eqdec x l')). 

  Proof.
    intros. apply path_suffix with l' x. hyp.
    rewrite <- (cut_head eqdec x l' H). apply suffix_cut.
  Qed.

  Lemma path_cut_bis : forall l' x y z,
    In z l' -> R x z -> path z y l' -> path x y (cut eqdec z l'). 

  Proof.
    intros. rewrite (cut_head eqdec z l'). simpl.
    assert (path z y (tail (cut eqdec z l'))).
    apply path_cut; hyp. destruct l'. pose (in_nil H).
    contr. tauto. hyp.
  Qed.

  Lemma path_shrink : forall y l' x, path x y l' -> path x y (shrink eqdec l').

  Proof.
    induction l'; simpl; intros. hyp.
    assert (path a y (shrink eqdec l')).
    apply IHl'; tauto. destruct (In_dec eqdec a (shrink eqdec l')).
    apply path_cut_bis; tauto. simpl. tauto.
  Qed.

End S.

(***********************************************************************)
(** paths and sub-relations *)

Section inclusion.

  Variable A : Type.

  Lemma path_preserved : forall R R' (y : A) l x,
    R << R' -> path R x y l -> path R' x y l.

  Proof.
    induction l; repeat intro; simpl in H0 |- * . apply H. hyp. 
    split. pose (H x a). tauto. pose (IHl a). tauto.
  Qed.

  Lemma path_restriction : forall R (y : A) l x,
    path R x y l -> path (restriction R (x::y::l)) x y l.

  Proof.
    unfold restriction. induction l; simpl; intros. tauto. split. tauto.
    simpl in IHl. apply path_preserved with (fun x0 y0 : A =>
      (a = x0 \/ y = x0 \/ In x0 l) /\ (a = y0 \/ y = y0 \/ In y0 l)
      /\ R x0 y0). repeat intro. tauto. 
    apply IHl. tauto.
  Qed.

End inclusion.

(***********************************************************************)
(** restriction *)

Section restriction.

  Variables (A : Type) (R : relation A) (l : list A).

  Lemma restricted_path_incl : is_restricted R l ->
    forall m x y, path R x y m -> x :: m ++ y :: nil [= l.

  Proof.
    induction m; simpl; intros.
    ded (H _ _ H0). unfold is_restricted in H. unfold List.incl. simpl. intuition.
    subst a. exact H2. subst a. exact H3.
    destruct H0. apply incl_cons. ded (H _ _ H0). unfold is_restricted in H2.
    intuition.
    apply IHm. exact H1.
  Qed.

  Variable eqdec : eq_dec A.

  Lemma long_path_occur : is_restricted R l ->
    forall x y m, path R x y m -> length m >= length l - 1 ->
      exists z, occur eqdec z (x :: m ++ y :: nil) >= 2.

  Proof.
    intros. apply pigeon_hole with l. apply restricted_path_incl.
    apply H. apply H0. simpl. rewrite length_app. simpl. lia.
  Qed.

  Lemma path_restriction_In_left : forall (x y : A) l', 
    path (restriction R l) x y l' -> In x l.

  Proof.
    unfold restriction. intros; destruct l'; simpl in H; tauto.
  Qed.

End restriction.

Arguments path_app_elim [A R l x y z m] _.
Arguments restricted_path_incl [A R l] _ [m x y] _ _ _.
