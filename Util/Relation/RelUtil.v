(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17

general definitions and results about relations
*)

(* $Id: RelUtil.v,v 1.11 2007-02-06 09:54:15 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export Relations.

Implicit Arguments transp.
Implicit Arguments inclusion.
Implicit Arguments clos_refl_trans [A].
Implicit Arguments clos_trans [A].
Implicit Arguments reflexive [A].
Implicit Arguments transitive [A].
Implicit Arguments antisymmetric [A].
Implicit Arguments symmetric [A].
Implicit Arguments equiv [A].
Implicit Arguments union [A].

Notation "x << y" := (inclusion x y) (at level 50) : relation_scope.
Notation "x 'U' y" := (union x y) (at level 45) : relation_scope.
Notation "x #" := (clos_refl_trans x) (at level 35) : relation_scope.
Notation "x !" := (clos_trans x) (at level 35) : relation_scope.

Bind Scope relation_scope with relation.

Arguments Scope transp [type_scope relation_scope].
Arguments Scope inclusion [type_scope relation_scope relation_scope].
Arguments Scope clos_refl_trans [type_scope relation_scope].
Arguments Scope union [type_scope relation_scope relation_scope].

Open Scope relation_scope.

(***********************************************************************)
(** basic properties *)

Section basic_properties.

Variables (A : Set) (R : relation A).

Definition Rel_dec := forall x y, {R x y}+{~R x y}.

Definition irreflexive := forall x, ~ R x x.

Definition asymmetric := forall x y, R x y -> ~ R y x.

End basic_properties.

(***********************************************************************)
(** basic definitions *)

Section basic_definitions.

Variables (A : Set) (R : relation A).

Definition quasi_ordering := reflexive R /\ transitive R. (* preorder in coq *)

Definition ordering := reflexive R /\ transitive R /\ antisymmetric R.

Definition strict_ordering := irreflexive R /\ transitive R.

Definition strict_part x y := R x y /\ ~ R y x.

End basic_definitions.

(***********************************************************************)
(** ordering structures *)

Section ordering_structures.

Variable A : Set.

Record Quasi_ordering : Type := mkQuasi_ordering {
  qord_rel :> relation A;
  qord_refl : reflexive qord_rel;
  qord_trans : transitive qord_rel
}.

Record Ordering : Type := mkOrdering {
  ord_rel :> relation A;
  ord_refl : reflexive ord_rel;
  ord_trans : transitive ord_rel;
  ord_antisym : antisymmetric ord_rel
}.

Record Strict_ordering : Type := mkStrict_ordering {
  sord_rel :> relation A;
  sord_irrefl : irreflexive sord_rel;
  sord_trans : transitive sord_rel
}.

End ordering_structures.

(***********************************************************************)
(** inclusion *)

Section inclusion.

Variables (A : Set) (R S : relation A).

Lemma incl_elim : R << S -> forall x y, R x y -> S x y.

Proof.
auto.
Qed.

Lemma incl_trans : forall T, R << S -> S << T -> R << T.

Proof.
intros T h h'. unfold inclusion. auto.
Qed.

Lemma incl_refl : R << R.

Proof.
unfold inclusion. auto.
Qed.

End inclusion.

Implicit Arguments incl_elim [A R S x y].

Ltac incl_refl := apply incl_refl.

Ltac trans S := apply incl_trans with (S); try incl_refl.

(***********************************************************************)
(** irreflexive *)

Section irrefl.

Variable A : Set.

Lemma incl_irrefl : forall R S : relation A,
  R << S -> irreflexive S -> irreflexive R.

Proof.
unfold inclusion, irreflexive. intros. intro. exact (H0 x (H x x H1)).
Qed.

End irrefl.

(***********************************************************************)
(** monotony *)

Section monotone.

Variable A : Set.

Definition monotone (R : relation A) f := forall x y, R x y -> R (f x) (f y).

Lemma monotone_transp : forall R f, monotone R f -> monotone (transp R) f.

Proof.
unfold monotone, transp. auto.
Qed.

End monotone.

(***********************************************************************)
(** reflexive closure *)

Definition clos_refl (A : Set) (R : relation A) x y := x = y \/ R x y.

Notation "x %" := (clos_refl x) (at level 35) : relation_scope.

Section clos_refl.

Variables (A : Set) (R S : relation A).

Lemma rc_refl : reflexive (R%).

Proof.
unfold reflexive, clos_refl. auto.
Qed.

Lemma rc_trans : transitive R -> transitive (R%).

Proof.
intro. unfold transitive, clos_refl. intros. decomp H0. subst y. assumption.
decomp H1. subst z. auto. right. apply H with (y := y); assumption.
Qed.

Lemma rc_incl : R << R%.

Proof.
unfold inclusion, clos_refl. auto.
Qed.

Lemma incl_rc : R << S -> R% << S%.

Proof.
intro. unfold clos_refl, inclusion. intros. destruct H0; auto.
Qed.

End clos_refl.

(***********************************************************************)
(** transitive closure *)

Section clos_trans.

Variables (A : Set) (R S : relation A).

Lemma tc_incl : R << R!.

Proof.
unfold inclusion. intros. apply t_step. exact H.
Qed.

Lemma tc_trans : transitive (R!).

Proof.
unfold transitive. intros. apply t_trans with (y := y); assumption.
Qed.

Lemma tc_transp : forall x y, R! y x -> (transp R)! x y.

Proof.
induction 1.
apply t_step. assumption.
eapply t_trans. apply IHclos_trans2. apply IHclos_trans1.
Qed.

Lemma tc_incl_rtc : R! << R#.

Proof.
unfold inclusion. intros. elim H; intros.
apply rt_step. exact H0.
apply rt_trans with (y := y0); assumption.
Qed.

Lemma incl_tc : R << S -> R! << S!.

Proof.
intro. unfold inclusion. intros. elim H0; intros.
apply t_step. apply H. exact H1.
apply t_trans with (y := y0); assumption.
Qed.

Lemma tc_split : forall x y, R! x y -> exists x', R x x' /\ R# x' y.

Proof.
induction 1. exists y. split. exact H. apply rt_refl.
destruct IHclos_trans1. destruct H1. exists x0. split. exact H1.
apply rt_trans with (y := y). exact H2. 
apply incl_elim with (R := R!). apply tc_incl_rtc. exact H0.
Qed.

Lemma trans_tc_incl : transitive R -> R! << R.

Proof.
unfold transitive, inclusion. intros. induction H0. assumption. 
apply H with y; assumption.
Qed.

End clos_trans.

(***********************************************************************)
(** reflexive transitive closure *)

Section clos_refl_trans.

Variables (A : Set) (R S : relation A).

Lemma rtc_incl : R << R#.

Proof.
unfold inclusion. intros. apply rt_step. exact H.
Qed.

Lemma rtc_refl : reflexive (R#).

Proof.
unfold reflexive. intro. apply rt_refl.
Qed.

Lemma rtc_trans : transitive (R#).

Proof.
unfold transitive. intros. eapply rt_trans. apply H. assumption.
Qed.

Lemma rtc_split : forall x y, R# x y -> x = y \/ R! x y.

Proof.
intros. elim H.
intros. right. apply t_step. assumption.
intro. left. reflexivity.
intros. destruct H1; destruct H3.
left. transitivity y0; assumption.
subst y0. right. assumption.
subst y0. right. assumption.
right. apply t_trans with (y := y0); assumption.
Qed.

Lemma rtc_split2 : forall x y,
  R# x y -> x = y \/ (exists x', R x x' /\ R# x' y).

Proof.
intros. elim H; clear H x y; intros.
right. exists y; split. exact H. apply rt_refl.
auto.
destruct H0. subst y. destruct H2. auto. destruct H0. right. exists x0. auto.
do 2 destruct H0. right. exists x0. split. exact H0.
apply rt_trans with (y := y); auto.
Qed.

Lemma rtc_transp : forall x y, R# y x -> (transp R)# x y.

Proof.
induction 1.
apply rt_step. assumption.
apply rt_refl.
eapply rt_trans. apply IHclos_refl_trans2. apply IHclos_refl_trans1.
Qed.

Lemma incl_rtc : R << S -> R# << S#.

Proof.
intro. unfold inclusion. intros. elim H0; intros.
apply rt_step. apply H. assumption.
apply rt_refl.
eapply rt_trans. apply H2. assumption.
Qed.

End clos_refl_trans.

(***********************************************************************)
(** inverse/transp *)

Section transp.

Variables (A : Set) (R S : relation A).

Lemma transp_refl : reflexive R -> reflexive (transp R).

Proof.
auto.
Qed.

Lemma transp_trans : transitive R -> transitive (transp R).

Proof.
unfold transitive, transp. intros. exact (H z y x H1 H0).
Qed.

Lemma transp_sym : symmetric R -> symmetric (transp R).

Proof.
unfold symmetric, transp. auto.
Qed.

Lemma transp_transp : transp (transp R) << R.

Proof.
unfold inclusion, transp. auto.
Qed.

Lemma incl_transp : R << S -> transp R << transp S.

Proof.
unfold inclusion, transp. auto.
Qed.

End transp.

(***********************************************************************)
(** composition *)

Definition compose (A : Set) (R S : relation A) x y :=
  exists z, R x z /\ S z y.

Notation "x @ y" := (compose x y) (at level 40) : relation_scope.

Section compose.

Variables (A : Set) (R R' S S' : relation A).

Lemma incl_comp : R << R' -> S << S' -> R @ S << R' @ S'.

Proof.
intros h1 h2. unfold inclusion, compose. intros. do 2 destruct H.
exists x0. auto.
Qed.

Lemma comp_assoc : forall T, (R @ S) @ T << R @ (S @ T).

Proof.
unfold inclusion. intros. do 4 destruct H. exists x1; split. assumption.
exists x0; split; assumption.
Qed.

Lemma comp_assoc' : forall T, R @ (S @ T) << (R @ S) @ T.

Proof.
unfold inclusion. intros. do 2 destruct H. do 2 destruct H0.
exists x1; split. exists x0; split; assumption. exact H1.
Qed.

Lemma comp_rtc_incl : R @ S << S -> R# @ S << S.

Proof.
intro. unfold inclusion, compose. intros. do 2 destruct H0.
generalize H1. clear H1. elim H0; intros; auto. apply H. exists y0. auto.
Qed.

Lemma comp_tc_incl : R @ S << S -> R! @ S << S.

Proof.
intro. unfold inclusion, compose. intros. do 2 destruct H0.
generalize H1. clear H1. elim H0; intros; auto. apply H. exists y0. auto.
Qed.

Lemma comp_incl_tc : R @ S << S -> R @ S! << S!.

Proof.
intro. unfold inclusion. intros. do 2 destruct H0. generalize x0 y H1 H0.
induction 1; intros. apply t_step. apply H. exists x1; split; assumption.
apply t_trans with (y := y0); auto.
Qed.

Lemma trans_intro : R @ R << R -> transitive R.

Proof.
unfold transitive. intros. apply H. exists y. intuition.
Qed.

Lemma tc_idem : R! @ R! << R!.

Proof.
unfold inclusion. intros. do 2 destruct H. apply t_trans with x0; assumption.
Qed.

End compose.

Ltac comp := apply incl_comp; try incl_refl.

(***********************************************************************)
(** union *)

Section union.

Variables (A : Set) (R R' S S' T: relation A).

Lemma incl_union : R << R' -> S << S' -> R U S << R' U S'.

Proof.
intros. unfold inclusion. intros. destruct H1.
left. apply (incl_elim H). assumption.
right. apply (incl_elim H0). assumption.
Qed.

Lemma union_commut : R U S << S U R.

Proof.
unfold inclusion. intros. destruct H. right. exact H. left. exact H.
Qed.

Lemma union_assoc : (R U S) U T << R U (S U T).

Proof.
unfold inclusion. intros. destruct H. destruct H. left. exact H.
right. left. exact H. right. right. exact H.
Qed.

End union.

Ltac union := apply incl_union; try incl_refl.

(***********************************************************************)
(** relations between closures, union and composition *)

Section properties.

Variables (A : Set) (R S : relation A).

Lemma rtc_step_incl_tc : R# @ R << R!.

Proof.
unfold inclusion. intros. do 2 destruct H. deduce (rtc_split H). destruct H1.
subst x0. apply t_step. exact H0.
apply t_trans with (y := x0). exact H1. apply t_step. exact H0.
Qed.

Lemma tc_incl_step_rtc : R! << R @ R#.

Proof.
unfold inclusion. induction 1. exists y. intuition.
destruct IHclos_trans1. destruct H1. exists x0. intuition.
apply rt_trans with y. exact H2. destruct IHclos_trans2. destruct H3.
apply rt_trans with x1. apply rt_step. exact H3. exact H4.
Qed.

Lemma rtc_comp_permut : R# @ (R# @ S)# << (R# @ S)# @ R#.

Proof.
unfold inclusion. intros. do 2 destruct H. deduce (rtc_split2 H0). destruct H1.
subst x0. exists x; split. apply rt_refl. exact H.
do 4 destruct H1. exists y; split. apply rt_trans with (y := x1).
apply rt_step. exists x2; split. apply rt_trans with (y := x0); assumption.
assumption. assumption. apply rt_refl.
Qed.

Lemma rtc_union : (R U S)# << (R# @ S)# @ R#.

Proof.
unfold inclusion. intros. elim H; intros.
(* step *)
destruct H0. exists x0; split. apply rt_refl. apply rt_step. exact H0.
exists y0; split. apply rt_step. exists x0; split. apply rt_refl. exact H0.
apply rt_refl.
(* refl *)
exists x0; split; apply rt_refl.
(* trans *)
do 2 destruct H1. do 2 destruct H3.
assert (h : ((R# @ S)# @ clos_refl_trans R) x1 x2).
apply incl_elim with (R := (R# @ clos_refl_trans (R# @ S))).
apply rtc_comp_permut. exists y0; split; assumption.
destruct h. destruct H6. exists x3; split.
apply rt_trans with (y := x1); assumption.
apply rt_trans with (y := x2); assumption.
Qed.

Lemma rtc_comp : R# @ S << S U R! @ S.

Proof.
unfold inclusion. intros. do 2 destruct H. deduce (rtc_split H). destruct H1.
subst x0. left. exact H0. right. exists x0; split; assumption.
Qed.

Lemma union_fact : R U R @ S << R @ S%.

Proof.
unfold inclusion. intros. destruct H.
exists y; split; unfold clos_refl; auto.
do 2 destruct H. exists x0; split; unfold clos_refl; auto.
Qed.

Lemma union_fact2 : R @ S U R << R @ S%.

Proof.
trans (R U R @ S). apply union_commut. apply union_fact.
Qed.

Lemma incl_rc_rtc : R << S! -> R% << S#.

Proof.
intro. unfold inclusion. intros. destruct H0. subst y. apply rt_refl.
apply incl_elim with (R := S!). apply tc_incl_rtc. apply H. exact H0.
Qed.

Lemma incl_tc_rtc : R << S# -> R! << S#.

Proof.
intro. unfold inclusion. induction 1. apply H. exact H0.
apply rt_trans with (y := y); assumption.
Qed.

End properties.

Section properties2.

Variables (A : Set) (R S : relation A).

Lemma rtc_comp_modulo : R# @ (R# @ S)! << (R# @ S)!.

Proof.
unfold inclusion. intros. do 2 destruct H.
deduce (tc_incl_step_rtc H0). do 2 destruct H1. do 2 destruct H1.
deduce (rtc_split H2). destruct H4. subst x1.
apply t_step. exists x2. intuition. apply rt_trans with x0; assumption.
apply t_trans with x1. apply t_step. exists x2. intuition.
apply rt_trans with x0; assumption. exact H4.
Qed.

Lemma tc_union : (R U S)! << R! U (R# @ S)! @ R#.

Proof.
unfold inclusion. induction 1. destruct H. left. apply t_step. exact H.
right. exists y. intuition. apply t_step. exists x. intuition.
destruct IHclos_trans1. destruct IHclos_trans2.
left. apply t_trans with y; assumption.
right. do 2 destruct H2. exists x0. intuition.
apply rtc_comp_modulo. exists y. intuition. apply tc_incl_rtc. exact H1.
right. do 2 destruct H1. destruct IHclos_trans2. exists x0.
intuition. apply rt_trans with y. exact H2. apply tc_incl_rtc. exact H3.
do 2 destruct H3. exists x1. intuition. apply t_trans with x0. exact H1.
apply rtc_comp_modulo. exists y. intuition.
Qed.

End properties2.

(***********************************************************************)
(** commutation properties *)

Section commut.

Variables (A : Set) (R S : relation A) (commut : R @ S << S @ R).

Lemma commut_rtc : R# @ S << S @ R#.

Proof.
unfold inclusion. intros. do 2 destruct H. generalize x x0 H y H0.
clear H0 y H x0 x. induction 1; intros.
assert ((S @ R) x y0). apply commut. exists y. intuition.
do 2 destruct H1. exists x0. intuition.
exists y. intuition.
deduce (IHclos_refl_trans2 _ H1). do 2 destruct H2.
deduce (IHclos_refl_trans1 _ H2). do 2 destruct H4.
exists x1. intuition. apply rt_trans with x0; assumption.
Qed.

End commut.

(***********************************************************************)
(** iteration of a relation *)

Section iter.

Require Import Omega.

Variables (A : Set) (R : relation A).

Fixpoint iter (n : nat) : relation A :=
  match n with
    | O => R
    | S p => R @ iter p
  end.

Lemma iter_tc : forall n, iter n << R!.

Proof.
induction n; intros; simpl. apply tc_incl. unfold inclusion. intros.
do 2 destruct H. apply t_trans with x0. apply t_step. exact H.
apply IHn. exact H0.
Qed.

Require Export NatUtil.

Lemma comp_iter : forall p q, iter p @ iter q << iter (p+q+1).

Proof.
induction p; simpl; intros. rewrite plus_1_S. simpl. apply incl_refl.
trans (R @ (iter p @ iter q)). apply comp_assoc. comp. apply IHp.
Qed.

Lemma iter_plus_1 : forall p q, iter (p+q+1) << iter p @ iter q.

Proof.
induction p; simpl; intros. rewrite plus_1_S. simpl. apply incl_refl.
trans (R @ (iter p @ iter q)). comp. apply IHp. apply comp_assoc'.
Qed.

Definition Iter_ge k x y := exists n, n >= k /\ iter n x y.

Definition Iter := Iter_ge 0.

Lemma tc_iter : R! << Iter.

Proof.
unfold inclusion. induction 1; simpl; intros. exists 0. auto.
destruct IHclos_trans1. destruct IHclos_trans2. intuition.
exists (x0+x1+1). intuition. eapply incl_elim. apply comp_iter. exists y. auto.
Qed.

Fixpoint iter_le (n : nat) : relation A :=
  match n with
    | O => R
    | S p => iter n U iter_le p
  end.

Lemma Iter_split : forall n, Iter << iter_le n U Iter_ge (S n).

Proof.
induction n; simpl; intros; unfold inclusion; intros.
do 2 destruct H. destruct x0. left. auto.
right. exists (S x0). intuition.
deduce (IHn _ _ H). destruct H0. left. right. exact H0.
do 2 destruct H0. case (le_lt_dec x0 (S n)); intro.
assert (x0 = S n). omega. subst x0. left. left. exact H1.
right. exists x0. intuition.
Qed.

End iter.

(***********************************************************************)
(** inverse image *)

Section inverse_image.

Variables (A B : Set) (R : relation B) (f : A->B).

Definition Rof a a' := R (f a) (f a').

Lemma Rof_refl : reflexive R -> reflexive Rof.

Proof.
intro. unfold reflexive, Rof. auto.
Qed.

Lemma Rof_trans : transitive R -> transitive Rof.

Proof.
intro. unfold transitive, Rof. intros. unfold transitive in H.
apply H with (y := f y); assumption.
Qed.

Variable F : A -> B -> Prop.

Definition RoF a a' := exists b', F a' b' /\ forall b, F a b -> R b b'.

End inverse_image.
