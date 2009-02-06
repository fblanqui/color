(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Adam Koprowski and Hans Zantema, 2007-03
- Joerg Endrullis and Dimitri Hendriks, 2008-07

general definitions and results about relations
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Export Relations.
Require Import Setoid.

Implicit Arguments transp [A].
Implicit Arguments inclusion [A].
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
(** equality on relations *)

Lemma same_relation_refl : forall A, reflexive (same_relation A).

Proof.
intuition.
Qed.

Lemma same_relation_sym : forall A, symmetric (same_relation A).

Proof.
unfold symmetric, same_relation. intuition.
Qed.

Lemma same_relation_trans : forall A, transitive (same_relation A).

Proof.
unfold transitive, same_relation. intuition.
Qed.

Add Parametric Relation (A : Type) : (relation A) (same_relation A)
  reflexivity proved by (@same_relation_refl A)
  symmetry proved by (@same_relation_sym A)
  transitivity proved by (@same_relation_trans A)
    as same_relation_rel.

Notation "R == S" := (same_relation _ R S) (at level 70).

(***********************************************************************)
(** basic properties *)

Section basic_properties1.

Variables (A B : Type) (R : A -> B -> Prop).

Definition classic_left_total := forall x, exists y, R x y.

Definition left_total := forall x, {y | R x y}.

Definition functional := forall x y z, R x y -> R x z -> y = z.

Require Import List.

Definition finitely_branching := forall x, {l | forall y, R x y <-> In y l}.

End basic_properties1.

Section basic_properties2.

Variables (A : Type) (R : relation A).

Definition irreflexive := forall x, ~R x x.

Definition asymmetric := forall x y, R x y -> ~R y x.

Definition IS f := forall i, R (f i) (f (S i)).

End basic_properties2.

(***********************************************************************)
(** basic definitions *)

Section basic_definitions.

Variables (A : Type) (R : relation A).

Definition quasi_ordering := reflexive R /\ transitive R. (* preorder in coq *)

Definition ordering := reflexive R /\ transitive R /\ antisymmetric R.

Definition strict_ordering := irreflexive R /\ transitive R.

Definition strict_part : relation A := fun x y => R x y /\ ~R y x.

Definition empty_rel : relation A := fun x y => False.

Definition intersection (S : relation A) : relation A :=
  fun x y => R x y /\ S x y.

End basic_definitions.

(***********************************************************************)
(** finitely branching relations *)

Section finitely_branching.

Variables (A : Type) (R : relation A) (FB : finitely_branching R).

Definition sons x := proj1_sig (FB x).

Lemma in_sons_R : forall x y, In y (sons x) -> R x y.

Proof.
intros x y. exact (proj2 (proj2_sig (FB x) y)).
Qed.

Lemma R_in_sons : forall x y, R x y -> In y (sons x).

Proof.
intros x y. exact (proj1 (proj2_sig (FB x) y)).
Qed.

End finitely_branching.

Implicit Arguments sons [A R].
Implicit Arguments in_sons_R [A R x y].
Implicit Arguments R_in_sons [A R x y].

(***********************************************************************)
(** ordering structures *)

Section ordering_structures.

Variable A : Type.

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

Variables (A : Type) (R S : relation A).

Lemma incl_elim : R << S -> forall x y, R x y -> S x y.

Proof.
auto.
Qed.

Lemma incl_trans : forall T, R << S -> S << T -> R << T.

Proof.
intros T h h'. unfold inclusion. auto.
Qed.

Lemma inclusion_refl : R << R.

Proof.
unfold inclusion. auto.
Qed.

End inclusion.

Implicit Arguments incl_elim [A R S x y].

Ltac inclusion_refl := apply inclusion_refl.

Ltac trans S := apply incl_trans with (S); try inclusion_refl.

Add Parametric Morphism (A : Type) : (@inclusion A)
  with signature (same_relation A) ==> (same_relation A) ==> iff
    as inclusion_mor.

Proof.
intros x y x_eq_y x' y' x'_eq_y'. destruct x_eq_y. destruct x'_eq_y'.
split; intro.
trans x; try assumption. trans x'; assumption.
trans y; try assumption. trans y'; assumption.
Qed.

(***********************************************************************)
(** irreflexive *)

Section irrefl.

Variable A : Type.

Lemma incl_irrefl : forall R S : relation A,
  R << S -> irreflexive S -> irreflexive R.

Proof.
unfold inclusion, irreflexive. intros. intro. exact (H0 x (H x x H1)).
Qed.

End irrefl.

(***********************************************************************)
(** monotony *)

Section monotone.

Variable A : Type.

Definition monotone (R : relation A) f := forall x y, R x y -> R (f x) (f y).

Lemma monotone_transp : forall R f, monotone R f -> monotone (transp R) f.

Proof.
unfold monotone, transp. auto.
Qed.

End monotone.

(***********************************************************************)
(** composition *)

Definition compose A (R S : relation A) : relation A :=
  fun x y => exists z, R x z /\ S z y.

Notation "x @ y" := (compose x y) (at level 40) : relation_scope.

Definition absorb A (R S : relation A) := S @ R << R.

Section compose.

Variables (A : Type) (R R' S S' : relation A).

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

End compose.

Ltac comp := apply incl_comp; try inclusion_refl.

Ltac assoc :=
  match goal with
    | |- (?s @ ?t) @ ?u << _ => trans (s @ (t @ u)); try apply comp_assoc
    | |- ?s @ (?t @ ?u) << _ => trans ((s @ t) @ u); try apply comp_assoc'
    | |- _ << (?s @ ?t) @ ?u => trans (s @ (t @ u)); try apply comp_assoc'
    | |- _ << ?s @ (?t @ ?u) => trans ((s @ t) @ u); try apply comp_assoc
  end.

Add Parametric Morphism (A : Type) : (@compose A)
  with signature
    (same_relation A) ==> (same_relation A) ==> (same_relation A)
  as compose_morph.

Proof.
unfold same_relation. intuition; comp; assumption.
Qed.

(***********************************************************************)
(** reflexive closure *)

Definition clos_refl A (R : relation A) : relation A :=
  fun x y => x = y \/ R x y.

Notation "x %" := (clos_refl x) (at level 35) : relation_scope.

Section clos_refl.

Variables (A : Type) (R S : relation A).

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

Add Parametric Morphism (A : Type)  : (@clos_refl A)
  with signature (same_relation A) ==> (same_relation A)
  as clos_refl_morph.

Proof.
unfold same_relation. intuition; apply incl_rc; assumption.
Qed.

(***********************************************************************)
(** transitive closure *)

Section clos_trans.

Variables (A : Type) (R S : relation A).

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

Lemma tc_split : R! << R @ R#.

Proof.
unfold inclusion. induction 1. exists y. split. exact H. apply rt_refl.
destruct IHclos_trans1. destruct H1. exists x0. split. exact H1.
apply rt_trans with (y := y). exact H2. 
apply incl_elim with (R := R!). apply tc_incl_rtc. exact H0.
Qed.


Lemma trans_tc_incl : transitive R -> R! << R.

Proof.
unfold transitive, inclusion. intros. induction H0. assumption. 
apply H with y; assumption.
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

End clos_trans.

Definition clos_trans : forall A, relation A -> relation A := clos_trans.

Add Parametric Morphism (A : Type) : (@clos_trans A)
  with signature (same_relation A) ==> (same_relation A)
  as clos_trans_morph.

Proof.
unfold same_relation. intuition; apply incl_tc; assumption.
Qed.

(***********************************************************************)
(** reflexive transitive closure *)

Section clos_refl_trans.

Variables (A : Type) (R S : relation A).

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

Lemma rc_incl_rtc : R% << R#.

Proof.
unfold inclusion, clos_refl. intros. destruct H.
subst y. apply rt_refl. apply rt_step. exact H.
Qed.

Lemma rtc_split : R# << @eq A U R!.

Proof.
unfold inclusion, union. intros. elim H.
intros. right. apply t_step. assumption.
intro. left. reflexivity.
intros. destruct H1; destruct H3.
left. transitivity y0; assumption.
subst y0. right. assumption.
subst y0. right. assumption.
right. apply t_trans with (y := y0); assumption.
Qed.

Lemma rtc_split2 : R# << @eq A U R @ R#.

Proof.
unfold inclusion, union. intros. elim H; clear H x y; intros.
right. exists y; split. exact H. apply rt_refl.
auto.
destruct H0. subst y. destruct H2. auto. destruct H0. right. exists x0. auto.
do 2 destruct H0. right. exists x0. split. exact H0.
apply rt_trans with (y := y); auto.
Qed.

Lemma tc_split_inv : R# @ R << R!.

Proof.
intros x y RRxy. destruct RRxy as [z [Rxz Rzy]].
destruct (rtc_split Rxz).
rewrite H. intuition.
constructor 2 with z. assumption.
constructor 1. assumption.
Qed.

Lemma tc_merge : R @ R# << R!.
Proof.
unfold inclusion. intros. destruct H. destruct H.
ded (rtc_split H0). destruct H1; subst.
apply t_step;assumption.
eapply t_trans. apply t_step.
eassumption. assumption.
Qed.

Lemma rtc_transp : transp (R#) << (transp R)#.

Proof.
unfold inclusion. induction 1.
apply rt_step. assumption.
apply rt_refl.
eapply rt_trans. apply IHclos_refl_trans2. apply IHclos_refl_trans1.
Qed.

Lemma incl_rtc_rtc : R << S# -> R# << S#.

Proof.
unfold inclusion. induction 2.
apply H. assumption.
constructor 2.
constructor 3 with y; assumption.
Qed.

Lemma incl_rtc : R << S -> R# << S#.

Proof.
intro. unfold inclusion. intros. elim H0; intros.
apply rt_step. apply H. assumption.
apply rt_refl.
eapply rt_trans. apply H2. assumption.
Qed.

Lemma rtc_idem : R# @ R# << R#.

Proof.
unfold inclusion. intros. do 2 destruct H. apply rt_trans with x0; assumption.
Qed.

End clos_refl_trans.

Definition clos_refl_trans : forall A, relation A -> relation A :=
  clos_refl_trans.

Add Parametric Morphism (A : Type) : (@clos_refl_trans A)
  with signature (same_relation A) ==> (same_relation A)
  as clos_refl_trans_morph.

Proof.
unfold same_relation. intuition; apply incl_rtc; assumption.
Qed.

(***********************************************************************)
(** inverse/transp *)

Section transp.

Variables (A : Type) (R S : relation A).

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
(** union *)

Section union.

Variables (A : Type) (R R' S S' T : relation A).

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

Lemma union_distr_comp : (R U S) @ T << (R @ T) U (S @ T).

Proof.
intros x y H. destruct H as [z [[Rxz | Sxz] Tzy]].
left. exists z. auto.
right. exists z. auto.
Qed.

Lemma union_distr_comp_inv : (R @ T) U (S @ T) << (R U S) @ T.

Proof.
intros x y H. destruct H as [[z [Rxz Tzy]] | [z [Sxz Tzy]]].
exists z. split; [left; assumption | assumption].
exists z. split; [right; assumption | assumption].
Qed.

Lemma union_empty_r : R U (@empty_rel A) << R.

Proof.
  intros x y Rxy. destruct Rxy. assumption. contradiction.
Qed.

Lemma union_empty_l : (@empty_rel A) U R << R.

Proof.
  intros x y Rxy. destruct Rxy. contradiction. assumption.
Qed.

End union.

Ltac union := apply incl_union; try inclusion_refl.

Definition union : forall A, relation A -> relation A -> relation A := union.

Add Parametric Morphism (A : Type) : (@union A)
  with signature
    (same_relation A) ==> (same_relation A) ==> (same_relation A)
  as union_morph.

Proof.
unfold same_relation. intuition; union; assumption.
Qed.

(***********************************************************************)
(** relations between closures, union and composition *)

Section properties.

Variables (A : Type) (R S : relation A).

Lemma rtc_step_incl_tc : R# @ R << R!.

Proof.
unfold inclusion. intros. do 2 destruct H. ded (rtc_split H). destruct H1.
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
unfold inclusion. intros. do 2 destruct H. ded (rtc_split2 H0). destruct H1.
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
unfold inclusion. intros. do 2 destruct H. ded (rtc_split H). destruct H1.
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

Variables (A : Type) (R S : relation A).

Lemma rtc_comp_modulo : R# @ (R# @ S)! << (R# @ S)!.

Proof.
unfold inclusion. intros. do 2 destruct H.
ded (tc_incl_step_rtc H0). do 2 destruct H1. do 2 destruct H1.
ded (rtc_split H2). destruct H4. subst x1.
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

Variables (A : Type) (R S : relation A) (commut : R @ S << S @ R).

Lemma commut_rtc : R# @ S << S @ R#.

Proof.
unfold inclusion. intros. do 2 destruct H. generalize x x0 H y H0.
clear H0 y H x0 x. induction 1; intros.
assert ((S @ R) x y0). apply commut. exists y. intuition.
do 2 destruct H1. exists x0. intuition.
exists y. intuition.
ded (IHclos_refl_trans2 _ H1). do 2 destruct H2.
ded (IHclos_refl_trans1 _ H2). do 2 destruct H4.
exists x1. intuition. apply rt_trans with x0; assumption.
Qed.

End commut.

(***********************************************************************)
(** inverse image *)

Section inverse_image.

Variables (A B : Type) (R : relation B) (f : A->B).

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

(***********************************************************************)
(** Alternative Definition of the Transitive Closure *)
(* (more convenient for certain inductive proofs) *)

Inductive clos_trans1 (A : Type) (R : relation A) : relation A :=
| t1_step : forall x y, R x y -> clos_trans1 R x y
| t1_trans : forall x y z, R x y -> clos_trans1 R y z -> clos_trans1 R x z.

Notation "x !1" := (clos_trans1 x) (at level 35) : relation_scope.

Section alternative_definition_clos_trans.

Variables (A : Type) (R : relation A).

Lemma clos_trans1_trans : forall x y z, R!1 x y -> R!1 y z -> R!1 x z.

Proof.
  intros x y z.
  induction 1; intro H1.
  exact (t1_trans x H H1).
  exact (t1_trans x H (IHclos_trans1 H1)).
Qed.

Lemma clos_trans_equiv : forall x y, R!1 x y <-> R! x y.

Proof.
  intros x y.
  split; intro H.
  induction H.
  constructor; exact H.
  exact (t_trans A R x y z (t_step A R x y H) IHclos_trans1).
  induction H.
  constructor; exact H.
  exact (clos_trans1_trans IHclos_trans1 IHclos_trans2).
Qed.

End alternative_definition_clos_trans.

(***********************************************************************)
(** Alternative Definition of the Reflexive Transitive Closure *)
(* (more convenient for certain inductive proofs) *)

Inductive clos_refl_trans1 (A : Type) (R : relation A) : relation A :=
| rt1_refl : forall x, clos_refl_trans1 R x x
| rt1_trans : forall x y z,
  R x y -> clos_refl_trans1 R y z -> clos_refl_trans1 R x z.

Notation "x #1" := (clos_refl_trans1 x) (at level 35) : relation_scope.

Section alternative_definition_clos_refl_trans.

Variables (A : Type) (R : relation A).

Lemma clos_refl_trans1_trans : forall x y z, R#1 x y -> R#1 y z -> R#1 x z.

Proof.
  intros x y z.
  induction 1; intro H1.
  assumption.
  exact (rt1_trans x H (IHclos_refl_trans1 H1)).
Qed.

Lemma clos_refl_trans_equiv : forall x y, R#1 x y <-> R# x y.

Proof.
  intros x y.
  split; intro H.
  induction H.
  apply rt_refl.
  exact (rt_trans A R x y z (rt_step A R x y H) IHclos_refl_trans1).
  induction H.
  exact (rt1_trans x H (rt1_refl R y)).
  apply rt1_refl.
  exact (clos_refl_trans1_trans IHclos_refl_trans1 IHclos_refl_trans2).
Qed.

Lemma incl_t_rt : R!1 << R#1.

Proof.
  intros x y xRy.
  induction xRy.
  apply rt1_trans with y. assumption. apply rt1_refl.
  apply rt1_trans with y; assumption.
Qed.

Lemma incl_rt_rt_rt : R#1 @ R#1 << R#1.

Proof.
  intros x y [z [xRz zRy]].
  induction xRz. trivial.
  apply rt1_trans with y0. assumption. 
  apply IHxRz. assumption.
Qed.

End alternative_definition_clos_refl_trans.

(***********************************************************************)
(** Alternative Definitions: Inclusion Properties *)

Section alternative_inclusion.

Variables (A : Type) (R S : relation A).

Lemma rtc1_union : (R U S)#1 << (S#1 @ R)#1 @ S#1.

Proof.
  intros x y xRSy.
  induction xRSy as [ | x y z xRSy yRSz]. 
  exists x. split; apply rt1_refl.
  destruct IHyRSz as [m [ym mz]].
  destruct ym as [m | m n o mn no oz].
  induction xRSy as [xRy | xSy].
  exists m. split; trivial. apply rt1_trans with m.
  exists x. split; trivial. apply rt1_refl. apply rt1_refl.
  exists x. split. apply rt1_refl. apply rt1_trans with m; trivial.
  exists o. split; trivial.
  induction xRSy as [xRy | xSy].
  apply rt1_trans with m.
  exists x. split. apply rt1_refl. assumption.
  apply clos_refl_trans1_trans with n; trivial.
  apply rt1_trans with n; trivial. apply rt1_refl.
  apply rt1_trans with n.
  destruct mn as [q [mq qn]]. exists q. split; trivial.
  apply rt1_trans with m; assumption. assumption.
Qed.

Lemma union_rel_rt_left : R#1 << (R U S)#1.

Proof.
  intros x y xRy.
  induction xRy. apply rt1_refl.
  apply rt1_trans with y. left. assumption. assumption.
Qed.

Lemma union_rel_rt_right : S#1 << (R U S)#1.

Proof.
  intros x y xRy.
  induction xRy. apply rt1_refl.
  apply rt1_trans with y. right. assumption. assumption.
Qed.

Lemma incl_rtunion_union : (R!1 U S!1)#1 << (R U S)#1.

Proof.
  intros x y xRy.
  induction xRy. apply rt1_refl.
  apply clos_refl_trans1_trans with y; trivial.
  destruct H.
  apply union_rel_rt_left. apply incl_t_rt. assumption.
  apply union_rel_rt_right. apply incl_t_rt. assumption.
Qed.

End alternative_inclusion.

Lemma incl_union_rtunion : forall A : Type, forall R S : relation A,
  (R U S)#1 << (R!1 U S!1)#1.

Proof.
  intros A R S x y xRy.
  induction xRy. apply rt1_refl.
  apply clos_refl_trans1_trans with y; trivial.
  destruct H.
  apply union_rel_rt_left. apply rt1_trans with y.
  apply t1_step. assumption. apply rt1_refl.
  apply union_rel_rt_right. apply rt1_trans with y.
  apply t1_step. assumption. apply rt1_refl.
Qed.
