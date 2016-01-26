(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Adam Koprowski and Hans Zantema, 2007-03
- Joerg Endrullis and Dimitri Hendriks, 2008-07

General definitions and results about relations.
*)

Set Implicit Arguments.

Require Import LogicUtil Setoid Basics Morphisms List Omega.
Require Export Relations RelMidex.

Arguments inclusion {A} R1 R2.
Arguments same_relation {A} R1 R2.
Arguments transp {A} R x y.
Arguments clos_refl_trans {A} R x y.
Arguments clos_trans {A} R x y.
Arguments reflexive {A} R.
Arguments transitive {A} R.
Arguments antisymmetric {A} R.
Arguments symmetric {A} R.
Arguments equiv {A} R.
Arguments union {A} R1 R2 x y.
Arguments lexprod [A B] _ _ _ _.
Arguments symprod [A B] _ _ _ _.

(***********************************************************************)
(** Notations for some relations and operations on relations. *)

Notation rel := relation.
Notation same_rel := same_relation.

Notation "x << y" := (inclusion x y) (at level 50) : relation_scope.
Notation "R == S" := (same_relation R S) (at level 70).

Notation "x 'U' y" := (union x y) (at level 45) : relation_scope.
Notation "x #" := (clos_refl_trans x) (at level 35) : relation_scope.
Notation "x !" := (clos_trans x) (at level 35) : relation_scope.

Bind Scope relation_scope with relation.

Arguments Scope transp [type_scope relation_scope].
Arguments Scope inclusion [type_scope relation_scope relation_scope].
Arguments Scope clos_refl_trans [type_scope relation_scope].
Arguments Scope union [type_scope relation_scope relation_scope].

Open Scope relation_scope.

Lemma sym A (R : rel A) x y : Symmetric R -> (R x y <-> R y x).

Proof. split_all. Qed.

(***********************************************************************)
(** Empty relation. *)

Definition empty_rel {A} : rel A := fun x y => False.

(***********************************************************************)
(** Relation associated to a boolean function. *)

Definition rel_of_bool A (f : A->A->bool) : rel A :=
  fun x y => f x y = true.

(***********************************************************************)
(** Boolean function associated to a decidable relation. *)

Definition bool_of_rel A (R : rel A) (R_dec : rel_dec R) t u :=
  match R_dec t u with
    | left _ => true
    | _ => false
  end.

(***********************************************************************)
(** Properties of [same_rel]. *)

Global Instance same_rel_equiv A : Equivalence (@same_rel A).

Proof. fo. Qed.

Lemma rel_eq A (R S : rel A) : R == S <-> forall x y, R x y <-> S x y.

Proof. fo. Qed.

Instance same_rel_sub_incl A : subrelation (@same_rel A) (@inclusion A).

Proof. fo. Qed.

(***********************************************************************)
(** Definition of some properties on relations. *)

Definition classic_left_total A B (R : A -> B -> Prop) :=
  forall x, exists y, R x y.

Definition left_total A B (R : A -> B -> Prop) :=
  forall x, {y | R x y}.

Definition functional A B (R : A -> B -> Prop) :=
  forall x y z, R x y -> R x z -> y = z.

Definition finitely_branching A B (R : A -> B -> Prop) :=
  forall x, {l | forall y, R x y <-> In y l}.

Definition irreflexive A (R : rel A) := forall x, ~R x x.

Definition asymmetric A (R : rel A) := forall x y, R x y -> ~R y x.

(** Predicate saying that [f] is an infinite sequence of [R]-steps. *)
Definition IS A (R : rel A) f := forall i, R (f i) (f (S i)).

Definition EIS A (R : rel A) := exists f, IS R f.

Definition NT A (R : rel A) x := exists f, f 0 = x /\ IS R f.

(** Predicate saying that [f] and [g] describe an infinite sequence
  of R-steps modulo E: for all i, f(i) E g(i) R f(i+1). *)
Definition ISMod A (E R : rel A) (f g : nat -> A) :=
  forall i, E (f i) (g i) /\ R (g i) (f (S i)).

(* Called PreOrder in Coq. *)
Definition quasi_ordering A (R : rel A) := reflexive R /\ transitive R.

Definition ordering A (R : rel A) :=
  reflexive R /\ transitive R /\ antisymmetric R.

Definition strict_ordering A (R : rel A) := irreflexive R /\ transitive R.

(***********************************************************************)
(** Strict part. *)

Definition strict_part A (R : rel A) : rel A := fun x y => R x y /\ ~R y x.

(***********************************************************************)
(** Intersection. *)

Definition intersection A (R S : rel A) : rel A := fun x y => R x y /\ S x y.

Lemma intersection_dec A (R S : rel A) (Rdec : rel_dec R) (Sdec : rel_dec S) :
  rel_dec (intersection R S).

Proof.
  intros x y. unfold intersection. case (Rdec x y); case (Sdec x y); intuition.
Defined.

(***********************************************************************)
(** Finitely branching relations. *)

Section finitely_branching.

  Variables (A : Type) (R : rel A) (FB : finitely_branching R).

  Definition sons x := proj1_sig (FB x).

  Lemma in_sons_R : forall x y, In y (sons x) -> R x y.

  Proof. intros x y. exact (proj2 (proj2_sig (FB x) y)). Qed.

  Lemma R_in_sons : forall x y, R x y -> In y (sons x).

  Proof. intros x y. exact (proj1 (proj2_sig (FB x) y)). Qed.

End finitely_branching.

Implicit Arguments in_sons_R [A R x y].
Implicit Arguments R_in_sons [A R x y].

(***********************************************************************)
(** Equivalence relation associated to a PreOrder. *)

Definition inter_transp A (R : rel A) : rel A := fun x y => R x y /\ R y x.

(*COQ: declaring these Lemma's as Instance's creates problems in
FSetUtil and FGraph *)

Lemma inter_transp_Reflexive A (R : rel A) :
  Reflexive R -> Reflexive (inter_transp R).

Proof. fo. Qed.

Lemma inter_transp_Symmetric A (R : rel A) : Symmetric (inter_transp R).

Proof. fo. Qed.

Lemma inter_transp_Transitive A (R : rel A) :
  Transitive R -> Transitive (inter_transp R).

Proof. fo. Qed.

(*WARNING: Do not declare following Lemmas as Instances. *)

Lemma R_inter_transp A (R : rel A) :
  Transitive R -> Proper (inter_transp R ==> inter_transp R ==> impl) R.

Proof. fo. Qed.

Lemma inter_transp_incl A (R : rel A) : inter_transp R << R.

Proof. fo. Qed.

(***********************************************************************)
(** Morphisms wrt [inter_transp]. *)

Lemma inter_transp_1 A1 (R1 : rel A1) B (S : rel B) f :
  Proper (R1 ==> S) f -> Proper (inter_transp R1 ==> inter_transp S) f.

Proof. fo. Qed.

Lemma inter_transp_2 A1 (R1 : rel A1) A2 (R2 : rel A2)
  B (S : rel B) f : Proper (R1 ==> R2 ==> S) f ->
  Proper (inter_transp R1 ==> inter_transp R2 ==> inter_transp S) f.

Proof. fo. Qed.

Lemma Proper_inter_transp_1 A1 (R1 : rel A1) B (S : rel B) f :
  Symmetric R1 -> Proper (R1 ==> S) f -> Proper (R1 ==> inter_transp S) f.

Proof. fo. Qed.

Lemma Proper_inter_transp_2 A1 (R1 : rel A1) A2 (R2 : rel A2)
  B (S : rel B) f : Symmetric R1 -> Symmetric R2 ->
  Proper (R1 ==> R2 ==> S) f -> Proper (R1 ==> R2 ==> inter_transp S) f.

Proof. intros s1 s2 hf x1 y1 e1 x2 y2 e2. split; apply hf; fo. Qed.

Lemma Proper_inter_transp_3 A1 (R1 : rel A1) A2 (R2 : rel A2)
  A3 (R3 : rel A3) B (S : rel B) f :
  Symmetric R1 -> Symmetric R2 -> Symmetric R3 ->
  Proper (R1 ==> R2 ==> R3 ==> S) f ->
  Proper (R1 ==> R2 ==> R3 ==> inter_transp S) f.

Proof. intros s1 s2 s3 hf x1 y1 e1 x2 y2 e2 x3 y3 e3. split; apply hf; fo. Qed.

Lemma Proper_inter_transp_4 A1 (R1 : rel A1) A2 (R2 : rel A2)
  A3 (R3 : rel A3) A4 (R4 : rel A4) B (S : rel B) f :
  Symmetric R1 -> Symmetric R2 -> Symmetric R3 -> Symmetric R4 ->
  Proper (R1 ==> R2 ==> R3 ==> R4 ==> S) f ->
  Proper (R1 ==> R2 ==> R3 ==> R4 ==> inter_transp S) f.

Proof.
  intros s1 s2 s3 s4 hf x1 y1 e1 x2 y2 e2 x3 y3 e3 x4 y4 e4.
  split; apply hf; fo.
Qed.

(***********************************************************************)
(** Properties of [inclusion]. *)

Instance inclusion_Refl A : Reflexive (@inclusion A).

Proof. fo. Qed.

Ltac incl_refl := apply inclusion_Refl.

Instance inclusion_Trans A : Transitive (@inclusion A).

Proof. fo. Qed.

Ltac incl_trans S := apply inclusion_Trans with S; try incl_refl.

Instance inclusion_same_rel A :
  Proper (same_rel ==> same_rel ==> impl) (@inclusion A).

Proof. fo. Qed.

(*FIXME: try to remove*)
Lemma inclusion_elim A (R S : rel A) : R << S -> forall x y, R x y -> S x y.

Proof. auto. Qed.

Implicit Arguments inclusion_elim [A R S x y].

(***********************************************************************)
(** Properties of [IS]. *)

Instance IS_inclusion A : Proper (inclusion ==> eq ==> impl) (@IS A).

Proof. intros R S RS f g fg h i. subst. apply RS. apply h. Qed.

Instance IS_same_rel A : Proper (same_rel ==> eq ==> impl) (@IS A).

Proof.
  intros R S [RS SR] f g fg h. eapply IS_inclusion. apply RS. apply fg. hyp.
Qed.

Instance EIS_same_rel A : Proper (same_rel ==> impl) (@EIS A).

Proof. intros R S RS h. destruct h as [f h]. exists f. rewrite <- RS. hyp. Qed.

Lemma NT_IS_elt A (R : rel A) : forall f k, IS R f -> NT R (f k).

Proof. intros f k hf. exists (fun i => f (i+k)). fo. Qed.

Lemma red_NT A (R : rel A) : forall t u, R t u -> NT R u -> NT R t.

Proof.
  intros t u tu [f [f0 hf]]. subst.
  exists (fun k => match k with 0 => t | S k' => f k' end).
  intuition. intro k. destruct k. hyp. apply hf.
Qed.

(***********************************************************************)
(** Properties of [irreflexive]. *)

Instance irreflexive_inclusion A : Proper (inclusion --> impl) (@irreflexive A).

Proof. fo. Qed.

(***********************************************************************)
(** Monotony. *)

Definition monotone A B (R : rel A) (S : rel B) f :=
  forall x y, R x y -> S (f x) (f y).

Lemma monotone_transp A B (R : rel A) (S : rel B) f :
  monotone R S f -> monotone (transp R) (transp S) f.

Proof. unfold monotone, transp. auto. Qed.

(***********************************************************************)
(** Composition. *)

Definition compose A (R S : rel A) : rel A :=
  fun x y => exists z, R x z /\ S z y.

Notation "R @ S" := (compose R S) (at level 40) : relation_scope.

Instance compose_inclusion A :
  Proper (inclusion ==> inclusion ==> inclusion) (@compose A).

Proof. fo. Qed.

(*FIXME: try to remove*)
Ltac comp := apply compose_inclusion; try incl_refl.

Instance compose_m A :
  Proper (same_rel ==> same_rel ==> same_rel) (@compose A).

Proof. fo. Qed.

Definition absorbs_right A (R S : rel A) := R @ S << R.

Definition absorbs_left A (R S : rel A) := S @ R << R.

Lemma comp_assoc A (R S T : rel A) : (R @ S) @ T << R @ (S @ T).

Proof.
  unfold inclusion. intros. do 4 destruct H. exists x1; split. hyp.
  exists x0; split; hyp.
Qed.

Lemma comp_assoc' A (R S T : rel A) : R @ (S @ T) << (R @ S) @ T.

Proof.
  unfold inclusion. intros. do 2 destruct H. do 2 destruct H0.
  exists x1; split. exists x0; split; hyp. exact H1.
Qed.

Ltac assoc :=
  match goal with
    | |- (?s @ ?t) @ ?u << _ => incl_trans (s @ (t @ u)); try apply comp_assoc
    | |- ?s @ (?t @ ?u) << _ => incl_trans ((s @ t) @ u); try apply comp_assoc'
    | |- _ << (?s @ ?t) @ ?u => incl_trans (s @ (t @ u)); try apply comp_assoc'
    | |- _ << ?s @ (?t @ ?u) => incl_trans ((s @ t) @ u); try apply comp_assoc
  end.

Lemma absorbs_left_rtc A (R S : rel A) : R @ S << S -> R# @ S << S.

Proof.
  intro. unfold inclusion, compose. intros. do 2 destruct H0.
  gen H1. clear H1. elim H0; intros; auto. apply H. exists y0. auto.
Qed.

Lemma absorbs_right_rtc A (R S : rel A) : S @ R << S -> S @ R# << S.

Proof. intros h t v [u [tu uv]]. induction uv; fo. Qed.

(***********************************************************************)
(** Reflexive closure. *)

Definition clos_refl A (R : rel A) : rel A := eq U R.

Notation "x %" := (clos_refl x) (at level 35) : relation_scope.

Instance clos_refl_m' A : Proper (inclusion ==> inclusion) (@clos_refl A).

Proof. fo. Qed.

Instance clos_refl_m A : Proper (same_rel ==> same_rel) (@clos_refl A).

Proof. fo. Qed.

Instance rc_refl A (R : rel A) : Reflexive (R%).

Proof. fo. Qed.

Instance rc_trans A (R : rel A) : Transitive R -> Transitive (R%).

Proof.
  intro. unfold Transitive, clos_refl, union. intros. decomp H0. subst y. hyp.
  decomp H1. subst z. auto. right. apply H with (y := y); hyp.
Qed.

Lemma rc_incl A (R : rel A) : R << R%.

Proof. fo. Qed.

(***********************************************************************)
(** Properties of [clos_trans]. *)

Instance tc_trans A (R : rel A) : Transitive (R!).

Proof. unfold Transitive. intros. apply t_trans with y; hyp. Qed.

Instance clos_trans_inclusion A :
  Proper (inclusion ==> inclusion) (@clos_trans A).

Proof.
  intros R R' H t u H0. elim H0; intros.
  apply t_step. apply H. hyp.
  trans y; hyp.
Qed.

Instance clos_trans_same_rel A :
  Proper (same_rel ==> same_rel) (@clos_trans A).

Proof. intros R S [RS SR]. split; apply clos_trans_inclusion; hyp. Qed.

Lemma incl_tc A (R S : rel A) : R << S -> R << S!.

Proof. fo. Qed.

Lemma trans_tc_incl A (R : rel A) : Transitive R -> R! << R.

Proof.
  unfold transitive, inclusion. intros. induction H0. hyp. 
  apply H with y; hyp.
Qed.

Lemma trans_comp_incl A (R : rel A) : Transitive R -> R @ R << R.

Proof. fo. Qed.

Lemma absorbs_left_tc A (R S : rel A) : R @ S << S -> R! @ S << S.

Proof.
  intro. unfold inclusion, compose. intros. do 2 destruct H0.
  gen H1. clear H1. elim H0; intros; auto. apply H. exists y0. auto.
Qed.

Lemma tc_absorbs_left A (R S : rel A) : R @ S << S -> R @ S! << S!.

Proof.
  intro. unfold inclusion. intros. do 2 destruct H0. generalize x0 y H1 H0.
  induction 1; intros. apply t_step. apply H. exists x1; split; hyp.
  trans y0; auto.
Qed.

Lemma trans_intro A (R : rel A) : R @ R << R <-> Transitive R.

Proof.
  split. unfold Transitive. intros. apply H. exists y. intuition.
  intros h x z [y [xy yz]]. apply (h _ _ _ xy yz).
Qed.

Lemma comp_tc_idem A (R : rel A) : R! @ R! << R!.

Proof.
  unfold inclusion. intros. do 2 destruct H. trans x0; hyp.
Qed.

Lemma tc_min A (R S : rel A) : R << S -> Transitive S -> R! << S.

Proof.
  intros RS Strans. intros x y. induction 1. apply RS. hyp. trans y; hyp.
Qed.

Lemma trans_tc A (R : rel A) : Transitive R -> R! == R.

Proof. intro t. split. apply tc_min. refl. hyp. apply incl_tc. refl. Qed.

Lemma tc_idem A (R : rel A) : R!! == R!.

Proof.
  split. intros x y. induction 1. hyp. trans y; hyp.
  apply incl_tc. refl.
Qed.

Lemma tc_eq A (R S : rel A) : S << R -> R << S! -> R! == S!.

Proof.
  intros SR RSt. split; apply tc_min. hyp. apply tc_trans.
  trans R. hyp. apply incl_tc. refl. apply tc_trans.
Qed.

Lemma tc_incl_trans A (R S : rel A) : Transitive S -> R << S -> R! << S.

Proof. intros S_trans RS. intros t u tu; revert t u tu. induction 1; fo. Qed.

Instance tc_proper A (E R : rel A) : Reflexive E ->
  Proper (E ==> E ==> impl) R -> Proper (E ==> E ==> impl) (R!).

Proof.
  intros E_refl RE x x' xx' y y' yy' xy. revert x y xy x' xx' y' yy'.
  induction 1; intros x' xx' y' yy'.
  apply t_step. eapply RE. apply xx'. apply yy'. hyp.
  trans y. apply IHxy1. hyp. refl. apply IHxy2. refl. hyp.
Qed.

Instance clos_trans_morph A (R : relation A) (eqA : relation A) :
  Equivalence eqA ->
  Proper (eqA ==> eqA ==> iff) R ->
  Proper (eqA ==> eqA ==> iff) (clos_trans R).

Proof.
  intros.
  reduce. split; intros.
  revert y y0 H1 H2.
  induction H3; intros.
  rewrite H2, H3 in H1. now constructor.
  trans y. apply IHclos_trans1; eauto. reflexivity.
  apply IHclos_trans2; eauto. reflexivity.

  revert x x0 H1 H2.
  induction H3; intros.
  rewrite <- H2, <- H3 in H1. now constructor.
  trans y.
  apply IHclos_trans1; eauto. reflexivity.
  apply IHclos_trans2; eauto. reflexivity.
Qed.

Lemma tc_step_l A (R : rel A) x y :
  R! x y -> R x y \/ (exists2 z, R x z & R! z y).

Proof.
  compute; intro xy; induction xy.
  left; trivial.
  inversion IHxy1; inversion IHxy2; right; solve [eauto |
    inversion H; try inversion H0; exists x0; 
    [trivial | constructor 2 with y; auto]].
Qed.

Lemma tc_step_r A (R : rel A) x y :
  R! x y -> R x y \/ (exists2 z, R! x z & R z y).

Proof.
  compute; intro xy; induction xy.
  left; trivial.
  inversion_clear IHxy1; inversion_clear IHxy2; right;
    solve [eauto | inversion H0; exists x0; 
    [constructor 2 with y; auto | trivial]].
Qed.

Lemma tc_transp A (R : rel A) : transp (R!) == (transp R)!.

Proof.
  intros; split; compute.
  induction 1.
  constructor; trivial.
  constructor 2 with y; auto.
  induction 1.
  constructor; trivial.
  constructor 2 with y; auto.
Qed.

(***********************************************************************)
(** Symmetric closure of a relation. *)

Section clos_sym.

  Variable (A : Type) (R : rel A).

  Inductive clos_sym : rel A :=
  | s_step : forall x y, R x y -> clos_sym x y
  | s_sym : forall x y, clos_sym y x -> clos_sym x y.

  Global Instance sc_sym : Symmetric clos_sym.

  Proof. intros x y xy. apply s_sym. hyp. Qed.
 
End clos_sym.

(***********************************************************************)
(** Reflexive, transitive and symmetric closure of a relation. *)

Section clos_equiv.

  Variable (A : Type) (R : rel A).

  Inductive clos_equiv : rel A :=
  | e_step : forall x y, R x y -> clos_equiv x y
  | e_refl : forall x, clos_equiv x x
  | e_trans : forall x y z, clos_equiv x y -> clos_equiv y z -> clos_equiv x z
  | e_sym : forall x y, clos_equiv x y -> clos_equiv y x.

  Global Instance ec_equiv : Equivalence clos_equiv.

  Proof. exact (Build_Equivalence _ e_refl e_sym e_trans). Qed.

End clos_equiv.

Instance clos_equiv_incl A : Proper (inclusion ==> inclusion) (@clos_equiv A).

Proof.
  intros R S RS x y; revert x y; induction 1.
  apply e_step. fo. refl. trans y; fo. sym. fo.
Qed.

Lemma ec_min A (R S : rel A) : Equivalence S -> R << S -> clos_equiv R << S.

Proof.
  intros S_eq RS. intros u v; revert u v; induction 1.
  fo. refl. trans y; hyp. hyp.
Qed.

(***********************************************************************)
(** Properties of [union]. *)

Instance union_inclusion A :
  Proper (inclusion ==> inclusion ==> inclusion) (@union A).

Proof. fo. Qed.

(*FIXME: try to remove*)
Ltac union := apply union_inclusion; try incl_refl.

Instance union_same_rel A :
  Proper (same_rel ==> same_rel ==> same_rel) (@union A).

Proof. fo. Qed.

Lemma union_commut : forall A (R S : rel A), R U S == S U R.

Proof. fo. Qed.

Lemma union_assoc : forall A (R S T : rel A), (R U S) U T == R U (S U T).

Proof. fo. Qed.

Lemma comp_union_l : forall A (R S T : rel A), (R U S) @ T == (R @ T) U (S @ T).

Proof. fo. Qed.

Lemma comp_union_r : forall A (R S T : rel A), T @ (R U S) == (T @ R) U (T @ S).

Proof. fo. Qed.

Lemma union_empty_r : forall A (R : rel A), R U empty_rel == R.

Proof. fo. Qed.

Lemma union_empty_l : forall A (R : rel A), empty_rel U R == R.

Proof. fo. Qed.

Lemma incl_union_l : forall A (R S T : rel A), R << S -> R << S U T.

Proof. fo. Qed.

Lemma incl_union_r : forall A (R S T : rel A), R << T -> R << S U T.

Proof. fo. Qed.

Lemma union_incl : forall A (R R' S : rel A), R U R' << S <-> R << S /\ R' << S.

Proof. fo. Qed.

(***********************************************************************)
(** Properties of [clos_refl_trans]. *)

Instance rtc_refl A (R : rel A) : Reflexive (R#).

Proof. fo. Qed.

Instance rtc_trans A (R : rel A) : Transitive (R#).

Proof. unfold Transitive. intros. eapply rt_trans. apply H. hyp. Qed.

Instance clos_refl_trans_inclusion A :
  Proper (inclusion ==> inclusion) (@clos_refl_trans A).

Proof.
  intro. unfold inclusion. intros. elim H0; intros.
  apply rt_step. apply H. hyp. refl. trans y1; hyp.
Qed.

Instance clos_refl_trans_same_rel A :
  Proper (same_rel ==> same_rel) (@clos_refl_trans A).

Proof. intros R S [RS SR]. split; apply clos_refl_trans_inclusion; hyp. Qed.

Lemma rtc_incl A (R : rel A) : R << R#.

Proof. fo. Qed.

Lemma tc_incl_rtc A (R : rel A) : R! << R#.

Proof. induction 1. apply rt_step. hyp. trans y; hyp. Qed.

Lemma tc_split A (R : rel A) : R! << R @ R#.

Proof.
  unfold inclusion. induction 1. exists y. split. hyp. refl.
  destruct IHclos_trans1. destruct H1. exists x0. split. hyp.
  trans y. hyp. apply inclusion_elim with (R:=R!). apply tc_incl_rtc. hyp.
Qed.

Lemma rc_incl_rtc A (R : rel A) : R% << R#.

Proof.
  unfold inclusion, clos_refl. intros. destruct H.
  subst y. refl. apply rt_step. exact H.
Qed.

Lemma rtc_split A (R : rel A) : R# << eq U R!.

Proof.
  unfold inclusion, union. intros. elim H.
  intros. right. apply t_step. hyp.
  intro. left. refl.
  intros. destruct H1; destruct H3.
  left. trans y0; hyp.
  subst y0. right. hyp.
  subst y0. right. hyp.
  right. trans y0; hyp.
Qed.

Lemma rtc_split_eq A (R : rel A) : R# == eq U R!.

Proof.
  split. apply rtc_split. rewrite union_incl. split.
  intros x y h. subst. refl. apply tc_incl_rtc.
Qed.

Lemma rtc_split2 A (R : rel A) : R# << eq U R @ R#.

Proof.
  unfold inclusion, union. intros. elim H; clear H x y; intros.
  right. exists y; split. exact H. refl. auto. destruct H0.
  subst y. destruct H2. auto. destruct H0. right. exists x0. auto.
  do 2 destruct H0. right. exists x0. split. exact H0.
  trans y; auto.
Qed.

Lemma tc_split_inv A (R : rel A) : R# @ R << R!.

Proof.
  intros x y RRxy. destruct RRxy as [z [Rxz Rzy]].
  destruct (rtc_split Rxz).
  rewrite H. intuition.
  constructor 2 with z. hyp.
  constructor 1. hyp.
Qed.

Lemma tc_merge A (R : rel A) : R @ R# << R!.

Proof.
  unfold inclusion. intros. destruct H. destruct H.
  ded (rtc_split H0). destruct H1; subst.
  apply t_step; hyp. trans x0. apply t_step. hyp. hyp.
Qed.

Lemma rtc_transp A (R : rel A) : transp (R#) << (transp R)#.

Proof.
  unfold inclusion. induction 1. apply rt_step. hyp. refl. trans y; hyp.
Qed.

Lemma incl_rtc_rtc A (R S : rel A) : R << S# -> R# << S#.

Proof. unfold inclusion. induction 2. apply H. hyp. refl. trans y; hyp. Qed.

Lemma comp_rtc_idem A (R : rel A) : R# @ R# << R#.

Proof. unfold inclusion. intros. do 2 destruct H. trans x0; hyp. Qed.

Lemma trans_rtc_incl A (R : rel A) : Reflexive R -> Transitive R -> R# << R.

Proof. intros R_refl R_trans x y. induction 1. hyp. refl. trans y; hyp. Qed.

Lemma rtc_invol A (R : rel A) : R # # == R #.

Proof.
  split. intros x y. induction 1. hyp. refl. trans y; hyp. apply rtc_incl.
Qed.

Lemma rtc_intro_seq A (R : rel A) f i : forall j, i <= j ->
  (forall k, i <= k < j -> R (f k) (f (1+k))) -> R# (f i) (f j).

Proof.
  cut (forall n, (forall k, i <= k < i + n -> R (f k) (f (1+k))) ->
    R# (f i) (f (n+i))).
  intros h j ij hij. assert (j = (j-i) + i). omega.
  rewrite H. apply h.
  intros k hk. apply hij. omega.
  induction n; intro h. refl. trans (f (n+i)).
  apply IHn. intros k hk. apply h. omega.
  apply rt_step. apply h. omega.
Qed.

Lemma rtc_min A (R S : rel A) : PreOrder S -> R << S -> R# << S.

Proof.
  intros S_PO RS. intros u v; revert u v; induction 1.
  fo. refl. trans y; hyp.
Qed.

Instance rtc_sym A (R : rel A) : Symmetric R -> Symmetric (R#).

Proof.
  intros R_sym x; revert x; induction 1.
  apply rt_step. hyp. refl. trans y; hyp.
Qed.

(***********************************************************************)
(** Properties of [transp]. *)

Instance transp_inclusion A : Proper (inclusion ==> inclusion) (@transp A).

Proof. fo. Qed.

Instance transp_same_rel A : Proper (same_rel ==> same_rel) (@transp A).

Proof. fo. Qed.

(*COQ: declaring these lemmas as Global Instance makes Coq loop
  later in some other files *)

Lemma transp_refl A (R : rel A) : Reflexive R -> Reflexive (transp R).

Proof. auto. Qed.

Lemma transp_trans A (R : rel A) : Transitive R -> Transitive (transp R).

Proof. fo. Qed.

Lemma transp_sym A (R : rel A) : Symmetric R -> Symmetric (transp R).

Proof. fo. Qed.

Lemma transp_invol A (R : rel A) : transp (transp R) == R.

Proof. fo. Qed.

Lemma transp_union A (R S : rel A) : transp (R U S) == transp R U transp S.

Proof. fo. Qed.

(***********************************************************************)
(** Relations between closures, union and composition. *)

Lemma rtc_comp_permut A (R S : rel A) : R# @ (R# @ S)# << (R# @ S)# @ R#.

Proof.
  unfold inclusion. intros. do 2 destruct H. ded (rtc_split2 H0). destruct H1.
  subst x0. exists x; split. refl. exact H.
  do 4 destruct H1. exists y; split. trans x1.
  apply rt_step. exists x2; split. trans x0; hyp.
  hyp. hyp. refl.
Qed.

Lemma rtc_union A (R S : rel A) : (R U S)# << (R# @ S)# @ R#.

Proof.
  unfold inclusion. intros. elim H; intros.
  (* step *)
  destruct H0. exists x0; split. refl. apply rt_step. exact H0.
  exists y0; split. apply rt_step. exists x0; split. refl. exact H0.
  refl.
  (* refl *)
  exists x0; split; refl.
  (* trans *)
  do 2 destruct H1. do 2 destruct H3.
  assert (h : ((R# @ S)# @ clos_refl_trans R) x1 x2).
  apply inclusion_elim with (R := (R# @ clos_refl_trans (R# @ S))).
  apply rtc_comp_permut. exists y0; split; hyp.
  destruct h. destruct H6. exists x3; split.
  trans x1; hyp. trans x2; hyp.
Qed.

Lemma rtc_comp A (R S : rel A) : R# @ S << S U R! @ S.

Proof.
  unfold inclusion. intros. do 2 destruct H. ded (rtc_split H). destruct H1.
  subst x0. left. exact H0. right. exists x0; split; hyp.
Qed.

Lemma union_fact A (R S : rel A) : R U R @ S << R @ S%.

Proof.
  unfold inclusion. intros. destruct H.
  exists y; split; unfold clos_refl, union; auto.
  do 2 destruct H. exists x0; split; unfold clos_refl, union; auto.
Qed.

Lemma union_fact2 A (R S : rel A) : R @ S U R << R @ S%.

Proof. incl_trans (R U R @ S). apply union_commut. apply union_fact. Qed.

Lemma incl_rc_rtc A (R S : rel A) : R << S! -> R% << S#.

Proof.
  intro. unfold inclusion. intros. destruct H0. subst y. refl.
  apply inclusion_elim with (R := S!). apply tc_incl_rtc. apply H. exact H0.
Qed.

Lemma incl_tc_rtc A (R S : rel A) : R << S# -> R! << S#.

Proof. intro. unfold inclusion. induction 1. apply H. hyp. trans y; hyp. Qed.

Lemma rtc_comp_modulo A (R S : rel A) : R# @ (R# @ S)! << (R# @ S)!.

Proof.
  unfold inclusion. intros. do 2 destruct H.
  ded (tc_split H0). do 2 destruct H1. do 2 destruct H1.
  ded (rtc_split H2). destruct H4. subst x1.
  apply t_step. exists x2. intuition. trans x0; hyp.
  trans x1. apply t_step. exists x2. intuition.
  trans x0; hyp. exact H4.
Qed.

Lemma tc_union A (R S : rel A) : (R U S)! << R! U (R# @ S)! @ R#.

Proof.
  unfold inclusion. induction 1. destruct H. left. apply t_step. exact H.
  right. exists y. intuition. apply t_step. exists x. intuition.
  destruct IHclos_trans1. destruct IHclos_trans2.
  left. trans y; hyp.
  right. do 2 destruct H2. exists x0. intuition.
  apply rtc_comp_modulo. exists y. intuition. apply tc_incl_rtc. exact H1.
  right. do 2 destruct H1. destruct IHclos_trans2. exists x0.
  intuition. trans y. exact H2. apply tc_incl_rtc. exact H3.
  do 2 destruct H3. exists x1. intuition. trans x0. exact H1.
  apply rtc_comp_modulo. exists y. intuition.
Qed.

(***********************************************************************)
(** Commutation properties. *)

Section commut.

  Variables (A : Type) (R S : rel A) (commut : R @ S << S @ R).

  Lemma commut_rtc : R# @ S << S @ R#.

  Proof.
    unfold inclusion. intros. do 2 destruct H. generalize x x0 H y H0.
    clear H0 y H x0 x. induction 1; intros.
    assert ((S @ R) x y0). apply commut. exists y. intuition.
    do 2 destruct H1. exists x0. intuition.
    exists y. intuition.
    ded (IHclos_refl_trans2 _ H1). do 2 destruct H2.
    ded (IHclos_refl_trans1 _ H2). do 2 destruct H4.
    exists x1. intuition. trans x0; hyp.
  Qed.

  Lemma commut_rtc_inv : R @ S# << S# @ R.

  Proof.
    unfold inclusion. intros. do 2 destruct H. generalize x0 y H0 x H.
    clear H x x0 H0 y. induction 1; intros.
    assert ((S @ R) x0 y). apply commut. exists x. intuition.
    do 2 destruct H1. exists x1. intuition.
    exists x0. intuition.
    ded (IHclos_refl_trans1 _ H). do 2 destruct H0.
    ded (IHclos_refl_trans2 _ H1). do 2 destruct H2.
    exists x2. intuition. apply rtc_trans with x1; hyp.
  Qed.

  Lemma commut_tc : R! @ S << S @ R!.

  Proof.
    intros x y H. destruct H as [z Hxy].
    destruct (tc_split (proj1 Hxy)) as [z' Hz'].
    assert (SE : (S @ R#) z' y). apply commut_rtc. exists z. intuition.
    destruct SE as [x' Rx'].
    assert (SRx : (S @ R) x x'). apply commut. exists z'. intuition.
    destruct SRx as [y' Sy']. exists y'. split. intuition.
    apply tc_merge. exists x'. intuition.
  Qed.

  Lemma commut_tc_inv : R @ S! << S! @ R.

  Proof.
    intros x y H. destruct H as [z Hxy].
    destruct (tc_split (proj2 Hxy)) as [z' Hz'].
    assert (SRx : (S @ R) x z'). apply commut. exists z. intuition.
    destruct SRx as [y' Sy']. 
    assert (SE : (S# @ R) y' y). apply commut_rtc_inv. exists z'. intuition.
    destruct SE as [x' Sx']. exists x'. split; try intuition.
    apply tc_merge. exists y'. intuition.
  Qed.

  Lemma commut_comp T : R @ (S @ T) << (S @ R) @ T.

  Proof. rewrite comp_assoc', commut. refl. Qed.

  Lemma comp_incl_assoc T V : R @ S << T -> R @ (S @ V) << T @ V.

  Proof. intro h. rewrite comp_assoc', h. refl. Qed.

End commut.

(***********************************************************************)
(** Inverse image. *)

Section inverse_image.

  Variables (A B : Type) (R : rel B) (f : A->B).

  Definition Rof : rel A := fun a a' => R (f a) (f a').

  (*COQ: declaring these lemmas as Global Instance makes Coq loop
  later in some other files *)

  Lemma Rof_refl : Reflexive R -> Reflexive Rof.

  Proof. fo. Qed.

  Lemma Rof_trans : Transitive R -> Transitive Rof.

  Proof. fo. Qed.

  Lemma Rof_sym : Symmetric R -> Symmetric Rof.

  Proof. fo. Qed.

  Variable F : A -> B -> Prop.

  Definition RoF : rel A :=
    fun a a' => exists b', F a' b' /\ forall b, F a b -> R b b'.

End inverse_image.

Instance Rof_incl A B :
  Proper (inclusion ==> Logic.eq ==> inclusion) (@Rof A B).

Proof. intros R S RS f g fg. subst g. fo. Qed.

(***********************************************************************)
(** Alternative definition of the transitive closure, more convenient
for some inductive proofs. *)

Inductive clos_trans1 A (R : rel A) : rel A :=
| t1_step : forall x y, R x y -> clos_trans1 R x y
| t1_trans : forall x y z, R x y -> clos_trans1 R y z -> clos_trans1 R x z.

Notation "x !1" := (clos_trans1 x) (at level 35) : relation_scope.

Instance tc1_trans A (R : rel A) : Transitive (R!1).

Proof.
  induction 1; intro H1.
  exact (t1_trans x H H1).
  exact (t1_trans x H (IHclos_trans1 H1)).
Qed.

Lemma tc1_eq A (R : rel A) x y : R!1 x y <-> R! x y.

Proof.
  split; induction 1.
  apply t_step. hyp. trans y. apply t_step. hyp. hyp.
  apply t1_step. hyp. trans y; hyp.
Qed.

(***********************************************************************)
(** Alternative definition of the reflexive and transitive closure,
more convenient for some inductive proofs. *)

Inductive clos_refl_trans1 A (R : rel A) : rel A :=
| rt1_refl : forall x, clos_refl_trans1 R x x
| rt1_trans : forall x y z,
  R x y -> clos_refl_trans1 R y z -> clos_refl_trans1 R x z.

Notation "x #1" := (clos_refl_trans1 x) (at level 9) : relation_scope.

Instance rtc1_trans A (R : rel A) : PreOrder (R#1).

Proof.
  split; intro x. apply rt1_refl.
  induction 1; intro H1. hyp.
  exact (rt1_trans x H (IHclos_refl_trans1 H1)).
Qed.

Lemma rtc1_eq A (R : rel A) x y : R#1 x y <-> R# x y.

Proof.
  split; induction 1.
  refl. trans y. apply rt_step. hyp. hyp.
  eapply rt1_trans. apply H. refl. refl. trans y; hyp.
Qed.

Lemma tc1_incl_rtc1 A (R : rel A) : R!1 << R#1.

Proof.
  induction 1.
  eapply rt1_trans. apply H. refl.
  eapply rt1_trans. apply H. hyp.
Qed.

(*REMOVE?
Lemma incl_rt_rt_rt A (R : rel A) : R#1 @ R#1 << R#1.

Proof.
  intros x y [z [xRz zRy]]. induction xRz.
  trivial.
  apply rt1_trans with y0. hyp. 
  apply IHxRz. hyp.
Qed.*)

Lemma rtc1_union A (R S : rel A) : (R U S)#1 << (S#1 @ R)#1 @ S#1.

Proof.
  intros x y xRSy. induction xRSy as [ | x y z xRSy yRSz]. 
  exists x. split; refl.
  destruct IHyRSz as [m [ym mz]].
  destruct ym as [m | m n o mn no oz].
  induction xRSy as [xRy | xSy].
  exists m. split; trivial. apply rt1_trans with m.
  exists x. split; trivial. refl. refl.
  exists x. split. refl. apply rt1_trans with m; trivial.
  exists o. split; trivial.
  induction xRSy as [xRy | xSy].
  apply rt1_trans with m.
  exists x. split. refl. hyp.
  apply rtc1_trans with n; trivial.
  apply rt1_trans with n; trivial. refl.
  apply rt1_trans with n.
  destruct mn as [q [mq qn]]. exists q. split; trivial.
  apply rt1_trans with m; hyp. hyp.
Qed.

Lemma union_rel_rt1_left A (R S : rel A) : R#1 << (R U S)#1.

Proof.
  intros x y xRy. induction xRy. refl.
  apply rt1_trans with y. left. hyp. hyp.
Qed.

Lemma union_rel_rt1_right A (R S : rel A) : S#1 << (R U S)#1.

Proof.
  intros x y xRy. induction xRy. refl.
  apply rt1_trans with y. right. hyp. hyp.
Qed.

Lemma incl_rt1_union_union A (R S : rel A) : (R!1 U S!1)#1 << (R U S)#1.

Proof.
  intros x y xRy. induction xRy. refl.
  apply rtc1_trans with y; trivial.
  destruct H.
  apply union_rel_rt1_left. apply tc1_incl_rtc1. hyp.
  apply union_rel_rt1_right. apply tc1_incl_rtc1. hyp.
Qed.

Lemma incl_union_rt1_union A (R S : rel A) : (R U S)#1 << (R!1 U S!1)#1.

Proof.
  intros x y xRy. induction xRy. refl.
  apply rtc1_trans with y; trivial.
  destruct H.
  apply union_rel_rt1_left. apply rt1_trans with y.
  apply t1_step. hyp. refl.
  apply union_rel_rt1_right. apply rt1_trans with y.
  apply t1_step. hyp. refl.
Qed.

Lemma comm_s_rt1 A (R S : rel A) :
  S@(R!1) << (R!1)@(S!1) -> (S!1)@(R!1) << (R!1)@(S!1).

Proof.
  intros comm x y [z [H1 H2]].
  induction H1 as [x z H | x y' z H H0 IH].
  apply comm. 
  exists z; split; hyp.
  assert (H1 := IH H2); clear IH H2.
  destruct H1 as [u [H2 H3]].
  assert ((R!1 @ S!1) x u).
  apply comm. exists y'; split; hyp.
  destruct H1 as [m [xRm mSu]].
  exists m; split. hyp.
  exact (tc1_trans mSu H3).
Qed.

Lemma comm_s_r A (R S : rel A) :
  S@R << (R!1)@(S#1) -> (R U S)#1 @ R @ (R U S)#1 << (R!1) @ (R U S)#1.

Proof.
  intros comm x y [z2 [[z1 [xRSz1 z1Rz2] z2RSy]]].
  induction xRSz1 as [ | m n z1 mRSn nRSz1 IH].
  exists z2. split. apply t1_step. hyp. hyp.
  (* m RUS n RUS# z1 R z2 RUS# y *)
  assert (((R!1) @ (R U S)#1) n y) as mRedy. apply IH. hyp.
  (* m RUS n R!1@RUS#1 y *)
  clear nRSz1 z1Rz2 z2RSy IH z1 z2.
  destruct mRedy as [o [nRo oRSy]].
  (* m RUS n R!1 o RUS#1 y *)
  induction mRSn.
  (* m R n *)
  exists o. split; auto. apply t1_trans with n; hyp.
  (* m S n *)
  destruct nRo as [o p oRp | o p q oRp pRq ];

  assert (((R!1)@(S#1)) m p) as mRedp. apply comm; exists o; split; hyp.
  destruct mRedp as [x [mRx xSp]].
  exists x. split. hyp.
  apply rtc1_trans with p.
  apply union_rel_rt1_right. hyp. hyp.

  assert (((R!1)@(S#1)) m p) as mRedp. apply comm; exists o; split; hyp.
  destruct mRedp as [x [mRx xSp]].
  exists x. split. hyp. hyp.
  destruct mRedp as [n [mRn sSp]].
  exists n; split. hyp.
  apply rtc1_trans with q.
  apply rtc1_trans with p.
  apply union_rel_rt1_right. hyp.
  apply union_rel_rt1_left. apply tc1_incl_rtc1. hyp.    
  hyp.
Qed.

(***********************************************************************)
(** Morphisms wrt [inclusion] and [same_rel] *)

Lemma eq_Refl_rel A (R : rel A) : Reflexive R -> eq << R.

Proof. intros hR x y xy. subst y. apply hR. Qed.

Instance Reflexive_same_rel A : Proper (same_rel ==> impl) (@Reflexive A).

Proof. fo. Qed.

Instance Symmetric_same_rel A : Proper (same_rel ==> impl) (@Symmetric A).

Proof. fo. Qed.

Instance Transitive_same_rel A : Proper (same_rel ==> impl) (@Transitive A).

Proof.
  intros R S e h x y z xy yz. rewrite rel_eq in e. rewrite <- e in *.
  apply h with y; hyp.
Qed.

Instance Equivalence_same_rel A : Proper (same_rel ==> impl) (@Equivalence A).

Proof. intros R S RS [hr hs ht]. constructor; rewrite <- RS; hyp. Qed.

Lemma Proper_inclusion_1 A1 B f :
  Proper (@inclusion A1 --> @inclusion B ==> impl)
  (fun R1 S => Proper (R1 ==> S) f).

Proof. fo. Qed.

Lemma Proper_inclusion_2 A1 A2 B f :
  Proper (@inclusion A1 --> @inclusion A2 --> @inclusion B ==> impl)
  (fun R1 R2 S => Proper (R1 ==> R2 ==> S) f).

Proof.
  intros R1 R1' R1'R1 R2 R2' R2'R2 S S' SS' hf x1 x1' x1x1' x2 x2' x2x2'.
  apply R1'R1 in x1x1'. apply R2'R2 in x2x2'. apply SS'. apply hf; hyp.
Qed.

Lemma Proper_inclusion_3 A1 A2 A3 B f : Proper
  (@inclusion A1 --> @inclusion A2 --> @inclusion A3 --> @inclusion B ==> impl)
  (fun R1 R2 R3 S => Proper (R1 ==> R2 ==> R3 ==> S) f).

Proof.
  intros R1 R1' R1'R1 R2 R2' R2'R2 R3 R3' R3'R3 S S' SS' hf
    x1 x1' x1x1' x2 x2' x2x2' x3 x3' x3x3'.
  apply R1'R1 in x1x1'. apply R2'R2 in x2x2'. apply R3'R3 in x3x3'.
  apply SS'. apply hf; hyp.
Qed.

Lemma Proper_inclusion_4 A1 A2 A3 A4 B f : Proper
  (@inclusion A1 --> @inclusion A2 --> @inclusion A3 --> @inclusion A4 -->
    @inclusion B ==> impl)
  (fun R1 R2 R3 R4 S => Proper (R1 ==> R2 ==> R3 ==> R4 ==> S) f).

Proof.
  intros R1 R1' R1'R1 R2 R2' R2'R2 R3 R3' R3'R3 R4 R4' R4'R4 S S' SS' hf
    x1 x1' x1x1' x2 x2' x2x2' x3 x3' x3x3' x4 x4' x4x4'.
  apply R1'R1 in x1x1'. apply R2'R2 in x2x2'. apply R3'R3 in x3x3'.
  apply R4'R4 in x4x4'. apply SS'. apply hf; hyp.
Qed.

Instance Proper2_proper A (E : rel A) :
  Proper (same_rel ==> impl) (Proper (E ==> E ==> impl)).

Proof.
  intros R S [RS SR] h x x' xx' y y' yy' xy.
  apply RS. eapply h. apply xx'. apply yy'. apply SR. hyp.
Qed.

(***********************************************************************)
(** Extension to [option A] of a relation on [A] so that it is
reflexive on [None]. *)

Section opt_r.

  Variables (A : Type) (R : rel A).

  Inductive opt_r : rel (option A) :=
  | opt_r_None : opt_r None None
  | opt_r_Some : forall a b, R a b -> opt_r (Some a) (Some b).

  Global Instance opt_r_Refl : Reflexive R -> Reflexive opt_r.

  Proof. intros h [x|]. apply opt_r_Some. refl. apply opt_r_None. Qed.

  Global Instance opt_r_Sym : Symmetric R -> Symmetric opt_r.

  Proof.
    intros h x y xy. inversion xy; subst. hyp. apply opt_r_Some. sym. hyp.
  Qed.

  Global Instance opt_r_Trans : Transitive R -> Transitive opt_r.

  Proof.
    intros h x y z xy yz. inversion xy; inversion yz; subst; try discr.
    apply opt_r_None. inversion H3; subst. apply opt_r_Some. trans b; hyp.
  Qed.

  Global Instance Some_Proper : Proper (R ==> opt_r) (@Some A).

  Proof. intros x y xy. apply opt_r_Some. hyp. Qed.

End opt_r.

(****************************************************************************)
(** Extension of a relation on [A] to [option A] so that it is
irreflexive on [None]. *)

Section opt.

  Variables (A : Type) (R : rel A).

  Inductive opt : rel (option A) :=
  | opt_intro : forall x y, R x y -> opt (Some x) (Some y).

  Global Instance opt_trans : Transitive R -> Transitive opt.

  Proof.
    intros R_trans x y z xy yz. inversion xy; inversion yz; clear xy yz; subst.
    inversion H3; clear H3; subst. apply opt_intro. trans y0; hyp.
  Qed.

  Global Instance opt_sym : Symmetric R -> Symmetric opt.

  Proof.
    intros R_sym x y xy. inversion xy; clear xy; subst. apply opt_intro. hyp.
  Qed.

  Global Instance opt_opt_r E : Proper (E ==> E ==> impl) R ->
    Proper (opt_r E ==> opt_r E ==> impl) opt.

  Proof.
    intros R_E x x' xx' y y' yy' xy.
    inversion xy; inversion xx'; inversion yy'; clear xy xx' yy'; subst;
      try discr. inversion H6; inversion H3; clear H6 H3; subst.
    apply opt_intro. eapply R_E. apply H2. apply H5. hyp.
  Qed.

  Lemma opt_absorbs_right_opt_r E : R @ E << R -> opt @ opt_r E << opt.

  Proof.
    intros RE x z [y [xy yz]].
    inversion xy; clear xy; subst. inversion yz; clear yz; subst.
    apply opt_intro. apply RE. exists y0. fo.
  Qed.

  Lemma opt_absorbs_left_opt_r E : E @ R << R -> opt_r E @ opt << opt.

  Proof.
    intros ER x z [y [xy yz]].
    inversion yz; clear yz; subst. inversion xy; clear xy; subst.
    apply opt_intro. apply ER. exists x0. fo.
  Qed.

End opt.

Instance opt_incl A : Proper (inclusion ==> inclusion) (@opt A).

Proof.
  intros R S RS x y xy. inversion xy; clear xy; subst. apply opt_intro. fo.
Qed.

Instance opt_proper A (E1 E2 R : rel A) :
  Proper (E1 ==> E2 ==> impl) R -> Proper (opt E1 ==> opt E2 ==> impl) (opt R).

Proof.
  intros h x x' xx' y y' yy' xy. inversion xx'; clear xx'; subst.
  inversion yy'; clear yy'; subst. inversion xy; clear xy; subst.
  apply opt_intro. eapply h. apply H. apply H0. hyp.
Qed.

Lemma opt_absorbs_right A (R E : rel A) :
  R @ E << R -> opt R @ opt E << opt R.

Proof.
  intros RE x z [y [xy yz]].
  inversion xy; clear xy; subst. inversion yz; clear yz; subst.
  apply opt_intro. apply RE. exists y0. fo.
Qed.

Lemma opt_absorbs_left A (R E : rel A) :
  E @ R << R -> opt E @ opt R << opt R.

Proof.
  intros ER x z [y [xy yz]].
  inversion yz; clear yz; subst. inversion xy; clear xy; subst.
  apply opt_intro. apply ER. exists x0. fo.
Qed.

(***********************************************************************)
(** Restriction of a relation to some set. *)

Section restrict.

  Variables (A : Type) (P : A -> Prop) (R : rel A).

  Definition restrict : rel A := fun x y => P x /\ R x y.

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

Lemma restrict_union A (P : A -> Prop) R S :
  restrict P (R U S) == restrict P R U restrict P S.

Proof. fo. Qed.
