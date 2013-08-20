(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-02-17
- Adam Koprowski and Hans Zantema, 2007-03
- Joerg Endrullis and Dimitri Hendriks, 2008-07

General definitions and results about relations.
*)

Set Implicit Arguments.

Require Import LogicUtil Setoid Basics Morphisms List.
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

Ltac class := fold impl; auto with typeclass_instances.

(***********************************************************************)
(** Notations for some relations and operations on relations. *)

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

(***********************************************************************)
(** Empty relation. *)

Definition empty_rel {A} : relation A := fun x y => False.

(***********************************************************************)
(** Relation associated to a boolean function. *)

Definition rel A (f : A->A->bool) : relation A := fun x y => f x y = true.

(***********************************************************************)
(** Boolean function associated to a decidable relation. *)

Definition brel A (R : relation A) (R_dec : rel_dec R) t u :=
  match R_dec t u with
    | left _ => true
    | _ => false
  end.

(***********************************************************************)
(** Equivalence on relations *)

Instance same_relation_equiv A : Equivalence (@same_relation A).

Proof. fo. Qed.

Lemma rel_eq : forall A (R S : relation A),
  R == S <-> forall x y, R x y <-> S x y.

Proof. fo. Qed.

(***********************************************************************)
(** Definition of some properties on relations. *)

Section basic_def1.

  Variables (A B : Type) (R : A -> B -> Prop).

  Definition classic_left_total := forall x, exists y, R x y.

  Definition left_total := forall x, {y | R x y}.

  Definition functional := forall x y z, R x y -> R x z -> y = z.

  Definition finitely_branching := forall x, {l | forall y, R x y <-> In y l}.

End basic_def1.

Section basic_def2.

  Variables (A : Type) (E R : relation A).

  Definition irreflexive := forall x, ~R x x.

  Definition asymmetric := forall x y, R x y -> ~R y x.

  (* Predicate saying that [f] is an infinite sequence of [R]-steps. *)
  Definition IS f := forall i, R (f i) (f (S i)).

  Definition EIS := exists f, IS f.

  Definition NT x := exists f, f 0 = x /\ IS f.

  (* Predicate saying that [f] and [g] describe an infinite sequence
  of R-steps modulo E: for all i, f(i) E g(i) R f(i+1). *)
  Definition ISMod (f g : nat -> A) :=
    forall i, E (f i) (g i) /\ R (g i) (f (S i)).

End basic_def2.

Section basic_def3.

  Variables (A : Type) (R S : relation A).

  (* Called PreOrder in Coq. *)
  Definition quasi_ordering := reflexive R /\ transitive R.

  Definition ordering := reflexive R /\ transitive R /\ antisymmetric R.

  Definition strict_ordering := irreflexive R /\ transitive R.

  Definition strict_part : relation A := fun x y => R x y /\ ~R y x.

  Definition intersection : relation A := fun x y => R x y /\ S x y.

End basic_def3.

(***********************************************************************)
(** Intersection. *)

Lemma intersection_dec A (R S : relation A)
  (Rdec : rel_dec R) (Sdec : rel_dec S) : rel_dec (intersection R S).

Proof.
  intros x y. unfold intersection. case (Rdec x y); case (Sdec x y); intuition.
Defined.

(***********************************************************************)
(** Finitely branching relations. *)

Section finitely_branching.

  Variables (A : Type) (R : relation A) (FB : finitely_branching R).

  Definition sons x := proj1_sig (FB x).

  Lemma in_sons_R : forall x y, In y (sons x) -> R x y.

  Proof. intros x y. exact (proj2 (proj2_sig (FB x) y)). Qed.

  Lemma R_in_sons : forall x y, R x y -> In y (sons x).

  Proof. intros x y. exact (proj1 (proj2_sig (FB x) y)). Qed.

End finitely_branching.

Implicit Arguments sons [A R].
Implicit Arguments in_sons_R [A R x y].
Implicit Arguments R_in_sons [A R x y].

(***********************************************************************)
(** Equivalence relation associated to a PreOrder. *)

Definition inter_transp A (R : relation A) : relation A :=
  fun x y => R x y /\ R y x.

(*COQ: declaring these Lemma's as Instance's creates problems in
FSetUtil and FGraph *)

Lemma inter_transp_Reflexive A (R : relation A) :
  Reflexive R -> Reflexive (inter_transp R).

Proof. fo. Qed.

Lemma inter_transp__Symmetric A (R : relation A) :
  Symmetric (inter_transp R).

Proof. fo. Qed.

Lemma inter_transp_Transitive A (R : relation A) :
  Transitive R -> Transitive (inter_transp R).

Proof. fo. Qed.

(*WARNING: do not declare following Lemmas as Instances *)

Lemma R_inter_transp A (R : relation A) :
  Transitive R -> Proper (inter_transp R ==> inter_transp R ==> impl) R.

Proof. fo. Qed.

Lemma inter_transp_incl A (R : relation A) : inter_transp R << R.

Proof. fo. Qed.

Lemma inter_transp_1 A1 (R1 : relation A1) B (S : relation B) f :
  Proper (R1 ==> S) f ->
  Proper (inter_transp R1 ==> inter_transp S) f.

Proof. fo. Qed.

Lemma inter_transp_2 A1 (R1 : relation A1) A2 (R2 : relation A2)
  B (S : relation B) f : Proper (R1 ==> R2 ==> S) f ->
  Proper (inter_transp R1 ==> inter_transp R2 ==> inter_transp S) f.

Proof. fo. Qed.

Lemma Proper_inter_transp_1 A1 (R1 : relation A1) B (S : relation B) f :
  Symmetric R1 -> Proper (R1 ==> S) f -> Proper (R1 ==> inter_transp S) f.

Proof. fo. Qed.

Lemma Proper_inter_transp_2 A1 (R1 : relation A1) A2 (R2 : relation A2)
  B (S : relation B) f : Symmetric R1 -> Symmetric R2 ->
  Proper (R1 ==> R2 ==> S) f -> Proper (R1 ==> R2 ==> inter_transp S) f.

Proof. intros s1 s2 hf x1 y1 e1 x2 y2 e2. split; apply hf; fo. Qed.

Lemma Proper_inter_transp_3 A1 (R1 : relation A1) A2 (R2 : relation A2)
  A3 (R3 : relation A3) B (S : relation B) f :
  Symmetric R1 -> Symmetric R2 -> Symmetric R3 ->
  Proper (R1 ==> R2 ==> R3 ==> S) f ->
  Proper (R1 ==> R2 ==> R3 ==> inter_transp S) f.

Proof. intros s1 s2 s3 hf x1 y1 e1 x2 y2 e2 x3 y3 e3. split; apply hf; fo. Qed.

Lemma Proper_inter_transp_4 A1 (R1 : relation A1) A2 (R2 : relation A2)
  A3 (R3 : relation A3) A4 (R4 : relation A4) B (S : relation B) f :
  Symmetric R1 -> Symmetric R2 -> Symmetric R3 -> Symmetric R4 ->
  Proper (R1 ==> R2 ==> R3 ==> R4 ==> S) f ->
  Proper (R1 ==> R2 ==> R3 ==> R4 ==> inter_transp S) f.

Proof.
  intros s1 s2 s3 s4 hf x1 y1 e1 x2 y2 e2 x3 y3 e3 x4 y4 e4.
  split; apply hf; fo.
Qed.

(***********************************************************************)
(** Inclusion. *)

Instance inclusion_Refl A : Reflexive (@inclusion A).

Proof. fo. Qed.

Ltac incl_refl := apply inclusion_Refl.

Instance inclusion_Trans A : Transitive (@inclusion A).

Proof. fo. Qed.

Ltac incl_trans S := apply inclusion_Trans with (S); try incl_refl.

Instance inclusion_same_relation A :
  Proper (same_relation ==> same_relation ==> impl) (@inclusion A).

Proof. fo. Qed.

(*FIXME: try to remove*)
Lemma inclusion_elim : forall A (R S : relation A),
  R << S -> forall x y, R x y -> S x y.

Proof. auto. Qed.

Implicit Arguments inclusion_elim [A R S x y].

(***********************************************************************)
(** Infinite sequences. *)

Instance IS_inclusion A : Proper (inclusion ==> eq ==> impl) (@IS A).

Proof. intros R S RS f g fg h i. subst. apply RS. apply h. Qed.

Instance IS_same_relation A : Proper (same_relation ==> eq ==> impl) (@IS A).

Proof.
  intros R S [RS SR] f g fg h. eapply IS_inclusion. apply RS. apply fg. hyp.
Qed.

Instance EIS_same_relation A : Proper (same_relation ==> impl) (@EIS A).

Proof. intros R S RS h. destruct h as [f h]. exists f. rewrite <- RS. hyp. Qed.

Section IS.

  Variables (A : Type) (R : relation A).

  Lemma NT_IS_elt : forall f k, IS R f -> NT R (f k).

  Proof. intros f k hf. exists (fun i => f (i+k)). fo. Qed.

  Lemma red_NT : forall t u, R t u -> NT R u -> NT R t.

  Proof.
    intros t u tu [f [f0 hf]]. subst.
    exists (fun k => match k with 0 => t | S k' => f k' end).
    intuition. intro k. destruct k. hyp. apply hf.
  Qed.

End IS.

(***********************************************************************)
(** Irreflexivivity. *)

Instance irreflexive_inclusion A : Proper (inclusion --> impl) (@irreflexive A).

Proof. fo. Qed.

(***********************************************************************)
(** Monotony. *)

Section monotone.

  Variables (A B : Type).

  Definition monotone (R : relation A) (S : relation B) f :=
    forall x y, R x y -> S (f x) (f y).

  Lemma monotone_transp : forall R S f,
    monotone R S f -> monotone (transp R) (transp S) f.

  Proof. unfold monotone, transp. auto. Qed.

End monotone.

(***********************************************************************)
(** Composition. *)

Definition compose A (R S : relation A) : relation A :=
  fun x y => exists z, R x z /\ S z y.

Notation "R @ S" := (compose R S) (at level 40) : relation_scope.

Instance compose_inclusion A :
  Proper (inclusion ==> inclusion ==> inclusion) (@compose A).

Proof. fo. Qed.

(*FIXME: try to remove*)
Ltac comp := apply compose_inclusion; try incl_refl.

Instance compose_m A :
  Proper (same_relation ==> same_relation ==> same_relation) (@compose A).

Proof. fo. Qed.

Section compose.

  Variables (A : Type) (R R' S S' : relation A).

  Lemma comp_assoc : forall T, (R @ S) @ T << R @ (S @ T).

  Proof.
    unfold inclusion. intros. do 4 destruct H. exists x1; split. hyp.
    exists x0; split; hyp.
  Qed.

  Lemma comp_assoc' : forall T, R @ (S @ T) << (R @ S) @ T.

  Proof.
    unfold inclusion. intros. do 2 destruct H. do 2 destruct H0.
    exists x1; split. exists x0; split; hyp. exact H1.
  Qed.

  Lemma incl_rtc_comp : R @ S << S -> R# @ S << S.

  Proof.
    intro. unfold inclusion, compose. intros. do 2 destruct H0.
    gen H1. clear H1. elim H0; intros; auto. apply H. exists y0. auto.
  Qed.

  Lemma incl_comp_rtc : S @ R << S -> S @ R# << S.

  Proof. intros h t v [u [tu uv]]. induction uv; fo. Qed.

End compose.

Ltac assoc :=
  match goal with
    | |- (?s @ ?t) @ ?u << _ => incl_trans (s @ (t @ u)); try apply comp_assoc
    | |- ?s @ (?t @ ?u) << _ => incl_trans ((s @ t) @ u); try apply comp_assoc'
    | |- _ << (?s @ ?t) @ ?u => incl_trans (s @ (t @ u)); try apply comp_assoc'
    | |- _ << ?s @ (?t @ ?u) => incl_trans ((s @ t) @ u); try apply comp_assoc
  end.

(***********************************************************************)
(** Absorbtion. *)

Definition absorb A (R S : relation A) := S @ R << R.

(***********************************************************************)
(** Reflexive closure. *)

Definition clos_refl A (R : relation A) : relation A := eq U R.

Notation "x %" := (clos_refl x) (at level 35) : relation_scope.

Instance clos_refl_m' A : Proper (inclusion ==> inclusion) (@clos_refl A).

Proof. fo. Qed.

Instance clos_refl_m A :
  Proper (same_relation ==> same_relation) (@clos_refl A).

Proof. fo. Qed.

Section clos_refl.

  Variables (A : Type) (R S : relation A).

  Global Instance rc_refl : Reflexive (R%).

  Proof. fo. Qed.

  Global Instance rc_trans : Transitive R -> Transitive (R%).

  Proof.
    intro. unfold Transitive, clos_refl, union. intros. decomp H0. subst y. hyp.
    decomp H1. subst z. auto. right. apply H with (y := y); hyp.
  Qed.

  Lemma rc_incl : R << R%.

  Proof. fo. Qed.

End clos_refl.

(***********************************************************************)
(** transitive closure *)

Instance clos_trans_inclusion A :
  Proper (inclusion ==> inclusion) (@clos_trans A).

Proof.
  intros R R' H t u H0. elim H0; intros.
  apply t_step. apply H. hyp.
  apply t_trans with y; hyp.
Qed.

Instance clos_trans_same_relation A :
  Proper (same_relation ==> same_relation) (@clos_trans A).

Proof. intros R S [RS SR]. split; apply clos_trans_inclusion; hyp. Qed.

Section clos_trans.

  Variable A : Type.

  Implicit Type R S : relation A.

  Lemma incl_tc R S : R << S -> R << S!.

  Proof. fo. Qed.

  Global Instance tc_trans R : Transitive (R!).

  Proof. unfold Transitive. intros. apply t_trans with y; hyp. Qed.

  Lemma tc_incl_rtc R : R! << R#.

  Proof.
    unfold inclusion. intros. elim H; intros.
    apply rt_step. hyp.
    apply rt_trans with y0; hyp.
  Qed.

  Lemma tc_split R : R! << R @ R#.

  Proof.
    unfold inclusion. induction 1. exists y. split. hyp. apply rt_refl.
    destruct IHclos_trans1. destruct H1. exists x0. split. hyp.
    apply rt_trans with y. hyp.
    apply inclusion_elim with (R:=R!). apply tc_incl_rtc. hyp.
  Qed.

  Lemma trans_tc_incl R : Transitive R -> R! << R.

  Proof.
    unfold transitive, inclusion. intros. induction H0. hyp. 
    apply H with y; hyp.
  Qed.

  Lemma trans_comp_incl R : Transitive R -> R @ R << R.

  Proof. fo. Qed.

  Lemma comp_tc_incl R S : R @ S << S -> R! @ S << S.

  Proof.
    intro. unfold inclusion, compose. intros. do 2 destruct H0.
    gen H1. clear H1. elim H0; intros; auto. apply H. exists y0. auto.
  Qed.

  Lemma comp_incl_tc R S : R @ S << S -> R @ S! << S!.

  Proof.
    intro. unfold inclusion. intros. do 2 destruct H0. generalize x0 y H1 H0.
    induction 1; intros. apply t_step. apply H. exists x1; split; hyp.
    apply t_trans with (y := y0); auto.
  Qed.

  Lemma trans_intro R : R @ R << R <-> Transitive R.

  Proof.
    split. unfold Transitive. intros. apply H. exists y. intuition.
    intros h x z [y [xy yz]]. apply (h _ _ _ xy yz).
  Qed.

  Lemma comp_tc_idem R : R! @ R! << R!.

  Proof.
    unfold inclusion. intros. do 2 destruct H. apply t_trans with x0; hyp.
  Qed.

  Lemma tc_min R S : R << S -> Transitive S -> R! << S.

  Proof.
    intros RS Strans. intros x y. induction 1. apply RS. hyp.
    apply Strans with y; hyp.
  Qed.

  Lemma trans_tc R : Transitive R -> R! == R.

  Proof.
    intro t. split. apply tc_min. refl. hyp. apply incl_tc. refl.
  Qed.

  Lemma tc_idem R : R!! == R!.

  Proof.
    split. intros x y. induction 1. hyp. apply t_trans with y; hyp.
    apply incl_tc. refl.
  Qed.

  Lemma tc_eq R S : S << R -> R << S! -> R! == S!.

  Proof.
    intros SR RSt. split; apply tc_min. hyp. apply tc_trans.
    trans R. hyp. apply incl_tc. refl. apply tc_trans.
  Qed.

  Lemma tc_incl_trans R S : Transitive S -> R << S -> R! << S.

  Proof. intros S_trans RS. intros t u tu; revert t u tu. induction 1; fo. Qed.

End clos_trans.

(***********************************************************************)
(** Symmetric closure of a relation. *)

Section clos_sym.

  Variable (A : Type) (R : relation A).

  Inductive clos_sym : relation A :=
  | s_step : forall x y, R x y -> clos_sym x y
  | s_sym : forall x y, clos_sym y x -> clos_sym x y.

  Global Instance sc_sym : Symmetric clos_sym.

  Proof. intros x y xy. apply s_sym. hyp. Qed.
 
End clos_sym.

(***********************************************************************)
(** Reflexive, transitive and symmetric closure of a relation. *)

Section clos_equiv.

  Variable (A : Type) (R : relation A).

  Inductive clos_equiv : relation A :=
  | e_step : forall x y, R x y -> clos_equiv x y
  | e_refl : forall x, clos_equiv x x
  | e_trans : forall x y z, clos_equiv x y -> clos_equiv y z -> clos_equiv x z
  | e_sym : forall x y, clos_equiv x y -> clos_equiv y x.

  Global Instance ec_equiv : Equivalence clos_equiv.

  Proof. exact (Build_Equivalence _ _ e_refl e_sym e_trans). Qed.

End clos_equiv.

(***********************************************************************)
(** Union. *)

Instance union_inclusion A :
  Proper (inclusion ==> inclusion ==> inclusion) (@union A).

Proof. fo. Qed.

(*FIXME: try to remove*)
Ltac union := apply union_inclusion; try incl_refl.

Instance union_same_relation A :
  Proper (same_relation ==> same_relation ==> same_relation) (@union A).

Proof. fo. Qed.

Section union.

  Variable A : Type.

  Implicit Type R S T : relation A.

  Lemma union_commut : forall R S, R U S == S U R.

  Proof. fo. Qed.

  Lemma union_assoc : forall R S T, (R U S) U T == R U (S U T).

  Proof. fo. Qed.

  Lemma comp_union_l : forall R S T, (R U S) @ T == (R @ T) U (S @ T).

  Proof. fo. Qed.

  Lemma comp_union_r : forall R S T, T @ (R U S) == (T @ R) U (T @ S).

  Proof. fo. Qed.

  Lemma union_empty_r : forall R, R U empty_rel == R.

  Proof. fo. Qed.

  Lemma union_empty_l : forall R, empty_rel U R == R.

  Proof. fo. Qed.

  Lemma incl_union_l : forall R S T, R << S -> R << S U T.

  Proof. fo. Qed.

  Lemma incl_union_r : forall R S T, R << T -> R << S U T.

  Proof. fo. Qed.

  Lemma union_incl : forall R R' S, R U R' << S <-> R << S /\ R' << S.

  Proof. fo. Qed.

End union.

(***********************************************************************)
(** Reflexive and transitive closure of a relation. *)

Instance clos_refl_trans_inclusion A :
  Proper (inclusion ==> inclusion) (@clos_refl_trans A).

Proof.
intro. unfold inclusion. intros. elim H0; intros.
apply rt_step. apply H. hyp.
apply rt_refl.
eapply rt_trans. apply H2. hyp.
Qed.

Instance clos_refl_trans_same_relation A :
  Proper (same_relation ==> same_relation) (@clos_refl_trans A).

Proof. intros R S [RS SR]. split; apply clos_refl_trans_inclusion; hyp. Qed.

Section clos_refl_trans.

  Variables (A : Type) (R S : relation A).

  Lemma rtc_incl : R << R#.

  Proof. fo. Qed.

  Global Instance rtc_refl : Reflexive (R#).

  Proof. fo. Qed.

  Global Instance rtc_trans : Transitive (R#).

  Proof. unfold Transitive. intros. eapply rt_trans. apply H. hyp. Qed.

  Lemma rc_incl_rtc : R% << R#.

  Proof.
    unfold inclusion, clos_refl. intros. destruct H.
    subst y. apply rt_refl. apply rt_step. exact H.
  Qed.

  Lemma rtc_split : R# << eq U R!.

  Proof.
    unfold inclusion, union. intros. elim H.
    intros. right. apply t_step. hyp.
    intro. left. refl.
    intros. destruct H1; destruct H3.
    left. trans y0; hyp.
    subst y0. right. hyp.
    subst y0. right. hyp.
    right. apply t_trans with (y := y0); hyp.
  Qed.

  Lemma rtc_split_eq : R# == eq U R!.

  Proof.
    split. apply rtc_split. rewrite union_incl. split.
    intros x y h. subst. apply rt_refl. apply tc_incl_rtc.
  Qed.

  Lemma rtc_split2 : R# << eq U R @ R#.

  Proof.
    unfold inclusion, union. intros. elim H; clear H x y; intros.
    right. exists y; split. exact H. apply rt_refl. auto. destruct H0.
    subst y. destruct H2. auto. destruct H0. right. exists x0. auto.
    do 2 destruct H0. right. exists x0. split. exact H0.
    apply rt_trans with (y := y); auto.
  Qed.

  Lemma tc_split_inv : R# @ R << R!.

  Proof.
    intros x y RRxy. destruct RRxy as [z [Rxz Rzy]].
    destruct (rtc_split Rxz).
    rewrite H. intuition.
    constructor 2 with z. hyp.
    constructor 1. hyp.
  Qed.

  Lemma tc_merge : R @ R# << R!.

  Proof.
    unfold inclusion. intros. destruct H. destruct H.
    ded (rtc_split H0). destruct H1; subst.
    apply t_step;hyp.
    eapply t_trans. apply t_step.
    ehyp. hyp.
  Qed.

  Lemma rtc_transp : transp (R#) << (transp R)#.

  Proof.
    unfold inclusion. induction 1.
    apply rt_step. hyp.
    apply rt_refl.
    eapply rt_trans. apply IHclos_refl_trans2. apply IHclos_refl_trans1.
  Qed.

  Lemma incl_rtc_rtc : R << S# -> R# << S#.

  Proof.
    unfold inclusion. induction 2.
    apply H. hyp.
    constructor 2.
    constructor 3 with y; hyp.
  Qed.

  Lemma comp_rtc_idem : R# @ R# << R#.

  Proof.
    unfold inclusion. intros. do 2 destruct H. apply rt_trans with x0; hyp.
  Qed.

  Lemma trans_rtc_incl : transitive R -> reflexive R -> R# << R.

  Proof.
    unfold transitive, inclusion, reflexive. intros. induction H1. hyp. 
    apply H0. apply H with y; hyp.
  Qed.

End clos_refl_trans.

Section clos_refl_trans2.

  Variables (A : Type) (R S : relation A).

  Lemma rtc_invol : R # # == R #.

  Proof.
    split. intros x y. induction 1. hyp. apply rt_refl.
    apply rt_trans with y; hyp. apply rtc_incl.
  Qed.

End clos_refl_trans2.

(***********************************************************************)
(** Inverse (transp in Coq). *)

Instance transp_inclusion A : Proper (inclusion ==> inclusion) (@transp A).

Proof. fo. Qed.

Instance transp_same_relation A :
  Proper (same_relation ==> same_relation) (@transp A).

Proof. fo. Qed.

Section transp.

  Variables (A : Type) (R S : relation A).

  (*COQ: declaring these lemmas as Global Instance makes Coq loop
  later in some other files *)

  Lemma transp_refl : Reflexive R -> Reflexive (transp R).

  Proof. auto. Qed.

  Lemma transp_trans : Transitive R -> Transitive (transp R).

  Proof. fo. Qed.

  Lemma transp_sym : Symmetric R -> Symmetric (transp R).

  Proof. fo. Qed.

  Lemma transp_transp : transp (transp R) << R.

  Proof. fo. Qed.

  Lemma transp_invol : transp (transp R) == R.

  Proof. fo. Qed.

  Lemma transp_union : transp (R U S) == transp R U transp S.

  Proof. fo. Qed.

End transp.

(***********************************************************************)
(** Relations between closures, union and composition. *)

Section properties.

  Variables (A : Type) (R S : relation A).

  Lemma rtc_comp_permut : R# @ (R# @ S)# << (R# @ S)# @ R#.

  Proof.
    unfold inclusion. intros. do 2 destruct H. ded (rtc_split2 H0). destruct H1.
    subst x0. exists x; split. apply rt_refl. exact H.
    do 4 destruct H1. exists y; split. apply rt_trans with (y := x1).
    apply rt_step. exists x2; split. apply rt_trans with (y := x0); hyp.
    hyp. hyp. apply rt_refl.
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
    apply inclusion_elim with (R := (R# @ clos_refl_trans (R# @ S))).
    apply rtc_comp_permut. exists y0; split; hyp.
    destruct h. destruct H6. exists x3; split.
    apply rt_trans with (y := x1); hyp.
    apply rt_trans with (y := x2); hyp.
  Qed.

  Lemma rtc_comp : R# @ S << S U R! @ S.

  Proof.
    unfold inclusion. intros. do 2 destruct H. ded (rtc_split H). destruct H1.
    subst x0. left. exact H0. right. exists x0; split; hyp.
  Qed.

  Lemma union_fact : R U R @ S << R @ S%.

  Proof.
    unfold inclusion. intros. destruct H.
    exists y; split; unfold clos_refl, union; auto.
    do 2 destruct H. exists x0; split; unfold clos_refl, union; auto.
  Qed.

  Lemma union_fact2 : R @ S U R << R @ S%.

  Proof. incl_trans (R U R @ S). apply union_commut. apply union_fact. Qed.

  Lemma incl_rc_rtc : R << S! -> R% << S#.

  Proof.
    intro. unfold inclusion. intros. destruct H0. subst y. apply rt_refl.
    apply inclusion_elim with (R := S!). apply tc_incl_rtc. apply H. exact H0.
  Qed.

  Lemma incl_tc_rtc : R << S# -> R! << S#.

  Proof.
    intro. unfold inclusion. induction 1. apply H. exact H0.
    apply rt_trans with (y := y); hyp.
  Qed.

End properties.

Section properties2.

  Variables (A : Type) (R S : relation A).

  Lemma rtc_comp_modulo : R# @ (R# @ S)! << (R# @ S)!.

  Proof.
    unfold inclusion. intros. do 2 destruct H.
    ded (tc_split H0). do 2 destruct H1. do 2 destruct H1.
    ded (rtc_split H2). destruct H4. subst x1.
    apply t_step. exists x2. intuition. apply rt_trans with x0; hyp.
    apply t_trans with x1. apply t_step. exists x2. intuition.
    apply rt_trans with x0; hyp. exact H4.
  Qed.

  Lemma tc_union : (R U S)! << R! U (R# @ S)! @ R#.

  Proof.
    unfold inclusion. induction 1. destruct H. left. apply t_step. exact H.
    right. exists y. intuition. apply t_step. exists x. intuition.
    destruct IHclos_trans1. destruct IHclos_trans2.
    left. apply t_trans with y; hyp.
    right. do 2 destruct H2. exists x0. intuition.
    apply rtc_comp_modulo. exists y. intuition. apply tc_incl_rtc. exact H1.
    right. do 2 destruct H1. destruct IHclos_trans2. exists x0.
    intuition. apply rt_trans with y. exact H2. apply tc_incl_rtc. exact H3.
    do 2 destruct H3. exists x1. intuition. apply t_trans with x0. exact H1.
    apply rtc_comp_modulo. exists y. intuition.
  Qed.

End properties2.

(***********************************************************************)
(** Commutation properties. *)

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
    exists x1. intuition. apply rt_trans with x0; hyp.
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

  Lemma absorb_comp T V (absorb : R @ S << T) : R @ (S @ V) << T @ V.

  Proof. rewrite comp_assoc', absorb. refl. Qed.

End commut.

(***********************************************************************)
(** Inverse image. *)

Section inverse_image.

  Variables (A B : Type) (R : relation B) (f : A->B).

  Definition Rof a a' := R (f a) (f a').

  (*COQ: declaring these lemmas as Global Instance makes Coq loop
  later in some other files *)

  Lemma Rof_refl : Reflexive R -> Reflexive Rof.

  Proof. fo. Qed.

  Lemma Rof_trans : Transitive R -> Transitive Rof.

  Proof. fo. Qed.

  Lemma Rof_sym : Symmetric R -> Symmetric Rof.

  Proof. fo. Qed.

  Variable F : A -> B -> Prop.

  Definition RoF a a' := exists b', F a' b' /\ forall b, F a b -> R b b'.

End inverse_image.

(***********************************************************************)
(** Alternative Definition of the Transitive Closure
(more convenient for some inductive proofs. *)

Inductive clos_trans1 (A : Type) (R : relation A) : relation A :=
| t1_step : forall x y, R x y -> clos_trans1 R x y
| t1_trans : forall x y z, R x y -> clos_trans1 R y z -> clos_trans1 R x z.

Notation "x !1" := (clos_trans1 x) (at level 35) : relation_scope.

Section alternative_definition_clos_trans.

  Variables (A : Type) (R : relation A).

  Lemma clos_trans1_trans : forall x y z, R!1 x y -> R!1 y z -> R!1 x z.

  Proof.
    intros x y z. induction 1; intro H1.
    exact (t1_trans x H H1).
    exact (t1_trans x H (IHclos_trans1 H1)).
  Qed.

  Lemma clos_trans_equiv : forall x y, R!1 x y <-> R! x y.

  Proof.
    intros x y. split; intro H.
    induction H.
    constructor; exact H.
    exact (t_trans A R x y z (t_step A R x y H) IHclos_trans1).
    induction H.
    constructor; exact H.
    exact (clos_trans1_trans IHclos_trans1 IHclos_trans2).
  Qed.

End alternative_definition_clos_trans.

(***********************************************************************)
(** Alternative definition of the reflexive and transitive closure
more convenient for some inductive proofs. *)

Inductive clos_refl_trans1 (A : Type) (R : relation A) : relation A :=
| rt1_refl : forall x, clos_refl_trans1 R x x
| rt1_trans : forall x y z,
  R x y -> clos_refl_trans1 R y z -> clos_refl_trans1 R x z.

Notation "x #1" := (clos_refl_trans1 x) (at level 9) : relation_scope.

Section alternative_definition_clos_refl_trans.

  Variables (A : Type) (R : relation A).

  Lemma clos_refl_trans1_trans : forall x y z, R#1 x y -> R#1 y z -> R#1 x z.

  Proof.
    intros x y z. induction 1; intro H1.
    hyp.
    exact (rt1_trans x H (IHclos_refl_trans1 H1)).
  Qed.

  Lemma clos_refl_trans_equiv : forall x y, R#1 x y <-> R# x y.

  Proof.
    intros x y. split; intro H.
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
    intros x y xRy. induction xRy.
    apply rt1_trans with y. hyp. apply rt1_refl.
    apply rt1_trans with y; hyp.
  Qed.

  Lemma incl_rt_rt_rt : R#1 @ R#1 << R#1.

  Proof.
    intros x y [z [xRz zRy]]. induction xRz.
    trivial.
    apply rt1_trans with y0. hyp. 
    apply IHxRz. hyp.
  Qed.

End alternative_definition_clos_refl_trans.

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
    exists x. split. apply rt1_refl. hyp.
    apply clos_refl_trans1_trans with n; trivial.
    apply rt1_trans with n; trivial. apply rt1_refl.
    apply rt1_trans with n.
    destruct mn as [q [mq qn]]. exists q. split; trivial.
    apply rt1_trans with m; hyp. hyp.
  Qed.

  Lemma union_rel_rt_left : R#1 << (R U S)#1.

  Proof.
    intros x y xRy.
    induction xRy. apply rt1_refl.
    apply rt1_trans with y. left. hyp. hyp.
  Qed.

  Lemma union_rel_rt_right : S#1 << (R U S)#1.

  Proof.
    intros x y xRy.
    induction xRy. apply rt1_refl.
    apply rt1_trans with y. right. hyp. hyp.
  Qed.

  Lemma incl_rtunion_union : (R!1 U S!1)#1 << (R U S)#1.

  Proof.
    intros x y xRy.
    induction xRy. apply rt1_refl.
    apply clos_refl_trans1_trans with y; trivial.
    destruct H.
    apply union_rel_rt_left. apply incl_t_rt. hyp.
    apply union_rel_rt_right. apply incl_t_rt. hyp.
  Qed.

End alternative_inclusion.

Lemma incl_union_rtunion : forall A (R S : relation A),
  (R U S)#1 << (R!1 U S!1)#1.

Proof.
  intros A R S x y xRy.
  induction xRy. apply rt1_refl.
  apply clos_refl_trans1_trans with y; trivial.
  destruct H.
  apply union_rel_rt_left. apply rt1_trans with y.
  apply t1_step. hyp. apply rt1_refl.
  apply union_rel_rt_right. apply rt1_trans with y.
  apply t1_step. hyp. apply rt1_refl.
Qed.

(***********************************************************************)
(** Morphisms wrt inclusion and same_relation. *)

Lemma eq_Refl_rel : forall A (R : relation A), Reflexive R -> eq << R.

Proof. intros A R hR x y xy. subst y. apply hR. Qed.

Instance Reflexive_same_relation A :
  Proper (same_relation ==> impl) (@Reflexive A).

Proof. fo. Qed.

Instance Symmetric_same_relation A :
  Proper (same_relation ==> impl) (@Symmetric A).

Proof. fo. Qed.

Instance Transitive_same_relation A :
  Proper (same_relation ==> impl) (@Transitive A).

Proof.
  intros R S e h x y z xy yz. rewrite rel_eq in e. rewrite <- e in *.
  apply h with y; hyp.
Qed.

Instance Equivalence_same_relation A :
  Proper (same_relation ==> impl) (@Equivalence A).

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

(***********************************************************************)
(** Option setoid. *)

Section option_setoid.

  Variables (A : Type) (eq : relation A).

  Inductive eq_opt : relation (option A) :=
  | eq_opt_None : eq_opt None None
  | eq_opt_Some : forall a b, eq a b -> eq_opt (Some a) (Some b).

  Global Instance eq_opt_Refl : Reflexive eq -> Reflexive eq_opt.

  Proof. intros h [x|]. apply eq_opt_Some. refl. apply eq_opt_None. Qed.

  Global Instance eq_opt_Sym : Symmetric eq -> Symmetric eq_opt.

  Proof.
    intros h x y xy. inversion xy; subst. hyp. apply eq_opt_Some. sym. hyp.
  Qed.

  Global Instance eq_opt_Trans : Transitive eq -> Transitive eq_opt.

  Proof.
    intros h x y z xy yz. inversion xy; inversion yz; subst; try discr.
    apply eq_opt_None. inversion H3; subst. apply eq_opt_Some. trans b; hyp.
  Qed.

  Global Instance Some_Proper : Proper (eq ==> eq_opt) (@Some A).

  Proof. intros x y xy. apply eq_opt_Some. hyp. Qed.

End option_setoid.
