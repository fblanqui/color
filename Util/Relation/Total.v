(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-02-23

on the total completion of a relation: Consider a decidable
(resp. middle-excluding) relation over an arbitrary set.  Equality on
the set is decidable (resp. middle-excluding) and the relation is
acyclic iff its restriction to any finite set has a decidable
(resp. middle-excluding) irreflexive linear extension.
*)

From Stdlib Require Import Sumbool Arith.
From CoLoR Require Import RelDec RelUtil ListUtil RelSub Path LogicUtil.

Set Implicit Arguments.

Section On_relation_completion.

Variable A : Type.

(***********************************************************************)
(** total *)

Section total.
 
Variable R : relation A.

Definition trichotomy x y : Prop := R x y \/ x=y \/ R y x.

Definition total l : Prop := forall x y,  In x l -> In y l -> trichotomy x y.

End total.

Lemma trichotomy_preserved : forall R R' x y,
  R << R' -> trichotomy R x y -> trichotomy R' x y.

Proof.
unfold inclusion, trichotomy. intros. pose (H x y). pose (H y x). tauto.
Qed. 
 
(***********************************************************************)
(** add *)

Section try_add_arc.

Variable R : relation A.

Inductive try_add_arc (x y : A) : relation A :=
| keep : forall z t, R z t -> try_add_arc x y z t
| try_add : x<>y -> ~R y x ->  try_add_arc x y x y.

Lemma sub_rel_try_add_arc : forall x y, R << try_add_arc x y.

Proof. unfold inclusion. intros. constructor. hyp.  Qed.

Lemma try_add_arc_sym :  forall x y z t,
  try_add_arc x y z t -> try_add_arc x y t z -> R z t.

Proof.
intros. inversion H. hyp. inversion H0. contr. rewrite H3 in H7. contr. 
Qed.

Lemma not_try_add_arc : rel_midex R -> forall x y, x<>y ->
  ~try_add_arc x y x y -> R y x. 

Proof.
intros. destruct (H y x). hyp. absurd (try_add_arc x y x y). hyp. 
constructor 2; hyp.  
Qed. 

Lemma restricted_try_add_arc : forall x y l, 
  In x l -> In y l -> is_restricted R l -> is_restricted (try_add_arc x y) l.

Proof.
unfold is_restricted. intros. inversion H2. apply H1. hyp. 
rewrite <- H5, <- H6. tauto.  
Qed.

Lemma try_add_arc_dec : eq_dec A -> forall x y,  rel_dec R ->
  rel_dec (try_add_arc x y).

Proof.
repeat intro. destruct (X0 x0 y0). do 2 constructor. hyp. 
destruct (X x0 y0). constructor 2. intro. inversion H; contr. 
destruct (X0 y0 x0). constructor 2. intro. inversion H; contr. 
destruct (X x x0). destruct (X y y0). rewrite e, e0. 
constructor. constructor 2; hyp. 
constructor 2. intro. inversion H; contr. 
constructor 2. intro. inversion H; contr. 
Qed.

Lemma try_add_arc_midex : eq_midex A -> forall x y, rel_midex R ->
  rel_midex (try_add_arc x y).

Proof.
do 6 intro. destruct (H0 x0 y0). do 2 constructor. hyp. 
destruct (H x0 y0). constructor 2. intro. inversion H3; contr. 
destruct (H0 y0 x0). constructor 2. intro. inversion H4; contr. 
destruct (H x x0). destruct (H y y0). rewrite H4, H5. 
constructor. constructor 2; hyp. 
constructor 2. intro. inversion H6; contr. 
constructor 2. intro. inversion H5; contr. 
Qed.

Lemma try_add_arc_trichotomy : eq_midex A -> rel_midex R ->
  forall x y, trichotomy (try_add_arc x y) x y.

Proof.
unfold trichotomy. intros. destruct (H x y). tauto. destruct (H0 x y).
do 2 constructor. hyp. 
destruct (H0 y x). do 2 constructor 2. constructor. hyp. constructor. 
constructor 2; hyp. 
Qed.

Lemma trichotomy_restriction : forall x y l,
  In x l -> In y l -> trichotomy R x y -> trichotomy (restriction R l) x y.

Proof.
unfold trichotomy, restriction. intros. tauto. 
Qed.

Lemma  path_try_add_arc_path : forall t x y l z, 
  ~(x=z \/ In x l) \/ ~(y=t \/ In y l) -> path (try_add_arc x y) z t l ->
  path R z t l. 

Proof.
induction l; simpl; intros. inversion H0; tauto. 
destruct H0. split. inversion H0. hyp. rewrite H5 in H. tauto. 
apply IHl. pose sym_equal. pose (e A x a). tauto. hyp. 
Qed.

Lemma trans_try_add_arc_sym : forall x y z t,
  transitive R -> try_add_arc x y z t -> try_add_arc x y t z -> R z z.

Proof.
unfold transitive. intros.
apply H with t; apply try_add_arc_sym with x y; hyp. 
Qed.

Lemma trans_bpath_try_add_arc : eq_midex A -> forall x y z n,
  transitive R -> bpath (try_add_arc x y ) n z z -> R z z.

Proof.
intros. induction n. inversion H1. destruct l. simpl in H2. 
apply trans_try_add_arc_sym with x y z; hyp. 
simpl in H1. pose (Nat.nle_succ_0 (length l) H2). contr. apply IHn.
inversion H1. clear IHn H1 H4 H5 x0 y0. 
(* nodup *)
destruct (path_nodup_length (try_add_arc x y) H z l z H3).
decompose [and] H1.
assert (length x0 <= S n). apply Nat.le_trans with (length l); hyp.
clear H1 H2 H3 H6 H7 H8. 
(* x0=nil *) 
destruct x0. exists (nil : list A). apply Nat.le_0_l. tauto. 
(* length x0 = 1 *) 
destruct x0; simpl in * |- . exists (nil : list A). apply Nat.le_0_l. simpl. 
apply sub_rel_try_add_arc. apply trans_try_add_arc_sym with x y a; tauto. 
(* length x0 >= 2*)
destruct H10.  destruct H2. 
inversion H1; inversion H2.
exists (a0::x0). simpl. apply le_S_n. hyp.
simpl. split. apply (sub_rel_try_add_arc). apply H0 with a; hyp.
hyp.  
(**)
absurd (R a0 a). tauto. apply trans_tc_incl. hyp. 
apply path_clos_trans with (x0++(z::nil)). apply path_app. 
apply path_try_add_arc_path with x y. rewrite H13. tauto. hyp. simpl.
hyp.  
(**)
absurd (R a z). tauto. apply trans_tc_incl. hyp. 
apply path_clos_trans with (a0::x0). split. hyp.  
apply path_try_add_arc_path with x y. rewrite H10. tauto. hyp. 
(**) 
rewrite H8 in H13. tauto. 
Qed.

Lemma try_add_arc_irrefl : eq_midex A -> forall x y, 
  transitive R ->  irreflexive R -> irreflexive (clos_trans (try_add_arc x y)).
 
Proof.
do 7 intro. apply H1 with x0. destruct (clos_trans_path H2).
apply trans_bpath_try_add_arc with x y (length x1); try hyp.
apply bp_intro with x1; trivial. 
Qed.

End try_add_arc.

(***********************************************************************)
(** try_add_arc_one_to_many: multiple try_add_arc with one list *)

Section try_add_arc_one_to_many.

Variable R : relation A.

Fixpoint try_add_arc_one_to_many (x : A) (l : list A) : relation A
  :=
  match l with
    | nil => R
    | y::l' => clos_trans (try_add_arc (try_add_arc_one_to_many x l') x y) 
  end.

Lemma sub_rel_try_add_arc_one_to_many : forall x l,
  R << (try_add_arc_one_to_many x l). 

Proof.
induction l; simpl; intros. refl.
trans (try_add_arc_one_to_many x l). hyp. 
trans (try_add_arc (try_add_arc_one_to_many x l) x a).
apply sub_rel_try_add_arc. apply incl_tc. refl. 
Qed. 

Lemma restricted_try_add_arc_one_to_many : forall l x l', 
  In x l -> incl l' l -> is_restricted R l ->
  is_restricted (try_add_arc_one_to_many x l') l.

Proof.
induction l'; simpl; intros. hyp. apply restricted_clos_trans. 
apply restricted_try_add_arc. hyp. apply H0. simpl. tauto. apply IHl'. 
hyp. exact (incl_cons_l_incl H0). hyp. 
Qed.

Lemma try_add_arc_one_to_many_dec : eq_dec A -> forall x l l',
  In x l -> incl l' l -> is_restricted R l -> rel_dec R ->
  rel_dec (try_add_arc_one_to_many x l').

Proof.
induction l'; simpl; intros. hyp. pose (incl_cons_l_incl H0). 
apply restricted_dec_clos_trans_dec with l. hyp. 
apply try_add_arc_dec. hyp. apply IHl'; tauto. 
apply restricted_try_add_arc. hyp. apply H0. simpl. tauto. 
apply restricted_try_add_arc_one_to_many; simpl; tauto. 
Qed.

Lemma try_add_arc_one_to_many_midex : eq_midex A -> forall x l l',
  In x l -> incl l' l -> is_restricted R l -> rel_midex R ->
  rel_midex (try_add_arc_one_to_many x l').

Proof.
induction l'; simpl; intros. hyp. pose (incl_cons_l_incl H1). 
apply restricted_midex_clos_trans_midex with l. hyp. 
apply try_add_arc_midex. hyp. apply IHl'; tauto. 
apply restricted_try_add_arc. hyp. apply H1. simpl. tauto. 
apply restricted_try_add_arc_one_to_many; simpl; tauto. 
Qed.

Lemma try_add_arc_one_to_many_trichotomy : eq_midex A -> rel_midex R ->
  forall x y l l', In y l' -> In x l ->  incl l' l -> is_restricted R l ->
    trichotomy (try_add_arc_one_to_many x l') x y.

Proof.
induction l';  simpl; intros. contr. pose (incl_cons_l_incl H3). 
apply trichotomy_preserved
  with (try_add_arc (try_add_arc_one_to_many x l') x a). 
apply incl_tc. refl. destruct H1. rewrite H1. 
apply try_add_arc_trichotomy. hyp.
apply try_add_arc_one_to_many_midex with l; hyp. 
apply trichotomy_preserved with (try_add_arc_one_to_many x l').
apply sub_rel_try_add_arc. tauto. 
Qed.

Lemma try_add_arc_one_to_many_irrefl : eq_midex A -> forall x l l',
  is_restricted R l -> transitive R -> irreflexive R ->
  irreflexive (try_add_arc_one_to_many x l').

Proof.
induction l'; simpl; intros. hyp.  
apply try_add_arc_irrefl. hyp. 
destruct l'; simpl. hyp. apply tc_trans. tauto. 
Qed.

End try_add_arc_one_to_many.

(***********************************************************************)
(** try_add_arc_many_to_many: multiple try_add_arc with two lists *)

Section try_add_arc_many_to_many.

Variable R : relation A.

Fixpoint try_add_arc_many_to_many (l' l: list A) : relation A :=
  match l' with
    | nil => R
    | x::l'' => try_add_arc_one_to_many (try_add_arc_many_to_many l'' l) x l
  end.

Lemma sub_rel_try_add_arc_many_to_many : forall l l',
  R << (try_add_arc_many_to_many l' l). 

Proof. 
induction l'; simpl; intros. refl.
trans (try_add_arc_many_to_many l' l). hyp. 
apply sub_rel_try_add_arc_one_to_many. 
Qed.

Lemma restricted_try_add_arc_many_to_many : forall l l', incl l' l ->
  is_restricted R l -> is_restricted (try_add_arc_many_to_many l' l) l. 

Proof.
induction l'; simpl; intros. hyp. 
apply restricted_try_add_arc_one_to_many. apply H. simpl. tauto.
refl. 
apply IHl'. exact (incl_cons_l_incl H). hyp. 
Qed.

Lemma try_add_arc_many_to_many_dec : eq_dec A ->  forall l l',
  incl l' l -> is_restricted R l -> rel_dec R ->
  rel_dec (try_add_arc_many_to_many l' l).

Proof.
induction l'; simpl; intros. hyp. pose (incl_cons_l_incl H). 
apply try_add_arc_one_to_many_dec with l. hyp. apply H. simpl. tauto.
refl. 
apply  restricted_try_add_arc_many_to_many; hyp. tauto. 
Qed.

Lemma try_add_arc_many_to_many_midex : eq_midex A ->  forall l l',
  incl l' l -> is_restricted R l -> rel_midex R ->
  rel_midex (try_add_arc_many_to_many l' l).

Proof.
induction l'; simpl; intros. hyp. pose (incl_cons_l_incl H0). 
apply try_add_arc_one_to_many_midex with l. hyp. apply H0. simpl. tauto.
refl. 
apply  restricted_try_add_arc_many_to_many; hyp. tauto. 
Qed.

Lemma try_add_arc_many_to_many_trichotomy : eq_midex A -> rel_midex R ->
  forall x y l l', is_restricted R l -> incl l' l -> In y l -> In x l' ->
    trichotomy (try_add_arc_many_to_many l' l) x y.

Proof.
induction l';  simpl; intros. contr. pose (incl_cons_l_incl H2). 
destruct H4. rewrite H4. 
apply try_add_arc_one_to_many_trichotomy with l; try hyp. 
apply try_add_arc_many_to_many_midex; hyp. 
rewrite <- H4. apply H2. simpl. tauto. refl. 
apply restricted_try_add_arc_many_to_many; hyp. 
apply trichotomy_preserved with  (try_add_arc_many_to_many l' l). 
apply sub_rel_try_add_arc_one_to_many. tauto. 
Qed.

Lemma try_add_arc_many_to_many_irrefl : eq_midex A -> forall l l',
  incl l' l -> is_restricted R l -> transitive R -> irreflexive R ->
  irreflexive (try_add_arc_many_to_many l' l).

Proof.
induction l'; simpl; intros. hyp. pose (incl_cons_l_incl H0).   
apply try_add_arc_one_to_many_irrefl with l. hyp. 
apply restricted_try_add_arc_many_to_many; hyp. 
destruct l'; simpl. hyp. destruct l. pose (i a0). simpl in i0. tauto. 
simpl. apply tc_trans. tauto.   
Qed. 

End try_add_arc_many_to_many.

(***********************************************************************)
(** Linear Extension and Topological Sorting *)

Section LETS.

Variable R : relation A.
Variable l : list A.

Definition LETS := try_add_arc_many_to_many (clos_trans (restriction R l)) l l.

Lemma LETS_restriction_clos_trans : clos_trans (restriction R l) << LETS.

Proof.
intros. unfold LETS. apply sub_rel_try_add_arc_many_to_many. 
Qed.

Lemma LETS_sub_rel : restriction R l << LETS.

Proof.
intros. unfold LETS.
trans (clos_trans (restriction R l)). 
apply incl_tc. refl. apply  LETS_restriction_clos_trans. 
Qed.

Lemma LETS_restricted : is_restricted LETS l.

Proof.
unfold LETS. intros. apply restricted_try_add_arc_many_to_many.
refl. 
apply restricted_clos_trans. apply restricted_restriction.  
Qed.

Lemma LETS_transitive : transitive LETS.

Proof.
intros. unfold LETS. destruct l; simpl; apply tc_trans.
Qed.

Lemma LETS_irrefl : eq_midex A -> 
  (irreflexive (clos_trans (restriction R l)) <-> irreflexive LETS).

Proof.
split;intros. unfold LETS.
apply try_add_arc_many_to_many_irrefl; try hyp. refl. 
apply restricted_clos_trans. apply restricted_restriction.
apply tc_trans.  
apply irreflexive_incl with LETS. apply LETS_restriction_clos_trans.
hyp. 
Qed. 

Lemma LETS_total : eq_midex A -> rel_midex R -> total LETS l.

Proof.
unfold LETS, total. intros. pose (R_midex_clos_trans_restriction_midex H H0 l). 
apply try_add_arc_many_to_many_trichotomy; try hyp.
apply restricted_clos_trans. 
apply restricted_restriction. refl. 
Qed.

Lemma LETS_dec : eq_dec A -> rel_dec R -> rel_dec LETS.

Proof.
intros. unfold LETS. apply try_add_arc_many_to_many_dec. hyp.
refl. 
apply restricted_clos_trans. apply restricted_restriction.  
apply R_dec_clos_trans_restriction_dec; hyp.  
Qed.

Lemma LETS_midex : eq_midex A -> rel_midex R -> rel_midex LETS.

Proof.
intros. unfold LETS. apply try_add_arc_many_to_many_midex. hyp.
refl. 
apply restricted_clos_trans. apply restricted_restriction.  
apply R_midex_clos_trans_restriction_midex; hyp.  
Qed.

End LETS.

(***********************************************************************)
(** Linear Extension *)

Definition linear_extension R l R' :=
  is_restricted R' l /\ (restriction R l) << R' /\ 
  transitive R' /\ irreflexive R' /\ total R' l.

Lemma local_global_acyclic : forall R : relation A,
  (forall l, exists R',
    (restriction R l) << R' /\ transitive R' /\ irreflexive R') ->
  irreflexive (clos_trans R).

Proof.
intros. do 2 intro. destruct (clos_trans_path H0). 
assert (clos_trans (restriction R (x::x::x0)) x x).
apply path_clos_trans with x0. 
apply path_restriction. hyp. destruct (H (x::x::x0)). destruct H3.
destruct H4. 
apply H5 with x. apply trans_tc_incl. hyp. 
apply tc_incl with (restriction R (x :: x :: x0)). hyp.
hyp. 
Qed.

Lemma total_order_eq_midex: 
  (forall l, exists R,
    transitive R /\ irreflexive R /\ total R l /\ rel_midex R) -> eq_midex A. 

Proof.
do 3 intro. destruct (H (x::y::nil)). decompose [and] H0.
destruct (H5 x y); destruct (H5 y x). 
absurd (x0 x x). apply H3. apply H1 with y; hyp. 
constructor 2. intro. rewrite H7 in H4. rewrite H7 in H6. contr.
constructor 2. intro. rewrite H7 in H4. rewrite H7 in H6. contr. 
destruct (H2 x y); simpl; try tauto. 
Qed.

Lemma linearly_extendable :  forall R, rel_midex R ->
  (eq_midex A /\ irreflexive (clos_trans R) <->
    forall l, exists R', linear_extension R l R' /\ rel_midex R').

Proof.
unfold linear_extension. split; intros. exists (LETS R l). split. split.
apply LETS_restricted. split. 
apply LETS_sub_rel. split. apply LETS_transitive. split.
destruct (LETS_irrefl R l). 
tauto. apply H1. apply irreflexive_incl with (clos_trans R).
unfold inclusion. apply tc_incl. apply incl_restriction. tauto.
apply LETS_total; tauto. apply LETS_midex; tauto. 
(**)
split. apply total_order_eq_midex. intro. destruct (H0 l). exists x. tauto. 
apply local_global_acyclic. intro. destruct (H0 l). exists x. tauto. 
Qed.

(***********************************************************************)
(** Topological Sorting *)

Definition topo_sortable R := 
  {F : list A -> A -> A -> bool |
    forall l, linear_extension R l (fun x y => F l x y = true)}.

Definition antisym R SC := forall x y : A, x<>y -> ~R x y -> ~R y x ->
  ~(SC (x::y::nil) x y /\ SC (y::x::nil) x y). 

Definition antisym_topo_sortable R := 
  {F : list A -> A -> A -> bool |
    let G := (fun l x y => F l x y = true) in 
      antisym R G /\ forall l, linear_extension R l (G l)}.

Lemma total_order_eq_dec : 
  {F : list A -> A -> A -> bool |
    forall l, let G := fun x y => F l x y = true in 
      transitive G /\ irreflexive G /\ total G l} -> eq_dec A. 

Proof.
unfold transitive, irreflexive, total, trichotomy. intros H x y. destruct H.
pose (a (x::y::nil)). 
assert ({x0 (x::y::nil) x y=true}+{x0  (x::y::nil) x y=false}).
case (x0 (x::y::nil) x y); tauto. 
assert ({x0 (x::y::nil) y x=true}+{x0 (x::y::nil) y x=false}).
case (x0 (x::y::nil) y x); tauto. 
destruct a0. destruct H2. pose (H3 x y). simpl in o. 
destruct H. constructor 2. intro. rewrite H in e. rewrite H in H2.
exact (H2 y e). 
destruct H0. constructor 2. intro. rewrite H in e0. rewrite H in H2.
exact (H2 y e0). 
constructor. destruct o; try tauto. rewrite H in e. inversion e. destruct H.
hyp. 
rewrite H in e0. inversion e0. 
Qed.

Lemma LETS_antisym : forall R, antisym R (LETS R). 

Proof.
unfold LETS. do 7 intro. simpl in *|- . destruct H2. 
assert (is_restricted (restriction R (x :: y :: nil)) (x::y::nil)).
apply restricted_restriction. 
assert (is_restricted
  (try_add_arc (clos_trans (restriction R (x :: y :: nil))) y y) (x::y::nil)). 
apply restricted_try_add_arc; simpl; try tauto. apply restricted_clos_trans.
hyp.
assert (is_restricted
  (try_add_arc (clos_trans (try_add_arc
    (clos_trans (restriction R (x :: y :: nil))) y y)) y x) (x::y::nil)). 
apply restricted_try_add_arc; simpl; try tauto. apply restricted_clos_trans.
hyp.
assert (is_restricted (try_add_arc (clos_trans
  (try_add_arc (clos_trans (try_add_arc
    (clos_trans (restriction R (x :: y :: nil))) y y)) y x)) x y) (x::y::nil)).
apply restricted_try_add_arc; simpl; try tauto. apply restricted_clos_trans.
hyp.
assert (is_restricted (try_add_arc (clos_trans (try_add_arc (clos_trans
  (try_add_arc (clos_trans (try_add_arc (clos_trans
    (restriction R (x :: y :: nil))) y y)) y x)) x y)) x x)  (x::y::nil)).
apply restricted_try_add_arc; simpl; try tauto. apply restricted_clos_trans.
hyp.
(**)
pose (clos_trans_restricted_pair H8 H2). inversion t; try tauto.
clear H10 H11 z t0.
pose (clos_trans_restricted_pair H7 H9). inversion t0. clear H11 H12 z t1.
pose (clos_trans_restricted_pair H6 H10). inversion t1; try tauto.
clear H12 H13 z t2.
pose (clos_trans_restricted_pair H5 H11). inversion t2. clear H13 H14 z t3.
assert (restriction R (x :: y :: nil) x y).
apply clos_trans_restricted_pair; hyp. 
unfold restriction in H13. tauto. tauto.
(**)
absurd (clos_trans  (try_add_arc (clos_trans (try_add_arc (clos_trans
  (restriction R (x :: y :: nil))) y y)) y x) y x). 
hyp. constructor. constructor 2. intro. rewrite H14 in H10. tauto. 
intro. pose (clos_trans_restricted_pair H5 H14). inversion t1; try tauto.
clear H16 H17 z t2. 
pose (clos_trans_restricted_pair H4 H15). unfold restriction in r. tauto. 
Qed.

Lemma possible_antisym_topo_sort : forall R, eq_dec A -> rel_dec R ->
  irreflexive (clos_trans R) -> antisym_topo_sortable R. 

Proof.
do 4 intro. assert (forall l, rel_dec (LETS R l)). intro.
apply LETS_dec; hyp. 
pose (eq_dec_midex X). pose (rel_dec_midex X0).
exists (fun l x y => if (X1 l x y) then true else false). simpl. split.
do 5 intro. case (X1 (x :: y :: nil) x y). case (X1 (y :: x :: nil) x y). 
do 2 intro. absurd (LETS R (x :: y :: nil) x y /\ LETS R (y :: x :: nil) x y). 
apply LETS_antisym; hyp. tauto. do 3 intro. destruct H3. inversion H4. 
do 2 intro. destruct H3. inversion H3. split.
do 3 intro. destruct (X1 l x y). apply (LETS_restricted R l x y). hyp.
inversion H0. split. 
do 3 intro. destruct (X1 l x y). trivial. absurd (LETS R l x y). hyp.
apply LETS_restriction_clos_trans. eapply incl_tc. refl. hyp. split. 
do 5 intro. destruct (X1 l x y). destruct (X1 l y z).
pose (LETS_transitive R l x y z l0 l1). 
destruct (X1 l x z). trivial. contr. inversion H1. inversion H0. split. 
do 2 intro. destruct (X1 l x x). absurd (LETS R l x x).
destruct (LETS_irrefl R l). 
hyp. apply H1. apply irreflexive_incl with (clos_trans R). 
apply tc_incl. apply incl_restriction. hyp. hyp.
inversion H0. 
do 4 intro. unfold trichotomy. destruct (X1 l x y). tauto. destruct (X1 l y x).
tauto. 
destruct (LETS_total l e r x y); tauto.  
Qed. 

Lemma antisym_topo_sortable_topo_sortable : forall R, 
  antisym_topo_sortable R -> topo_sortable R.

Proof.
intros R H. exists (let (f,s):= H in f). intros. destruct H. destruct a.
pose (H0 l). unfold linear_extension in *|-* . tauto. 
Qed. 

Lemma antisym_topo_sortable_rel_dec : forall R, 
  rel_midex R -> antisym_topo_sortable R -> rel_dec R.

Proof.
unfold antisym_topo_sortable, linear_extension. 
intros R H H0. assert (irreflexive (clos_trans R)). apply local_global_acyclic.
intro. exists (fun x y => (let (f,s):= H0 in f) l x y=true). destruct H0.
destruct a. pose (H1 l). tauto. 
assert (eq_dec A). apply total_order_eq_dec. exists (let (f,s):= H0 in f).
intro. destruct H0. 
destruct a. pose (H2 l). split; tauto. 
(**)
do 2 intro. destruct (X x y). rewrite e. constructor 2. intro. apply (H1 y).
constructor. hyp. 
destruct H0. destruct a. pose (H0 x y). decompose [and] (H2 (x::y::nil)). 
destruct (sumbool_of_bool (x0 (x::y::nil) x y)).
destruct (sumbool_of_bool (x0 (y::x::nil) x y)). 
constructor. destruct (H x y). hyp. destruct (H y x).
absurd (x0 (x :: y :: nil) y x=true). 
intro. apply (H6 x). apply H4 with y; hyp. apply H5. unfold restriction.
simpl. tauto. generalize n0 e e0.
case (x0 (x :: y :: nil) x y); case (x0 (y :: x :: nil) x y); tauto.  
constructor 2. intro. absurd (x0 (y :: x :: nil) x y=true). intro.
rewrite e0 in H9. inversion H9. 
pose (H2 (y::x::nil)). decompose [and] a. apply H11. unfold restriction. simpl.
tauto. 
constructor 2. intro. absurd (x0 (x::y:: nil) x y=true). intro.
rewrite e in H9. inversion H9. 
apply H5. unfold restriction. simpl. tauto. 
Qed. 

Lemma rel_dec_topo_sortable_eq_dec :  forall R, 
  rel_dec R -> topo_sortable R -> eq_dec A.

Proof.
intros R Rd H. apply total_order_eq_dec. exists (let (first,second):=H in first).
destruct H. intro. pose (l l0). destruct l1. split; tauto. 
Qed. 

Lemma rel_dec_topo_sortable_acyclic :  forall R, 
  rel_dec R -> topo_sortable R -> irreflexive (clos_trans R).

Proof.
intros R Rd H. apply local_global_acyclic. intro. destruct H.
exists (fun x0 y => x l x0 y=true). destruct (l0 l). tauto. 
Qed.

End On_relation_completion.
