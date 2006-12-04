(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17

************************************************************************)

(* $Id: Total.v,v 1.1 2006-12-04 18:04:57 blanqui Exp $ *)

Set Implicit Arguments.

Section On_total_completion.

Require Export Path.

Variable A : Set.
Variable A_dec : forall x y : A, {x=y}+{x<>y}.

(***********************************************************************)
(* total *)

Section total.

Variable R : relation A.

Definition xytotal x y := R x y \/ x=y \/ R y x.

Definition total (l : list A) := forall x y, In x l -> In y l -> xytotal x y.

End total.

Definition trans_total_irrefl  (R : relation A) (l : list A) :=
  transitive R /\ total R l /\ irreflexive R.

Lemma xytotal_monotonic : forall (R R' : relation A) x y,
  R << R' -> xytotal R x y -> xytotal R' x y.

Proof.
unfold inclusion, xytotal. intros. pose (H x y). pose (H y x). tauto.
Qed. 

(***********************************************************************)
(* add *)

Section add.

Variable R : relation A.
Variable R_dec : Rel_dec R.
Variable l : list A. 

Definition add (x y z t : A) := R z t \/ (z<>t /\ x=z /\ y=t /\ ~R t z).

Lemma add_refl : forall x y z, add x y z z -> R z z.

Proof.
intros. inversion H. assumption. tauto. 
Qed.

Lemma inclusion_R_add : forall x y, R << add x y.

Proof.
unfold inclusion, add. intros. tauto.
Qed.

Lemma inclusion_add_R : forall x y, R x y \/ R y x -> add x y << R.

Proof.
unfold inclusion, add; intros. destruct H0. assumption. decompose [and] H0. 
rewrite H3 in H. rewrite H2 in H. tauto.
Qed.

Lemma add2_R :  forall x y z t, add x y z t -> add x y t z -> R z t.

Proof.
unfold add. intros. decompose [or and] H. assumption.  
decompose [or and] H0. tauto. rewrite H1 in H4. tauto.
Qed.

Lemma add_notR : forall x y z t, 
  ~R z t -> add x y z t -> (x=z \/ x=t) /\ (y=z \/ y=t) /\ z<>t.

Proof.
unfold add. intros. tauto.
Qed. 

Lemma add_dec : forall x y, Rel_dec R -> Rel_dec (add x y).

Proof.
unfold Rel_dec. intros. unfold add. destruct (H x0 y0). tauto. 
destruct (A_dec x0 y0). tauto. destruct (H y0 x0). tauto. destruct (A_dec x x0).
destruct (A_dec y y0).
destruct (A_dec x0 y0). tauto. tauto. tauto. tauto. 
Qed.

Lemma add_xytotal : forall x y, xytotal (add x y) x y.

Proof.
unfold xytotal. intros. destruct (A_dec x y). tauto. unfold add.
destruct (R_dec x y). tauto. 
destruct (R_dec y x). tauto. tauto.
Qed.

Lemma xytotal_sub : forall x y,
  In x l -> In y l -> xytotal R x y -> xytotal (sub R l) x y.

Proof.
unfold xytotal, sub. intros. tauto. 
Qed.

Lemma  path_add_path : forall y z t (l' : list A) x, 
  ~(z=x \/ In z l') \/ ~(t=y \/ In t l') ->
  path (add z t) x y l' -> path R x y l'. 

Proof.
unfold add. induction l'; simpl; intuition. apply IHl'.
constructor. intro. destruct H3. rewrite H3 in H0. tauto. tauto. assumption.
apply IHl'. constructor 2. intro. destruct H3. rewrite H3 in H0. tauto. tauto.
assumption. rewrite H3 in H0. tauto. 
Qed.

Lemma trans_add2_R : forall x y z t,
  transitive R -> add x y z t -> add x y t z -> R z z.

Proof.
unfold transitive. intros. apply H with t; apply add2_R with x y; assumption. 
Qed.

Require Import Arith.

Lemma trans_bound_path_add : forall x y z n,
  transitive R -> bound_path (add x y ) n z z -> R z z.

Proof.
intros. induction n. inversion H0. destruct l'. simpl in H2. 
apply trans_add2_R with x y z; assumption. 
simpl in H1. pose (le_Sn_O (length l') H1). contradiction. apply IHn.
inversion H0. clear H0 H3 H4 x0 y0. 
(* mono *)
destruct (path_mono_length A_dec (add x y)  z z l' H2). destruct H0. 
destruct H3. assert (length x0 <= S n).
apply le_trans with (length l'); assumption.
clear H1 H2 H3 l'. 
(* x0=nil *) 
destruct x0. exists (nil : list A). apply le_O_n. assumption. 
(* length x0 = 1 *) 
(* z in x0 *)
destruct (In_dec A_dec z (a::x0)). exists (tail (cut A_dec z (a::x0))). 
apply le_trans with (length x0). apply length_tail_cut_cons. apply le_S_n. tauto.
apply path_cut; assumption. 
(* z not in x0 *)
destruct x0; simpl in * |- . exists (nil : list A). apply le_O_n. simpl. 
apply inclusion_R_add. apply trans_add2_R with x y a; tauto. 
(* length x0 >= 2*)
destruct H4. destruct H2. unfold add in H1, H2. intuition. 
exists (a0::x0). simpl. apply le_S_n. assumption.
simpl. split. apply (inclusion_R_add). apply H with a; assumption. tauto. 
(**)
absurd (R a0 a). tauto. apply trans_tc_incl. assumption. 
apply path_clos_trans with (x0++(z::nil)). apply path_app. 
apply path_add_path with x y. rewrite H1. tauto. assumption. simpl. assumption.  
(**)
absurd (R a z). tauto. apply trans_tc_incl. assumption. 
apply path_clos_trans with (a0::x0). split. assumption.  
apply path_add_path with x y. rewrite H8. tauto. assumption. 
(**) 
rewrite H9 in H6. tauto. 
Qed.

Lemma add_irrefl : forall x y,
  transitive R -> irreflexive R -> irreflexive (add x y !).
 
Proof.
unfold irreflexive. intros. intro. apply H0 with x0.
destruct (clos_trans_path H1).
apply trans_bound_path_add with x y (length x1). assumption.
apply bp_intro with x1; trivial. 
Qed.

End add.

(***********************************************************************)
(* ladd: multiple add with one list *)

Section ladd.

Variable R : relation A.
Variable R_dec : Rel_dec R.
Variable l : list A.

Fixpoint ladd (x : A) (l' : list A) {struct l'} : relation A :=
  sub (match l' with
         | nil => R
         | y::l' => add (ladd x l') x y 
       end) l !.

Lemma ladd_dec : forall x l', Rel_dec (ladd x l').

Proof.
induction l'; simpl; intros. apply R_dec_clos_trans_sub_dec; assumption. 
apply R_dec_clos_trans_sub_dec. assumption. apply add_dec. apply IHl'.
Qed.

Lemma transitive_ladd : forall x l', transitive (ladd x l'). 

Proof.
intros. unfold ladd. destruct l'; apply tc_trans.
Qed.

Lemma restricted_ladd : forall x l', restricted (ladd x l') l.

Proof.
destruct l'; simpl; apply restricted_clos_trans_sub; assumption. 
Qed.

Lemma  inclusion_subR_ladd :  forall x l', sub R l << ladd x l'.

Proof.
induction l'; simpl; intros. apply tc_incl.
apply incl_trans with (ladd x l'). assumption. 
apply incl_trans with (sub (add (ladd x l') x a) l). 
apply incl_trans with (sub (ladd x l') l). apply restricted_ladd. 
apply sub_monotonic. apply inclusion_R_add. apply tc_incl.
Qed. 

Lemma ladd_xytotal : forall x y l',
  In x l -> In y l -> In y l' -> xytotal (ladd x l') x y.

Proof.
induction l';  simpl; intros. contradiction. 
apply xytotal_monotonic with (sub (add (ladd x l') x a) l). 
apply tc_incl. apply xytotal_sub. assumption. assumption.
destruct H1. rewrite H1. apply add_xytotal. apply ladd_dec. 
apply xytotal_monotonic with (ladd x l'). apply inclusion_R_add. tauto.
Qed.

Lemma ladd_irrefl : forall x l',
  irreflexive (sub R l !) -> irreflexive (ladd x l').

Proof.
induction l'; simpl; intros. assumption. 
apply incl_irrefl with (add (ladd x l') x a !). 
apply incl_tc. apply inclusion_sub. unfold ladd.
destruct l'; apply add_irrefl; try apply tc_trans; try tauto.
Qed.

End ladd.

(***********************************************************************)
(* lladd: multiple add with two lists *)

Section lladd.

Variable R : relation A.
Variable R_dec : Rel_dec R.
Variable l : list A.

Fixpoint lladd (l' : list A) : relation A :=
  match l' with
    | nil => sub R l !
    | x::l' => ladd (lladd l') l x l 
  end.

Lemma lladd_dec : forall l', Rel_dec (lladd l').

Proof.
induction l'; simpl; intros. apply R_dec_clos_trans_sub_dec. assumption. 
assumption. apply ladd_dec. assumption. 
Qed.

Lemma transitive_lladd : forall l', transitive (lladd l').

Proof.
unfold lladd. destruct l'. apply tc_trans. apply transitive_ladd.
Qed.

Lemma restricted_lladd : forall l', restricted (lladd l') l.

Proof.
destruct l'; simpl. apply restricted_clos_trans_sub. apply restricted_ladd.  
Qed.

Lemma  inclusion_subR_lladd : forall l', sub R l << lladd l'.
 
Proof.
induction l'; simpl; intros. apply tc_incl.
apply incl_trans with (lladd l'). assumption. 
apply incl_trans with (sub (lladd l') l). apply restricted_lladd.  
apply inclusion_subR_ladd.  
Qed.

Lemma lladd_xytotal : forall x y l',
  In x l -> In y l -> In x l' -> xytotal (lladd l') x y.

Proof.
induction l';  simpl; intros. contradiction. destruct H1. rewrite H1. 
apply ladd_xytotal. apply lladd_dec. assumption. assumption. assumption. 
apply xytotal_monotonic with (lladd l'). 
apply incl_trans with (sub (lladd l') l). apply restricted_lladd. 
apply inclusion_subR_ladd. tauto.
Qed.

Lemma lladd_irrefl : forall (l' : list A),
  irreflexive (sub R l !) -> irreflexive (lladd l').

Proof.
induction l'; simpl; intros. assumption. 
apply ladd_irrefl. apply incl_irrefl with (lladd l').
apply incl_trans with (lladd l' !). apply incl_tc. apply inclusion_sub.
apply trans_tc_incl. apply transitive_lladd. tauto.
Qed. 

End lladd.

(***********************************************************************)
(*  *)

Section TC.

Variable R : relation A.
Variable R_dec : Rel_dec R.
Variable l : list A.

Definition TC := lladd R l l.

Theorem TC_dec : Rel_dec TC.

Proof.
intros. unfold TC. apply lladd_dec. assumption.
Qed.

Lemma TC_inclusion : sub R l << TC.

Proof.
intros. unfold TC. apply inclusion_subR_lladd. 
Qed.

Lemma TC_restricted : restricted TC l.

Proof.
unfold inclusion, TC. intros. apply restricted_lladd.  
Qed.

Lemma TC_trans : transitive TC.

Proof.
intros. unfold TC. destruct l; simpl; apply tc_trans.
Qed.

Lemma TC_total : total TC l.

Proof.
unfold TC, total. intros. pose (R_dec_clos_trans_sub_dec A_dec R_dec l). 
apply lladd_xytotal; assumption.
Qed.

Lemma TC_irrefl : irreflexive (sub R l !) -> irreflexive TC.

Proof.
intros. unfold TC. apply lladd_irrefl. assumption. 
Qed. 

Lemma TC_strict_total_order :
  irreflexive (sub R l !) -> trans_total_irrefl TC l.

Proof.
split. apply TC_trans. split. apply TC_total. apply TC_irrefl. assumption.
Qed.

End TC.
 
Theorem  TC_properties : forall R : relation A,
  Rel_dec R -> irreflexive (R!) ->
  forall l, sub R l << TC R l /\ restricted (TC R l) l
    /\ trans_total_irrefl (TC R l) l.

Proof.
intros. split. apply TC_inclusion. split. apply TC_restricted.
apply TC_strict_total_order. assumption. 
apply incl_irrefl with (R!). apply incl_tc. apply inclusion_sub. assumption.
Qed.

Theorem total_completion_converse : forall (R : relation A),
  (forall l, exists R', sub R l << R' /\ transitive R' /\ irreflexive R') ->
  irreflexive (R!).

Proof.
intros. do 2 intro. destruct (clos_trans_path H0). 
assert (sub R (x::x::x0) ! x x). apply path_clos_trans with x0. 
apply path_sub. assumption. destruct (H (x::x::x0)). destruct H3. destruct H4. 
apply H5 with x. apply trans_tc_incl. assumption.
apply incl_tc with (sub R (x :: x :: x0)). assumption. assumption.
Qed.

End On_total_completion. 
