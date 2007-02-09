(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17

*)

(* $Id: Path.v,v 1.7 2007-02-09 10:10:27 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Variable A : Set.
Variable eq_dec : forall x y : A, {x=y}+{x<>y}.

Require Export RelUtil.
Require Export ListShrink.

(***********************************************************************)
(** path *)

Section Path.

Variable R : relation A.

Fixpoint path (x y : A) (l : list A) {struct l} : Prop :=
  match l with
    | nil => R x y
    | z::l => R x z /\ path z y l
  end.

Lemma path_app_elim : forall l x y z m,
  path x y (l ++ z :: m) -> path x z l /\ path z y m.

Proof.
induction l; simpl; intros. exact H. destruct H. deduce (IHl _ _ _ _ H0).
intuition.
Qed.

Lemma path_app_intro : forall l x y z m,
  path x z l -> path z y m -> path x y (l ++ z :: m).

Proof.
induction l; simpl; intuition.
Qed.

Lemma path_clos_trans : forall (y : A) l x, path x y l -> R! x y.

Proof.
induction l; simpl; intros. constructor. assumption.
constructor 2 with a. constructor. tauto. apply IHl. tauto.
Qed.

Lemma path_app : forall (y z: A) l' l (x : A),
  path x y l -> path y z l' -> path x z (l++(y::l')). 

Proof.
induction l; simpl; intros. tauto. split. tauto. apply IHl; tauto.
Qed. 

Lemma clos_trans_path : forall (x y : A), R! x y -> exists l, path x y l.

Proof.
intros. induction H. exists (nil : list A). simpl. assumption.
destruct IHclos_trans1. destruct IHclos_trans2. exists (x0++(y::x1)). 
apply path_app; assumption.
Qed.

Lemma path_suffix : forall (y z : A) l' l'' (x : A),
  path x y l' -> suffix (z::l'') l' -> path z y l''.

Proof.
induction l'; intros. assert (rev (z :: l'')=nil). apply prefix_nil. assumption.
simpl in H1. symmetry in H1. pose (app_cons_not_nil (rev l'') nil z H1). tauto.
destruct (list_eq_dec eq_dec (z :: l'')(a :: l')). inversion e. simpl in H.
tauto. simpl in H. 
apply IHl' with a. tauto. apply suffix_smaller with a; assumption.
Qed.

Lemma path_cut : forall (y : A) l' (x : A),
  In x l' -> path x y l' -> path x y (tail(cut eq_dec x l')). 

Proof.
intros. apply path_suffix with l' x. assumption.
rewrite <- (cut_head eq_dec x l' H). apply suffix_cut.
Qed.

Lemma path_cut_bis : forall l' (x y z : A),
  In z l' -> R x z -> path z y l' -> path x y (cut eq_dec z l'). 

Proof.
intros. rewrite (cut_head eq_dec z l'). simpl.
assert (path z y (tail (cut eq_dec z l'))).
apply path_cut; assumption. destruct l'. pose (in_nil H).
contradiction. tauto. assumption. 
Qed.

Lemma path_shrink : forall (y : A) l' (x : A),
  path x y l' -> path x y (shrink eq_dec l').

Proof.
induction l'; simpl; intros. assumption. assert (path a y (shrink eq_dec l')).
apply IHl'; tauto. destruct (In_dec eq_dec a (shrink eq_dec l')).
apply path_cut_bis; tauto. simpl. tauto.
Qed.

Lemma path_mono_length : forall (x y : A) l', path x y l' ->
  exists l'', mono l'' /\ length l''<= length l' /\ path x y l''.

Proof.
intros. exists (shrink eq_dec l'). 
split. apply mono_shrink. split. apply length_shrink. apply incl_refl. 
apply path_shrink. assumption.
Qed. 

(***********************************************************************)
(** bound_path *)

Require Import Arith.

Inductive bound_path (n : nat) : relation A :=
| bp_intro : forall (x y : A) l',
  length l'<= n -> path x y l' -> bound_path n x y.

Lemma bound_path_n_Sn : forall (n : nat) (x y : A),
  bound_path n x y -> bound_path (S n) x y.

Proof.
intros. inversion H. apply bp_intro with l'. apply le_trans with n. assumption. 
apply le_n_Sn. assumption.
Qed.

Lemma bound_path_clos_trans : forall n : nat, bound_path n << R!.

Proof.
unfold inclusion. intros. inversion H. apply path_clos_trans with l'.
assumption. 
Qed.

Lemma bound_path_Sn_n_or_Rn : forall (n : nat) (x y : A),
  bound_path (S n) x y ->
  bound_path n x y \/ exists z : A, R x z /\ bound_path n z y.

Proof.
intros. inversion H. destruct (le_le_S_dec (length l') n). 
constructor. apply bp_intro with l'; assumption. constructor 2. 
destruct l'. simpl in l. pose (le_Sn_O n l). tauto. exists a. simpl in H0, H1. 
split. tauto. apply bp_intro with l'. apply le_S_n. assumption. tauto.
Qed.

Lemma R_bound_path_n_Sn : forall (x y z : A) (n : nat),
  R x y -> bound_path n y z -> bound_path (S n) x z.

Proof.
intros. inversion H0. apply bp_intro with (y::l'). simpl. apply le_n_S.
assumption. simpl. tauto. 
Qed.

End Path.

Lemma path_monotonic : forall (R R' : relation A) (y : A) l' (x : A),
  R << R' -> path R x y l' -> path R' x y l'.

Proof.
unfold inclusion. induction l'; intros; simpl in H0 |- * . apply H. assumption. 
split. pose (H x a). tauto. pose (IHl' a). tauto.
Qed.

(***********************************************************************)
(** restriction *)

Section sub_Rel.

Variable R : relation A.
Variable l : list A.

Definition sub (x y : A) := In x l /\ In y l /\ R x y.

Definition restricted := R << sub.

Lemma restricted_path_incl : restricted ->
  forall m x y, path R x y m -> incl m l.

Proof.
induction m; simpl; intros. apply incl_nil. destruct H0. apply incl_cons.
deduce (incl_elim H H0). unfold sub in H2. intuition.
eapply IHm. apply H1.
Qed.

Lemma inclusion_sub : sub << R.

Proof.
unfold inclusion, sub. intros. tauto.
Qed.

Lemma path_sub_In_left : forall (x y : A) l', path sub x y l' -> In x l.

Proof.
unfold sub. intros; destruct l'; simpl in H; tauto.
Qed.

Lemma path_sub_incl : forall (y : A) l' (x : A), path sub x y l' -> incl l' l.

Proof.
induction l'; simpl; intros. apply incl_nil.
destruct H. unfold incl. intros. simpl in H1. destruct H1. subst a0.
eapply path_sub_In_left. apply H0. unfold incl in IHl'. eapply IHl'. apply H0.
exact H1.
Qed. 

End sub_Rel.

Lemma path_sub : forall (R : relation A) (y : A) l (x : A),
  path R x y l -> path (sub R (x::y::l)) x y l.

Proof.
unfold sub. induction l; simpl; intros. tauto. split. tauto. simpl in IHl. 
apply path_monotonic with (fun x0 y0 : A => (a = x0 \/ y = x0 \/ In x0 l) /\
(a = y0 \/ y = y0 \/ In y0 l) /\ R x0 y0). unfold inclusion. intros. tauto. 
apply IHl. tauto.
Qed.

Lemma restricted_clos_trans_sub : forall (R : relation A) (l : list A),
  restricted (sub R l !) l.

Proof.
unfold restricted, sub, inclusion. intros. induction H. 
split. tauto. split. tauto. constructor. assumption.  
split. tauto. split. tauto. constructor 2 with y; assumption. 
Qed. 

Lemma sub_monotonic : forall (R' R'' : relation A) l,
  R' << R'' -> sub R' l << sub R'' l.

Proof.
unfold inclusion, sub. intros. pose (H x y). tauto.
Qed.

End S.

Implicit Arguments path_app_elim [A R l x y z m].