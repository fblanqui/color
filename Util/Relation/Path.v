(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17

*)

(* $Id: Path.v,v 1.4 2007-02-07 11:16:46 blanqui Exp $ *)

Set Implicit Arguments.

Section On_transitive_closure.

Variable A : Set.
Variable A_dec : forall x y : A, {x=y}+{x<>y}.

Require Export RelUtil.
Require Export ListUtil.

(***********************************************************************)
(** path *)

Section Path.

Variable R : relation A.

Fixpoint path (x y : A) (l : list A) {struct l} : Prop :=
  match l with
    | nil => R x y
    | z::l => R x z /\ path z y l
  end.

Definition cycle x := path x x.

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
destruct (list_eq_dec A_dec (z :: l'')(a :: l')). inversion e. simpl in H.
tauto. simpl in H. 
apply IHl' with a. tauto. apply suffix_smaller with a; assumption.
Qed.

Lemma path_cut : forall (y : A) l' (x : A),
  In x l' -> path x y l' -> path x y (tail(cut A_dec x l')). 

Proof.
intros. apply path_suffix with l' x. assumption.
rewrite <- (cut_head  A_dec x l' H). apply suffix_cut.
Qed.

Lemma path_cut_bis : forall l' (x y z : A),
  In z l' -> R x z -> path z y l' -> path x y (cut A_dec z l'). 

Proof.
intros. rewrite (cut_head A_dec z l'). simpl.
assert (path z y (tail (cut A_dec z l'))).
apply path_cut; assumption. destruct l'. pose (in_nil H).
contradiction. tauto. assumption. 
Qed.

Lemma path_shrink : forall (y : A) l' (x : A),
  path x y l' -> path x y (shrink A_dec l').

Proof.
induction l'; simpl; intros. assumption. assert (path a y (shrink A_dec l')).
apply IHl'; tauto. destruct (In_dec A_dec a (shrink A_dec l')).
apply path_cut_bis; tauto. simpl. tauto.
Qed.

Lemma path_mono_length : forall (x y : A) l', path x y l' ->
  exists l'', mono l'' /\ length l''<= length l' /\ path x y l''.

Proof.
intros. exists (shrink A_dec l'). 
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

Lemma inclusion_sub : sub << R.

Proof.
unfold inclusion, sub. intros. tauto.
Qed.

Lemma sub_dec : Rel_dec R -> Rel_dec sub.

Proof.
unfold Rel_dec, sub. intros. destruct (H x y). destruct (In_dec A_dec x l).
destruct (In_dec A_dec y l). constructor. tauto. constructor 2. intro. tauto. 
constructor 2. intro. tauto. constructor 2. intro. tauto.
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
apply path_monotonic with (fun x0 y0 : A =>  (a = x0 \/ y = x0 \/ In x0 l) /\
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

(***********************************************************************)
(** bound_path is decidable for sub *)

Section bp_sub_decidable.

Variable R : relation A.
Variable l : list A.

Lemma dec_lem : forall (R' R'': relation A) (x y : A) l',
  Rel_dec R' -> Rel_dec R'' -> 
  {z : A | In z l' /\ R' x z /\ R'' z y}
  +{~exists z, In z l' /\ R' x z /\ R'' z y}.

Proof.
induction l'; intros. simpl. constructor 2. intro. destruct H1. tauto. 
destruct (IHl' H H0). constructor. destruct s. exists x0. simpl. tauto. 
destruct (H x a). destruct (H0 a y). constructor. exists a. simpl. tauto. 
constructor 2. intro. destruct H1. simpl in H1. decompose [and or] H1.  
rewrite H4 in n0. tauto. assert (exists z : A, In z l' /\ R' x z /\ R'' z y).
exists x0. 
tauto. contradiction. constructor 2. intro. destruct H1. simpl in H1. 
decompose  [and or] H1. rewrite H4 in n0. contradiction.
assert (exists z : A, In z l' /\ R' x z /\ R'' z y). exists x0. tauto.
contradiction.
Qed. 

Lemma bound_path_dec : forall n : nat,
  Rel_dec (sub R l) -> Rel_dec (bound_path (sub R l) n).

Proof.
unfold Rel_dec. induction n; intros. destruct (H x y). constructor. 
apply bp_intro with (nil : list A). trivial. simpl. assumption. constructor 2.
intro. 
inversion H0. destruct l'. simpl in H2. contradiction. simpl in H1.
exact (le_Sn_O (length l') H1). 
destruct (IHn H x y). constructor. apply bound_path_n_Sn. assumption. 
assert ({z : A | In z l /\ (sub R l) x z /\ bound_path (sub R l) n z y}
+{~exists z : A, In z l /\ (sub R l) x z /\ bound_path (sub R l) n z y}).
apply dec_lem; tauto. destruct H0. constructor. destruct s. 
apply R_bound_path_n_Sn with x0; tauto. 
constructor 2. intro. pose (bound_path_Sn_n_or_Rn H0). destruct o. contradiction.
destruct H1.
assert (exists z : A, In z l /\ (sub R l) x z /\ bound_path (sub R l) n z y). 
exists x0. split. unfold sub in H1. tauto. assumption. contradiction.   
Qed.

End bp_sub_decidable.

(***********************************************************************)
(** decidability of a relation is equivalent to decidability of the
transitive closure of every finite restriction of the relation *)

Section dec_clos_trans.

Variable R : relation A.

Lemma clos_trans_sub_bound_path : forall l : list A,
  sub R l ! << bound_path (sub R l) (length l).

Proof.
unfold inclusion. intros. destruct (clos_trans_path H).
destruct (path_mono_length (sub R l) x y x0 H0). apply bp_intro with x1. 
apply mono_incl_length. assumption. tauto. apply path_sub_incl with R y x. 
tauto. tauto. 
Qed.

Theorem R_dec_clos_trans_sub_dec :
  Rel_dec R -> forall l : list A, Rel_dec (sub R l !).

Proof.
unfold Rel_dec. intros. pose (sub_dec l H). 
destruct (bound_path_dec (length l) r x y). constructor. 
pose bound_path_clos_trans. unfold inclusion in i. 
apply i with (length l). assumption. constructor 2. intro.
pose (clos_trans_sub_bound_path H0). contradiction. 
Qed. 

Lemma clos_trans_sub_R : forall x y : A,
  sub R (x :: y :: nil) ! x y -> R x y.

Proof.
intros. pose (clos_trans_sub_bound_path H). inversion b.  
assert (incl l' (x :: y :: nil)). apply path_sub_incl with R y x. assumption. 
unfold incl in H4. simpl in H4. 
pose inclusion_sub. unfold inclusion in i.
destruct l'; simpl in H1. apply i with (x :: y :: nil). assumption. 
destruct (A_dec y a). apply i with (x::y::nil). rewrite <- e in H1. tauto. 
simpl in H4. assert (x=a). pose (H4 a). tauto.
destruct l'; simpl in H1. apply i with (x :: y :: nil). rewrite <- H5 in H1.
tauto. 
destruct (A_dec y a0). apply i with (x::y::nil). rewrite <- e in H1. 
rewrite <- H5 in H1. tauto. 
simpl in H4. assert (x=a0). pose (H4 a0). tauto.
destruct l'; simpl in H1. apply i with (x :: y :: nil). rewrite <- H6 in H1.
tauto. 
simpl in H0. inversion H0. inversion H8. inversion H10. 
Qed.

Lemma R_clos_trans_sub : forall x y : A,
  R x y -> sub R (x :: y :: nil) ! x y.

Proof.
intros. pose bound_path_clos_trans. unfold inclusion in i. 
apply i with 2. apply bp_intro with (nil : list A). simpl. apply le_O_n.
unfold sub. 
simpl. tauto. 
Qed.

Theorem clos_trans_sub_dec_R_dec :
  (forall l : list A, Rel_dec (sub R l !)) -> Rel_dec R.

Proof.
unfold Rel_dec. intros. destruct (H (x::y::nil) x y). constructor. 
apply clos_trans_sub_R. assumption. constructor 2. intro. 
pose (R_clos_trans_sub H0). contradiction. 
Qed. 

End dec_clos_trans.

End On_transitive_closure.
