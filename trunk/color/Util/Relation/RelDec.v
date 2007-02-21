(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17

decidability of a relation
*)

(* $Id: RelDec.v,v 1.3 2007-02-21 12:38:33 stephaneleroux Exp $ *)

Set Implicit Arguments.

Require Export Path.

Section S.

Variable A : Set.

(***********************************************************************)
(* bound_path preserves middle exclusion and decidability for restrictions *)

Section bp_restriction_midex_dec.

Variable R : relation A.

Lemma dec_lem : forall R' R'' x y l,
rel_dec R' -> rel_dec R'' -> 
{z : A| In z l /\ R' x z /\ R'' z y}+{~exists z : A, In z l /\ R' x z /\ R'' z y}.

Proof.
induction l; intros. simpl. constructor 2. intro. destruct H1. tauto. 
destruct IHl; try assumption. constructor. destruct s. exists x0. simpl. tauto. 
destruct (H x a). destruct (H0 a y). constructor. exists a. simpl. tauto. 
constructor 2. intro. destruct H1. simpl in H1. decompose [and or] H1.  
rewrite H4 in n0. tauto. assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. 
tauto. contradiction. constructor 2. intro. destruct H1. simpl in H1. 
decompose  [and or] H1. rewrite H4 in n0. contradiction.
assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. tauto. contradiction.
Qed. 

Lemma midex_lem : forall R' R'' x y l, rel_midex R' -> rel_midex R'' -> 
(exists z : A,  In z l /\ R' x z /\ R'' z y) \/ (~exists z : A, In z l /\ R' x z /\ R'' z y).

Proof.
induction l; intros. simpl. constructor 2. intro. destruct H1. tauto.  
destruct IHl; try assumption. constructor. destruct H1. exists x0. simpl. tauto. 
destruct (H x a). destruct (H0 a y). constructor. exists a. simpl. tauto. 
constructor 2. intro. destruct H4. simpl in H4. decompose [and or] H4.  
rewrite H7 in H3. tauto. assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. 
tauto. contradiction. constructor 2. intro. destruct H3. simpl in H3. 
decompose  [and or] H3. rewrite H6 in H2. contradiction.
assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. tauto. contradiction.
Qed.

Lemma bound_path_dec : forall l n,
is_restricted R l -> rel_dec R -> rel_dec (bound_path R n).

Proof.
unfold rel_dec. induction n; intros. destruct (H0 x y). constructor. 
apply bp_intro with (nil : list A). trivial. simpl. assumption. constructor 2. intro. 
inversion H1. destruct l0. simpl in H3. contradiction. simpl in H2. 
exact (le_Sn_O (length l0) H2). destruct (IHn H H0 x y). constructor. 
apply bound_path_n_Sn. assumption. 
assert ({z : A | In z l /\ R x z /\ bound_path R n z y}
+{~exists z : A, In z l /\ R x z /\ bound_path R n z y}).
apply dec_lem; tauto. destruct H1. constructor. destruct s. 
apply R_bound_path_n_Sn with x0; tauto. 
constructor 2. intro. pose (bound_path_Sn_n_or_Rn H1). destruct o. contradiction.
destruct H2. assert (exists z : A, In z l /\ R x z /\ bound_path R n z y). 
exists x0. split. pose (H x x0). tauto. assumption. contradiction.   
Qed.

Lemma bound_path_midex : forall l n,
is_restricted R l -> rel_midex R -> rel_midex (bound_path R n).

Proof.
unfold rel_midex. induction n; intros. destruct (H0 x y). constructor. 
apply bp_intro with (nil : list A). trivial. simpl. assumption. constructor 2. intro. 
inversion H2. destruct l0. simpl in H4. contradiction. simpl in H3. 
exact (le_Sn_O (length l0) H3). destruct (IHn H H0 x y). constructor. 
apply bound_path_n_Sn. assumption. 
assert ((exists z : A,  In z l /\ R x z /\  bound_path R n z y) \/
(~exists z : A,  In z l /\ R x z /\  bound_path R n z y)).
apply midex_lem; tauto. destruct H2. destruct H2. constructor. 
apply R_bound_path_n_Sn with x0; tauto. 
constructor 2. intro. destruct (bound_path_Sn_n_or_Rn H3). contradiction.
destruct H4. assert (exists z : A, In z l /\ R x z /\ bound_path R n z y). 
exists x0. split. pose (H x x0). tauto. assumption. contradiction.   
Qed.

Lemma resticted_dec_clos_trans_dec : 
eq_dec A -> rel_dec R -> forall l, is_restricted R l  -> rel_dec (clos_trans R).

Proof.
do 6 intro. destruct (bound_path_dec (length l) H1 H0 x y) . 
constructor. apply (bound_path_clos_trans b). 
constructor 2. intro. pose (clos_trans_bound_path (eq_dec_midex H) H1 H2). 
contradiction. 
Qed. 

Lemma resticted_midex_clos_trans_midex : 
eq_midex A -> rel_midex R -> forall l, is_restricted R l  -> rel_midex (clos_trans R).

Proof.
do 6 intro. destruct (bound_path_midex (length l) H1 H0 x y) . 
constructor. apply (bound_path_clos_trans H2). 
constructor 2. intro. pose (clos_trans_bound_path H H1 H3). 
contradiction. 
Qed. 

End bp_restriction_midex_dec.

(***********************************************************************)
(* middle-excluding/decidability of a relation
is equivalent to middle-excluding/decidability of
the transitive closure of every finite restriction of the relation *)

Section em_dec_clos_trans.

Variable R : relation A.


Theorem R_midex_clos_trans_restriction_midex :
eq_midex A -> rel_midex R -> forall l, rel_midex (clos_trans (restriction R l)).

Proof.
intros. apply resticted_midex_clos_trans_midex with l. assumption. 
apply restriction_midex; assumption. apply restricted_restriction.  
Qed.  

Theorem R_dec_clos_trans_restriction_dec :
eq_dec A -> rel_dec R -> forall l, rel_dec (clos_trans (restriction R l)).

Proof.
intros. apply resticted_dec_clos_trans_dec with l. assumption. 
apply restriction_dec; assumption. apply restricted_restriction.  
Qed. 

Theorem clos_trans_restriction_dec_R_dec :
(forall l, rel_dec (clos_trans (restriction R l))) -> rel_dec R.

Proof.
do 3 intro. destruct (H (x::y::nil) x y). constructor.
pose sub_rel_restriction. unfold sub_rel in s. apply s with A (x::y::nil). 
apply clos_trans_restricted_pair. apply restricted_restriction. assumption. 
constructor 2. intro. pose (clos_trans_restriction R x y). tauto.  
Qed. 

Theorem clos_trans_restriction_midex_R_midex :
(forall l, rel_midex (clos_trans (restriction R l))) -> rel_midex R.

Proof.
do 3 intro. destruct (H (x::y::nil) x y). constructor.
pose sub_rel_restriction. unfold sub_rel in s. apply s with A (x::y::nil). 
apply clos_trans_restricted_pair. apply restricted_restriction. assumption. 
constructor 2. intro. pose (clos_trans_restriction R x y). tauto. 
Qed. 

End em_dec_clos_trans.

End S.

(*
Section S.

Variable A : Set.
Variable eq_dec : forall x y : A, {x=y}+{x<>y}.

(***********************************************************************)
(** bound_path is decidable for sub *)

Section bp_sub_decidable.

Variable R : relation A.
Variable l : list A.

Lemma sub_dec : Rel_dec R -> Rel_dec (sub R l).

Proof.
unfold Rel_dec, sub. intros. destruct (H x y). destruct (In_dec eq_dec x l).
destruct (In_dec eq_dec y l). constructor. tauto. constructor 2. intro. tauto. 
constructor 2. intro. tauto. constructor 2. intro. tauto.
Qed. 

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
destruct (path_mono_length eq_dec (sub R l) x y x0 H0). apply bp_intro with x1. 
apply mono_incl_length. assumption. tauto. apply path_sub_incl with R y x. 
tauto. tauto. 
Qed.

Lemma R_dec_clos_trans_sub_dec :
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
destruct l'; simpl in H1. apply i with (l := x::y::nil). assumption. 
destruct (eq_dec y a). apply i with (l := x::y::nil). rewrite <- e in H1. tauto. 
simpl in H4. assert (x=a). pose (H4 a). tauto.
destruct l'; simpl in H1. apply i with (l := x::y::nil). rewrite <- H5 in H1.
tauto. 
destruct (eq_dec y a0). apply i with (l := x::y::nil). rewrite <- e in H1. 
rewrite <- H5 in H1. tauto. 
simpl in H4. assert (x=a0). pose (H4 a0). tauto.
destruct l'; simpl in H1. apply i with (l :=  x::y::nil). rewrite <- H6 in H1.
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

Lemma clos_trans_sub_dec_R_dec :
  (forall l : list A, Rel_dec (sub R l !)) -> Rel_dec R.

Proof.
unfold Rel_dec. intros. destruct (H (x::y::nil) x y). constructor. 
apply clos_trans_sub_R. assumption. constructor 2. intro. 
pose (R_clos_trans_sub H0). contradiction. 
Qed. 

End dec_clos_trans.

End S.*)
