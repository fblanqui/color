(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2007-02-20

sub-relation, restriction, etc.
*)

Require Export ListShrink.

Set Implicit Arguments.

(***********************************************************************)
(* GENERAL DEFINITIONS AND LEMMAS ON BINARY RELATIONS *)

Section On_Rel_Gen.

Variable A : Set.

Definition sub_rel (A : Set) (R R' : relation A) := forall x y, R x y -> R' x y.

Lemma transitive_sub_rel : forall R R' R'' : relation A,
  sub_rel R R' -> sub_rel R' R'' -> sub_rel R R''.

Proof.
unfold sub_rel. intros. apply H0. apply H. assumption.
Qed.

Lemma clos_trans_monotonic : forall R' R'',
  sub_rel R' R'' -> sub_rel (clos_trans A R') (clos_trans A R'').

Proof.
unfold sub_rel. intros. induction H0. constructor. apply H. assumption. 
constructor 2 with y; assumption.  
Qed. 

Definition irreflexive (R : relation A) := forall x, ~R x x.

Lemma irreflexive_preserved : forall R R',
  sub_rel R R' -> irreflexive R' -> irreflexive R.

Proof.
unfold sub_rel, irreflexive. intros. intro. exact (H0 x (H x x H1)).
Qed.

Section restriction.

Variable R : relation A.
Variable l : list A.

Lemma reflexive_sub_rel : sub_rel R R.

Proof. 
do 2 intro. tauto. 
Qed.

Lemma sub_rel_clos_trans : sub_rel R (clos_trans A R).

Proof. 
do 3 intro. constructor. assumption. 
Qed.

Lemma transitive_clos_trans : transitive A (clos_trans A R).

Proof.
do 5 intro. constructor 2 with y; assumption.   
Qed.

Lemma transitive_sub_rel_clos_trans :
  transitive A R -> sub_rel (clos_trans A R) R.

Proof.
unfold transitive, sub_rel. intros. induction H0. assumption. 
apply H with y; assumption.   
Qed.

(***********************************************************************)
(* Restriction *)

Definition restriction x y := In x l /\ In y l /\ R x y.

Definition is_restricted := forall x y, R x y -> In x l /\ In y l.

Lemma sub_rel_restriction : sub_rel restriction R.

Proof.
unfold sub_rel, restriction. intros. tauto.
Qed. 

Lemma restriction_dec : eq_dec A -> rel_dec R -> rel_dec restriction.

Proof.
unfold restriction. do 4 intro. destruct (H0 x y). destruct (In_dec H x l).
destruct (In_dec H y l). 
constructor. tauto. constructor 2. tauto. constructor 2. tauto. constructor 2.
tauto.
Qed. 

Lemma restriction_midex : eq_midex A -> rel_midex R -> rel_midex restriction.

Proof.
unfold restriction. do 4 intro. destruct (H0 x y). destruct (In_midex H x l).
destruct (In_midex H y l). 
constructor. tauto. constructor 2. tauto. constructor 2. tauto. constructor 2.
tauto.
Qed. 

End restriction.

Lemma restricted_restriction : forall R l, is_restricted (restriction R l) l.

Proof.
unfold restriction, is_restricted. tauto. 
Qed.

Lemma restricted_clos_trans : forall R l,
  is_restricted R l -> is_restricted (clos_trans  A R) l.

Proof.
unfold is_restricted. intros. induction H0. apply H. assumption. tauto. 
Qed. 

Lemma clos_trans_restricted_pair : forall R x y,
  is_restricted R (x::y::nil) -> clos_trans A R x y -> R x y.

Proof.
intros. induction H0. assumption. 
destruct (restricted_clos_trans H H0_).
destruct H1. rewrite H1 in H. rewrite H1. tauto.
destruct H1. rewrite H1 in H. rewrite H1. tauto.
contradiction. 
Qed.

Lemma clos_trans_restricted_pair_bis : forall R x y,
  is_restricted R (x::y::nil) -> clos_trans A R y x -> R y x.

Proof.
intros. induction H0. assumption. 
destruct (restricted_clos_trans H H0_).
destruct H1. rewrite H1 in H. rewrite H1. tauto.
destruct H1. rewrite H1 in H. rewrite H1. tauto.
contradiction. 
Qed.

Lemma clos_trans_restriction : forall (R : relation A) x y,
  R x y -> clos_trans A (restriction R (x :: y :: nil)) x y.

Proof.
intros. constructor. unfold restriction. simpl. tauto.
Qed.

End On_Rel_Gen.
