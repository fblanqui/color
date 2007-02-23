(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2007-02-23

decidability of a relation:
In an arbitrary set with decidable (resp. middle-excluding) equality,
a binary relation  is decidable (resp. middle-excluding) 
iff the transitive closures of its finite restrictions are decidable
(resp. middle-excluding)
*)

(* $Id: RelDec.v,v 1.5 2007-02-23 18:03:10 blanqui Exp $ *)

Set Implicit Arguments.

Require Export Path.

Section S.

Variable A : Set.

(***********************************************************************)
(* bound_path preserves middle exclusion and decidability for restrictions *)

Section bp_restriction_midex_dec.

Variable R : relation A.

Lemma dec_lem : forall R' R'' x y l, rel_dec R' -> rel_dec R'' -> 
  {z : A| In z l /\ R' x z /\ R'' z y}
  + {~exists z : A, In z l /\ R' x z /\ R'' z y}.

Proof.
induction l; intros. simpl. constructor 2. intro. destruct H1. tauto. 
destruct IHl; try assumption. constructor. destruct s. exists x0. simpl. tauto. 
destruct (H x a). destruct (H0 a y). constructor. exists a. simpl. tauto. 
constructor 2. intro. destruct H1. simpl in H1. decompose [and or] H1.  
rewrite H4 in n0. tauto. assert (exists z : A, In z l /\ R' x z /\ R'' z y).
exists x0. 
tauto. contradiction. constructor 2. intro. destruct H1. simpl in H1. 
decompose  [and or] H1. rewrite H4 in n0. contradiction.
assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. tauto.
contradiction.
Qed. 

Lemma midex_lem : forall R' R'' x y l, rel_midex R' -> rel_midex R'' -> 
  (exists z : A,  In z l /\ R' x z /\ R'' z y)
  \/ (~exists z : A, In z l /\ R' x z /\ R'' z y).

Proof.
induction l; intros. simpl. constructor 2. intro. destruct H1. tauto.  
destruct IHl; try assumption. constructor. destruct H1. exists x0. simpl. tauto. 
destruct (H x a). destruct (H0 a y). constructor. exists a. simpl. tauto. 
constructor 2. intro. destruct H4. simpl in H4. decompose [and or] H4.  
rewrite H7 in H3. tauto. assert (exists z : A, In z l /\ R' x z /\ R'' z y).
exists x0. 
tauto. contradiction. constructor 2. intro. destruct H3. simpl in H3. 
decompose  [and or] H3. rewrite H6 in H2. contradiction.
assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. tauto.
contradiction.
Qed.

Lemma bound_path_dec : forall l n,
  is_restricted R l -> rel_dec R -> rel_dec (bound_path R n).

Proof.
unfold rel_dec. induction n; intros. destruct (H0 x y). constructor. 
apply bp_intro with (nil : list A). trivial. simpl. assumption. constructor 2.
intro. 
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
apply bp_intro with (nil : list A). trivial. simpl. assumption. constructor 2.
intro. 
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
 
Lemma resticted_dec_clos_trans_dec : eq_dec A -> rel_dec R ->
  forall l, is_restricted R l  -> rel_dec (clos_trans R).

Proof.
do 6 intro. destruct (bound_path_dec (length l) H1 H0 x y) . 
constructor. apply (bound_path_clos_trans b). 
constructor 2. intro. pose (clos_trans_bound_path (eq_dec_midex H) H1 H2). 
contradiction. 
Qed. 

Lemma resticted_midex_clos_trans_midex : eq_midex A -> rel_midex R ->
  forall l, is_restricted R l  -> rel_midex (clos_trans R).

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

Lemma R_midex_clos_trans_restriction_midex : eq_midex A -> rel_midex R ->
  forall l, rel_midex (clos_trans (restriction R l)).

Proof.
intros. apply resticted_midex_clos_trans_midex with l. assumption. 
apply restriction_midex; assumption. apply restricted_restriction.  
Qed.  

Lemma R_dec_clos_trans_restriction_dec : eq_dec A -> rel_dec R ->
  forall l, rel_dec (clos_trans (restriction R l)).

Proof.
intros. apply resticted_dec_clos_trans_dec with l. assumption. 
apply restriction_dec; assumption. apply restricted_restriction.  
Qed. 

Lemma clos_trans_restriction_dec_R_dec :
  (forall l, rel_dec (clos_trans (restriction R l))) -> rel_dec R.

Proof.
do 3 intro. destruct (H (x::y::nil) x y). constructor.
pose sub_rel_restriction. unfold sub_rel in s. apply s with A (x::y::nil). 
apply clos_trans_restricted_pair. apply restricted_restriction. assumption. 
constructor 2. intro. pose (clos_trans_restriction R x y). tauto.  
Qed. 

Lemma clos_trans_restriction_midex_R_midex :
  (forall l, rel_midex (clos_trans (restriction R l))) -> rel_midex R.

Proof.
do 3 intro. destruct (H (x::y::nil) x y). constructor.
pose sub_rel_restriction. unfold sub_rel in s. apply s with A (x::y::nil). 
apply clos_trans_restricted_pair. apply restricted_restriction. assumption. 
constructor 2. intro. pose (clos_trans_restriction R x y). tauto. 
Qed. 

End em_dec_clos_trans.

End S.