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

Set Implicit Arguments.

From Coq Require Import Relations List Arith.
From CoLoR Require Import Path RelMidex RelSub LogicUtil.

Section S.

  Variable A : Type.

(***********************************************************************)
(** bound_path preserves middle exclusion and decidability for restrictions *)

  Section bp_restriction_midex_dec.

    Variable R : relation A.

    Lemma dec_lem : forall R' R'' x y l, rel_dec R' -> rel_dec R'' -> 
      {z : A | In z l /\ R' x z /\ R'' z y}
      + {~exists z : A, In z l /\ R' x z /\ R'' z y}.

    Proof.
      induction l; intros. simpl. constructor 2. intro. destruct H. tauto. 
      destruct IHl; try hyp. constructor. destruct s. exists x0. simpl. tauto. 
      destruct (X x a). destruct (X0 a y). constructor. exists a. simpl. tauto. 
      constructor 2. intro. destruct H. simpl in H. decompose [and or] H.  
      rewrite H2 in n0. tauto.
      assert (exists z : A, In z l /\ R' x z /\ R'' z y).
      exists x0. 
      tauto. contr. constructor 2. intro. destruct H. simpl in H. 
      decompose [and or] H. rewrite H2 in n0. contr.
      assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. tauto.
      contr.
    Qed.

    Lemma midex_lem : forall R' R'' x y l, rel_midex R' -> rel_midex R'' -> 
      (exists z : A,  In z l /\ R' x z /\ R'' z y)
      \/ (~exists z : A, In z l /\ R' x z /\ R'' z y).

    Proof.
      induction l; intros. simpl. constructor 2. intro. destruct H1. tauto.  
      destruct IHl; try hyp. constructor. destruct H1. exists x0. simpl.
      tauto.
      destruct (H x a). destruct (H0 a y). constructor. exists a. simpl. tauto. 
      constructor 2. intro. destruct H4. simpl in H4. decompose [and or] H4.  
      rewrite H7 in H3. tauto.
      assert (exists z : A, In z l /\ R' x z /\ R'' z y).
      exists x0. 
      tauto. contr. constructor 2. intro. destruct H3. simpl in H3. 
      decompose  [and or] H3. rewrite H6 in H2. contr.
      assert (exists z : A, In z l /\ R' x z /\ R'' z y). exists x0. tauto.
      contr.
    Qed.

    Lemma bpath_dec : forall l n,
      is_restricted R l -> rel_dec R -> rel_dec (bpath R n).

    Proof.
      unfold rel_dec. induction n; intros. destruct (X x y). constructor. 
      apply bp_intro with (nil : list A). trivial. simpl. hyp. constructor 2.
      intro.
      inversion H0. destruct l0. simpl in H2. contr. simpl in H1. 
      exact (Nat.nle_succ_0 (length l0) H1). destruct (IHn H X x y). constructor. 
      apply bpath_n_Sn. hyp.
      assert ({z : A | In z l /\ R x z /\ bpath R n z y}
        +{~exists z : A, In z l /\ R x z /\ bpath R n z y}).
      apply dec_lem; tauto. destruct X0. constructor. destruct s. 
      apply R_bpath_n_Sn with x0; tauto. 
      constructor 2. intro. pose (bpath_Sn_n_or_Rn H0). destruct o.
      contr.
      destruct H1. assert (exists z : A, In z l /\ R x z /\ bpath R n z y). 
      exists x0. split. pose (H x x0). tauto. hyp. contr.   
    Qed.

    Lemma bpath_midex : forall l n,
      is_restricted R l -> rel_midex R -> rel_midex (bpath R n).

    Proof.
      unfold rel_midex. induction n; intros. destruct (H0 x y). constructor. 
      apply bp_intro with (nil : list A). trivial. simpl. hyp. constructor 2.
      intro.
      inversion H2. destruct l0. simpl in H4. contr. simpl in H3. 
      exact (Nat.nle_succ_0 (length l0) H3). destruct (IHn H H0 x y). constructor. 
      apply bpath_n_Sn. hyp. 
      assert ((exists z : A,  In z l /\ R x z /\  bpath R n z y) \/
        (~exists z : A,  In z l /\ R x z /\  bpath R n z y)).
      apply midex_lem; tauto. destruct H2. destruct H2. constructor. 
      apply R_bpath_n_Sn with x0; tauto.
      constructor 2. intro. destruct (bpath_Sn_n_or_Rn H3). contr.
      destruct H4. assert (exists z : A, In z l /\ R x z /\ bpath R n z y). 
      exists x0. split. pose (H x x0). tauto. hyp. contr.  
    Qed.
 
    Lemma restricted_dec_clos_trans_dec : eq_dec A -> rel_dec R ->
      forall l, is_restricted R l  -> rel_dec (clos_trans R).

    Proof.
      do 6 intro. destruct (bpath_dec (length l) H X0 x y) . 
      constructor. apply (bpath_clos_trans b). 
      constructor 2. intro. pose (clos_trans_bpath (eq_dec_midex X) H H0). 
      contr.
    Qed.

    Lemma restricted_midex_clos_trans_midex : eq_midex A -> rel_midex R ->
      forall l, is_restricted R l  -> rel_midex (clos_trans R).

    Proof.
      do 6 intro. destruct (bpath_midex (length l) H1 H0 x y) . 
      constructor. apply (bpath_clos_trans H2). 
      constructor 2. intro. pose (clos_trans_bpath H H1 H3). 
      contr.
    Qed.

  End bp_restriction_midex_dec.

(***********************************************************************)
(** middle-excluding/decidability of a relation
is equivalent to middle-excluding/decidability of
the transitive closure of every finite restriction of the relation *)

  Section em_dec_clos_trans.

    Variable R : relation A.

    Lemma R_midex_clos_trans_restriction_midex : eq_midex A -> rel_midex R ->
      forall l, rel_midex (clos_trans (restriction R l)).

    Proof.
      intros. apply restricted_midex_clos_trans_midex with l. hyp. 
      apply restriction_midex; hyp. apply restricted_restriction.  
    Qed.

    Lemma R_dec_clos_trans_restriction_dec : eq_dec A -> rel_dec R ->
      forall l, rel_dec (clos_trans (restriction R l)).

    Proof.
      intros. apply restricted_dec_clos_trans_dec with l. hyp. 
      apply restriction_dec; hyp. apply restricted_restriction.  
    Qed.

    Lemma clos_trans_restriction_dec_R_dec :
      (forall l, rel_dec (clos_trans (restriction R l))) -> rel_dec R.

    Proof.
      do 3 intro. destruct (X (x::y::nil) x y). constructor.
      pose incl_restriction. unfold inclusion in i. apply i with A (x::y::nil). 
      apply clos_trans_restricted_pair. apply restricted_restriction. hyp. 
      constructor 2. intro. pose (clos_trans_restriction R x y). tauto.  
    Qed.

    Lemma clos_trans_restriction_midex_R_midex :
      (forall l, rel_midex (clos_trans (restriction R l))) -> rel_midex R.

    Proof.
      do 3 intro. destruct (H (x::y::nil) x y). constructor.
      pose incl_restriction. unfold inclusion in i. apply i with A (x::y::nil). 
      apply clos_trans_restricted_pair. apply restricted_restriction. hyp. 
      constructor 2. intro. pose (clos_trans_restriction R x y). tauto. 
    Qed.

  End em_dec_clos_trans.

End S.
