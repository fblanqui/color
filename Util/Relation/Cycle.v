(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-06

cycles
*)

(* $Id: Cycle.v,v 1.3 2007-02-12 17:10:03 blanqui Exp $ *)

Set Implicit Arguments.

Require Export Path.

Section S.

Variables (A : Set) (R : relation A).
Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Definition cycle x := path R x x.

Definition cycle_min x l := cycle x l /\ ~In x l.

Lemma path_cycle : forall x y l, path R x y l -> In x l ->
  exists m, exists p, l = m ++ x :: p /\ cycle x m.

Proof.
intros. deduce (in_elim H0). do 2 destruct H1. subst l.
deduce (path_app_elim H). destruct H1.
exists x0. exists x1. intuition.
Qed.

Implicit Arguments path_cycle [x y l].

Lemma path_cycle_min : forall x y l, path R x y l -> In x l ->
  exists m, exists p, l = m ++ x :: p /\ cycle_min x m.

Proof.
intros. deduce (in_elim_dec eq_dec H0). do 3 destruct H1. subst l.
deduce (path_app_elim H). destruct H1. exists x0. exists x1.
unfold cycle_min. intuition.
Qed.

Implicit Arguments path_cycle_min [x y l].

Lemma cycle_cycle_min : forall x l, cycle x l ->
  exists m, exists p, l = m ++ p /\ cycle_min x m.

Proof.
intros. case (In_dec eq_dec x l); intro.
deduce (path_cycle_min H i). do 3 destruct H0. subst l.
exists x0. exists (x :: x1). intuition.
exists l. exists (@nil A). unfold cycle_min. intuition.
Qed.

Require Export ListOccur.

Notation occur := (occur eq_dec).

Lemma long_path_occur : forall s, restricted R s ->
  forall x y l, path R x y l -> length l >= length s - 1 ->
    exists z, occur z (x :: l ++ y :: nil) >= 2.

Proof.
intros. apply pigeon_hole with s. eapply restricted_path_incl.
apply H. apply H0. simpl. rewrite length_app. simpl. omega.
Qed.

End S.