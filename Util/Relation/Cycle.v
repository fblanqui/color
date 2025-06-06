(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-06

cycles
*)

Set Implicit Arguments.

From Stdlib Require Import Relations.
From CoLoR Require Import LogicUtil Path ListUtil ListNodup.

Section S.

Variables (A : Type) (R : relation A) (eq_dec : forall x y : A, {x=y}+{~x=y}).

(***********************************************************************)
(** cycles *)

Definition cycle x := path R x x.

Lemma path_cycle : forall x y l, path R x y l -> In x l ->
  exists m, exists p, l = m ++ x :: p /\ cycle x m.

Proof.
intros. ded (in_elim H0). do 2 destruct H1. subst l.
ded (path_app_elim H). destruct H1.
exists x0. exists x1. intuition.
Qed.

Arguments path_cycle [x y l] _ _.

(***********************************************************************)
(** cycles of minimum length *)

Definition cycle_min x l := cycle x l /\ ~In x l /\ nodup l.

Lemma cycle_min_intro : forall x l, cycle x l ->
  exists m, exists y, exists p, exists q,
    x :: l = m ++ y :: p ++ q /\ cycle_min y p.

Proof.
intros. unfold cycle_min. ded (nodup_intro eq_dec (x::l)). decomp H0.
(* nodup (x::l) *)
exists nil. exists x. exists l. exists nil. rewrite app_nil_r.
simpl in H1. intuition.
(* x::l = x0++x1::x2 *)
rewrite H1. ded (in_elim H4). decomp H0. rewrite H5.
exists x3. exists x1. exists x4. exists (x1::x2). rewrite <- app_assoc. simpl.
rewrite H5 in H2. ded (nodup_app_elim H2). simpl in H0. decomp H0.
intuition.
(* cycle x1 x4 *)
destruct x0. contr. injection H1; intros. subst a.
unfold cycle in H. destruct x3; injection H5; intros.
(* x3=nil *)
subst x1. subst x4. rewrite H0 in H. ded (path_app_elim H). intuition.
(* x3=x::x3 *)
subst a. subst x0. rewrite <- app_assoc in H0. simpl in H0. rewrite H0 in H.
ded (path_app_elim H). destruct H7. ded (path_app_elim H10). intuition.
Qed.

End S.

(***********************************************************************)
(** implicit arguments *)

Arguments cycle_min_intro [A R] _ [x l] _.
