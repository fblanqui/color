(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-06

cycles
*)

Set Implicit Arguments.

Require Import Path.
Require Import ListRepeatFree.
Require Import Relations.
Require Import ListUtil.
Require Import LogicUtil.

Section S.

Variables (A : Type) (R : relation A).
Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

(***********************************************************************)
(** cycles *)

Definition cycle x := is_path R x x.

Lemma path_cycle : forall x y l, is_path R x y l -> In x l ->
  exists m, exists p, l = m ++ x :: p /\ cycle x m.

Proof.
intros. ded (in_elim H0). do 2 destruct H1. subst l.
ded (path_app_elim H). destruct H1.
exists x0. exists x1. intuition.
Qed.

Implicit Arguments path_cycle [x y l].

(***********************************************************************)
(** cycles of minimum length *)

Definition cycle_min x l := cycle x l /\ ~In x l /\ repeat_free l.

Lemma cycle_min_intro : forall x l, cycle x l ->
  exists m, exists y, exists p, exists q,
    x :: l = m ++ y :: p ++ q /\ cycle_min y p.

Proof.
intros. unfold cycle_min. ded (repeat_free_intro eq_dec (x::l)). decomp H0.
(* repeat_free (x::l) *)
exists (@nil A). exists x. exists l. exists (@nil A). rewrite <- app_nil_end.
simpl in H1. intuition.
(* x::l = x0++x1::x2 *)
rewrite H1. ded (in_elim H4). decomp H0. rewrite H5.
exists x3. exists x1. exists x4. exists (x1::x2). rewrite app_ass. simpl.
rewrite H5 in H2. ded (repeat_free_app_elim H2). simpl in H0. decomp H0.
intuition.
(* cycle x1 x4 *)
destruct x0. contradiction. injection H1; intros. subst a.
unfold cycle in H. destruct x3; injection H5; intros.
(* x3=nil *)
subst x1. subst x4. rewrite H0 in H. ded (path_app_elim H). intuition.
(* x3=x::x3 *)
subst a. subst x0. rewrite app_ass in H0. simpl in H0. rewrite H0 in H.
ded (path_app_elim H). destruct H7. ded (path_app_elim H10). intuition.
Qed.

End S.

(***********************************************************************)
(** implicit arguments *)

Implicit Arguments cycle_min_intro [A R x l].
