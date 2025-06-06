(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

auxiliary lemmas on Coq's sort and lelistA predicates
and on Coq's multiplicity function 
*)

Set Implicit Arguments.

From Stdlib Require Export Sorting.
From Stdlib Require Import List Morphisms Lia.
From CoLoR Require Import RelUtil LogicUtil.

(***********************************************************************)
(** lelistA and sort *)

Lemma sort_incl_aux : forall B (T S : relation B) a l,
  T << S -> lelistA T a l  -> lelistA S a l.

Proof. induction l; intros. intuition. destruct H0; intuition. Qed.

Lemma sort_incl : forall B (T S : relation B) l,
  T << S -> sort T l -> sort S l.

Proof.
intros; induction l. intuition.
inversion H0. apply cons_sort; intuition. subst.
eapply sort_incl_aux; ehyp.
Qed.

Lemma sort_transitive : forall B (a : B) L rel,
  transitive rel -> sort rel (a::L) -> forall x, In x L -> rel a x.

Proof.
intros. induction L. destruct H1.
simpl in H1; destruct H1. subst. inversion H0; subst; auto.
inversion H4; subst; auto. apply IHL; auto. inversion H0; inversion H4.
subst. apply cons_sort. subst; auto. inversion H5. subst. inversion H9.
apply nil_leA. subst. apply cons_leA. eapply H; eauto.
Qed.

Lemma lelistA_map A (R : relation A) B (S : relation B) (f : A->B)
      (f_mon : Proper (R ==> S) f) a :
  forall l, lelistA R a l -> lelistA S (f a) (map f l).

Proof.
  induction l; intro h; simpl.
  apply nil_leA.
  inversion h; subst. apply cons_leA. apply f_mon. hyp.
Qed.

Lemma sort_map A (R : relation A) B (S : relation B) (f : A->B)
      (f_mon : Proper (R ==> S) f) :
  forall l, sort R l -> sort S (map f l).

Proof.
  induction l; intro h; simpl.
  apply nil_sort.
  inversion h; subst. apply cons_sort.
  apply IHl. hyp.
  eapply lelistA_map. apply f_mon. hyp.
Qed.

From CoLoR Require Import ListNodup.

Lemma nodup_lelistA_strict : forall B a S (mb : list B)
  (HL : nodup (a::mb)), lelistA (S%) a mb -> lelistA S a mb.

Proof.
intros. induction mb; intuition.
simpl in *. inversion H; subst. apply cons_leA.
destruct H1; subst; try tauto.
Qed.

Lemma nodup_sort_strict : forall B S (mb : list B)
  (HL : nodup mb), sort (S%) mb -> sort S mb.

Proof.
intros. induction mb. apply nil_sort.
gen HL; intro. simpl in HL0. inversion H; subst.
assert (sort S mb). tauto.
clear IHmb. apply cons_sort; auto. apply nodup_lelistA_strict; auto.
Qed.

(***********************************************************************)
(** multiplicity *)

From CoLoR Require Import ListPermutation.

Section multiplicity.

  Variables (B : Type) (B_eq_dec : forall x y : B, {x=y}+{x<>y}).

  Lemma In_multiplicity : forall mb a, In a mb ->
    multiplicity (list_contents B_eq_dec mb) a >= 1.

  Proof.
    intros; induction mb; simpl in *; try tauto.
    destruct H; destruct (B_eq_dec a0 a); subst; try congruence; simpl;
      try lia.
    tauto.
  Qed.

  Lemma multiplicity_nodup : forall mb,
    (forall a, multiplicity (list_contents B_eq_dec mb) a <= 1) -> nodup mb.

  Proof.
    intros. induction mb; simpl; auto. simpl in H. split.
    ded (H a). intuition. ded (In_multiplicity _ _ H1).
    destruct (B_eq_dec a a); auto. lia.
    apply IHmb. intros. ded (H a0). destruct (B_eq_dec a a0); simpl in *; lia.
  Qed.

End multiplicity.

(***********************************************************************)
(** Sorted *)

From Stdlib Require Import Morphisms.
From CoLoR Require Import NatUtil.

Section Sorted.

  Variables (A : Type) (lt : relation A) (lt_trans : Transitive lt) (d : A).

  Lemma Sorted_nth_S : forall l i, Sorted lt l ->
    i < length l -> S i < length l -> lt (nth i l d) (nth (S i) l d).

  Proof.
    induction l; destruct i; simpl; intros. lia. lia.
    inversion H. subst. destruct l. simpl in H1. lia.
    inversion H5. hyp.
    inversion H. apply IHl. hyp. lia. lia.
  Qed.

  Lemma HdRel_nth : forall l i n, Sorted lt l ->
    HdRel lt n l -> i < length l -> lt n (nth i l d).

  Proof.
    induction l; destruct i; simpl; intros.
    lia. lia. inversion H0. hyp.
    apply IHl. inversion H. hyp.
    destruct l. apply HdRel_nil. apply HdRel_cons.
    inversion H0. inversion H. inversion H8. subst. trans a; hyp. lia.
  Qed.

  Lemma Sorted_nth : forall j l i, Sorted lt l ->
    i < length l -> j < length l -> i < j -> lt (nth i l d) (nth j l d).

  Proof.
    induction j; intros. lia.
    destruct l; simpl in *. lia.
    inversion H. subst. destruct i; simpl.
    apply HdRel_nth. hyp. hyp. lia.
    apply IHj. hyp. lia. lia. lia.
  Qed.

End Sorted.
