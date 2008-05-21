(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

auxiliary lemmas on sorting
*)

Set Implicit Arguments.

Require Export Sorting.
Require Export RelUtil.
Require Export ListUtil.

(***********************************************************************)
(** lelistA and sort *)

Lemma sort_incl_aux : forall (B : Set) (T S : relation B) a l,
  T << S -> lelistA T a l  -> lelistA S a l.

Proof.
induction l; intros. intuition. destruct H0; intuition.
Qed.

Lemma sort_incl : forall (B : Set) (T S : relation B) l,
  T << S -> sort T l -> sort S l.

Proof.
intros; induction l. intuition.
inversion H0. apply cons_sort; intuition. subst.
eapply sort_incl_aux; eassumption.
Qed.

Lemma sort_transitive : forall (B : Set) (a : B) L rel,
  transitive rel -> sort rel (a::L) -> forall x, In x L  -> rel a x.

Proof.
intros. induction L. destruct H1.
simpl in H1; destruct H1. subst. inversion H0; subst; auto.
inversion H4; subst; auto. apply IHL; auto. inversion H0; inversion H4.
subst. apply cons_sort. subst; auto. inversion H5. subst. inversion H9.
apply nil_leA. subst. apply cons_leA. eapply H; eauto.
Qed.

Require Export ListRepeatFree.

Lemma rp_free_lelistA_strict : forall (B: Set) a S (mb : list B)
  (HL : repeat_free (a::mb)), lelistA (S%) a mb -> lelistA S a mb.

Proof.
intros. induction mb; intuition.
simpl in *. inversion H; subst. apply cons_leA.
destruct H1; subst; try tauto.
Qed.

Lemma rp_free_sort_strict : forall (B: Set) S (mb : list B)
  (HL : repeat_free mb), sort (S%) mb -> sort S mb.

Proof.
intros. induction mb. apply nil_sort.
generalize HL; intro. simpl in HL0. inversion H; subst.
assert (sort S mb). tauto.
clear IHmb. apply cons_sort; auto. apply rp_free_lelistA_strict; auto.
Qed.

(***********************************************************************)
(** multiplicity *)

Require Export Multiset.
Require Export Permutation.

Section multiplicity.

Variables (B : Set) (B_eq_dec : forall x y : B, {x=y}+{x<>y}).

Lemma In_multiplicity : forall mb a, In a mb ->
  multiplicity (list_contents (eq (A:=B)) B_eq_dec mb) a >= 1.

Proof.
intros; induction mb; simpl in *; try tauto.
destruct H; destruct (B_eq_dec a0 a); subst; try congruence; simpl; try omega.
tauto.
Qed.

Lemma multiplicity_repeat_free : forall mb,
  (forall a, multiplicity (list_contents (eq (A:=B)) B_eq_dec mb) a <= 1)
  -> repeat_free mb.

Proof.
intros. induction mb; simpl; auto. simpl in H. split.
ded (H a). intuition. ded (In_multiplicity _ _ H1).
destruct (B_eq_dec a a); auto. omega.
apply IHmb. intros. ded (H a0). destruct (B_eq_dec a a0); simpl in *; omega.
Qed.

End multiplicity.
