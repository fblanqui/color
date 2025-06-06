(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-01-25
- Sebastien Hinderer, 2004-02-09

general definitions and results about relations on terms
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs RelUtil ListUtil ARelation SN LogicUtil.

Section S.

Variable Sig : Signature.

Notation term := (term Sig).
Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** compatibility *)

Section compat.

Variable succ : relation term.

Definition compat R := forall l r : term, In (mkRule l r) R -> succ l r.

Lemma compat_empty : compat nil.

Proof.
  intros l r lr. inversion lr.
Qed.

Lemma compat_red : forall R,
  rewrite_ordering succ -> compat R -> red R << succ.

Proof.
intro. unfold inclusion. intros (Hsubs,Hcont) Hcomp u v H. redtac.
subst u. subst v. apply Hcont. apply Hsubs. apply Hcomp. hyp.
Qed.

Lemma compat_hd_red : forall R,
  substitution_closed succ -> compat R -> hd_red R << succ.

Proof.
unfold inclusion. intros. redtac. subst x. subst y. apply H. apply H0. hyp.
Qed.

Lemma incl_compat : forall R S, incl R S -> compat S -> compat R.

Proof.
unfold compat. intros. apply H0. apply H. hyp.
Qed.

Lemma compat_red_mod_tc : forall R E,
  rewrite_ordering succ -> compat E -> compat R -> red_mod E R << succ!.

Proof.
intros. unfold red_mod. incl_trans (succ# @ succ). comp.
apply rtc_incl. apply compat_red; hyp. apply compat_red; hyp.
apply tc_split_inv.
Qed.

Lemma compat_cons : forall l r R,
  succ l r -> compat R -> compat (mkRule l r :: R).

Proof.
unfold compat. simpl. intros. destruct H1.
injection H1. intros. subst l0. subst r0. exact H.
apply H0. exact H1.
Qed.

Lemma compat_cons_elim : forall l r R,
  compat (mkRule l r :: R) -> succ l r /\ compat R.

Proof.
unfold compat. simpl. intros. split; intros; apply H; intuition.
Qed.

Lemma compat_app : forall R R',
  compat R -> compat R' -> compat (R ++ R').

Proof.
intros R R' Rsucc R'succ l r lr. destruct (in_app_or lr).
apply Rsucc. hyp. apply R'succ. hyp.
Qed.

Definition compat_rule a := match a with mkRule l r => succ l r end.

Lemma compat_lforall : forall R, lforall compat_rule R -> compat R.

Proof.
induction R; unfold compat; simpl; intros.
contr. intuition. subst a. exact H1.
Qed.

(***********************************************************************)
(** decidability *)

Variable succ_dec : rel_dec succ.

Function is_compat (R : rules) : bool :=
  match R with
    | nil => true
    | cons a R' =>
      match a with mkRule l r =>
        match succ_dec l r with
          | left _ => is_compat R'
          | right _ => false
        end
      end
  end.

Lemma is_compat_correct : forall R,
  is_compat R = true -> compat R /\ is_compat R = false -> ~compat R.

Proof.
induction R; simpl. intuition auto with *.
destruct a. case (succ_dec lhs rhs); intros;
  destruct H0; ded (compat_cons_elim H0); intuition auto with *.
Qed.

Lemma is_compat_complete : forall R,
  compat R -> is_compat R = true /\ ~compat R -> is_compat R = false.

Proof.
induction R; simpl. intuition.
destruct a. intro. ded (compat_cons_elim H). destruct H0.
case (succ_dec lhs rhs); intros; destruct H2.
apply IHR. exact H1. intuition. refl.
Qed.

End compat.

Lemma compat_incl : forall succ succ' R,
  succ << succ' -> compat succ R -> compat succ' R.

Proof.
intros. intros l r h. apply H. apply H0. hyp.
Qed.

(***********************************************************************)
(** reduction pair *)

Section reduction_pair.

Variables succ succ_eq : relation term.

Lemma compat_red_mod : forall R E,
  rewrite_ordering succ -> rewrite_ordering succ_eq ->
  compat succ_eq E -> compat succ R ->
  absorbs_left succ succ_eq -> red_mod E R << succ.

Proof.
intros. unfold red_mod. incl_trans (succ_eq# @ succ). comp.
apply rtc_incl.
apply compat_red; hyp. destruct H0. apply compat_red; hyp.
apply absorbs_left_rtc. exact H3.
Qed.

End reduction_pair.

(***********************************************************************)
(** weak reduction pair *)

Section weak_reduction_pair.

Variables succ succ_eq : relation term.

Lemma compat_hd_red_mod : forall R E,
  substitution_closed succ -> rewrite_ordering succ_eq ->
  compat succ_eq E -> compat succ R ->
  absorbs_left succ succ_eq -> hd_red_mod E R << succ.

Proof.
intros. unfold hd_red_mod. incl_trans (succ_eq# @ succ). comp.
apply rtc_incl.
apply compat_red; hyp. apply compat_hd_red; hyp.
apply absorbs_left_rtc. exact H3.
Qed.

End weak_reduction_pair.

(***********************************************************************)
(** partitioning rewrite rules according to some decidable relation *)

Lemma red_partition : forall (R R1 R2 : rules),
  (forall r, In r R -> In r R1 \/ In r R2) -> red R << red R1 U red R2.

Proof with auto.
  intros. incl_trans (red (R1 ++ R2)).
  apply red_incl. unfold incl. intros.
  destruct (H a); solve [hyp | apply in_or_app; auto].
  apply red_union.
Qed.

Section rule_partition.
  
  Variable R : rules.

  Definition rule_partition succ (succ_dec : rel_dec succ) (r : rule) := 
    partition_by_rel succ_dec (lhs r, rhs r).

  Lemma rule_partition_left : forall succ (succ_dec : rel_dec succ) l r rs,
    In (mkRule l r) (fst (partition (rule_partition succ_dec) rs)) ->
    partition_by_rel succ_dec (l, r) = true.

  Proof.
    intros. unfold rule_partition in H.
    set (w := partition_left
      (fun r => partition_by_rel succ_dec (lhs r, rhs r))). simpl in w.
    change l with (lhs (mkRule l r)). change r with (rhs (mkRule l r)).
    apply w with rs. hyp.
  Qed.

  Lemma rule_partition_compat : forall succ (succ_dec : rel_dec succ),
    snd (partition (rule_partition succ_dec) R) = nil ->
    compat succ R.

  Proof.
    intros. intros l r Rlr.
    apply partition_by_rel_true with term succ_dec.
    apply rule_partition_left with R.
    destruct (partition_complete (rule_partition succ_dec) (mkRule l r) R).
    hyp. hyp. rewrite H in H0. destruct H0.
  Qed.

  Lemma rule_partition_complete : forall pf (R : rules),
    let part := partition pf R in
      red R << red (fst part) U red (snd part).

  Proof.
    clear R. intros. apply red_partition. intros. unfold part.
    apply partition_complete. hyp.
  Qed.

  Lemma hd_rule_partition_complete : forall pf (R : rules),
    let part := partition pf R in
      hd_red R << hd_red (fst part) U hd_red (snd part).

  Proof.
    clear R. intros. incl_trans (hd_red (fst part ++ snd part)).
    apply hd_red_incl. unfold incl. intros.
    destruct (partition_complete pf a R). hyp.
    apply in_or_app. auto.
    apply in_or_app. auto.
    apply hd_red_union.
  Qed.

End rule_partition.

End S.
