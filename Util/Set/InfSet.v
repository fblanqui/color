(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2014-12-11

Infinite sets
*)

Set Implicit Arguments.

From Coq Require Import Basics Morphisms Setoid Lia.
From CoLoR Require Import ClassicUtil IotaUtil EpsilonUtil LogicUtil SetUtil
     FinSet FunUtil BoundNat IotaUtil EpsilonUtil.

Section S.

  Variable A : Type.

(** * Definition of infinite sets *)

  Definition infinite (P : set A) := ~finite P.

(** * Properties of [infinite]. *)

  Global Instance infinite_subset : Proper (subset ==> impl) infinite.

  Proof. intros P Q PQ P_inf Q_fin. rewrite <- PQ in Q_fin. contr. Qed.

  Global Instance infinite_equiv : Proper (equiv ==> iff) infinite.

  Proof.
    intros P Q PQ. unfold infinite. split.
    intros P_inf Q_fin. apply P_inf. rewrite PQ. hyp.
    intros Q_inf P_fin. apply Q_inf. rewrite <- PQ. hyp.
  Qed.

(** A set [P] is infinite if there is an injection from [nat] to [P]. *)

  Lemma infinite_inj P : (exists f : nat -> elts P, injective f) -> infinite P.

  Proof.
    intros [f f_inj] [n [g [g_inj g_surj]]].
    assert (S n <= n). 2: lia.
    apply N_inj_le with (f := inverse g_surj o f o (@N_val _)).
    inj. apply inj_N_val.
  Qed.

(** * Set constructors preserve infiniteness. *)

  Lemma infinite_rem a P : infinite (rem a P) <-> infinite P.

  Proof. unfold infinite. gen (finite_rem_eq a P). tauto. Qed.

  Lemma infinite_union P Q : infinite (union P Q) <-> infinite P \/ infinite Q.

  Proof. unfold infinite. gen (finite_union_eq P Q). tauto. Qed.

  Lemma infinite_diff P Q : infinite (diff P Q) -> infinite P.

  Proof. intro P_Q_inf. intro P_fin. apply P_Q_inf. apply finite_diff. hyp. Qed.

  Lemma infinite_diff_finite P Q (Q_dec : forall x, {Q x}+{~Q x}) :
    infinite P -> finite Q -> infinite (diff P Q).

  Proof.
    intros P_inf Q_fin P_Q_fin. apply P_inf. cut (finite (union P Q)).
    rewrite finite_union_eq. fo. rewrite <- union_diff, finite_union_eq; auto.
  Qed.

  Lemma infinite_not_empty P : infinite P -> exists x, mem x P.

  Proof.
    intro P_inf. apply not_all_not_ex. intro h.
    assert (e : P [=] empty). fo. rewrite e in P_inf.
    gen finite_empty. fo.
  Qed.

(****************************************************************************)
(** * Type for infinite subsets of some set [P] *)

  Definition Pinf P := {Q | Q [<=] P /\ infinite Q}.

  Definition mk_Pinf P Q : Q [<=] P -> infinite Q -> Pinf P.

  Proof. intros QP Qinf. ex Q. auto. Defined.

  Definition Pinf_val P (Q : Pinf P) := proj1_sig Q.

  Global Coercion Pinf_val : Pinf >-> set.

  Definition Pinf_sub P (Q : Pinf P) : Q [<=] P.

  Proof. destruct Q as [Q [QP Qinf]]. hyp. Defined.

  Global Coercion Pinf_sub : Pinf >-> subset.

  Definition Pinf_inf P (Q : Pinf P) : infinite Q.

  Proof. destruct Q as [Q [QP Qinf]]. hyp. Defined.

  Global Coercion Pinf_inf : Pinf >-> infinite.

  Definition Pinf_subset P Q : P [<=] Q -> Pinf P -> Pinf Q.

  Proof. intros PQ [X [XP Xinf]]. ex X. split. trans P; hyp. hyp. Defined.

  Definition Pinf_self P (Q : Pinf P) : Pinf Q.

  Proof. ex Q. split. refl. destruct Q as [Q [QP Qinf]]; hyp. Defined.

(****************************************************************************)
(** An infinite set contains finite subsets of every cardinality. *)

  Section Pcard_of_inf.

    Variable W : set A.

    Lemma Pcard_of_inf_spec (P : Pinf W) :
      forall n, exists X : Pf A, X [<=] P /\ card X = S n.

    Proof.
      induction n.
      (* n=0 *)
      destruct (infinite_not_empty P) as [a aP]. ex (Pf_singleton a).
      split. 2: apply card_singleton.
      simpl. intro x. unfold impl. fo. subst. fo.
      (* n>0 *)
      destruct IHn as [X [XP cX]]. set (Q := diff P X).

      assert (Qinf : infinite Q).
      unfold Q. apply infinite_diff_finite. intro x. apply dec.
      destruct P as [P [Pall Pinf]]. hyp.
      destruct X as [X Xfin]; hyp.
  
      destruct (infinite_not_empty Qinf) as [a aQ]. ex (Pf_add a X). split.
      simpl. intro x. unfold impl. fo. subst. fo.
      rewrite card_add, cX. destruct (dec (mem a X)). fo. lia.
    Qed.

    Definition Pcard_of_inf (P : Pinf W) n : Pcard P (S n).

    Proof.
      destruct (cid (Pcard_of_inf_spec P n)) as [X [XP cX]]. ex X. auto.
    Defined.

  End Pcard_of_inf.

End S.
