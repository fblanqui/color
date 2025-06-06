(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Joerg Endrullis, 2008-07-28
- Frederic Blanqui, 2007-02-05

when the union of two wellfounded relations is wellfounded
*)

Set Implicit Arguments.

From Stdlib Require Import Lia Wellfounded.Union.
From CoLoR Require Import SN RelUtil LogicUtil AccUtil NotSN_IS ClassicUtil
     LeastNat DepChoice.
    
Section S.

  Variables (A : Type) (R S : relation A).

(***********************************************************************)
(** When the two relations commute. *)

  Lemma SN_union_commut t :
    (forall x, SN S x -> SN R x) -> SN S t -> R @ S << S @ R -> SN (R U S) t.

  Proof.
    intros h s c. apply Acc_transp_SN. rewrite transp_union. apply Acc_union.
    intros x y. unfold transp. intros xy z yz.
    assert (a : (R@S) x z). exists y. fo.
    apply c in a. fo.
    intros x hx. apply SN_Acc_transp. apply h. apply Acc_transp_SN. hyp.
    apply SN_Acc_transp. hyp.
  Qed.

  Lemma WF_union_commut : WF R -> WF S -> R @ S << S @ R -> WF (R U S).

  Proof.
    intros R_wf S_wf commut. apply wf_transp_WF. rewrite transp_union.
    apply wf_union. intros x y. unfold transp. intros xy z yz.
    assert (a : (R@S) x z). exists y. fo.
    apply commut in a. fo. apply WF_wf_transp. hyp. apply WF_wf_transp. hyp.
  Qed.

(***********************************************************************)
(** When a relation absorbs the other. *)

  Lemma wf_union_absorb : WF R -> WF S -> R @ S << R -> WF (R U S).

  Proof.
    intros R_wf S_wf RS x. apply notNT_SN. intros [f [f1 f2]].
    (* We prove that, for all [i], there is [j > i] such that
       [R (f j) (f (j+1))]. *)
    assert (a1 : forall i, exists j, i < j /\ R (f j) (f (1+j))).
    apply NNPP. rewrite not_forall_eq. intros [i0 hi0].
    rewrite not_exists_eq in hi0.
    assert (hi0' : forall i, i0 < i -> S (f i) (f (1+i))).
    intros i ii0. gen (hi0 i). rewrite not_and_eq. fo.
    absurd (NT S (f (i0+1))). apply SN_notNT. fo.
    exists (fun i => f (i+(i0+1))). split. refl. intro i. apply hi0'. lia.
    (* We prove that, for all [i], there is [j > i] such that
       [R (f j) (f (j+1))] and, for all [k] between [i] and [j],
       [S (f k) (f (k+1))]. *)
    assert (a2 : forall i, exists j, i < j /\ R (f j) (f (1+j))
        /\ forall k, i < k < j -> S (f k) (f (1+k))).
    intro i. gen (ch_min (a1 i)); intros [j [[[j1 j2] j3] j4]].
    ex j. split. hyp. split. hyp. intros k ikj. destruct (f2 k). 2: hyp.
    assert (j <= k). apply j3. fo. lia.
    (* Let [i0] be the first or second [R] step in [f]. *)
    destruct (a2 0) as [i0 [i0h [i0r i0s]]].
    (* Let [b] be the function mapping [j] to [i] and such that [b 0 = i0]. *)
    destruct (dep_choice i0 a2) as [b [b1 b2]].
    (* We prove that there is an infinite sequence of [R @ S#] steps
       starting from [f i0]. *)
    assert (a3 : NT (R @ S#) (f i0)). ex (fun i => f (b i)). split.
    rewrite b2. refl.
    intro i. ex (f (1 + b i)). split.
    destruct i. rewrite b2. hyp. gen (b1 i). fo.
    apply rtc_intro_seq. gen (b1 i). lia.
    intros k hk. gen (b1 i). intros [c1 [c2 c3]]. apply c3. lia.
    (* We therefore get a contradiction since [R @ S# << R] and [R] is WF. *)
    revert a3. apply SN_notNT. apply (SN_incl R).
    apply absorbs_right_rtc. hyp. fo.
  Qed.

(***********************************************************************)
(** Commutation and SN *)

  Lemma sn_comm_sntr :
    forall x, SN R x -> (forall y, R#1 x y -> SN S y) ->
      S@R << R!1@S#1 -> SN (R!1 U S!1) x.

  Proof.
    intros x snr sns comm.
    assert (snrt := SN_tc1 snr); clear snr.

    (* Induction on x R! ... *)
    induction snrt as [x _ IHr].
    apply SN_intro. intros y xRSy.
    destruct xRSy as [xRy | xSy]. apply IHr. hyp.
    assert (SN (S!1) y) as sny.
    apply SN_tc1. apply sns. apply tc1_incl_rtc1; hyp.

    (* x R! y *)
    intros y0 yRy0. apply sns.
    apply trans_comp_incl. class. exists y; split; trivial.
    apply tc1_incl_rtc1. hyp.

    (* x S! y *)
    assert (SN (S!1) y) as sny. apply SN_tc1.
    apply SN_inv_rtc1 with x. apply tc1_incl_rtc1. hyp.
    apply sns. refl.

    (* Induction on y S! ... *)
    induction sny as [y _ IHs].
    apply SN_intro. intros z yRSz.
    destruct yRSz as [yRz | ySz].

    assert ((R!1 @ (R U S)#1) x z) as xRz.
    apply comm_s_r; trivial.
    destruct yRz as [y z yRz | y m z yRm mRz].
    exists z. split. exists y. split; trivial.
    apply union_rel_rt1_right. apply tc1_incl_rtc1. hyp. refl.
    exists m. split. exists y. split; trivial.
    apply union_rel_rt1_right. apply tc1_incl_rtc1. hyp.
    apply union_rel_rt1_left. apply tc1_incl_rtc1. hyp.

    destruct xRz as [m [xRm mz]].
    assert (SN (R!1 U S!1) m) as SNm.
    apply IHr. hyp. intros y0 mRy0.
    apply sns. apply trans_comp_incl. class. exists m.
    split; trivial. apply tc1_incl_rtc1. hyp.

    apply SN_inv_rtc1 with m. apply incl_union_rt1_union. hyp. hyp.
    apply IHs; trivial. trans y; trivial.
  Qed.

  Lemma sn_comm_sn :
    forall x, SN R x -> (forall y, R#1 x y -> SN S y) ->
      S@R << R!1@S#1 -> SN (R U S) x.

  Proof.
    intros x snr sns comm.
    assert (SN (R!1 U S!1) x) as sntr.
    apply sn_comm_sntr; trivial.
    apply (SN_incl (R!1 U S!1)).
    apply union_incl.
    intros a b. apply t1_step.
    intros a b. apply t1_step.
    hyp.
  Qed.

End S.
