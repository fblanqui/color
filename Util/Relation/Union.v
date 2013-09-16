(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Joerg Endrullis, 2008-07-28
- Frederic Blanqui, 2007-02-05

when the union of two wellfounded relations is wellfounded
*)

Set Implicit Arguments.

Require Import SN RelUtil LogicUtil.

Section S.

  Variables (A : Type) (R S : relation A) (R_wf : WF R) (S_wf : WF S).

(***********************************************************************)
(** When the two relations commute. *)

  Lemma WF_union_commut : R @ S << S @ R -> WF (R U S).

  Proof. Require Import AccUtil Wellfounded.Union.
    intro commut. apply wf_transp_WF. rewrite transp_union. apply wf_union.
    intros x y. unfold transp. intros xy z yz.
    assert (a : (R@S) x z). exists y. fo.
    apply commut in a. fo. apply WF_wf_transp. hyp. apply WF_wf_transp. hyp.
  Qed.

(***********************************************************************)
(** When a relation absorbs the other. *)

  Lemma wf_union_absorb : R @ S << R -> WF (R U S).

  Proof.
    Require Import NotSN_IS ClassicUtil NatLeast DepChoice.
    intros RS x. apply notNT_SN. intros [f [f1 f2]].
    (* We prove that, for all [i], there is [j > i] such that
       [R (f j) (f (j+1))]. *)
    assert (a1 : forall i, exists j, i < j /\ R (f j) (f (1+j))).
    apply NNPP. rewrite not_forall_eq. intros [i0 hi0].
    rewrite not_exists_eq in hi0.
    assert (hi0' : forall i, i0 < i -> S (f i) (f (1+i))).
    intros i ii0. gen (hi0 i). rewrite not_and_eq. fo.
    absurd (NT S (f (i0+1))). apply SN_notNT. fo.
    exists (fun i => f (i+(i0+1))). split. refl. intro i. apply hi0'. omega.
    (* We prove that, for all [i], there is [j > i] such that
       [R (f j) (f (j+1))] and, for all [k] between [i] and [j],
       [S (f k) (f (k+1))]. *)
    assert (a2 : forall i, exists j, i < j /\ R (f j) (f (1+j))
        /\ forall k, i < k < j -> S (f k) (f (1+k))).
    intro i. gen (ch_min (a1 i)); intros [j [[[j1 j2] j3] j4]].
    ex j. split. hyp. split. hyp. intros k ikj. destruct (f2 k). 2: hyp.
    assert (j <= k). apply j3. fo. omega.
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
    apply rtc_intro_seq. gen (b1 i). omega.
    intros k hk. gen (b1 i). intros [c1 [c2 c3]]. apply c3. omega.
    (* We therefore get a contradiction since [R @ S# << R] and [R] is WF. *)
    revert a3. apply SN_notNT. apply SN_incl with (S:=R).
    apply absorbs_right_rtc. hyp. fo.
  Qed.

(***********************************************************************)
(** Additional commutation properties *)

  Lemma comm_s_rt : S@(R!1) << (R!1)@(S!1) -> (S!1)@(R!1) << (R!1)@(S!1).

  Proof.
    intros comm x y [z [H1 H2]].
    induction H1 as [x z H | x y' z H H0 IH].
    apply comm. 
    exists z; split; hyp.
    assert (H1 := IH H2); clear IH H2.
    destruct H1 as [u [H2 H3]].
    assert ((clos_trans1 R @ clos_trans1 S) x u).
    apply comm. exists y'; split; hyp.
    destruct H1 as [m [xRm mSu]].
    exists m; split. hyp.
    exact (clos_trans1_trans mSu H3).
  Qed.

  Lemma comm_s_r : S@R << (R!1)@(S#1) ->
    (R U S)#1 @ R @ (R U S)#1 << (R!1) @ (R U S)#1.

  Proof.
    intros comm x y [z2 [[z1 [xRSz1 z1Rz2] z2RSy]]].
    induction xRSz1 as [ | m n z1 mRSn nRSz1 IH].
    exists z2. split. apply t1_step. hyp. hyp.
    (* m RUS n RUS# z1 R z2 RUS# y *)
    assert (((R!1) @ (R U S)#1) n y) as mRedy. apply IH. hyp.
    (* m RUS n R!1@RUS#1 y *)
    clear nRSz1 z1Rz2 z2RSy IH z1 z2.
    destruct mRedy as [o [nRo oRSy]].
    (* m RUS n R!1 o RUS#1 y *)
    induction mRSn.
    (* m R n *)
    exists o. split; auto. apply t1_trans with n; hyp.
    (* m S n *)
    destruct nRo as [o p oRp | o p q oRp pRq ];

    assert (((R!1)@(S#1)) m p) as mRedp.
    apply comm. exists o; split; hyp.
    destruct mRedp as [x [mRx xSp]].
    exists x. split. hyp.
    apply clos_refl_trans1_trans with p.
    apply union_rel_rt_right. hyp. hyp.

    assert (((R!1)@(S#1)) m p) as mRedp.
    apply comm. exists o. split; hyp.
    destruct mRedp as [x [mRx xSp]].
    exists x. split. hyp. hyp.
    destruct mRedp as [n [mRn sSp]].
    exists n; split. hyp.
    apply clos_refl_trans1_trans with q.
    apply clos_refl_trans1_trans with p.
    apply union_rel_rt_right. hyp.
    apply union_rel_rt_left. apply incl_t_rt. hyp.    
    hyp.
  Qed.

(***********************************************************************)
(** Commutation and SN *)

  Lemma sn_comm_sntr :
    forall x, SN R x -> (forall y, (R#1) x y -> SN S y) ->
      (S@R << R!1@S#1) -> SN (R!1 U S!1) x.

  Proof.
    intros x snr sns comm.
    assert (snrt := SN_tc1 snr); clear snr.

    (* Induction on x R! ... *)
    induction snrt as [x _ IHr].
    apply SN_intro. intros y xRSy.
    destruct xRSy as [xRy | xSy]. apply IHr. hyp.
    assert (SN (S!1) y) as sny.
    apply SN_tc1. apply sns. apply incl_t_rt; hyp.

    (* x R! y *)
    intros y0 yRy0. apply sns.
    apply incl_rt_rt_rt. exists y; split; trivial.
    apply incl_t_rt. hyp.

    (* x S! y *)
    assert (SN (S!1) y) as sny. apply SN_tc1.
    apply SN_rtc1 with x. apply sns. apply rt1_refl.
    apply incl_t_rt. hyp.

    (* Induction on y S! ... *)
    induction sny as [y _ IHs].
    apply SN_intro. intros z yRSz.
    destruct yRSz as [yRz | ySz].

    assert ((R!1 @ (R U S)#1) x z) as xRz.
    apply comm_s_r; trivial.
    destruct yRz as [y z yRz | y m z yRm mRz].
    exists z. split. exists y. split; trivial.
    apply union_rel_rt_right. apply incl_t_rt. hyp. apply rt1_refl.
    exists m. split. exists y. split; trivial.
    apply union_rel_rt_right. apply incl_t_rt. hyp.
    apply union_rel_rt_left. apply incl_t_rt. hyp.

    destruct xRz as [m [xRm mz]].
    assert (SN (R!1 U S!1) m) as SNm.
    apply IHr. hyp. intros y0 mRy0.
    apply sns. apply incl_rt_rt_rt. exists m.
    split; trivial. apply incl_t_rt. hyp.

    apply SN_rtc1 with m. hyp.
    apply incl_union_rtunion. hyp.
    apply IHs; trivial. apply clos_trans1_trans with y; trivial.
  Qed.

  Lemma sn_comm_sn :
    forall x, SN R x -> (forall y, (R#1) x y -> SN S y) ->
      (S@R << R!1@S#1) -> SN (R U S) x.

  Proof.
    intros x snr sns comm.
    assert (SN (R!1 U S!1) x) as sntr.
    apply sn_comm_sntr; trivial.
    apply SN_incl with (R!1 U S!1).
    apply union_inclusion.
    intros a b. apply t1_step.
    intros a b. apply t1_step.
    hyp.
  Qed.

End S.
