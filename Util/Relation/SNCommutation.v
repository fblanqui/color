(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Joerg Endrullis, 2008-07

Commutation properties of relations and SN.
The main theorem is:
  forall x : T, 
    SN R x 
    -> (forall y : T, (R#1) x y -> SN S y) 
    -> (S@R << R!1@S#1)
    -> SN (R U S) x.
Thus commutation allows to prove SN in a modular way.
*)

(* $Id: SNCommutation.v,v 1.2 2008-07-28 21:29:22 joerg Exp $ *)

Set Implicit Arguments.

Require Export ACompat.
Require Import RelUtil.

Section Commutation_and_SN.

Variable T : Type.
Variable R S : relation T.

(***********************************************************************)
(* Commutation Properties *)

Lemma comm_s_rt : 
  S@(R!1) << (R!1)@(S!1) -> (S!1)@(R!1) << (R!1)@(S!1).

Proof.
  intros comm x y [z [H1 H2]].
  induction H1 as [x z H | x y' z H H0 IH].
  apply comm. 
  exists z; split; assumption.
  assert (H1 := IH H2); clear IH H2.
  destruct H1 as [u [H2 H3]].
  assert ((clos_trans1 R @ clos_trans1 S) x u).
  apply comm. exists y'; split; assumption.
  destruct H1 as [m [xRm mSu]].
  exists m; split. assumption.
  exact (clos_trans1_trans mSu H3).
Qed.

Lemma comm_s_r :
  S@R << (R!1)@(S#1) ->
    (R U S)#1 @ R @ (R U S)#1 << (R!1) @ (R U S)#1.

Proof.
  intros comm x y [z2 [[z1 [xRSz1 z1Rz2] z2RSy]]].
  induction xRSz1 as [ | m n z1 mRSn nRSz1 IH].
  exists z2. split. apply t1_step. assumption. assumption.
  (* m RUS n RUS# z1 R z2 RUS# y *)
  assert (((R!1) @ (R U S)#1) n y) as mRedy. apply IH. assumption.
  (* m RUS n R!1@RUS#1 y *)
  clear nRSz1 z1Rz2 z2RSy IH z1 z2.
  destruct mRedy as [o [nRo oRSy]].
  (* m RUS n R!1 o RUS#1 y *)
  induction mRSn.
  (* m R n *)
    exists o. split; auto. apply t1_trans with n; assumption.
  (* m S n *)
    destruct nRo as [o p oRp | o p q oRp pRq ];

    assert (((R!1)@(S#1)) m p) as mRedp.
    apply comm. exists o; split; assumption.
    destruct mRedp as [x [mRx xSp]].
    exists x. split. assumption.
    apply clos_refl_trans1_trans with p.
    apply union_rel_rt_right. assumption. assumption.

    assert (((R!1)@(S#1)) m p) as mRedp.
    apply comm. exists o. split; assumption.
    destruct mRedp as [x [mRx xSp]].
    exists x. split. assumption. assumption.
    destruct mRedp as [n [mRn sSp]].
    exists n; split. assumption.
    apply clos_refl_trans1_trans with q.
    apply clos_refl_trans1_trans with p.
    apply union_rel_rt_right. assumption.
    apply union_rel_rt_left. apply incl_t_rt. assumption.    
    assumption.
Qed.

(***********************************************************************)
(* Commutation and SN *)

Lemma sn_comm_sntr :
  forall x : T, SN R x -> (forall y : T, (R#1) x y -> SN S y) ->
    (S@R << R!1@S#1) -> SN (R!1 U S!1) x.

Proof.
  intros x snr sns comm.
  assert (snrt := SN_tc1 snr); clear snr.

  (* Induction on x R! ... *)
  induction snrt as [x _ IHr].
  apply SN_intro. intros y xRSy.
  destruct xRSy as [xRy | xSy]. apply IHr. assumption.
  assert (SN (S!1) y) as sny.
  apply SN_tc1. apply sns. apply incl_t_rt; assumption.

  (* x R! y *)
  intros y0 yRy0. apply sns.
  apply incl_rt_rt_rt. exists y; split; trivial.
  apply incl_t_rt. assumption.

  (* x S! y *)
  assert (SN (S!1) y) as sny. apply SN_tc1.
  apply SN_rtc1 with x. apply sns. apply rt1_refl.
  apply incl_t_rt. assumption.

  (* Induction on y S! ... *)
  induction sny as [y _ IHs].
  apply SN_intro. intros z yRSz.
  destruct yRSz as [yRz | ySz].

  assert ((R!1 @ (R U S)#1) x z) as xRz.
    apply comm_s_r; trivial.
    destruct yRz as [y z yRz | y m z yRm mRz].
    exists z. split. exists y. split; trivial.
    apply union_rel_rt_right. apply incl_t_rt. assumption. apply rt1_refl.
    exists m. split. exists y. split; trivial.
    apply union_rel_rt_right. apply incl_t_rt. assumption.
    apply union_rel_rt_left. apply incl_t_rt. assumption.

  destruct xRz as [m [xRm mz]].
  assert (SN (R!1 U S!1) m) as SNm.
  apply IHr. assumption. intros y0 mRy0.
  apply sns. apply incl_rt_rt_rt. exists m.
  split; trivial. apply incl_t_rt. assumption.

  apply SN_rtc1 with m. assumption.
  apply incl_union_rtunion. assumption.
  apply IHs; trivial. apply clos_trans1_trans with y; trivial.
Qed.

Lemma sn_comm_sn :
  forall x : T, SN R x -> (forall y : T, (R#1) x y -> SN S y) ->
    (S@R << R!1@S#1) -> SN (R U S) x.

Proof.
  intros x snr sns comm.
  assert (SN (R!1 U S!1) x) as sntr.
  apply sn_comm_sntr; trivial.
  apply SN_incl with (R!1 U S!1).
  apply incl_union.
  intros a b. apply t1_step.
  intros a b. apply t1_step.
  assumption.
Qed.

End Commutation_and_SN.
