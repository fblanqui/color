From Coq Require Import Setoid List Relations Lia Arith.
From CoLoR Require Import weaved_relation list_permut terminaison.
From CoLoR Require rpo equational_theory equational_extension term subterm_dp
     order_extension.

Set Implicit Arguments.

Section MakePrecedence.
  Variable A : Type.
  Variable status : A -> rpo.status_type.
  Variable prec_nat : A -> nat.

   Definition prec (a1 a2 : A) := prec_nat a1 < prec_nat a2.

   Definition prec_eq (a1 a2 : A) :=  eq_nat (prec_nat a1) (prec_nat a2).

  Definition prec_bool (a1 a2 : A) := leb (S (prec_nat a1)) (prec_nat a2).

  Definition prec_eq_bool (a1 a2 : A) := Nat.eqb (prec_nat a1)  (prec_nat a2).


Lemma prec_bool_ok : forall a1 a2,
    if prec_bool a1 a2 then prec a1 a2 else ~prec a1 a2.
  Proof.
    intros; case_eq (prec_bool a1 a2); intros;
    [ apply leb_complete; assumption |];
    unfold prec; unfold lt; intros H0;
    apply leb_correct in H0;
    unfold prec_bool in H; rewrite H0 in H;
    discriminate H.
  Qed.

Lemma prec_eq_bool_ok: forall a1 a2, match prec_eq_bool a1 a2 with true => prec_eq a1 a2 | false => ~prec_eq a1 a2 end.
Proof.
unfold prec. unfold prec_eq.    unfold prec_eq_bool. 
intros; case_eq( Nat.eqb (prec_nat a1) (prec_nat a2)); intros.
assert (prec_nat a1 = prec_nat a2).   
apply Nat.eqb_eq. rewrite H. trivial. rewrite H0. apply eq_nat_refl.
intro.
assert (prec_nat a1 = prec_nat a2).
apply eq_nat_eq; trivial.
contradict H1.
apply Nat.eqb_neq. trivial.
Qed.

  Lemma prec_antisym : forall a, prec a a -> False.
  Proof.
    intros; apply (Nat.lt_irrefl _ H).
  Qed.

  Lemma prec_transitive : transitive A prec.
  Proof.
    intros a b c H1 H2; apply Nat.lt_trans with (prec_nat b); assumption.
  Qed.

  Lemma prec_eq_transitive : transitive A prec_eq.
  Proof.
intros a b c H1 H2. unfold prec_eq. unfold prec_eq in H2. unfold prec_eq in H1. assert (H3: prec_nat a = prec_nat b).  apply eq_nat_eq.  trivial. assert (H4: prec_nat b = prec_nat c). apply eq_nat_eq. trivial. assert (H5: prec_nat a = prec_nat c). lia. rewrite H5. apply eq_nat_refl.
  Qed.

Lemma prec_eq_prec1: forall a1 a2 a3, prec a1 a2 -> prec_eq a2 a3 -> prec a1 a3.
Proof.
unfold prec. unfold prec_eq. intros. assert (prec_nat a2 = prec_nat a3). apply eq_nat_eq. trivial. rewrite <- H1. trivial. 
Qed.

Lemma prec_eq_prec2:  forall a1 a2 a3, prec a1 a2 -> prec_eq a1 a3 -> prec a3 a2.
Proof.
unfold prec. unfold prec_eq. intros. assert (prec_nat a1= prec_nat a3). apply eq_nat_eq. trivial. rewrite <- H1. trivial. 
Qed.
  
Lemma  prec_eq_sym : forall s t, prec_eq s t -> prec_eq t s.
Proof.
unfold prec_eq. intros. assert (prec_nat s = prec_nat t). apply eq_nat_eq. trivial. rewrite H0. apply eq_nat_refl.
Qed.

Lemma  prec_eq_refl : forall s, prec_eq s s.
Proof.
unfold prec_eq. intros. apply eq_nat_refl.
Qed.
 
Hypothesis  prec_eq_status: forall f g, prec_eq f g -> status f = status g. 

(* Proof. *)
(* unfold prec. unfold prec_eq. *)
(* intros. *)
(* assert (prec_nat f = prec_nat g). apply eq_nat_eq. trivial. lia. *)
(* Qed. *)

Lemma prec_not_prec_eq: forall f g, prec f g -> prec_eq f g -> False.
Proof.
unfold prec. unfold prec_eq. intros.
assert (prec_nat f = prec_nat g). apply eq_nat_eq. trivial. lia.
Qed.

Lemma prec_wf : well_founded prec.
  Proof.
    apply Inverse_Image.wf_inverse_image with (f:=prec_nat); apply lt_wf.
  Qed.

  Definition Precedence := rpo.Build_Precedence status
    prec_bool prec_eq_bool prec_bool_ok prec_eq_bool_ok prec_antisym prec_transitive prec_eq_transitive prec_eq_prec1 prec_eq_prec2 prec_eq_sym prec_eq_refl prec_eq_status prec_not_prec_eq.
End MakePrecedence.

Module MakeRpoExt (Eqt : equational_theory_spec.EqTh).

  Module M := Eqt.T.
  Module Rpo := rpo.Make(M).
  Module Import op := order_extension.OrderingPair(Eqt).

  Section S.
    Variable n : nat.
    Variable prec : M.symbol -> nat.
    Variable status : M.symbol -> rpo.status_type.

    Variable prec_eq_status: forall f, forall g, prec_eq prec f g -> status f = status g. 

    Definition P := Precedence status  prec prec_eq_status.

    Lemma rpo_eq_trans : transitive _ (Rpo.rpo_eq P n).
    Proof.
      intros x y z; do 2 inversion 1; subst;
      [ constructor; destruct (Rpo.equiv_equiv P); transitivity y
      | constructor 2; rewrite (@Rpo.equiv_rpo_equiv_2 P n  x y)
      | constructor 2; apply (@Rpo.equiv_rpo_equiv_1 P n y z H4 x)
      | constructor 2; apply Rpo.rpo_trans with y ]; assumption.
    Qed.

    Lemma rpo_rpo_eq_compat : Trel_compat (Rpo.rpo P n) (Rpo.rpo_eq P n).
    Proof.
      intros t1 t2 t3 H H0; inversion H0; subst;
      [ apply (proj1 (@Rpo.equiv_rpo_equiv_1 P _ _ _ H1 _) H)
      | apply Rpo.rpo_trans with t2; assumption ].
    Qed.

    Lemma osl_R_pos : forall R f l1 l2,
      one_step_list R l1 l2 -> exists p, exists s, exists t,
        R s t /\ M.is_a_pos (M.Term f l1) (p::nil) = true /\
        M.Term f l1 = M.replace_at_pos (M.Term f l1) s (p::nil) /\
        M.Term f l2 = M.replace_at_pos (M.Term f l1) t (p::nil).
    Proof.
      intros R f l1 l2 H;
      revert l2 H; induction l1; intros l2 H; inversion H; subst;
      [ exists O; exists a; exists t2; repeat split; assumption |];
      apply IHl1 in H3; destruct H3 as [p [s [t [H0 [H1 [H2 H3]]]]]];
      exists (S p); exists s; exists t; repeat split; try assumption;
      [ simpl in H2; injection H2 | simpl in H3; injection H3 ];
      intros Heq; simpl; rewrite <- Heq; reflexivity.
    Qed.

    Lemma rpo_eq_monotone : Trel_monotone (Rpo.rpo_eq P n).
    Proof.
      intros f l1 l2 H;
      apply osl_R_pos with (f:=f) in H;
      destruct H as [p [s [t [H0 [H1 [H2 H3]]]]]];
      rewrite H2; rewrite H3; apply Rpo.rpo_eq_add_context; assumption.
    Qed.

    Lemma rpo_monotone : Trel_monotone (Rpo.rpo P n).
    Proof.
      intros f l1 l2 H;
      apply osl_R_pos with (f:=f) in H;
      destruct H as [p [s [t [H0 [H1 [H2 H3]]]]]];
      rewrite H2; rewrite H3; apply Rpo.rpo_add_context; assumption.
    Qed.

    Definition rpo_inf_nil : Rpo.rpo_inf P.
    Proof.
      apply Rpo.Build_rpo_inf with (bb:=n)
        (rpo_l:=nil) (equiv_l:=nil) (rpo_eq_l:=nil);
      simpl in |-*; intros t1 t2 H; contradiction H.
    Defined.

    Definition rpo_eic (t1 t2 : M.term) :=
      @Rpo.rpo_eval_is_complete P rpo_inf_nil
        (M.size t1 + M.size t2) t1 t2 (le_n _).
  End S.

  Ltac prove_rpo prec stat :=
    simpl; match goal with
    |- ?rpo _ ?n ?t1 ?t2 =>
      let H := fresh "H" in
      set (H:=@rpo_eic n prec stat t1 t2);
      vm_compute in H;
      match rpo with
      | Rpo.rpo => exact H
      | Rpo.rpo_eq => constructor; exact H
      end
    end.
End MakeRpoExt.

Module MakeRpoLexAFS (Eqt : equational_theory_spec.EqTh).

  Module Ext := MakeRpoExt(Eqt).
  Module Afs := order_extension.OrdSafeAFS(Eqt).
  Module Lex := order_extension.MakeLEX(Eqt).

  Module M := Eqt.T.
  Module Rpo := Ext.Rpo.

  Section S.
    Variable n : nat.
    Variable prec : M.symbol -> nat.
    Variable status : M.symbol -> rpo.status_type.
    Variable afs_symb : M.symbol -> Afs.afs_val.
   Variable prec_eq_status: forall f, forall g, prec_eq prec f g -> status f = status g. 

    Definition P := Precedence status prec prec_eq_status.

    Let afs := Afs.afs_term afs_symb.
    Let rpo_afs (t1 t2 : M.term) := Rpo.rpo P n (afs t1) (afs t2).
    Let rpo_eq_afs (t1 t2 : M.term) := Rpo.rpo_eq P n (afs t1) (afs t2).

    Variable R_rules : relation M.term.
    Hypothesis rules_decrease : inclusion _ R_rules rpo_afs.

    Lemma rpo_stable_afs : Ext.op.Trel_stable R_rules rpo_afs.
    Proof.
      intros t1 t2 sigma H; unfold rpo_afs; unfold afs;
      rewrite Afs.afs_subst; rewrite Afs.afs_subst;
      apply Rpo.rpo_subst; apply rules_decrease; assumption.
    Qed.

    Lemma wf : well_founded (Eqt.one_step R_rules).
    Proof.
      apply Lex.wf_R with (Tlt:=rpo_afs).
      apply Inverse_Image.wf_inverse_image with (f:=afs);
      apply Rpo.wf_rpo; apply (prec_wf prec ).
      apply Afs.Tlt_monotone_afs;
      [ apply Ext.rpo_monotone
      | intros x y z; apply Rpo.rpo_trans ].
      apply rpo_stable_afs.
    Qed.

    Variables R_large R_union : relation M.term.
    Hypothesis rules_large_decrease : inclusion _ R_large rpo_eq_afs.
    Hypothesis rules_large_wf : well_founded (Eqt.one_step R_large).
    Hypothesis rules_union_def : forall (t1 t2 : M.term),
      R_union t1 t2 -> R_rules t1 t2 \/ R_large t1 t2.

    Lemma wf_union : well_founded (Eqt.one_step R_union).
    Proof.
      apply Lex.wf_union_R with (Tle:=rpo_eq_afs) (Tlt:=rpo_afs)
        (R_rules:=R_rules) (R_large:=R_large); try assumption.
      unfold rpo_afs; apply Inverse_Image.wf_inverse_image;
      apply Rpo.wf_rpo; apply (prec_wf prec).
      apply Afs.Tle_monotone_afs;
      [ apply Ext.rpo_eq_monotone
      | apply Ext.rpo_eq_trans ].
      apply Afs.Tlt_monotone_afs;
      [ apply Ext.rpo_monotone
      | intros x y z; apply Rpo.rpo_trans ].
      apply Afs.Tlt_Tle_compat_afs;
      apply Ext.rpo_rpo_eq_compat.
      apply rpo_stable_afs.

      intros t1 t2 sigma H; unfold rpo_eq_afs; unfold afs;
      rewrite Afs.afs_subst; rewrite Afs.afs_subst;
      apply Rpo.rpo_eq_subst; apply rules_large_decrease;
      assumption.
    Qed.
  End S.

  Ltac prove_wf bb prc stat afs :=
    let t1 := fresh "t1" in let t2 := fresh "t2" in
    let H  := fresh "H"  in
    match goal with
    |- well_founded (?os ?R) =>
       apply wf with (n:=bb) (prec:=prc) (status:=stat) (afs_symb:=afs);
       intros t1 t2 H; inversion H; subst; Ext.prove_rpo prc stat
    end.

  Ltac prove_wf_union bb nprec nstat nafs ds dl wfl := 
    let t1 := fresh "t1" in let t2 := fresh "t2" in
      let l1 := fresh "l1" in let l2 := fresh "l2" in
        let f  := fresh "f"  in let H  := fresh "H"  in
          let Hl := fresh "Hl" in let Ht := fresh "Ht" in
            match goal with
              |- well_founded (?one_step ?R) =>
                apply wf_union with (n:=bb) (R_rules:=ds) (R_large:=dl)
                  (prec:=nprec) 
                  (status:=nstat)
                  (afs_symb:=nafs); 
                  [
                    intros t1 t2 H; inversion H; subst;
                      Ext.prove_rpo  nprec nstat|
                        intros t1 t2 H; inversion H; subst;
                          Ext.prove_rpo  nprec nstat|
                            apply wfl|
                              intros t1 t2 H; inversion H; subst;
                                try solve [left; constructor]; right; constructor                  ]
            end.

End MakeRpoLexAFS.

Module MakeRpoSdpAFS (Eqt : equational_theory_spec.EqTh).

  Module Ext := MakeRpoExt(Eqt).
  Module Afs := order_extension.OrdAFS(Eqt).
  Module Sdp := order_extension.MakeSDP(Eqt).

  Module M := Eqt.T.
  Module Rpo := Ext.Rpo.

  Section S.
    Variable n : nat.
    Variable prec : M.symbol -> nat.
    Variable status : M.symbol -> rpo.status_type.
    Variable afs_symb : M.symbol -> Afs.afs_val.
   Variable prec_eq_status: forall f, forall g, prec_eq prec f g -> status f = status g. 

    Definition P := Precedence status prec prec_eq_status.

    Let afs := Afs.afs_term afs_symb.
    Let rpo_afs (t1 t2 : M.term) := Rpo.rpo P n (afs t1) (afs t2).
    Let rpo_eq_afs (t1 t2 : M.term) := Rpo.rpo_eq P n (afs t1) (afs t2).

    Variable R_rules dps : relation M.term.
    Hypothesis rules_decrease : inclusion _ R_rules rpo_eq_afs.
    Hypothesis dps_strictly_decrease : inclusion _ dps rpo_afs.

    Lemma rpo_eq_stable_afs : Ext.op.Trel_stable R_rules rpo_eq_afs.
    Proof.
      intros t1 t2 sigma H; unfold rpo_eq_afs; unfold afs;
      rewrite Afs.afs_subst; rewrite Afs.afs_subst; apply Rpo.rpo_eq_subst;
      apply rules_decrease; assumption.
    Qed.

    Lemma rpo_stable_afs : Ext.op.Trel_stable dps rpo_afs.
    Proof.
      intros t1 t2 sigma H; unfold rpo_afs; unfold afs;
      rewrite Afs.afs_subst; rewrite Afs.afs_subst; apply Rpo.rpo_subst;
      apply dps_strictly_decrease; assumption.
    Qed.

    Lemma wf : well_founded (Sdp.sdp.Rcdp_min R_rules dps).
    Proof.
      apply Sdp.wf_Rcdp_rest with (Tle:=rpo_eq_afs) (Tlt:=rpo_afs).
      unfold rpo_afs; apply Inverse_Image.wf_inverse_image;
      apply Rpo.wf_rpo; apply (prec_wf prec).
      apply Afs.Tle_monotone_afs;
      [ apply Ext.rpo_eq_monotone
      | constructor; constructor
      | apply Ext.rpo_eq_trans ].
      apply Afs.Tlt_Tle_compat_afs;
      apply Ext.rpo_rpo_eq_compat.
      apply rpo_eq_stable_afs.
      apply rpo_stable_afs.
    Qed.

    Variables dps_large dps_union : relation M.term.
    Hypothesis dps_large_decrease : inclusion _ dps_large rpo_eq_afs.
    Hypothesis dps_large_wf : well_founded (Sdp.sdp.Rcdp_min R_rules dps_large).
    Hypothesis dps_union_def : forall (t1 t2 : M.term),
      dps_union t1 t2 -> dps t1 t2 \/ dps_large t1 t2.

    Lemma wf_union : well_founded (Sdp.sdp.Rcdp_min R_rules dps_union).
    Proof.
      apply Sdp.wf_union_Rcdp_rest with (Tle:=rpo_eq_afs) (Tlt:=rpo_afs)
        (dps:=dps) (dps_large:=dps_large); try assumption.
      unfold rpo_afs; apply Inverse_Image.wf_inverse_image;
      apply Rpo.wf_rpo; apply (prec_wf prec).
      apply Afs.Tle_monotone_afs;
      [ apply Ext.rpo_eq_monotone
      | constructor; constructor
      | apply Ext.rpo_eq_trans ].
      apply Afs.Tlt_Tle_compat_afs;
      apply Ext.rpo_rpo_eq_compat.
      apply rpo_eq_stable_afs.
      apply rpo_stable_afs.

      intros t1 t2 sigma H; unfold rpo_eq_afs; unfold afs;
      rewrite Afs.afs_subst; rewrite Afs.afs_subst;
      apply Rpo.rpo_eq_subst;
      apply dps_large_decrease; assumption.
    Qed.
  End S.
End MakeRpoSdpAFS.

Module MakeRpoSdpMarkedAFS (Eqt : equational_theory_spec.EqTh).

  Module Mrk := order_extension.MakeMarkedEqTh(Eqt).
  Module EqtM := Mrk.EQT.

  Module Ext := MakeRpoExt(EqtM).
  Module Afs := order_extension.OrdAFS(Eqt).
  Module AfsM := order_extension.OrdAFS(EqtM).
  Module Sdp := order_extension.MakeMarkedSDP(Eqt)(EqtM).

  Module T := Eqt.T.
  Module M := EqtM.T.
  Module Rpo := Ext.Rpo.

  Section S.
    Variable n : nat.

    Variable prec : T.symbol -> nat.
    Variable prec_marked : T.symbol -> nat.

    Variable status : T.symbol -> rpo.status_type.
    Variable status_marked : T.symbol -> rpo.status_type.

    Variable afs_symb : T.symbol -> Afs.afs_val.
    Variable afs_symb_marked : T.symbol -> Afs.afs_val.
  

    Definition prec_union (f : M.symbol) : nat :=
      match f with
      | (true, f) => prec_marked f
      | (_, f) => prec f
      end.

    Definition status_union (f : M.symbol) : rpo.status_type :=
      match f with
      | (true, f) => status_marked f
      | (_, f) => status f
      end.

    Definition afs_symb_union (f : M.symbol) : AfsM.afs_val :=
      match f with
      | (true, f) =>
        match afs_symb_marked f with
        | Afs.AFS_id g =>
          AfsM.AFS_id (Nat.eqb (prec_marked f) (prec_marked g), g)
        | Afs.AFS_arg i =>
          AfsM.AFS_arg i
        | Afs.AFS_filt g p =>
          AfsM.AFS_filt (Nat.eqb (prec_marked f) (prec_marked g), g) p
        end
      | (_, f) =>
        match afs_symb f with
        | Afs.AFS_id g =>
          AfsM.AFS_id (Nat.eqb (prec f) (prec_marked g), g)
        | Afs.AFS_arg i =>
          AfsM.AFS_arg i
        | Afs.AFS_filt g p =>
          AfsM.AFS_filt (Nat.eqb (prec f) (prec_marked g), g) p
        end
      end.

   Variable prec_eq_status: forall f, forall g, prec_eq prec_union f g -> status_union f = status_union g. 

  Definition P := Precedence status_union prec_union prec_eq_status.

    Let afs := AfsM.afs_term afs_symb_union.
    Let rpo_afs (t1 t2 : M.term) := Rpo.rpo P n (afs t1) (afs t2).
    Let rpo_eq_afs (t1 t2 : M.term) := Rpo.rpo_eq P n (afs t1) (afs t2).

    Let mark_term := Sdp.mark_term Mrk.mark_symb.
    Let inject_term := Sdp.inject_term Mrk.inject_symb.

    Let Tlt_mark (t1 t2 : T.term) :=
      rpo_afs (mark_term (inject_term t1)) (mark_term (inject_term t2)).

    Let Tle_mark (t1 t2 : T.term) :=
      rpo_eq_afs (mark_term (inject_term t1)) (mark_term (inject_term t2)).

    Let Tle_inject (t1 t2 : T.term) :=
      rpo_eq_afs (inject_term t1) (inject_term t2).

    Variable R_rules dps : relation T.term.
    Hypothesis rules_decrease : inclusion _ R_rules Tle_inject.
    Hypothesis dps_strictly_decrease : inclusion _ dps Tlt_mark.
    Hypothesis dps_non_variable : forall (t1 t2 : T.term),
      dps t1 t2 -> Sdp.is_fapp t1 /\ Sdp.is_fapp t2.

    Lemma rpo_eq_stable_afs : Sdp.opT.Trel_stable R_rules Tle_inject.
    Proof.
      intros t1 t2 sigma H; unfold Tle_inject; unfold inject_term;
      rewrite Sdp.inject_subst; rewrite Sdp.inject_subst;
      unfold rpo_eq_afs; unfold afs;
      rewrite AfsM.afs_subst; rewrite AfsM.afs_subst;
      apply Rpo.rpo_eq_subst; apply rules_decrease; assumption.
    Qed.

    Lemma rpo_stable_afs : Sdp.opT.Trel_stable dps Tlt_mark.
    Proof.
      intros t1 t2 sigma H; unfold Tlt_mark;
      unfold inject_term; unfold mark_term;
      rewrite Sdp.mark_inject_subst; [| apply (dps_non_variable H) ];
      rewrite Sdp.mark_inject_subst; [| apply (dps_non_variable H) ];
      unfold rpo_afs; unfold afs;
      rewrite AfsM.afs_subst; rewrite AfsM.afs_subst;
      apply Rpo.rpo_subst; apply dps_strictly_decrease; assumption.
    Qed.

    Lemma wf : well_founded (Sdp.sdp.Rcdp_min R_rules dps).
    Proof.
      apply Sdp.wf_Rcdp_rest with
        (Tle:=rpo_eq_afs) (Tlt:=rpo_afs)
        (inject_symb:=Mrk.inject_symb) (mark_symb:=Mrk.mark_symb).
      unfold rpo_afs; apply Inverse_Image.wf_inverse_image;
      apply Rpo.wf_rpo; apply (prec_wf prec_union).
      apply AfsM.Tle_monotone_afs;
      [ apply Ext.rpo_eq_monotone
      | constructor; constructor
      | apply Ext.rpo_eq_trans ].
      apply AfsM.Tlt_Tle_compat_afs;
      apply Ext.rpo_rpo_eq_compat.
      apply rpo_eq_stable_afs.
      apply rpo_stable_afs.
    Qed.

    Variables dps_large dps_union : relation T.term.
    Hypothesis dps_large_decrease : inclusion _ dps_large Tle_mark.
    Hypothesis dps_large_non_variable : forall (t1 t2 : T.term),
      dps_large t1 t2 -> Sdp.is_fapp t1 /\ Sdp.is_fapp t2.

    Hypothesis dps_large_wf : well_founded (Sdp.sdp.Rcdp_min R_rules dps_large).
    Hypothesis dps_union_def : forall (t1 t2 : T.term),
      dps_union t1 t2 -> dps t1 t2 \/ dps_large t1 t2.

    Lemma wf_union : well_founded (Sdp.sdp.Rcdp_min R_rules dps_union).
    Proof.
      apply Sdp.wf_union_Rcdp_rest with
        (Tle:=rpo_eq_afs) (Tlt:=rpo_afs)
        (dps:=dps) (dps_large:=dps_large)
        (inject_symb:=Mrk.inject_symb) (mark_symb:=Mrk.mark_symb);
      try assumption.
      unfold rpo_afs; apply Inverse_Image.wf_inverse_image;
      apply Rpo.wf_rpo; apply (prec_wf prec_union).
      apply AfsM.Tle_monotone_afs;
      [ apply Ext.rpo_eq_monotone
      | constructor; constructor
      | apply Ext.rpo_eq_trans ].
      apply AfsM.Tlt_Tle_compat_afs;
      apply Ext.rpo_rpo_eq_compat.
      apply rpo_eq_stable_afs.
      apply rpo_stable_afs.

      intros t1 t2 sigma H; unfold Tlt_mark;
      unfold inject_term; unfold mark_term;
      rewrite Sdp.mark_inject_subst; [| apply (dps_large_non_variable H) ];
      rewrite Sdp.mark_inject_subst; [| apply (dps_large_non_variable H) ];
      unfold rpo_eq_afs; unfold afs;
      rewrite AfsM.afs_subst; rewrite AfsM.afs_subst;
      apply Rpo.rpo_eq_subst; apply dps_large_decrease; assumption.
    Qed.
  End S.

  Ltac prove_wf bb nprec nstat nafs mprec mstat mafs :=
    let t1 := fresh "t1" in let t2 := fresh "t2" in
    let l1 := fresh "l1" in let l2 := fresh "l2" in
    let f  := fresh "f"  in let H  := fresh "H"  in
    let Hl := fresh "Hl" in let Ht := fresh "Ht" in
    match goal with
    |- well_founded (?rcdp ?R ?du) =>
       apply Inclusion.wf_incl with (Sdp.sdp.Rcdp_min R du);
       [ intros t1 t2 [[f l1 l2 Hl Ht] H];
         split; [ constructor 1 with l2 |]; assumption |];
       apply wf with (n:=bb)
         (prec:=nprec) (prec_marked:=mprec)
         (status:=nstat) (status_marked:=mstat)
         (afs_symb:=nafs) (afs_symb_marked:=mafs);
       [ intros t1 t2 H; inversion H; subst;
         Ext.prove_rpo (prec_union nprec mprec) (status_union nstat mstat)
       | intros t1 t2 H; inversion H; subst;
         Ext.prove_rpo (prec_union nprec mprec) (status_union nstat mstat)
       | intros t1 t2 H; inversion H; subst;
         split; simpl; trivial ]
    end.

  Ltac prove_wf_union bb nprec nstat nafs mprec mstat mafs ds dl wfl :=
    let t1 := fresh "t1" in let t2 := fresh "t2" in
    let l1 := fresh "l1" in let l2 := fresh "l2" in
    let f  := fresh "f"  in let H  := fresh "H"  in
    let Hl := fresh "Hl" in let Ht := fresh "Ht" in
    match goal with
    |- well_founded (?rcdp ?R ?du) =>
       apply Inclusion.wf_incl with (Sdp.sdp.Rcdp_min R du);
       [ intros t1 t2 [[f l1 l2 Hl Ht] H];
         split; [ constructor 1 with l2 |]; assumption |];
       apply wf_union with (n:=bb) (dps:=ds) (dps_large:=dl)
         (prec:=nprec) (prec_marked:=mprec)
         (status:=nstat) (status_marked:=mstat)
         (afs_symb:=nafs) (afs_symb_marked:=mafs);
       [ intros t1 t2 H; inversion H; subst;
         Ext.prove_rpo (prec_union nprec mprec) (status_union nstat mstat)
       | intros t1 t2 H; inversion H; subst;
         Ext.prove_rpo (prec_union nprec mprec) (status_union nstat mstat)
       | intros t1 t2 H; inversion H; subst;
         split; simpl; trivial
       | intros t1 t2 H; inversion H; subst;
         Ext.prove_rpo (prec_union nprec mprec) (status_union nstat mstat)
       | intros t1 t2 H; inversion H; subst;
         split; simpl; trivial
       | idtac
       | intros t1 t2 H; inversion H; subst;
         try solve [left; constructor]; right; constructor ];
       apply Inclusion.wf_incl with (rcdp R dl);
       [ intros t1 t2 [[f l1 l2 Hl Ht] H];
         split; [ constructor 1 with l2 |]; assumption
       | apply wfl ]
    end.
End MakeRpoSdpMarkedAFS.
