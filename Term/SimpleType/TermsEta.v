(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

The eta-reduction relation of simply typed lambda-calculus.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras.
From Stdlib Require Import Lia.
From CoLoR Require TermsBeta.

Module TermsEta (Sig : TermsSig.Signature).

  Module Export TB := TermsBeta.TermsBeta Sig.

  Definition Eta_preterm Pt A := \A => prelift Pt 1 @@ %0.

  Definition EtaApp : forall M A B, type M = A --> B ->
    { M': Term | env M' = env M
      /\ term M' = Eta_preterm (term M) A /\ type M' = type M }.

  Proof.
     (* from M we need to construct \x. @(M', x) where M' = lift M 1 *)
    intros.
    set (RE := decl A (env M)).
     (* build M' *)
    assert (LT: RE |- prelift (term M) 1 := A --> B).
    replace RE with ((decl A EmptyEnv) [+] (declDummy (env M))).
    apply typing_ext_env_l.
    rewrite <- lift_term.
    rewrite <- H.
    rewrite <- (lift_type M 1).
    replace (declDummy (env M)) with (liftedEnv 1 (env M) 0).
    rewrite <- (lift_env).
    exact (typing (lift M 1)).
    unfold liftedEnv, declDummy, finalSeg; simpl.
    rewrite initialSeg_full; solve [trivial | lia].
    rewrite env_comp_sum_comm.
    unfold declDummy.
    replace (None :: env M)
      with (copy (length (decl A EmptyEnv)) None ++ env M); auto.
    rewrite env_sum_disjoint; auto.
    unfold decl, declDummy.
    apply env_comp_cons; auto.
    apply env_comp_sym.
    apply env_comp_empty.
    set (L := buildT LT).
     (* build x *)
    assert (RV: RE |= 0 := A).
    constructor.
    set (RT := TVar RV).
    set (R := buildT RT).
     (* build @(M, x) *)
    assert (typeOk: type_left (type L) = type R).
    trivial.
    set (Mx_cond := Build_appCond L R (eq_refl (env L)) I typeOk).
    set (Mx := buildApp Mx_cond).
    assert (envOk: env Mx |= 0 := A).
    trivial.
    set (xMx_cond := Build_absCond Mx envOk).
    set (xMx := buildAbs xMx_cond).
    exists xMx; repeat split; trivial.
    rewrite H; trivial.
  Qed.

  Inductive EtaExpansionStep : relation Term :=
  | EtaExp: forall M A B (Mtyp: type M = A --> B), EtaExpansionStep M (proj1_sig (EtaApp M Mtyp)).
    
  Definition EtaExpansion := Reduction EtaExpansionStep.
  Notation "M -e+-> N" := (EtaExpansion M N) (at level 30).

  Inductive EtaReductionStep : relation Term :=
  | EtaRed: forall M A B (Mtyp: type M = A --> B), EtaReductionStep (proj1_sig (EtaApp M Mtyp)) M.
    
  Definition EtaReduction := Reduction EtaReductionStep.
  Notation "M -e-> N" := (EtaRed M N) (at level 30).

End TermsEta.
