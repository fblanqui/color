(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-25

  This file contains a proof checker for termination criteria based
on (extended) weakly monotone algebra.
*)

From Stdlib Require Import Program.
From CoLoR Require Import ATrs RelUtil SN AWFMInterpretation AMannaNess ACompat
     ListUtil ARelation LogicUtil OptUtil IntBasedChecker Problem
     NaryFunction Proof.

Set Implicit Arguments.

Section MonAlgChecker.

Variable Sig : Signature.

Notation Problem := (Problem Sig).
Notation term := (term Sig).
Notation rule := (@rule Sig).
Notation rules := (@list rule).

Variable domain : Type.
Let D := domain.
Variable domain_elt : D.

Variable succ : relation D.
Variable succeq : relation D.
Variable succ_wf : WF succ.
Variable succ_succeq_compat : absorbs_left succ succeq.

Variable arSymInt : nat -> Set.
Notation symInt := (symInt Sig arSymInt).
Notation funInt := (funInt Sig arSymInt).

Variable defaultInt : forall n, arSymInt n.

Variable interpret : forall n, arSymInt n -> naryFunction1 domain n.

Program Definition makeI (int : forall f, funInt f) :=
  mkInterpretation (Sig:=Sig) domain_elt (fun f => interpret (int f)).

Variable check_succ : forall i r, option (IR (makeI i) succ (lhs r) (rhs r)).
Variable check_succeq : forall i r, option (IR (makeI i) succeq (lhs r) (rhs r)).

Section given_int.

Variable i : forall f, funInt f.
Notation I := (makeI i).

Notation IR_succ := (IR I succ).
Notation IR_succeq := (IR I succeq).

Section reduction_pairs.

Variable wm : monotone I succeq.

Lemma wf_IR_succ : WF IR_succ.

Proof.
  intros. apply IR_WF. apply succ_wf.
Qed.

Lemma absorb_succ_succeq : absorbs_left IR_succ IR_succeq.

Proof.
  intros x z xz val.
  apply succ_succeq_compat.
  destruct xz as [y [ge_xy gt_yz]].
  exists (term_int val y). split; auto.
Qed.

Definition wrp := mkWeak_reduction_pair 
  (IR_substitution_closed (I:=I) (R:=succ))
  (IR_substitution_closed (I:=I) (R:=succeq))
  (IR_context_closed wm) absorb_succ_succeq wf_IR_succ.

Section sm.

Variable sm : monotone I succ.

Definition rp := mkReduction_pair 
  (IR_substitution_closed (I:=I) (R:=succ))
  (IR_substitution_closed (I:=I) (R:=succeq))
  (IR_context_closed sm) (IR_context_closed wm)
  absorb_succ_succeq wf_IR_succ.

End sm.

End reduction_pairs.

Section prover.

Variable check_int_wm : option (monotone I succeq).
Variable check_int_sm : option (monotone I succeq /\ monotone I succ).

Program Definition check_compat (R : rules) (F : relation D)
  (check_compat : forall i r, option (IR (makeI i) F (lhs r) (rhs r))) :
  option (compat (IR (makeI i) F) R) :=
  match lforall_opt _ (check_compat i) R with
  | Some _ => Some _
  | None => None
  end. 

Next Obligation.
Proof with try discr; auto.
  destruct_call lforall_opt...
  intros t u Rtu. destruct (lforall_in wildcard' Rtu). hyp.
Qed.

Program Definition simplify (R : rules) : 
  option { Rge : rules  | 
          exists Rgt : rules,
            compat IR_succ Rgt /\ 
            compat IR_succeq Rge /\
            incl R (Rgt ++ Rge)
      } := 
  let (Rp, obl) := partition_opt _ (check_succ i) R in
    match check_compat (snd Rp) check_succeq with
    | None => None
    | Some _ => Some (snd Rp)
    end.

Next Obligation.
Proof with try discr; auto.
  exists l. destruct_call check_compat...
  repeat split...
  intros t u Rtu. exact (lforall_in H Rtu).
  intros p pR. apply in_or_app. apply H1...
Qed.

Program Definition applyMonotoneAlgebra (P : Problem) : 
  option { P' : Problem | Prob_WF P' -> Prob_WF P } :=

  match P with
  | FullTerm R =>
      match check_int_sm with
      | None => None
      | Some sm =>
          match simplify R with
          | None => None
          | Some R' => Some (FullTerm R')
          end
      end
  | RelTopTerm T R =>
      match check_int_wm with
      | None => None
      | Some wm =>
        match check_compat T check_succeq with
        | None => None
        | Some _ => 
            match simplify R with
            | None => None
            | Some R' => Some (RelTopTerm T R')
            end
        end
      end
  | RelTerm T R =>
      match check_int_sm with
      | None => None
      | Some sm =>
          match simplify T with
          | None => None
          | Some T' =>
              match simplify R with
              | None => None
              | Some R' => Some (RelTerm T' R')
              end
          end
      end
  end.

Next Obligation.
Proof with try discr; auto.
  destruct_call simplify... 
  clear Heq_anonymous s.
  apply WF_incl with (red (H0 ++ R')). apply red_incl...
  apply rule_elimination with (rp m m0)...
Qed.
Next Obligation.
Proof with try discr; auto.
  destruct_call simplify... 
  apply WF_incl with (hd_red_mod T (H0 ++ R')).
  comp. apply hd_red_incl...
  apply rule_elimination_hd_mod with (wrp wm)...
Qed.
Next Obligation.
Proof with try discr; auto.
  do 2 destruct_call simplify... 
  clear Heq_anonymous s0 Heq_anonymous0 s.
  apply WF_incl with (red_mod (H1 ++ T') (H0 ++ R')).
  comp. apply rtc_incl. apply red_incl... apply red_incl...
  apply rule_elimination_mod with (rp m m0)...
Qed.

End prover.

End given_int.

Record monSpec monR := 
  { monP : symInt -> Prop
  ; mon_check : forall (i : symInt), option (monP i)
  ; mon_ok : forall (i : symInt), 
      monP i -> Vmonotone1 (interpret (projT2 i)) monR
  }.

Let buildSymInt := buildSymInt Sig arSymInt.
Let defaultIntForSymbol := defaultIntForSymbol Sig arSymInt defaultInt.

Variable wm : monSpec succeq.
Variable sm : monSpec succ.
Variable sm_imp_wm : forall s, monP sm s -> monP wm s.
Variable sm_default : forall f, (monP sm) 
  (buildSymInt (defaultIntForSymbol f)).

Lemma wm_default : forall f,
  (monP wm) (buildSymInt (defaultIntForSymbol f)).

Proof with auto.
  intros. apply sm_imp_wm...
Qed.

Section monotonicityChecker.

Variable i : list symInt.
Let I := (makeI (buildInt defaultInt i)).

Let buildInt := (buildInt defaultInt i).

Program Definition check_wm : option (monotone I succeq) :=
  match @checkProp Sig arSymInt defaultInt
    (monP wm) (mon_check wm) wm_default i with
  | None => None
  | Some _ => Some _
  end.

Next Obligation.
Proof with auto.
  intro f. apply (mon_ok wm (buildSymInt (buildInt f))).
  destruct_call checkProp... 
Qed.

Program Definition check_sm : 
  option (monotone I succeq /\ monotone I succ) :=
  match @checkProp Sig arSymInt defaultInt
    (monP sm) (mon_check sm) sm_default i with
  | None => None
  | Some _ => Some _
  end.

Next Obligation.
Proof with auto.
  split; intro f.
  apply (mon_ok wm (buildSymInt (buildInt f))).
  apply sm_imp_wm.
  destruct_call checkProp...
  apply (mon_ok sm (buildSymInt (buildInt f))).
  destruct_call checkProp... 
Qed.

End monotonicityChecker.

Section solver.

Variable rawSymInt : Type.
Variable rti : rawTrsInt Sig rawSymInt.
Variable check_ri : Sig -> rawSymInt -> option symInt.

Program Definition monotoneAlgebraSolver (P : Problem) :
  option { P' : Problem | Prob_WF P' -> Prob_WF P } :=

  match processInt check_ri rti with
  | None => None
  | Some fis =>
      applyMonotoneAlgebra (check_wm fis) (check_sm fis) P
  end.

End solver.

End MonAlgChecker.
