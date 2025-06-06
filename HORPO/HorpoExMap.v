(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-01-22

*)

From CoLoR Require Import TermsSig Horpo HorpoWf RelExtras Terms LogicUtil.
From Stdlib Require Import List Wf_nat.

Module BT <: BaseTypes.

  Inductive BaseType_aux := Star.

  Definition BaseType := BaseType_aux.

  Lemma eq_BaseType_dec : forall A B : BaseType, {A = B} + {A <> B}.

  Proof. (*COQ:decide equality*)destruct A. destruct B. auto. Defined.

  Lemma baseTypesNotEmpty : BaseType.

  Proof Star.

End BT.

Module Sig <: Signature.

  Module BT := BT.

  Module Export ST := SimpleTypes BT.

  Inductive FunctionSymbol_aux := nil | cons | map.

  Definition FunctionSymbol := FunctionSymbol_aux.

  Lemma eq_FunctionSymbol_dec :
    forall f g : FunctionSymbol, {f = g} + {f <> g}.

  Proof. decide equality. Defined.

  Lemma functionSymbolsNotEmpty : FunctionSymbol.

  Proof nil.

  Definition f_type (f : FunctionSymbol) :=
    match f with
    | nil => #Star
    | cons => #Star --> #Star --> #Star
    | map => #Star --> (#Star --> #Star) --> #Star
    end.

End Sig.

Module Terms := Terms Sig.

Module P <: Precedence.

  Module Import S := Sig.

  Module FS <: SetA.
    Definition A := Sig.FunctionSymbol.
  End FS.

  Module Import FS_eq := Eqset_def FS.

  Module Import P <: Poset.

    Definition A := A.

    Module Export O <: Ord.

      Module S := FS_eq.

      Definition A := A.

      Definition gtA f g := 
        match f, g with
        | map, cons => True
        | _, _ => False
        end.

      Definition gtA_eqA_compat := @Eqset_def_gtA_eqA_compat A gtA.

    End O.

    Lemma gtA_so : strict_order gtA.

    Proof.
      split.
      intros x y z xy yz. destruct x; destruct y; destruct z; try_solve.
      intros x y. destruct x; try_solve.
    Qed.

  End P.

  Lemma Ord_wf : well_founded (transp gtA).

  Proof.
    apply well_founded_lt_compat with (f := fun x => 
      match x with map => 1 | _ => 0 end).
    destruct x; destruct y; try_solve.
  Qed.

  Lemma Ord_dec : forall a b, {gtA a b} + {~gtA a b}.

  Proof.
    intros x y. destruct x; try_solve.
    destruct y; try_solve.
  Defined.

End P.

Module Horpo := HorpoWf Sig P.

Import Horpo.HC.

(* -- Uncomment to verify that the theorem of well-foundedness of horpo 
   does not depend on any axioms.
 Print Assumptions Horpo.horpo_beta_wf.
*)

Section HorpoMap.

  Definition env_1 := (#Star --> #Star) [#] EmptyEnv.
  Definition rule_1_l := ^map [^nil, %0].
  Definition rule_1_r := ^nil.

  Definition env_2 := #Star [#] #Star [#] (#Star --> #Star) [#] EmptyEnv.
  Definition rule_2_l := ^map [^cons [%0, %1], %2].
  Definition rule_2_r := ^cons [%2 @@ %0, ^map [%1, %2]].

  Definition t_1_l : env_1 |- rule_1_l := #Star.

  Proof. infer_tt. Defined.

  Definition t_1_r : env_1 |- rule_1_r := #Star.

  Proof. infer_tt. Defined.

  Definition t_2_l : env_2 |- rule_2_l := #Star.

  Proof. infer_tt. Defined.

  Definition t_2_r : env_2 |- rule_2_r := #Star.

  Proof. infer_tt. Defined.

  Lemma rule_1 : buildT t_1_l >> buildT t_1_r.

  Proof.
    constructor; try_solve.
    apply AlgFunApp; try_solve. compute. trivial.
    intros. destruct H as [M'eq | [M'eq | false]]; try_solve.
    rewrite <- M'eq. apply AlgFunApp; try_solve. compute. trivial.
    rewrite <- M'eq. apply AlgVar. try_solve.
    apply AlgFunApp; try_solve. compute. trivial.
    apply HSub. compute. trivial.
    exists (@appBodyR (@appBodyL (buildT t_1_l) I) I).
    left. trivial.
    right.
  Qed.

  Lemma rule_2 : buildT t_2_l >> buildT t_2_r.

  Proof.
    assert (t2alg: algebraic (buildT t_2_l)).
    apply AlgFunApp; try_solve. compute. trivial.
    intros. destruct H as [M'eq | [M'eq | false]]; try_solve.
    rewrite <- M'eq. apply AlgFunApp; try_solve. compute. trivial.
    intros. destruct H as [M''eq | [M''eq | false]]; try_solve.
    rewrite <- M''eq. apply AlgVar; try_solve. 
    rewrite <- M''eq. apply AlgVar; try_solve.
    rewrite <- M'eq. apply AlgVar; try_solve.

    constructor; try_solve.
    apply AlgFunApp; try_solve. compute. trivial.
    intros. destruct H as [M'eq | [M'eq | false]]; try_solve.
    rewrite <- M'eq. apply AlgApp; try_solve. 
    intros. destruct H as [M''eq | [M''eq | false]]; try_solve.
    rewrite <- M''eq. apply AlgVar; try_solve.
    rewrite <- M''eq. apply AlgVar; try_solve.
    rewrite <- M'eq. apply AlgFunApp; try_solve. compute. trivial.
    intros. destruct H as [M''eq | [M''eq | false]]; try_solve.
    rewrite <- M''eq. apply AlgVar; try_solve.
    rewrite <- M''eq. apply AlgVar; try_solve.
     (* map(cons(x, l), F) > cons(@(F, x), map(l, F)) *)
    apply HFun with map cons; try_solve.
    compute. apply HArgsConsEqT.
     (*   map(cons(x, l), F) > @(F, x) *)
    constructor; try_solve.
    apply AlgApp; try_solve. 
    intros. destruct H as [M'eq | [M'eq | false]]; try_solve.
    rewrite <- M'eq. apply AlgVar; try_solve.
    rewrite <- M'eq. apply AlgVar; try_solve.
    match goal with
    | |- _ >-> buildT (TApp ?X ?Y) => 
      set (Vx := buildT X); set (Vy := buildT Y)
    end.
    apply HAppFlat with (Vx :: Vy :: List.nil); try_solve.
    compute. trivial.
    apply HArgsConsNotEqT.
     (*    map(cons(x, l), F) >= F *)
    exists (@appBodyR (buildT t_2_l) I). 
    apply appArg_right with I. trivial. right.   
    apply HArgsConsNotEqT.
     (*    map(cons(x, l), F) >= x *)
    exists (@appBodyR (@appBodyL (buildT t_2_l) I) I).
    left. trivial. left.
     (*      cons(x, l) > x *)
    constructor; try_solve.
    apply AlgFunApp; try_solve. compute. trivial.
    intros. destruct H as [M'eq | [M'eq | false]]; try_solve.
    rewrite <- M'eq. apply AlgVar; try_solve.
    rewrite <- M'eq. apply AlgVar; try_solve.
    apply AlgVar. try_solve.
    apply HSub. compute. trivial.
    eexists (buildT (@TVar env_2 0 #(Star) _)).
    compute. left. trivial.
    constructor 2.     
    apply HArgsNil.
     (*   map(cons(x, l), F) > map(l, F) *)
    apply HArgsConsEqT.
    constructor; try_solve.
    apply AlgFunApp; try_solve. compute. trivial.
    intros. destruct H as [M'eq | [M'eq | false]]; try_solve.
    rewrite <- M'eq. apply AlgVar; try_solve.
    rewrite <- M'eq. apply AlgVar; try_solve.
    match goal with
    | |- ?L >-> ?R => set (TL := L); set (TR := R)
    end.
     (*     cons(x, l) > l *)
    assert (@appBodyR (@appBodyL TL I) I >> @appBodyR (@appBodyL TR I) I).
    constructor; try_solve.
    apply AlgFunApp; try_solve. compute. trivial.
    intros. destruct H as [M'eq | [M'eq | false]]; try_solve.
    rewrite <- M'eq. apply AlgVar; try_solve.
    rewrite <- M'eq. apply AlgVar; try_solve.
    apply AlgVar; try_solve.
    apply HSub. compute. trivial.
    match goal with
    | |- exists2 _, isArg _ ?T & _ => exists (@appBodyR T I)
    end.
    right. left. trivial.
    right.
    apply HMul with map; try_solve.
    constructor.
    set (w := pair_mOrd_fromList). unfold MSet.list2multiset in w. apply w.
    apply horpo_eq_compat'.
    left. hyp.
    right. compute. trivial.
    left. hyp.
    apply HArgsNil.
  Qed.

End HorpoMap.
