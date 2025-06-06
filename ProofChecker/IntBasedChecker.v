(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2009-03-25

  A module with results for solvers using interpretations.
*)

From Stdlib Require Import Program.
From CoLoR Require Import LogicUtil OptUtil ATrs NaryFunction
  AInterpretation Proof ListUtil.

Set Implicit Arguments.

Section IntBasedSolver.

Variable Sig : Signature.

Variable rawSymInt : Type.

Definition rawTrsInt := trsInt Sig rawSymInt.

Variable arSymInt : nat -> Set.

Variable defaultInt : forall n, arSymInt n.

Definition funInt (f : Sig) := arSymInt (arity f).
Definition symInt := { f : Sig & funInt f }.

Definition defaultIntForSymbol f := @defaultInt (@arity Sig f).

Definition buildSymInt f (fi : funInt f) : symInt := existT fi.

Variable checkInt : Sig -> rawSymInt -> option symInt.

Fixpoint processInt (ri : rawTrsInt) : option (list symInt) :=
  match ri with
  | nil => Some nil
  | cons i is =>
      match checkInt (fst i) (snd i) with
      | None => None
      | Some fi => 
          match processInt is with
          | None => None
          | Some fis => Some (fi :: fis)
          end
      end
  end.

Definition buildInt (i : list symInt) : forall f, funInt f :=
  fun f => lookup_dep (el := f) (@eq_symb_dec Sig) defaultIntForSymbol i.

Variable P : symInt -> Prop.
Variable check_P : forall (i : symInt), option (P i).
Variable default_P : forall f, P (buildSymInt (defaultIntForSymbol f)).

Program Fixpoint checkProp (i : list symInt) : 
  option (forall f, P (buildSymInt (buildInt i f))) :=
  match lforall_opt P check_P i with
  | None => None
  | Some _ => Some _
  end.

Next Obligation.
  apply (lookup_dep_prop (P := fun _ fi => P (buildSymInt fi))); intros.
  destruct_call lforall_opt; try discr.
  ded (lforall_in l H). decomp H0. destruct x. hyp.
  apply default_P.
Qed.

End IntBasedSolver.
