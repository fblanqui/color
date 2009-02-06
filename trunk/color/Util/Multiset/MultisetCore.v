(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2004-09-06

This file provides a specification of finite multiset data-type along
with specification of operations on multisets.
*)

Set Implicit Arguments.

Require Import RelExtras.
Require Import Omega.
Require Import Min.

Module Type MultisetCore.

  Declare Module Sid: Eqset_dec.
  Export Sid.  

  Open Scope sets_scope.

Section Operations.  

  Parameter Multiset : Type.

  Parameter mult : A -> Multiset -> nat.

  Parameter meq : Multiset -> Multiset -> Prop.

  Parameter empty : Multiset.

  Parameter singleton : A -> Multiset.

  Parameter union : Multiset -> Multiset -> Multiset.

  Parameter intersection : Multiset -> Multiset -> Multiset.

  Parameter diff : Multiset -> Multiset -> Multiset.

End Operations.

  Notation "X =mul= Y" := (meq X Y) (at level 70) : msets_scope.
  Notation "X <>mul Y" := (~meq X Y) (at level 50) : msets_scope.
  Notation "{{ x }}" := (singleton x) (at level 5) : msets_scope.
  Notation "X + Y" := (union X Y) : msets_scope.
  Notation "X - Y" := (diff X Y) : msets_scope.
  Notation "X # Y" := (intersection X Y) (at level 50, left associativity) : msets_scope.
  Notation "x / M" := (mult x M) : msets_scope.

  Delimit Scope msets_scope with msets.
  Open Scope msets_scope.
  Bind Scope msets_scope with Multiset.

Section Specification.

  Variables M N P : Multiset.
  Variables x y z : A.
  Variable n : nat.

  Open Scope msets_scope.

  Parameter mult_eqA_compat: x =A= y -> x/M = y/M.

  Parameter meq_multeq: M =mul= N -> (forall x, x/M = x/N).

  Parameter multeq_meq: (forall x, x/M = x/N) -> M =mul= N.

  Parameter empty_mult: x/empty = 0.

  Parameter union_mult: x/(M+N) = (x/M + x/N)%nat.

  Parameter diff_mult: x/(M-N) = (x/M - x/N)%nat.

  Parameter intersection_mult: x/(M#N) = Min.min (x/M) (x/N).

  Parameter singleton_mult_in: x =A= y -> x/{{y}} = 1.

  Parameter singleton_mult_notin: ~x =A= y -> x/{{y}} = 0.

  Parameter mset_ind_type: forall P : Multiset -> Type,
    P empty -> (forall M a, P M -> P (M + {{a}})) -> forall M, P M.

End Specification.

  Hint Unfold meq 
	      empty
              singleton
              mult
              union
              diff : multisets.

  Hint Resolve mult_eqA_compat 
               meq_multeq
               multeq_meq
               empty_mult
               union_mult
               diff_mult
               intersection_mult
               singleton_mult_in
               singleton_mult_notin : multisets.
  Hint Rewrite empty_mult
               union_mult
	       diff_mult
	       intersection_mult using trivial : multisets.

End MultisetCore.

Section Multiset_IntersectionAsDifference.

  Variable A : Type.
  Variable Multiset : Type.
  Variable meq : Multiset -> Multiset -> Prop.
  Variable mult : A -> Multiset -> nat.
  Variable diff : Multiset -> Multiset -> Multiset.
  Variable diff_mult : forall M N x, mult x (diff M N) = mult x M - mult x N.

  Definition inter_as_diff x y := diff x (diff x y).

  Lemma inter_as_diff_ok : forall M N x,
    mult x (inter_as_diff M N) = Min.min (mult x M) (mult x N).

  Proof.
    intros M N x.
    unfold inter_as_diff.
    repeat rewrite diff_mult.
    set (m := mult x M) in *.
    set (n := mult x N) in *.
    case (Compare_dec.le_lt_dec n m); intro n_m.
    rewrite Min.min_r; [omega | trivial].
    rewrite Min.min_l; [omega | auto with arith].
  Qed.

End Multiset_IntersectionAsDifference.
