(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2004-09-06

This file provides a specification of finite multiset data-type along
with specification of operations on multisets.
*)

Set Implicit Arguments.

From CoLoR Require RelExtras.
From Stdlib Require Import Relations Psatz.

Declare Scope msets_scope.

Module Type MultisetCore.

  Declare Module Export Sid : RelExtras.Eqset_dec.

  Parameter Multiset : Type.

  Parameter mult : A -> Multiset -> nat.

  Parameter meq : relation Multiset.
  
  Parameter empty : Multiset.

  Parameter singleton : A -> Multiset.

  Parameter union : Multiset -> Multiset -> Multiset.

  Parameter intersection : Multiset -> Multiset -> Multiset.

  Parameter diff : Multiset -> Multiset -> Multiset.

  Notation "X =mul= Y" := (meq X Y) (at level 70) : msets_scope.
  Notation "X <>mul Y" := (~meq X Y) (at level 50) : msets_scope.
  Notation "{{ x }}" := (singleton x) (at level 5) : msets_scope.
  Notation "X + Y" := (union X Y) : msets_scope.
  Notation "X - Y" := (diff X Y) : msets_scope.
  Notation "X # Y" := (intersection X Y) (at level 50, left associativity)
                      : msets_scope.
  Notation "x / M" := (mult x M) : msets_scope.

  Delimit Scope msets_scope with msets.
  Open Scope msets_scope.
  Bind Scope msets_scope with Multiset.

  Section Specification.

    Variables (M N P : Multiset) (x y z : A) (n : nat).

    Parameter mult_eqA_compat: x =A= y -> x/M = y/M.

    Parameter meq_multeq: M =mul= N -> (forall x, x/M = x/N).

    Parameter multeq_meq: (forall x, x/M = x/N) -> M =mul= N.

    Parameter empty_mult: x/empty = 0.

    Parameter union_mult: x/(M+N) = (x/M + x/N)%nat.

    Parameter diff_mult: x/(M-N) = (x/M - x/N)%nat.

    Parameter intersection_mult: x/(M#N) = min (x/M) (x/N).

    Parameter singleton_mult_in: x =A= y -> x/{{y}} = 1.

    Parameter singleton_mult_notin: ~x =A= y -> x/{{y}} = 0.

    Parameter mset_ind_type: forall P : Multiset -> Type,
        P empty -> (forall M a, P M -> P (M + {{a}})) -> forall M, P M.

  End Specification.

  #[global] Hint Resolve mult_eqA_compat 
               meq_multeq
               multeq_meq
               empty_mult
               union_mult
               diff_mult
               intersection_mult
               singleton_mult_in
               singleton_mult_notin : multisets.

  Global Hint Rewrite empty_mult
               union_mult
	       diff_mult
	       intersection_mult using trivial : multisets.

End MultisetCore.

Section Multiset_IntersectionAsDifference.

  Variables
    (A : Type) (Multiset : Type) (meq : relation Multiset)
    (mult : A -> Multiset -> nat)
    (diff : Multiset -> Multiset -> Multiset)
    (diff_mult : forall M N x, mult x (diff M N) = mult x M - mult x N).

  Definition inter_as_diff x y := diff x (diff x y).

  Lemma inter_as_diff_ok : forall M N x,
    mult x (inter_as_diff M N) = Nat.min (mult x M) (mult x N).

  Proof.
    intros M N x. unfold inter_as_diff. rewrite !diff_mult. lia.
  Qed.

End Multiset_IntersectionAsDifference.
