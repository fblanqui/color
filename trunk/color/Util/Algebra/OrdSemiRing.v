(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2007-04-14

  Semi-ring equipped with two (strict and non-strict) orders.
*)

(** Semi-rings equipped with orders *)

Module Type OrdSemiRingType.

  Declare Module SR : SemiRingType.
  Export SR.

  Parameter gt : relation A.
  Parameter ge : relation A.

  Notation "x > y" := (gt x y).
  Notation "x >= y" := (ge x y).

  Parameter ge_refl : reflexive ge.
  Parameter ge_trans : transitive ge.
  Parameter ge_antisym : antisymmetric ge.

  Parameter ge_dec : rel_dec ge.

  Parameter plus_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m + n >= m' + n'.
  Parameter mult_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m * n >= m' * n'.

  Hint Resolve ge_refl ge_antisym : arith.

End OrdSemiRingType.

Module OrdSemiRing (OSR : OrdSemiRingType).

  Module SR := SemiRing OSR.SR.
  Export SR.
  Export OSR.

End OrdSemiRing.

Module NOrdSemiRingT <: OrdSemiRingType.

  Module SR := NSemiRingT.
  Export SR.

  Definition gt := Peano.gt.
  Definition ge := Peano.ge.

  Lemma ge_refl : reflexive ge.

  Proof.
    intro m. unfold ge. auto with arith.
  Qed.

  Lemma ge_trans : transitive ge.

  Proof.
    intros m n p. unfold ge. intros. 
  Admitted.

  Lemma ge_antisym : antisymmetric ge.

  Proof.
  Admitted.

  Lemma ge_dec : rel_dec ge.

  Proof.
    unfold rel_dec. intros.
    destruct (nat_ge_dec x y); auto.
  Qed.

  Lemma plus_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m + n >= m' + n'.

  Proof.
    intros. unfold Peano.ge.
    apply plus_le_compat; assumption.
  Qed.

  Lemma mult_ge_compat : forall m n m' n',
    m >= m' -> n >= n' -> m * n >= m' * n'.

  Proof.
    intros. unfold Peano.ge.
    apply mult_le_compat; assumption.
  Qed.

End NOrdSemiRingT.

Module NOrdSemiRing := OrdSemiRing NOrdSemiRingT.
