(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-19
- Sebastien Hinderer, 2004-02-25

well-founded monotone interpretations
*)

Set Implicit Arguments.

From CoLoR Require Export AInterpretation.
From CoLoR Require Import ATerm RelUtil ASubstitution NaryFunction AContext
     VecUtil SN ARelation LogicUtil.
From Stdlib Require Import Lia PeanoNat.

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).

  Variable I : interpretation Sig.

  Section IR.

    Variable R : relation I.

    Definition IR : relation term :=
      fun t u => forall xint, R (term_int xint t) (term_int xint u).

(***********************************************************************)
(** properties of IR *)

    Lemma IR_reflexive : reflexive R -> reflexive IR.

    Proof.
      intro. unfold reflexive, IR. auto.
    Qed.

    Lemma IR_transitive : transitive R -> transitive IR.

    Proof.
      intro. unfold transitive, IR. intros. exact (H _ _ _ (H0 xint) (H1 xint)).
    Qed.

    Lemma IR_substitution_closed : substitution_closed IR.

    Proof.
      unfold transp, substitution_closed, IR. intros t1 t2 s H xint0.
      rewrite !substitution_lemma. apply (H (beta xint0 s)).
    Qed.

    Definition monotone := forall f, Vmonotone1 (fint I f) R.

    Lemma IR_context_closed : monotone -> context_closed IR.

    Proof.
      unfold transp, context_closed, IR. intros.
      gen (H0 xint). clear H0. intro. induction c.
      simpl. exact H0.
      simpl fill. simpl.
      do 2 (rewrite Vmap_cast, Vmap_app). simpl. apply H. exact IHc.
    Qed.

    Lemma IR_WF : WF R -> WF IR.

    Proof.
      intro. set (xint := fun x:nat => some_elt I).
      apply (WF_incl (fun t1 t2 => R (term_int xint t1) (term_int xint t2))).
      unfold Basics.flip, inclusion. auto. apply (WF_inverse (term_int xint) H).
    Qed.

    Lemma IR_reduction_ordering : monotone -> WF R -> reduction_ordering IR.

    Proof.
      split. apply IR_WF. exact H0. split. apply IR_substitution_closed.
      apply IR_context_closed. exact H.
    Qed.

(***********************************************************************)
(** equivalent definition *)

    Definition IR' : relation term := fun t u =>
      let n := 1 + max (maxvar t) (maxvar u) in
        forall v : vector I n,
          let xint := val_of_vec I v in
            R (term_int xint t) (term_int xint u).

    Lemma IR_incl_IR' : IR << IR'.

    Proof.
      unfold inclusion, IR, IR'. intros. apply H.
    Qed.

    Lemma IR'_incl_IR : IR' << IR.

    Proof.
      unfold inclusion, IR, IR'. intros. set (m := max (maxvar x) (maxvar y)).
      assert (maxvar x <= m). unfold m. apply Nat.le_max_l.
      assert (maxvar y <= m). unfold m. apply Nat.le_max_r.
      assert (term_int xint x = term_int (fval xint (1+m)) x).
      apply term_int_eq_fval_lt. lia. rewrite H2.
      assert (term_int xint y = term_int (fval xint (1+m)) y).
      apply term_int_eq_fval_lt. lia. rewrite H3.
      unfold fval. apply H.
    Qed.

    Lemma IR_eq_IR' : IR == IR'.

    Proof.
      split. exact IR_incl_IR'. exact IR'_incl_IR.
    Qed.

  End IR.

(***********************************************************************)
(** monotony wrt R *)

  Section inclusion.

    Variables R R' : relation I.

    Lemma IR_inclusion : R << R' -> IR R << IR R'.

    Proof.
      intro. unfold inclusion, IR. intros. apply H. apply H0.
    Qed.

  End inclusion.

End S.
