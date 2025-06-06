(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Solange Coupet-Grimal and William Delobel, 2006-01-09

Various properties of preorders
*)

From CoLoR Require Import LogicUtil.
From Stdlib Require Import Relations.

Section PreOrderFacts.
  Variable A : Type.
  Variable leA : relation A.

  Definition eqA : relation A := fun (f g : A) => leA f g /\ leA g f.
  Definition ltA : (relation A) := fun (f g : A) => leA f g /\ ~ eqA f g.

  Variable leA_preorder : preorder A leA.
  
  Lemma eqA_equivalence : equivalence A eqA.
  Proof.
    inversion leA_preorder.
    split.
    (* reflexive : *)
    intro a; split; apply preord_refl.
    (* transitive : *)
    intros a b c H1 H2.
    elim H1; clear H1; intros a_le_g b_le_a.
    elim H2; clear H2; intros b_le_c c_le_b.
    split.
    apply preord_trans with b; hyp.
    apply preord_trans with b; hyp.
    (* symmetric : *)
    intros a b H.
    elim H; split; hyp.
  Qed.
    
  Lemma ltA_antisym : forall (a b : A), ltA a b -> ltA b a -> False.
  Proof.
    intros a b H1 H2.
    elim H1; clear H1; intros a_le_b b_neq_a.
    elim H2; clear H2; intros b_le_a a_neq_b.
    apply a_neq_b; split; hyp.
  Qed.
    
  Lemma ltA_trans : transitive A ltA.
  Proof.
    inversion leA_preorder.
    intros a b c H1 H2.
    elim H1; clear H1; intros a_le_b a_neq_b.
    elim H2; clear H2; intros b_le_c b_neq_c.
    split.
    apply preord_trans with b; hyp.
    intro H.
    elim H; clear H; intros a_le_c c_le_a.
    apply a_neq_b; split.
    hyp.
    apply preord_trans with c; hyp.
  Qed.

  Lemma leA_dec_to_eqA_dec : (forall (a b : A), leA a b \/ ~ leA a b) ->
    forall (a b : A), eqA a b \/ ~ eqA a b.
  Proof.
    intros leA_dec a b; elim (leA_dec a b); intro case_a_le_b.
    elim (leA_dec b a); intro case_b_le_a; [left | right].
    split; trivial.
    intro H; elim H; clear H; intros H1 H2.
    apply case_b_le_a; trivial.
    right; intro H; apply case_a_le_b.
    elim H; trivial.
  Qed.

  Lemma ltA_eqA_compat_r : forall (a b b' :A), eqA b b' -> ltA a b -> ltA a b'.
  Proof.
    inversion leA_preorder.
    intros a b b' b_eq a_lt_b.
    elim a_lt_b; clear a_lt_b; intros a_le_b a_neq_b.
    split.
    elim b_eq; clear b_eq; intros b_le_b' b'_le_b.
    apply preord_trans with b; hyp.
    elim (eqA_equivalence); intros eqA_refl eqA_trans eqA_sym.
    intro; apply a_neq_b; apply eqA_trans with b'; trivial.
    elim b_eq; split; trivial.
  Qed.

  Lemma ltA_eqA_compat_l : forall (a b b' :A), eqA b b' -> ltA b a -> ltA b' a. 
  Proof.
    inversion leA_preorder.
    intros a b b' b_eq b_lt_a.
    elim b_lt_a; clear b_lt_a; intros b_le_a b_neq_a.
    split.
    elim b_eq; clear b_eq; intros b_le_b' b'_le_b.
    apply preord_trans with b; hyp.
    elim (eqA_equivalence); intros eqA_refl eqA_trans eqA_sym.
    intro; apply b_neq_a; apply eqA_trans with b'; trivial.
  Qed.

  Section Decidability.

    Variable leA_dec : forall a b, {leA a b} + {~leA a b}.

    Lemma eqA_dec : forall a b, {eqA a b} + {~eqA a b}.

    Proof.
      intros. unfold eqA.
      destruct (leA_dec a b); intuition.
      destruct (leA_dec b a); intuition.
    Defined.

    Lemma ltA_dec : forall a b, {ltA a b} + {~ltA a b}.

    Proof.
      intros. unfold ltA.
      destruct (leA_dec a b); intuition.
      destruct (eqA_dec a b); intuition.
    Defined.

  End Decidability.

End PreOrderFacts.  
