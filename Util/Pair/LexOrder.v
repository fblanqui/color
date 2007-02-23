(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Lexicographic order on a product and some results
concerning it are introduced in this file.
*)

(* $Id: LexOrder.v,v 1.4 2007-02-23 18:03:10 blanqui Exp $ *)

Set Implicit Arguments.

Require Import RelExtras.
Require Import Notations.
Require Import Setoid.

Section LexPair.

  Variable lp_L : Set.
  Variable lp_R : Set.

  Variable lp_eqL : relation lp_L.
  Variable lp_sid_theoryL : Setoid_Theory lp_L lp_eqL.

  Hint Resolve (Seq_refl  lp_L lp_eqL lp_sid_theoryL) : sets.
  Hint Resolve (Seq_trans lp_L lp_eqL lp_sid_theoryL) : sets.
  Hint Resolve (Seq_sym   lp_L lp_eqL lp_sid_theoryL) : sets.

  Variable lp_eqR : relation lp_R.
  Variable lp_sid_theoryR : Setoid_Theory lp_R lp_eqR.

  Hint Resolve (Seq_refl  lp_R lp_eqR lp_sid_theoryR) : sets.
  Hint Resolve (Seq_trans lp_R lp_eqR lp_sid_theoryR) : sets.
  Hint Resolve (Seq_sym   lp_R lp_eqR lp_sid_theoryR) : sets.
 
  Variable lp_gtL : lp_L -> lp_L -> Prop.

  Definition lp_ltL := transp lp_L lp_gtL.

  Variable lp_gtL_eqL_compat: forall (x x' y y': lp_L), 
    lp_eqL x x' -> lp_eqL y y' -> lp_gtL x y -> lp_gtL x' y'.

  Definition lp_AccL := Acc lp_ltL.

  Add Setoid lp_L lp_eqL lp_sid_theoryL as lp_L_Setoid. 

  Add Morphism lp_gtL : lp_gtL_morph.

  Proof.
    split; eauto with sets.
  Qed.

  Variable lp_gtR : lp_R -> lp_R -> Prop.

  Definition lp_ltR := transp lp_R lp_gtR.

  Variable lp_gtR_eqR_compat: forall (x x' y y': lp_R), 
    lp_eqR x x' -> lp_eqR y y' -> lp_gtR x y -> lp_gtR x' y'.

  Definition AccR := Acc lp_ltR.

  Add Setoid lp_R lp_eqR lp_sid_theoryR as lp_R_Setoid. 

  Add Morphism lp_gtR : lp_gtR_morph.

  Proof.
    split; eauto with sets.
  Qed.

  Definition lp_pair := (lp_L * lp_R).

  Definition lp_eqPair (x y: lp_pair) :=
    lp_eqL (fst x) (fst y) /\ lp_eqR (snd x) (snd y).

  (* --- Definition of an order *)
  Reserved Notation "a >lex b" (at level 40).

  Inductive lp_LexProd_Gt : lp_pair -> lp_pair -> Prop :=
  | GtL: forall a a' b b', lp_gtL a a' ->                (a, b) >lex (a', b')
  | GtR: forall a a' b b', lp_eqL a a' -> lp_gtR b b' -> (a, b) >lex (a', b')
    where "a >lex b" := (lp_LexProd_Gt a b).

  Definition lp_LexProd_Lt := transp lp_pair lp_LexProd_Gt.

  Notation "a <lex b" := (lp_LexProd_Lt a b) (at level 40).

  Definition lp_Acc_LexProd := Acc lp_LexProd_Lt.

  Hint Unfold lp_eqPair : sets.

  (* --- Extension of setoids on components to setoid on pair *)
  Lemma lp_sid_theory_pair : Setoid_Theory lp_pair lp_eqPair.

  Proof.
    constructor.
    auto with sets.
    intros x y xy; inversion xy; auto with sets.
    intros x y z xy yz; inversion xy; inversion yz; eauto with sets.
  Qed.

  Add Setoid lp_pair lp_eqPair lp_sid_theory_pair as lp_pair_Setoid.

  Add Morphism lp_LexProd_Gt : lp_LexProdGt_morph_equiv.

  Proof.
    intros p p' pp' q q' qq'. split; intro p_q;
    destruct p; destruct q; destruct p'; destruct q'; destruct pp'; destruct qq';
    simpl in *; inversion p_q.
    constructor 1; rewrite <- H; rewrite <- H1; trivial.
    constructor 2. rewrite <- H; rewrite <- H1; trivial.
    rewrite <- H0; rewrite <- H2; trivial.
    constructor 1; rewrite H; rewrite H1; trivial.
    constructor 2. rewrite H; rewrite H1; trivial.
    rewrite H0; rewrite H2; trivial.
  Qed.

  Lemma lp_LexProdGt_morph : forall x1 x2 : lp_pair, lp_eqPair x1 x2 ->
    forall x3 x4 : lp_pair, lp_eqPair x3 x4 -> x1 >lex x3 -> x2 >lex x4.

  Proof.
    intros. apply (proj1 (lp_LexProdGt_morph_equiv H H0)). assumption.
  Qed.

  Add Morphism lp_LexProd_Lt : lp_LexProdLt_morph.

  Proof.
    unfold lp_LexProd_Lt, transp. intros p p' pp' q q' qq'. split; intro p_q.
    rewrite <- pp'; rewrite <- qq'; trivial.
    rewrite pp'; rewrite qq'; trivial.
  Qed.

  Add Morphism lp_Acc_LexProd : lp_AccLexProd_morph.

  Proof.
    intros p p' p_p'. split.
    intro acc_p. inversion acc_p. constructor. intros q q_p'.
    apply H. rewrite p_p'. trivial.
    intro acc_p'. inversion acc_p'. constructor. intros q q_p.
    apply H. rewrite <- p_p'. trivial.
  Qed.

(* =============================================================== *)
(** Proof of the fact that lexicographic order is a strict order.  *)
(* =============================================================== *)

  Section LexProd_StrictOrder.

  Variable lp_gtL_so: strict_order lp_gtL.

  Hint Resolve (sord_trans lp_gtL_so) : sets.
  Hint Resolve (sord_irrefl lp_gtL_so) : sets.
  Hint Resolve (so_not_symmetric lp_gtL_so) : sets.
  Hint Resolve (so_strict lp_gtL_so lp_gtL_eqL_compat lp_sid_theoryL) : sets.

  Variable lp_gtR_so: strict_order lp_gtR.

  Hint Resolve (sord_trans lp_gtR_so) : sets.
  Hint Resolve (sord_irrefl lp_gtR_so) : sets.
  Hint Resolve (so_not_symmetric lp_gtR_so) : sets.
  Hint Resolve (so_strict lp_gtR_so lp_gtR_eqR_compat lp_sid_theoryR) : sets.

  Lemma lp_lexprod_irreflex  : forall a, a >lex a -> False.

  Proof.
    intros a gt_aa; inversion gt_aa.
    absurd (lp_gtL a0 a0); auto with sets.
    absurd (lp_gtR b b); auto with sets.
  Qed.

  Lemma lp_lexprod_trans : forall a b c, a >lex b -> b >lex c -> a >lex c.

  Proof.
    intros a b c ab bc;
      inversion ab as [ la la' lb lb' gt_la lL lR 
                      | la la' lb lb' eq_la gt_lb lL lR ];
      inversion bc as [ ra ra' rb rb' gt_ra rL rR 
                      | ra ra' rb rb' eq_ra gt_rb rL rR ];
      assert (eq1: la' = ra); try solve [congruence];
      assert (eq2: lb' = rb); try solve [congruence].
     (* case 1 *)
    constructor 1; apply (sord_trans lp_gtL_so la la' ra'); 
      solve [trivial | rewrite eq1; trivial].
     (* case 2 *)
    constructor 1. setoid_rewrite <- eq_ra. setoid_rewrite <- eq1. assumption.
     (* case 3 *)
    constructor 1. setoid_rewrite eq_la. setoid_rewrite eq1. assumption.
     (* case 4 *)
    constructor 2. setoid_rewrite eq_la. setoid_rewrite <- eq_ra. rewrite eq1.
    auto with sets.
    apply (sord_trans lp_gtR_so lb lb' rb'); 
      [ trivial 
      | rewrite eq2; trivial ].
  Qed.

  Lemma lp_lexprod_so : strict_order lp_LexProd_Gt.

  Proof.
    exact (Build_strict_order lp_lexprod_trans lp_lexprod_irreflex).
  Qed.

  End LexProd_StrictOrder.

(* ================================================================= *)
(** Proof of the fact that lexicographic order is well-founded
  (if so are the underlying orders) *)
(* ================================================================= *)

  Section LexProd_WellFounded.

  Variable lp_wf_ltL : well_founded lp_ltL.
  Variable lp_wf_ltR : well_founded lp_ltR.

  Lemma lp_lexprod_wf : well_founded lp_LexProd_Lt.

  Proof.
    unfold well_founded; intro x.
    destruct x as [a b]; generalize b.
    apply well_founded_ind with 
      (R := lp_ltL)
      (P := fun A => forall B, lp_Acc_LexProd (A, B)); 
      trivial.
    intros l wf_l.
    apply well_founded_ind with 
      (R := lp_ltR)
      (P := fun B => lp_Acc_LexProd (l, B)); 
      trivial.
    intros r wf_r.
    constructor; intros p p_lt; inversion p_lt.
    apply wf_l; auto with sets.
    fold lp_Acc_LexProd.
(* #NN#, Coq error!, following does not work: *)
(*    setoid_replace (a', b') with (l, b'). *)
    cut (lp_eqPair (a',b') (l,b')).
    intro. apply (proj2 (lp_AccLexProd_morph H4)). apply wf_r. assumption.
    auto with sets.
  Qed.

  End LexProd_WellFounded.

End LexPair.


Module LexicographicOrder (A_ord B_ord : Ord).

  Module A_ext := OrdLemmas A_ord.
  Import A_ext.

  Module B_ext := OrdLemmas B_ord.
  Import B_ext.
 
(* --- Some shortcuts for convenience *)
  Notation L := A_ord.S.A.
  Notation R := B_ord.S.A.
  Notation eqL := A_ord.S.eqA.
  Notation eqR := B_ord.S.eqA.
  Notation gtL := A_ord.gtA.
  Notation gtR := B_ord.gtA.
  Notation ltL := A_ext.ltA.
  Notation ltR := B_ext.ltA.

  Definition pair := lp_pair L R.

  Definition eqPair (x y: pair) := lp_eqPair eqL eqR x y.

  Definition LexProd_Gt (x y: pair) := lp_LexProd_Gt eqL gtL gtR x y.

  Notation "a >lex b" := (LexProd_Gt a b) (at level 40).

  Definition LexProd_Lt := transp pair LexProd_Gt.

  Notation "a <lex b" := (LexProd_Lt a b) (at level 40).

  Definition Acc_LexProd := Acc LexProd_Lt.

(* --- Extension of setoids on components to setoid on pair *)
  Hint Unfold eqPair : sets.

  Definition sid_theory_pair : Setoid_Theory pair eqPair := 
    lp_sid_theory_pair A_ord.S.sid_theoryA B_ord.S.sid_theoryA.

  Add Setoid pair eqPair sid_theory_pair as pair_Setoid.

  Hint Resolve A_ord.S.sid_theoryA B_ord.S.sid_theoryA : sets.

  Add Morphism LexProd_Gt : LexProdGt_morph.

  Proof.
    intros p p' pp' q q' qq'. split.
    intro pq. unfold LexProd_Gt.
    eapply lp_LexProdGt_morph with (lp_eqR := eqR); eauto with sets.
    cut (eqPair p' p). intro. cut (eqPair q' q). intro.
    intro p'q'. unfold LexProd_Gt.
    eapply lp_LexProdGt_morph with (lp_eqR := eqR); eauto with sets.
    apply Seq_sym; auto with sets. exact sid_theory_pair.
    apply Seq_sym; auto with sets. exact sid_theory_pair.
  Qed.

  Add Morphism LexProd_Lt : LexProdLt_morph.

  Proof.
    unfold LexProd_Lt; unfold transp.
    intros p p' pp' q q' qq'. split; intro p_q.
    rewrite <- pp'; rewrite <- qq'; trivial.
    rewrite pp'; rewrite qq'; trivial.
  Qed.

  Add Morphism Acc_LexProd : AccLexProd_morph.

  Proof.
    compute; intros.
    set (w := lp_AccLexProd_morph); compute in w.
    eapply w; eauto with sets.  
  Qed.

(* =============================================================== *)
(** Proof of the fact that lexicographic order is a strict order.  *)
(* =============================================================== *)

Module LexProd_StrictOrder 
  (pA: Poset with Definition A := A_ord.S.A with Module O := A_ord)
  (pB: Poset with Definition A := B_ord.S.A with Module O := B_ord).

  Hint Resolve pA.gtA_so pB.gtA_so : sets.

  Lemma lexprod_irreflex : forall a, a >lex a -> False.

  Proof.
    intros.
    exact (lp_lexprod_irreflex pA.gtA_so pB.gtA_so H).
  Qed.

  Lemma lexprod_trans : forall a b c, a >lex b -> b >lex c -> a >lex c.

  Proof.
    unfold LexProd_Gt; intros.
    eapply lp_lexprod_trans; eauto with sets.
  Qed.

  Lemma lexprod_so : strict_order LexProd_Gt.

  Proof.
    exact (Build_strict_order lexprod_trans lexprod_irreflex).
  Qed.

End LexProd_StrictOrder.

(* ================================================================= *)
(**     Proof of the fact that lexicographic order is well-founded
  (if so are the underlaying orders) *)
(* ================================================================= *)

Section LexProd_WellFounded.

  Variable wf_ltL : well_founded ltL.
  Variable wf_ltR : well_founded ltR.

  Lemma lexprod_wf : well_founded LexProd_Lt.

  Proof.
    change LexProd_Lt with (lp_LexProd_Lt eqL gtL gtR).
    unfold pair.
    eapply lp_lexprod_wf; eauto with sets.
  Qed.

End LexProd_WellFounded.

Module Rel <: Ord.

  Module S <: Eqset.

    Definition A := pair.
    Definition eqA := eqPair.
    Definition sid_theoryA := sid_theory_pair.

  End S.

  Definition A := pair.

  Definition gtA := LexProd_Gt.

  Lemma gtA_eqA_compat : forall (x x' y y': pair), 
    eqPair x x' -> eqPair y y' -> x >lex  y -> x' >lex y'.

  Proof.
    intros x x' y y' xx' yy' x_y.
    rewrite <- xx'; rewrite <- yy'; trivial.
  Qed.

End Rel.

End LexicographicOrder.

Module LexicographicOrderTriple (A_ord B_ord C_ord : Ord).

  Require Import Notations.
  Require Import Relation_Operators.

  Module A_ext := OrdLemmas A_ord.
  Import A_ext.

  Module B_ext := OrdLemmas B_ord.
  Import B_ext.

  Module C_ext := OrdLemmas C_ord.
  Import C_ext.
 
(* --- Some shortcuts for convenience *)
  Notation L := A_ord.S.A.
  Notation M := B_ord.S.A.
  Notation R := C_ord.S.A.
  Notation eqL := A_ord.S.eqA.
  Notation eqM := B_ord.S.eqA.
  Notation eqR := C_ord.S.eqA.
  Notation gtL := A_ord.gtA.
  Notation gtM := B_ord.gtA.
  Notation gtR := C_ord.gtA.
  Notation ltL := A_ext.ltA.
  Notation ltM := B_ext.ltA.
  Notation ltR := C_ext.ltA.

  Definition triple := (L * M * R).
  Definition fst3 (t : triple) : L := fst (fst t).
  Definition snd3 (t : triple) : M := snd (fst t).
  Definition trd3 (t : triple) : R := snd t.

  Hint Unfold fst3 snd3 trd3.

  Module LR_ord := LexicographicOrder A_ord B_ord.
  Module Lex3 := LexicographicOrder LR_ord.Rel C_ord.

  Definition LexProd3_Gt : triple -> triple -> Prop := Lex3.LexProd_Gt.
  Definition LexProd3_Lt : triple -> triple -> Prop := Lex3.LexProd_Lt.

  Notation "a >lex3 b" := (LexProd3_Gt a b) (at level 40).
  Notation "a <lex3 b" := (LexProd3_Lt a b) (at level 40).

Section Well_foundedness.

   Variable WF_L : well_founded ltL.
   Variable WF_M : well_founded ltM.
   Variable WF_R : well_founded ltR.

   Lemma lexprod_wf : well_founded LexProd3_Lt.

   Proof.
     apply Lex3.lexprod_wf; trivial.
     apply LR_ord.lexprod_wf; trivial.
   Qed.

End Well_foundedness.

  Lemma LexProd3_Gt_inv : forall a b c a' b' c', (a, b, c) >lex3 (a', b', c') ->
     gtL a a' \/ (eqL a a' /\ gtM b b') \/ (eqL a a' /\ eqM b b' /\ gtR c c').

  Proof.
    intros a b c a' b' c' ord.
    inversion_clear ord; inversion_clear H; auto.
  Qed.

  Lemma LexProd3_1 : forall a a' b b' c c',
    gtL a a' -> (a, b, c) >lex3 (a', b', c').

  Proof.
    intros a a' b b' c c' a_a'.
    constructor 1; constructor 1; trivial.
  Qed.

  Lemma LexProd3_2 : forall a a' b b' c c',
    eqL a a' -> gtM b b' -> (a, b, c) >lex3 (a', b', c').

  Proof.
    intros a a' b b' c c' a_a' b_b'.
    constructor 1; constructor 2; trivial.
  Qed.

  Lemma LexProd3_3 : forall a a' b b' c c', eqL a a' -> eqM b b' -> gtR c c' ->
    (a, b, c) >lex3 (a', b', c').

  Proof.
    intros a a' b b' c c' a_a' b_b' c_c'.
    constructor 2; trivial.
    compute; auto.
  Qed.

  Lemma LexProd3_lt : forall a a' b b' c c', (a, b, c) >lex3 (a', b', c') ->
    (a', b', c') <lex3 (a, b, c).

  Proof.
    intros a a' b b' c c' ord.
    unfold LexProd3_Lt, Lex3.LexProd_Lt, transp.
    trivial.
  Qed.

  Lemma LexProd3_lt_1 : forall a a' b b' c c',
    gtL a' a -> (a, b, c) <lex3 (a', b', c').

  Proof.
    intros a a' b b' c c' a_a'.
    apply LexProd3_lt.
    apply LexProd3_1; trivial.
  Qed.

  Lemma LexProd3_lt_2 : forall a a' b b' c c',
    eqL a' a -> gtM b' b -> (a, b, c) <lex3 (a', b', c').

  Proof.
    intros a a' b b' c c' a_a' b_b'.
    apply LexProd3_lt.
    apply LexProd3_2; trivial.
  Qed.

  Lemma LexProd3_lt_3 : forall a a' b b' c c',
    eqL a' a -> eqM b' b -> gtR c' c -> (a, b, c) <lex3 (a', b', c').

  Proof.
    intros a a' b b' c c' a_a' b_b' c_c'.
    apply LexProd3_lt.
    apply LexProd3_3; trivial.
  Qed.

End LexicographicOrderTriple.
