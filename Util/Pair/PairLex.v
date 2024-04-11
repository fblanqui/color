(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Lexicographic order on a product and some results
concerning it are introduced in this file.
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil RelUtil RelExtras.
From Coq Require Import Setoid Morphisms Basics.
From Coq Require Notations Relation_Operators.

Section LexPair.

  Variables (L : Type) (R : Type)
            (eqL : relation L) (eqL_Equivalence : Equivalence eqL).

  Existing Instance eqL_Equivalence.

  Hint Extern 0 (eqL _ _) => simple apply (Seq_refl  L eqL eqL_Equivalence) : sets.
  Hint Extern 3 (eqL _ _) => simple eapply (Seq_trans L eqL eqL_Equivalence) : sets.
  Hint Extern 1 (eqL _ _) => simple apply (Seq_sym   L eqL eqL_Equivalence) : sets.

  Variables (eqR : relation R) (eqR_Equivalence : Equivalence eqR).

  Existing Instance eqR_Equivalence.

  Hint Extern 0 (eqR _ _) => simple apply (Seq_refl  R eqR eqR_Equivalence) : sets.
  Hint Extern 3 (eqR _ _) => simple eapply (Seq_trans R eqR eqR_Equivalence) : sets.
  Hint Extern 1 (eqR _ _) => simple apply (Seq_sym   R eqR eqR_Equivalence) : sets.
 
  Variable gtL : relation L.

  Definition ltL := transp gtL.

  Variable gtL_eqL_compat : Proper (eqL ==> eqL ==> impl) gtL.

  Existing Instance gtL_eqL_compat.

  Definition AccL := Acc ltL.

(*REMOVE?*)
  Instance gtL_morph : Proper (eqL ==> eqL ==> iff) gtL.

  Proof. intros a b ab c d cd. split; apply gtL_eqL_compat; hyp. Qed.

  Variable gtR : relation R.

  Definition ltR := transp gtR.

  Variable gtR_eqR_compat: Proper (eqR ==> eqR ==> impl) gtR.

  Existing Instance gtR_eqR_compat.

  Definition AccR := Acc ltR.

(*REMOVE?*)
  Instance gtR_morph : Proper (eqR ==> eqR ==> iff) gtR.

  Proof. intros a b ab c d cd. split; apply gtR_eqR_compat; hyp. Qed.

  Definition pair := (L * R)%type.

  Definition eqPair (x y : pair) := eqL (fst x) (fst y) /\ eqR (snd x) (snd y).

  (* --- Definition of an order *)
  Reserved Notation "a >lex b" (at level 40).

  Inductive LexProd_Gt : relation pair :=
  | GtL: forall a a' b b', gtL a a' ->             (a, b) >lex (a', b')
  | GtR: forall a a' b b', eqL a a' -> gtR b b' -> (a, b) >lex (a', b')
    where "a >lex b" := (LexProd_Gt a b).

  Definition LexProd_Lt := transp LexProd_Gt.

  Notation "a <lex b" := (LexProd_Lt a b) (at level 40).

  Definition Acc_LexProd := Acc LexProd_Lt.

  Hint Unfold eqPair : sets.

  (* --- Extension of setoids on components to setoid on pair *)
  Instance eqPair_Equivalence : Equivalence eqPair.

  Proof.
    constructor.
    auto with sets.
    intros x y xy; inversion xy; auto with sets.
    intros x y z xy yz; inversion xy; inversion yz; eauto with sets.
  Qed.

  Instance LexProd_Gt_morph_equiv :
    Proper (eqPair ==> eqPair ==> iff) LexProd_Gt.

  Proof.
    intros p p' pp' q q' qq'. split; intro p_q;
    destruct p; destruct q; destruct p'; destruct q'; destruct pp';
      destruct qq';
    simpl in *; inversion p_q.
    constructor 1; rewrite <- H, <- H1; trivial.
    constructor 2. rewrite <- H, <- H1; trivial.
    rewrite <- H0, <- H2; trivial.
    constructor 1; rewrite H, H1; trivial.
    constructor 2. rewrite H, H1; trivial.
    rewrite H0, H2; trivial.
  Qed.

  Lemma LexProd_Gt_morph : forall x1 x2 : pair, eqPair x1 x2 ->
    forall x3 x4 : pair, eqPair x3 x4 -> x1 >lex x3 -> x2 >lex x4.

  Proof. intros. apply (proj1 (LexProd_Gt_morph_equiv H H0)). hyp. Qed.

  Instance LexProd_Lt_morph : Proper (eqPair ==> eqPair ==> iff) LexProd_Lt.

  Proof.
    unfold LexProd_Lt, transp. intros p p' pp' q q' qq'. split; intro p_q.
    rewrite <- pp', <- qq'; trivial.
    rewrite pp', qq'; trivial.
  Qed.

  Instance Acc_LexProd_morph : Proper (eqPair ==> iff) Acc_LexProd.

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

    Variable gtL_so: strict_order gtL.

    Hint Extern 0 => exact (sord_trans gtL_so) : sets.
    Hint Extern 0 => simple apply (sord_irrefl gtL_so) : sets.
    Hint Extern 3 False => simple eapply (so_not_symmetric gtL_so) : sets.
    Hint Extern 1 => simple apply (so_strict gtL_so gtL_eqL_compat eqL_Equivalence) : sets.

    Variable gtR_so: strict_order gtR.

    Hint Extern 0 => exact (sord_trans gtR_so) : sets.
    Hint Extern 0 => simple apply (sord_irrefl gtR_so) : sets.
    Hint Extern 3 False => simple eapply (so_not_symmetric gtR_so) : sets.
    Hint Extern 1 => simple apply (so_strict gtR_so gtR_eqR_compat eqR_Equivalence) : sets.

    Lemma lexprod_irreflex  : forall a, a >lex a -> False.

    Proof.
      intros a gt_aa; inversion gt_aa.
      absurd (gtL a0 a0); auto with sets.
      absurd (gtR b b); auto with sets.
    Qed.

    Lemma lexprod_trans : forall a b c, a >lex b -> b >lex c -> a >lex c.

    Proof.
      intros a b c ab bc;
        inversion ab as [ la la' lb lb' gt_la lL lR 
                        | la la' lb lb' eq_la gt_lb lL lR ];
        inversion bc as [ ra ra' rb rb' gt_ra rL rR 
                        | ra ra' rb rb' eq_ra gt_rb rL rR ];
        assert (eq1: la' = ra); try solve [congruence];
        assert (eq2: lb' = rb); try solve [congruence].
      (* case 1 *)
      constructor 1; apply (sord_trans gtL_so la la' ra'); 
        solve [trivial | rewrite eq1; trivial].
      (* case 2 *)
      constructor 1. rewrite <- eq_ra, <- eq1. hyp.
       (* case 3 *)
      constructor 1. rewrite eq_la, eq1. hyp.
       (* case 4 *)
      constructor 2. rewrite eq_la, <- eq_ra, eq1.
      auto with sets.
      apply (sord_trans gtR_so lb lb' rb'); 
        [ trivial 
        | rewrite eq2; trivial ].
    Qed.

    Lemma lexprod_so : strict_order LexProd_Gt.

    Proof.
      exact (Build_strict_order lexprod_trans lexprod_irreflex).
    Qed.

  End LexProd_StrictOrder.

(* ================================================================= *)
(** Proof of the fact that lexicographic order is well-founded
  (if so are the underlying orders) *)
(* ================================================================= *)

  Section LexProd_WellFounded.

    Variables (wf_ltL : well_founded ltL) (wf_ltR : well_founded ltR).

    Lemma lexprod_wf : well_founded LexProd_Lt.

    Proof.
      unfold well_founded; intro x.
      destruct x as [a b]; gen b.
      apply well_founded_ind with 
        (R := ltL) (P := fun A => forall B, Acc_LexProd (A, B)); trivial.
      intros l wf_l.
      apply well_founded_ind with 
      (R := ltR) (P := fun B => Acc_LexProd (l, B)); trivial.
      intros r wf_r.
      constructor; intros p p_lt; inversion p_lt.
      apply wf_l; auto with sets.
      fold Acc_LexProd.
      (*COQ: following does not work: setoid_replace (a', b') with (l, b'). *)
      cut (eqPair (a',b') (l,b')).
      intro. apply (proj2 (Acc_LexProd_morph H4)). apply wf_r. hyp.
      auto with sets.
    Qed.

  End LexProd_WellFounded.

End LexPair.

Module LexicographicOrder (Import A_ord B_ord : Ord).

  Module Import A_ext := OrdLemmas A_ord.
  Module Import B_ext := OrdLemmas B_ord.
 
(* --- Some shortcuts for convenience *)
  Notation L := A_ord.S.A.
  Notation R := B_ord.S.A.
  Notation eqL := A_ord.S.eqA.
  Notation eqR := B_ord.S.eqA.
  Notation gtL := A_ord.gtA.
  Notation gtR := B_ord.gtA.
  Notation ltL := A_ext.ltA.
  Notation ltR := B_ext.ltA.

  Definition pair := pair L R.

  Definition eqPair (x y : pair) := eqPair eqL eqR x y.

  Section Eq_dec.

    Variables (eqA_dec : forall x y : L, {eqL x y} + {~eqL x y})
              (eqB_dec : forall x y : R, {eqR x y} + {~eqR x y}).

    Lemma eqPair_dec : forall x y : pair, {eqPair x y} + {~eqPair x y}.
  
    Proof.
      intros.
      destruct (eqA_dec (fst x) (fst y)).
      destruct (eqB_dec (snd x) (snd y)).
      left. split; trivial.
      right. intro. destruct H. contr.
      right. intro. destruct H. contr.
    Defined.

  End Eq_dec.

  Definition LexProd_Gt x y := LexProd_Gt eqL gtL gtR x y.

  Notation "a >lex b" := (LexProd_Gt a b) (at level 40).

  Definition LexProd_Lt := transp LexProd_Gt.

  Notation "a <lex b" := (LexProd_Lt a b) (at level 40).

  Definition Acc_LexProd := Acc LexProd_Lt.

(* --- Extension of setoids on components to setoid on pair *)
  #[global] Hint Unfold eqPair : sets.

  Global Instance eqPair_Equivalence : Equivalence eqPair := 
    eqPair_Equivalence A_ord.S.eqA_Equivalence B_ord.S.eqA_Equivalence.

  #[global] Hint Resolve A_ord.S.eqA_Equivalence B_ord.S.eqA_Equivalence : sets.

  Global Instance LexProd_Gt_morph : Proper (eqPair ==> eqPair ==> iff) LexProd_Gt.

  Proof.
    intros p p' pp' q q' qq'. split.
    intro pq. eapply LexProd_Gt_morph with (eqR := eqR); eauto with sets.
    cut (eqPair p' p). intro. cut (eqPair q' q). intro.
    intro p'q'. eapply LexProd_Gt_morph with (eqR := eqR); eauto with sets.
    hyp. hyp.
  Qed.

  Global Instance LexProd_Lt_morph : Proper (eqPair ==> eqPair ==> iff) LexProd_Lt.

  Proof.
    unfold LexProd_Lt; unfold transp.
    intros p p' pp' q q' qq'. split; intro p_q.
    rewrite <- pp', <- qq'; trivial.
    rewrite pp', qq'; trivial.
  Qed.

  Global Instance Acc_LexProd_morph : Proper (eqPair ==> iff) Acc_LexProd.

  Proof.
    intros p q pq.
    compute; intros. set (w := Acc_LexProd_morph); compute in w.
    eapply w; eauto with sets.
    apply A_ord.gtA_eqA_compat. apply B_ord.gtA_eqA_compat.
  Qed.

(* =============================================================== *)
(** Proof of the fact that lexicographic order is a strict order.  *)
(* =============================================================== *)

  Module LexProd_StrictOrder 
         (pA: Poset with Definition A := A_ord.S.A with Module O := A_ord)
         (pB: Poset with Definition A := B_ord.S.A with Module O := B_ord).

    #[global] Hint Resolve pA.gtA_so pB.gtA_so : sets.

    Lemma lexprod_irreflex : forall a, a >lex a -> False.

    Proof. intros. exact (lexprod_irreflex pA.gtA_so pB.gtA_so H). Qed.

    Lemma lexprod_trans : forall a b c, a >lex b -> b >lex c -> a >lex c.

    Proof.
      unfold LexProd_Gt; intros. eapply lexprod_trans; eauto with sets.
    Qed.

    Lemma lexprod_so : strict_order LexProd_Gt.

    Proof. exact (Build_strict_order lexprod_trans lexprod_irreflex). Qed.

  End LexProd_StrictOrder.

(* ================================================================= *)
(**     Proof of the fact that lexicographic order is well-founded
  (if so are the underlaying orders) *)
(* ================================================================= *)

  Section LexProd_WellFounded.

    Variables (wf_ltL : well_founded ltL) (wf_ltR : well_founded ltR).

    Lemma lexprod_wf : well_founded LexProd_Lt.

    Proof. eapply lexprod_wf; eauto with sets. Qed.

  End LexProd_WellFounded.

  Module Rel <: Ord.

    Module S <: Eqset.
      Definition A := pair.
      Definition eqA := eqPair.
      Definition eqA_dec := eqPair_dec.
      Definition eqA_Equivalence := eqPair_Equivalence.
    End S.

    Definition A := pair.

    Definition gtA := LexProd_Gt.

    Global Instance gtA_eqA_compat : Proper (S.eqA ==> S.eqA ==> impl) gtA.

    Proof. intros x x' xx' y y' yy' x_y. rewrite <- xx', <- yy'; trivial. Qed.

  End Rel.

End LexicographicOrder.

Module LexicographicOrderTriple (A_ord B_ord C_ord : Ord).

  Import Notations Relation_Operators.

  Module Import A_ext := OrdLemmas A_ord.
  Module Import B_ext := OrdLemmas B_ord.
  Module Import C_ext := OrdLemmas C_ord.
 
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

  #[global] Hint Unfold fst3 snd3 trd3 : core.

  Module LR_ord := LexicographicOrder A_ord B_ord.
  Module Lex3 := LexicographicOrder LR_ord.Rel C_ord.

  Definition LexProd3_Gt : relation triple := Lex3.LexProd_Gt.
  Definition LexProd3_Lt : relation triple := Lex3.LexProd_Lt.

  Notation "a >lex3 b" := (LexProd3_Gt a b) (at level 40).
  Notation "a <lex3 b" := (LexProd3_Lt a b) (at level 40).

  Section Well_foundedness.

    Variables (WF_L : well_founded ltL) (WF_M : well_founded ltM)
              (WF_R : well_founded ltR).

    Lemma lexprod_wf : well_founded LexProd3_Lt.

    Proof.
      apply Lex3.lexprod_wf; trivial. apply LR_ord.lexprod_wf; trivial.
    Qed.

  End Well_foundedness.

  Lemma LexProd3_Gt_inv a b c a' b' c' : (a, b, c) >lex3 (a', b', c') ->
     gtL a a' \/ (eqL a a' /\ gtM b b') \/ (eqL a a' /\ eqM b b' /\ gtR c c').

  Proof. intro ord. inversion_clear ord; inversion_clear H; auto. Qed.

  Lemma LexProd3_1 a a' b b' c c' : gtL a a' -> (a, b, c) >lex3 (a', b', c').

  Proof. intro a_a'. constructor 1; constructor 1; trivial. Qed.

  Lemma LexProd3_2 a a' b b' c c' :
    eqL a a' -> gtM b b' -> (a, b, c) >lex3 (a', b', c').

  Proof. intros a_a' b_b'. constructor 1; constructor 2; trivial. Qed.

  Lemma LexProd3_3 a a' b b' c c' :
    eqL a a' -> eqM b b' -> gtR c c' -> (a, b, c) >lex3 (a', b', c').

  Proof. intros a_a' b_b' c_c'. constructor 2; trivial. compute; auto. Qed.

  Lemma LexProd3_lt a a' b b' c c' :
    (a, b, c) >lex3 (a', b', c') -> (a', b', c') <lex3 (a, b, c).

  Proof. fo. Qed.

  Lemma LexProd3_lt_1 a a' b b' c c' : gtL a' a -> (a, b, c) <lex3 (a', b', c').

  Proof. intro a_a'. apply LexProd3_lt. apply LexProd3_1; trivial. Qed.

  Lemma LexProd3_lt_2 a a' b b' c c' :
    eqL a' a -> gtM b' b -> (a, b, c) <lex3 (a', b', c').

  Proof. intros a_a' b_b'. apply LexProd3_lt. apply LexProd3_2; trivial. Qed.

  Lemma LexProd3_lt_3 a a' b b' c c' :
    eqL a' a -> eqM b' b -> gtR c' c -> (a, b, c) <lex3 (a', b', c').

  Proof.
    intros a_a' b_b' c_c'. apply LexProd3_lt. apply LexProd3_3; trivial.
  Qed.

End LexicographicOrderTriple.
