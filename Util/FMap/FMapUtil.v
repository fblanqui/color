(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-01-28
- Pierre-Yves Strub, 2009-04-09

Wrapper for Coq's FMaps definition + additional facts
*)

Set Implicit Arguments.

Require Import LogicUtil FMaps FMapAVL FMapFacts RelUtil BoolUtil.

Module Make (X : OrderedType).

  Module Export XMap := FMapAVL.Make X.
  Module Export XMapProps := Properties XMap.
  Module Export XMapFacts := Facts XMap.
  Module Export XMapOrdProps := OrdProperties XMap.

  Instance Equiv_m' A :
    Proper (@inclusion A ==> @inclusion (XMap.t A)) (@Equiv A).

  Proof. firstorder. Qed.

  Instance Equiv_m A :
    Proper (@same_relation A ==> @same_relation (XMap.t A)) (@Equiv A).

  Proof. firstorder. Qed.

  Section morphisms.

    Variables (A : Type) (eq : A->A->Prop).

    Instance Equiv_Refl : Reflexive eq -> Reflexive (Equiv eq).

    Proof.
      intros heq m. unfold Equiv. firstorder. rewrite find_mapsto_iff in H, H0.
      rewrite H in H0. inversion H0. subst e'. refl.
    Qed.

    Instance Equiv_Sym : Symmetric eq -> Symmetric (Equiv eq).

    Proof.
      firstorder.
    Qed.

    Instance Equiv_Trans : Transitive eq -> Transitive (Equiv eq).

    Proof.
      intros h m n p. unfold Equiv, XMap.Equiv. intuition.
      rewrite <- H. rewrite <- H1. hyp.
      rewrite H1. rewrite H. hyp.
      unfold In, Raw.In0 in H1, H.
      assert (exists e, Raw.MapsTo k e m). exists e. hyp.
      rewrite H1 in H5. destruct H5 as [f].
      transitivity f. apply H2 with k; hyp. apply H3 with k; hyp.
    Qed.

    Instance Equiv_Equiv : Equivalence eq -> Equivalence (Equiv eq).

    Instance add_m : Proper (X.eq ==> eq ==> Equiv eq ==> Equiv eq) (@add A).

    Proof. (* by Cedric Auger *)
      intros k1 k2 Hk e1 e2 He m1 m2 Hm.
      split.
       intro k.
       generalize (proj1 Hm k); clear -Hm Hk.
       intros [Hm1 Hm2]; split; intros [a_ Ha_].
        destruct (eq_dec k2 k).
         split with e2.
         now apply add_1.
        destruct Hm1.
         split with a_.
         apply add_3 with k1 e1; auto.
         intro H; destruct n.
         now apply X.eq_trans with k1; auto.
        split with x.
        now apply add_2; auto.
       destruct (eq_dec k1 k).
        split with e1.
        now apply add_1.
       destruct Hm2.
        split with a_.
        apply add_3 with k2 e2; auto.
        intro H; destruct n.
        now apply X.eq_trans with k2; auto.
       split with x.
       now apply add_2; auto.
      intro k.
      destruct (eq_dec k2 k).
       intros e_ e_' H H'.
       revert He.
       generalize (find_1 H').
       rewrite (find_1 (add_1 _ _ e)).
       generalize (find_1 H).
       rewrite (find_1 (add_1 _ _ (X.eq_trans Hk e))).
       clear.
       intro H; inversion_clear H.
       intro H; inversion_clear H.
       now auto.
      intros e_ e_' H H'.
      generalize (add_3 n H').
      cut (not (X.eq k1 k)).
       intro n'; generalize (add_3 n' H).
       exact (proj2 Hm k e_ e_').
      clear -n Hk.
      intro H; destruct n.
      now apply X.eq_trans with k1; auto.
    Qed.

    Lemma find_None : forall k m,
      find k m = None <-> (forall x:A, ~MapsTo k x m).

    Proof.
      intros k m. split.
      intros h x. rewrite find_mapsto_iff. rewrite h. intro. discr.
      intro h. case_eq (find k m). rewrite <- find_mapsto_iff in H.
      ded (h a). contradiction. refl.
    Qed.

    Lemma Equiv_MapsTo : forall m m', Equiv eq m m' -> forall k x,
      MapsTo k x m -> exists x', MapsTo k x' m' /\ eq x x'.

    Proof.
      intros m m' [h1 h2] k x kx. unfold In, Raw.In0 in h1.
      assert (exists e, Raw.MapsTo k e m). exists x. hyp.
      rewrite h1 in H. destruct H as [x']. exists x'. intuition.
      apply h2 with k; hyp.
    Qed.

    Implicit Arguments Equiv_MapsTo [m m' k x].

    Lemma Equiv_find_Some : forall m m', Equiv eq m m' -> forall k x,
      find k m = Some x -> exists x', find k m' = Some x' /\ eq x x'.

    Proof.
      intros m m' mm' k x kx. rewrite <- find_mapsto_iff in kx.
      destruct (Equiv_MapsTo mm' kx) as [x']. exists x'.
      rewrite <- find_mapsto_iff. hyp.
    Qed.

    Implicit Arguments Equiv_find_Some [m m' k x].

    Lemma Equiv_MapsTo' : forall m m', Equiv eq m m' -> forall k x,
      MapsTo k x m' -> exists x', MapsTo k x' m /\ eq x' x.

    Proof.
      intros m m' [h1 h2] k x kx. unfold In, Raw.In0 in h1.
      assert (exists e, Raw.MapsTo k e m'). exists x. hyp.
      rewrite <- h1 in H. destruct H as [x']. exists x'. intuition.
      apply h2 with k; hyp.
    Qed.

    Implicit Arguments Equiv_MapsTo' [m m' k x].

    Lemma Equiv_find_Some' : forall m m', Equiv eq m m' -> forall k x,
      find k m' = Some x -> exists x', find k m = Some x' /\ eq x' x.

    Proof.
      intros m m' mm' k x kx. rewrite <- find_mapsto_iff in kx.
      destruct (Equiv_MapsTo' mm' kx) as [x']. exists x'.
      rewrite <- find_mapsto_iff. hyp.
    Qed.

    Implicit Arguments Equiv_find_Some' [m m' k x].
 
    Lemma Equiv_find_None : forall m m', Equiv eq m m' ->
      forall k, find k m = None <-> find k m' = None.

    Proof.
      intros m m' [h1 h2] k. split; intro hk.
      case_eq (find k m'). 2: refl.
      destruct (Equiv_find_Some' (conj h1 h2) H). destruct H0.
      rewrite hk in H0. discr.
      case_eq (find k m). 2: refl.
      destruct (Equiv_find_Some (conj h1 h2) H). destruct H0.
      rewrite hk in H0. discr.
    Qed.

    Instance find_m : Proper (X.eq ==> Equiv eq ==> eq_opt eq) (@find A).

    Proof.
      intros k k' kk' m m' [h1 h2]. rewrite <- kk'. clear k' kk'.
      unfold eq_opt. case_eq (find k m).
      destruct (Equiv_find_Some (conj h1 h2) H). destruct H0. rewrite H0. hyp.
      rewrite (Equiv_find_None (conj h1 h2) k) in H. rewrite H. auto.
    Qed.

    Instance Empty_m : Proper (Equiv eq ==> iff) (@Empty A).

    Proof.
      intros m m' mm'. unfold Empty, Raw.Proofs.Empty. split; intros h k x kx.
      destruct (Equiv_MapsTo' mm' kx) as [x' [h1 h2]]. firstorder.
      destruct (Equiv_MapsTo mm' kx) as [x' [h1 h2]]. firstorder.
    Qed.

    Instance is_empty_m : Proper (Equiv eq ==> @Logic.eq bool) (@is_empty A).

    Proof.
      intros m m' mm'. apply beq_true. repeat rewrite <- is_empty_iff.
      apply Empty_m. hyp.
    Qed.

    Section fold.

      Variables (eq_Refl : PreOrder eq)
        (B : Type) (eqB : relation B) (eqB_Equiv : Equivalence eqB)
        (f : X.t -> A -> B -> B) (f_m : Proper (X.eq ==> eq ==> eqB ==> eqB) f).

      Instance fold_m : Proper (Equiv eq ==> eqB ==> eqB) (fold f).

      Proof.
        intros m m' mm' b b' bb'; gen bb'; gen b'; gen b; gen mm'; gen m'.
        pattern m; apply map_induction_bis; clear m.
        (* Equal *)
        intros m n mn hm n' nn' b b' bb'.
        assert (Equiv eq m n). apply Equiv_m' with (x:=@Logic.eq A).
        intros x y xy. subst. refl. rewrite <- Equal_Equiv. hyp.
        transitivity (fold f m b).
        symmetry. apply hm. hyp. refl.
        apply hm. transitivity n; hyp. hyp.
        (* Empty *)
        (* Add *)
      Abort.

    End fold.

  End morphisms.

  Implicit Arguments Equiv_find_Some [A eq0 m m' k x].
  Implicit Arguments Equiv_find_Some' [A eq0 m m' k x].

End Make.
