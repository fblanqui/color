(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2010-01-28
- Pierre-Yves Strub, 2009-04-09

Wrapper for Coq's FMaps definition + additional facts
*)

Set Implicit Arguments.

Require Import LogicUtil FMaps FMapAVL FMapFacts RelUtil BoolUtil ListUtil.

Module Make (X : OrderedType).

  Module Export XMap := FMapAVL.Make X.
  Module Export XMapProps := Properties XMap.
  Module Export XMapFacts := Facts XMap.
  Module Export XMapOrdProps := OrdProperties XMap.

(***********************************************************************)
(** Equiv is a morphism wrt inclusion *)

  Instance Equiv_m' A :
    Proper (@inclusion A ==> @inclusion (XMap.t A)) (@Equiv A).

  Proof. firstorder. Qed.

  Instance Equiv_m A :
    Proper (@same_relation A ==> @same_relation (XMap.t A)) (@Equiv A).

  Proof. firstorder. Qed.

(***********************************************************************)
(** In the following, we assume given a type A equipped with a relation eq *)

  Section morphisms.

    Variables (A : Type) (eq : A->A->Prop).

(***********************************************************************)
(** Equiv preserves reflexivity, symmetry and transitivity *)

    Global Instance Equiv_Refl : Reflexive eq -> Reflexive (Equiv eq).

    Proof.
      intros heq m. unfold Equiv. firstorder. rewrite find_mapsto_iff in H, H0.
      rewrite H in H0. inversion H0. subst e'. refl.
    Qed.

    Global Instance Equiv_Sym : Symmetric eq -> Symmetric (Equiv eq).

    Proof.
      firstorder.
    Qed.

    Global Instance Equiv_Trans : Transitive eq -> Transitive (Equiv eq).

    Proof.
      intros h m n p. unfold Equiv, XMap.Equiv. intuition.
      rewrite <- H. rewrite <- H1. hyp.
      rewrite H1. rewrite H. hyp.
      unfold In, Raw.In0 in H1, H.
      assert (exists e, Raw.MapsTo k e m). exists e. hyp.
      rewrite H1 in H5. destruct H5 as [f].
      transitivity f. apply H2 with k; hyp. apply H3 with k; hyp.
    Qed.

    (*REMOVE: useful?
    Global Instance Equiv_Equiv : Equivalence eq -> Equivalence (Equiv eq).*)

(***********************************************************************)
(** add is a morphism wrt Equiv *)

    Global Instance add_m :
      Proper (X.eq ==> eq ==> Equiv eq ==> Equiv eq) (@add A).

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

(***********************************************************************)
(** Some properties of find *)

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

(***********************************************************************)
(** find is a morphism wrt Equiv *)

    Global Instance find_m : Proper (X.eq ==> Equiv eq ==> eq_opt eq) (@find A).

    Proof.
      intros k k' kk' m m' [h1 h2]. rewrite <- kk'. clear k' kk'.
      unfold eq_opt. case_eq (find k m).
      destruct (Equiv_find_Some (conj h1 h2) H). destruct H0. rewrite H0. hyp.
      rewrite (Equiv_find_None (conj h1 h2) k) in H. rewrite H. auto.
    Qed.

(***********************************************************************)
(** Empty and is_empty are morphisms wrt Equiv *)

    Global Instance Empty_m : Proper (Equiv eq ==> iff) (@Empty A).

    Proof.
      intros m m' mm'. unfold Empty, Raw.Proofs.Empty. split; intros h k x kx.
      destruct (Equiv_MapsTo' mm' kx) as [x' [h1 h2]]. firstorder.
      destruct (Equiv_MapsTo mm' kx) as [x' [h1 h2]]. firstorder.
    Qed.

    Global Instance is_empty_m :
      Proper (Equiv eq ==> @Logic.eq bool) (@is_empty A).

    Proof.
      intros m m' mm'. apply beq_true. repeat rewrite <- is_empty_iff.
      apply Empty_m. hyp.
    Qed.

(***********************************************************************)
(** Properties of Equiv wrt empty and add *)

    Lemma Equiv_empty : forall m, Equiv eq (empty A) m <-> Empty m.

    Proof.
      intro m. unfold Equiv, Empty, Raw.Proofs.Empty. intuition.
      assert (In a m). exists e. hyp.
      rewrite <- H0 in H2. rewrite empty_in_iff in H2. hyp.
      rewrite empty_in_iff in H0. contradiction.
      rewrite empty_in_iff. destruct H0. eapply H. apply H0.
      assert (In k (empty A)). exists e. hyp.
      rewrite empty_in_iff in H2. contradiction.
    Qed.

    Lemma Equiv_add_remove : forall n k x m', ~In k n ->
      Equiv eq (add k x n) m' -> Equiv eq n (remove k m').

    Proof.
      intros n k x m' hk [h1 h2]. split.
      (* In *)
      intro l. rewrite remove_in_iff. intuition. apply hk. rewrite H0. hyp.
      rewrite <- h1. rewrite add_in_iff. auto.
      rewrite <- h1 in H1. rewrite add_in_iff in H1. intuition.
      (* eq *)
      intros l y z ly lz.
      assert (~X.eq k l). intro e. apply hk. exists y.
      change (MapsTo k y n). rewrite (MapsTo_iff _ _ e). hyp.
      apply h2 with l. rewrite add_mapsto_iff. right. intuition.
      rewrite remove_mapsto_iff in lz. intuition.
    Qed.

    Lemma Equiv_add : forall n k x m', ~In k n -> Equiv eq (add k x n) m' ->
      exists x', eq x x' /\ Add k x' (remove k m') m'.

    Proof.
      intros n k x m' hk [h1 h2].
      assert (In k (add k x n)). rewrite add_in_iff. auto.
      rewrite h1 in H. destruct H as [x']. exists x'. split.
      apply h2 with k. rewrite add_mapsto_iff. auto. hyp.
      intro l. rewrite add_o. rewrite remove_o. destruct (eq_dec k l).
      rewrite <- e. rewrite <- find_mapsto_iff. hyp. refl.
    Qed.

(***********************************************************************)
(** weakening of the induction principle by using Equiv instead of Equal *)

    Lemma map_induction_bis_Equiv : Reflexive eq ->
      forall P : XMap.t A -> Type,
      (forall m m', Equiv eq m m' -> P m -> P m') ->
      P (empty A) ->
      (forall k x m, ~In k m -> P m -> P (add k x m)) -> 
      forall m, P m.

    Proof.
      intros. apply map_induction_bis; auto. intros n n' nn' h. eapply X.
      2: apply h. apply Equiv_m' with (x:=@Logic.eq A).
      intros x y xy. subst. refl. rewrite <- Equal_Equiv. hyp.
    Qed.

(***********************************************************************)
(** (inclusion) relation on lists of elements of type (key*A) *)

    Definition le_list l l' := forall k x, InA (@eq_key_elt A) (k,x) l ->
      exists x', eq x x' /\ InA (@eq_key_elt A) (k,x') l'.

(***********************************************************************)
(** le_list preserves reflexivity and transitivity *)

    Global Instance le_list_Refl : Reflexive eq -> Reflexive le_list.

    Proof.
      intros heq l k x h. exists x. intuition.
    Qed.

    Global Instance le_list_Trans : Transitive eq -> Transitive le_list.

    Proof.
      intros heq l m n lm mn k x1 h1. destruct (lm _ _ h1) as [x2 [e h2]].
      destruct (mn _ _ h2) as [x3 [e' h3]]. exists x3. intuition.
      transitivity x2; hyp.
    Qed.

    (*REMOVE: useful?
    Global Instance le_list_PO : PreOrder eq -> PreOrder le_list.*)

(***********************************************************************)
(** (equivalence) relation on lists of elements of type (key*A) *)

    Definition eq_list l l' := le_list l l' /\ le_list l' l.

(***********************************************************************)
(** eq_list preserves reflexivity, transitivity and symmetry *)

    Global Instance eq_list_Reflexive : Reflexive eq -> Reflexive eq_list.

    Proof.
      intros heq l. split; refl.
    Qed.

    Global Instance eq_list_Transitive : Transitive eq -> Transitive eq_list.

    Proof.
      intros heq l m n [lm ml] [mn nm]. split; transitivity m; hyp.
    Qed.

    Global Instance eq_list_Symmetric : Symmetric eq -> Symmetric eq_list.

    Proof.
      intros heq l m. unfold eq_list. tauto.
    Qed.

(***********************************************************************)
(** elements is a morphism wrt le_list and eq_list *)

    Global Instance elements_m' : Proper (Equiv eq ==> le_list) (@elements A).

    Proof.
      intros m m' [h1 h2] k x h. rewrite <- elements_mapsto_iff in h.
      assert (In k m). exists x. hyp. rewrite h1 in H. destruct H as [x'].
      exists x'. split. apply h2 with k; hyp.
      rewrite <- elements_mapsto_iff. hyp.
    Qed.

    Global Instance elements_m : Symmetric eq ->
      Proper (Equiv eq ==> eq_list) (@elements A).

    Proof.
      intros heq m m' mm'. split; apply elements_m'. hyp. symmetry. hyp.
    Qed.

(***********************************************************************)
(* (fold f) is a morphism wrt (Equiv eq) if f is a morphism wrt eq
and satisfies some commutation property *)

    Section fold.

      Variables (heq : PreOrder eq)
        (B : Type) (eqB : relation B) (heqB : Equivalence eqB)
        (f : X.t -> A -> B -> B) (f_m : Proper (X.eq ==> eq ==> eqB ==> eqB) f)
        (hf : transpose_neqkey eqB f).

      Global Instance fold_m : Proper (Equiv eq ==> eqB ==> eqB) (fold f).

      Proof.
        intros m m' mm' b b' bb'; gen bb'; gen b'; gen b; gen mm'; gen m'.
        pattern m; apply map_induction_bis_Equiv; clear m.
        destruct heq. hyp.
        (* Equiv *)
        intros m n mn hm n' nn' b b' bb'. transitivity (fold f m b).
        symmetry. apply hm. hyp. refl.
        apply hm. transitivity n; hyp. hyp.
        (* Empty *)
        intros m hm b b' bb'. rewrite Equiv_empty in hm.
        rewrite fold_Empty; auto. 2: apply empty_1.
        rewrite fold_1. rewrite elements_Empty in hm. rewrite hm. hyp.
        (* Add *)
        intros k x m nxm hm m' xemm' b b' bb'.
        assert (f_m': Proper (X.eq ==> Logic.eq ==> eqB ==> eqB) f).
        intros l l' ll' y y' yy' c c' cc'. subst y'. apply f_m; auto. refl.
        rewrite fold_add; auto. destruct (Equiv_add nxm xemm') as [x' [h1 h2]].
        assert (n: ~In k (remove k m')). apply remove_1. refl.
        rewrite fold_Add with (m2:=m'); auto. 2: apply n. 2: apply h2.
        apply f_m; auto. apply hm; auto.
        eapply Equiv_add_remove. hyp. apply xemm'.
      Qed.
 
    End fold.

  End morphisms.

  Implicit Arguments Equiv_find_Some [A eq0 m m' k x].
  Implicit Arguments Equiv_find_Some' [A eq0 m m' k x].

End Make.
