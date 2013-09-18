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

  Arguments empty {elt}.

(***********************************************************************)
(** In the following, we assume given a type [A] and a relation [eq] on [A]. *)

  Section S.

    Variables (A : Type) (eq : relation A).

(***********************************************************************)
(* Properties of [remove]. *)

    Lemma remove_empty : forall x, Equal (remove x empty) (@empty A).

    Proof.
      intros x k. rewrite remove_o, empty_o. destruct (eq_dec x k); refl.
    Qed.

(***********************************************************************)
(** Properties of [Equiv]. *)

    Arguments inclusion {A} R1 R2.

    Global Instance Equiv_m' : Proper (inclusion ==> inclusion) (@Equiv A).

    Proof. fo. Qed.

    Global Instance Equiv_m A :
      Proper (same_relation ==> same_relation) (@Equiv A).

    Proof. fo. Qed.

    Lemma Equal_Equiv : Reflexive eq -> Equal << Equiv eq.

    Proof.
      intros heq m m'. rewrite Equal_Equiv. apply Equiv_m'.
      intros x y xy. subst. refl.
    Qed.

    Global Instance Equiv_Refl : Reflexive eq -> Reflexive (Equiv eq).

    Proof.
      intros heq m. unfold Equiv. fo. rewrite find_mapsto_iff in H, H0.
      rewrite H in H0. inversion H0. subst e'. refl.
    Qed.

    Global Instance Equiv_Sym : Symmetric eq -> Symmetric (Equiv eq).

    Proof. fo. Qed.

    Global Instance Equiv_Trans : Transitive eq -> Transitive (Equiv eq).

    Proof.
      intros h m n p. unfold Equiv, XMap.Equiv. intuition.
      rewrite <- H. rewrite <- H1. hyp.
      rewrite H1. rewrite H. hyp.
      unfold In, Raw.In0 in H1, H.
      assert (exists e, Raw.MapsTo k e m). exists e. hyp.
      rewrite H1 in H5. destruct H5 as [f].
      trans f. apply H2 with k; hyp. apply H3 with k; hyp.
    Qed.

(***********************************************************************)
(** Properties of [transpose_neqkey]. *)

    Global Instance transpose_neqkey_m' : forall B,
      Proper (inclusion ==> Logic.eq ==> impl) (@transpose_neqkey A B).

    Proof.
      intros B R R' RR' f f' ff' h. subst f'. unfold transpose_neqkey.
      intros k k' e e' b n. apply RR'. apply h. hyp.
    Qed.

    Global Instance transpose_neqkey_m : forall B,
      Proper (same_relation ==> Logic.eq ==> iff) (@transpose_neqkey A B).

    Proof.
      intros B R R' [h1 h2] f f' ff'. split; apply transpose_neqkey_m'; auto.
    Qed.

(***********************************************************************)
(** Properties of [add]. *)

    Lemma add_transp : transpose_neqkey Equal (@add A).

    Proof.
      unfold transpose_neqkey. intros k l x y m n. unfold Equal.
      intro k'. rewrite !add_o.
      destruct (eq_dec k k'); destruct (eq_dec l k'); try refl.
      absurd (X.eq k l). hyp. trans k'. hyp. sym. hyp.
    Qed.

    Definition add_add_neq := add_transp.

    Lemma add_add_eq : forall k l, X.eq k l ->
      forall (x y : A) m, Equal (add k x (add l y m)) (add k x m).

    Proof.
      intros k l kl x y m. unfold Equal. intro k'. rewrite !add_o.
      destruct (eq_dec k k'); destruct (eq_dec l k'); try refl.
      absurd (X.eq k k'). hyp. trans l; hyp.
    Qed.

    Lemma add_add : forall k l (x y : A) m,
      Equal (add k x (add l y m))
      (if eq_dec k l then add k x m else add l y (add k x m)).

    Proof.
      intros k l x y m. destruct (eq_dec k l).
      apply add_add_eq; hyp. apply add_add_neq; hyp.
    Qed.

    Lemma add_transp_Equiv :
      Reflexive eq -> transpose_neqkey (Equiv eq) (@add A).

    Proof.
      intro heq. eapply transpose_neqkey_m'. apply Equal_Equiv. intuition.
      refl. apply add_transp.
    Qed.

    Definition add_add_neq_Equiv := add_transp_Equiv.

    Lemma add_add_eq_Equiv : Reflexive eq -> forall k l, X.eq k l ->
      forall x y m, Equiv eq (add k x (add l y m)) (add k x m).

    Proof.
      intros heq k l kl x y m. apply Equal_Equiv.
      intuition. apply add_add_eq. hyp.
    Qed.

    Lemma add_add_Equiv : Reflexive eq -> forall k l x y m,
      Equiv eq (add k x (add l y m))
      (if eq_dec k l then add k x m else add l y (add k x m)).

    Proof.
      intros heq k l x y m. destruct (eq_dec k l).
      apply add_add_eq_Equiv; hyp. apply add_add_neq_Equiv; hyp.
    Qed.

(***********************************************************************)
(** [add] is a morphism wrt Equiv. *)

    Global Instance add_Equiv :
      Proper (X.eq ==> eq ==> Equiv eq ==> Equiv eq) (@add A).

    Proof. (* by Cedric Auger *)
      intros k1 k2 Hk e1 e2 He m1 m2 Hm.
      split.
       intro k.
       gen (proj1 Hm k); clear -Hm Hk.
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
       gen (find_1 H').
       rewrite (find_1 (add_1 _ _ e)).
       gen (find_1 H).
       rewrite (find_1 (add_1 _ _ (X.eq_trans Hk e))).
       clear.
       intro H; inversion_clear H.
       intro H; inversion_clear H.
       now auto.
      intros e_ e_' H H'.
      gen (add_3 n H').
      cut (not (X.eq k1 k)).
       intro n'; gen (add_3 n' H).
       exact (proj2 Hm k e_ e_').
      clear -n Hk.
      intro H; destruct n.
      now apply X.eq_trans with k1; auto.
    Qed.

(***********************************************************************)
(** Properties of [find]. *)

    Lemma find_None : forall k m,
      find k m = None <-> (forall x:A, ~MapsTo k x m).

    Proof.
      intros k m. split.
      intros h x. rewrite find_mapsto_iff. rewrite h. intro. discr.
      intro h. case_eq (find k m); intros.
      rewrite <- find_mapsto_iff in H. ded (h a). contr. refl.
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
      case_eq (find k m'); intros. 2: refl.
      destruct (Equiv_find_Some' (conj h1 h2) H). destruct H0.
      rewrite hk in H0. discr.
      case_eq (find k m); intros. 2: refl.
      destruct (Equiv_find_Some (conj h1 h2) H). destruct H0.
      rewrite hk in H0. discr.
    Qed.

    Global Instance find_m : Proper (X.eq ==> Equiv eq ==> opt_r eq) (@find A).

    Proof.
      intros k k' kk' m m' [h1 h2]. rewrite <- kk'. clear k' kk'.
      case_eq (find k m); intros.
      destruct (Equiv_find_Some (conj h1 h2) H). destruct H0. rewrite H0.
      apply opt_r_Some. hyp.
      rewrite (Equiv_find_None (conj h1 h2) k) in H. rewrite H.
      apply opt_r_None.
    Qed.

(***********************************************************************)
(** Properties of [Empty] and [is_empty]. *)

    Global Instance Empty_Equiv : Proper (Equiv eq ==> iff) (@Empty A).

    Proof.
      intros m m' mm'. unfold Empty, Raw.Proofs.Empty. split; intros h k x kx.
      destruct (Equiv_MapsTo' mm' kx) as [x' [h1 h2]]. fo.
      destruct (Equiv_MapsTo mm' kx) as [x' [h1 h2]]. fo.
    Qed.

    Global Instance is_empty_Equiv :
      Proper (Equiv eq ==> Logic.eq) (@is_empty A).

    Proof.
      intros m m' mm'. apply beq_true. rewrite <- !is_empty_iff.
      apply Empty_Equiv. hyp.
    Qed.

(***********************************************************************)
(** Other properties of [Equiv]. *)

    Lemma Equiv_empty : forall m, Equiv eq empty m <-> Empty m.

    Proof.
      intro m. unfold Equiv, Empty, Raw.Proofs.Empty. intuition.
      assert (In a m). exists e. hyp.
      rewrite <- H0 in H2. rewrite empty_in_iff in H2. hyp.
      rewrite empty_in_iff in H0. contr.
      rewrite empty_in_iff. destruct H0. eapply H. apply H0.
      assert (In k (@empty A)). exists e. hyp.
      rewrite empty_in_iff in H2. contr.
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
(* [fold f] is a morphism wrt [Equiv eq] if [f] is a morphism wrt [eq]
and satisfies some commutation property. *)

    Section fold.

      Variables (heq : PreOrder eq)
        (B : Type) (eqB : relation B) (heqB : Equivalence eqB).

      Global Instance fold_Equiv : forall (f : X.t -> A -> B -> B)
        (f_m : Proper (X.eq ==> eq ==> eqB ==> eqB) f)
        (hf : transpose_neqkey eqB f),
        Proper (Equiv eq ==> eqB ==> eqB) (fold f).

      Proof.
        intros f f_m hf m m' mm' b b' bb'; revert m' mm' b b' bb'.
        pattern m; apply map_induction_bis; clear m.
        (* Equal *)
        intros m n mn hm n' nn' b b' bb'. apply Equal_Equiv in mn.
        2: intuition. trans (fold f m b).
        sym. apply hm. hyp. refl. apply hm. trans n; hyp. hyp.
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

      Lemma fold_Equiv_ext : forall (f : X.t -> A -> B -> B)
        (f_m : Proper (X.eq ==> eq ==> eqB ==> eqB) f)
        (hf : transpose_neqkey eqB f) f',
        (forall k k', X.eq k k' -> forall x x', eq x x' ->
          forall b b', eqB b b' -> eqB (f k x b) (f' k' x' b')) ->
        forall m m', Equiv eq m m' -> forall b b', eqB b b' ->
          eqB (fold f m b) (fold f' m' b').

      Proof.
        intros f f_m hf f' ff' m m' mm' b b' bb'. rewrite !fold_1.
        set (F := fun a (p:key*A) => f (fst p) (snd p) a).
        set (F' := fun a (p:key*A) => f' (fst p) (snd p) a).
        trans (fold_left F (elements m') b').
        unfold F. rewrite <- !fold_1. apply fold_Equiv; auto||refl.
        apply fold_left_m_ext with (eqB:=@eq_key_elt A); try refl.
        intros a a' aa' [k x] [k' x'] e. inversion e. unfold F, F'. simpl in *.
        subst x'. apply ff'; auto||refl.
      Qed.
 
    End fold.

(***********************************************************************)
(* Properties of [In]. *)

    Global Instance In_Equiv' : Proper (X.eq ==> Equiv eq ==> impl) (@In A).

    Proof.
      intros k k' kk' m m' [h1 h2]. rewrite h1. rewrite kk'. unfold impl. auto.
    Qed.

    Global Instance In_Equiv : Reflexive eq ->
      Proper (X.eq ==> Equiv eq ==> iff) (@In A).

    Proof.
      intros heq k k' kk' m m' [h1 h2]. rewrite h1. apply In_m. hyp. refl.
    Qed.

(***********************************************************************)
(* Properties of [for_all]. *)

    Section for_all.

      Variable f : X.t -> A -> bool.

      Definition for_all_aux k x b := f k x && b.

      Global Instance for_all_aux_m : Proper (X.eq ==> eq ==> Logic.eq) f ->
        Proper (X.eq ==> eq ==> Logic.eq ==> Logic.eq) for_all_aux.

      Proof.
        intros fm k k' kk' x x' xx' b b' bb'. subst b'. unfold for_all_aux.
        apply (f_equal (fun c => c && b)). apply fm; hyp.
      Qed.

      Lemma for_all_aux_transp : transpose_neqkey Logic.eq for_all_aux.

      Proof.
        unfold transpose_neqkey. intros k k' x x' b n.
        unfold for_all_aux. bool. rewrite andb_comm with (b1:=f k x). refl.
      Qed.

      Lemma for_all_eq : forall m, for_all f m = fold for_all_aux m true.

      Proof. refl. Qed.

      Lemma for_all_add : Reflexive eq ->
        Proper (X.eq ==> eq ==> Logic.eq) f -> forall k m, ~In k m ->
          forall x, for_all f (add k x m) = f k x && for_all f m.

      Proof.
        intros heq fm k m n x. rewrite for_all_eq. rewrite fold_add; intuition.
        clear - heq fm. intros k k' kk' x x' xx' b b' bb'.
        apply for_all_aux_m; intuition. subst x'. refl.
        apply for_all_aux_transp.
      Qed.

      Global Instance for_all_Equiv : PreOrder eq ->
        Proper (X.eq ==> eq ==> Logic.eq) f ->
        Proper (Equiv eq ==> Logic.eq) (for_all f).

      Proof.
        intros heq fm m m' mm'. rewrite !for_all_eq.
        apply fold_Equiv; intuition. apply for_all_aux_transp.
      Qed.

      Global Instance for_all_m : Reflexive eq ->
        Proper (X.eq ==> eq ==> Logic.eq) f ->
        Proper (Equal ==> Logic.eq) (for_all f).

      Proof.
        intros heq fm m m' mm'. rewrite !for_all_eq.
        apply fold_Equal; intuition. eapply Proper_inclusion_3.
        5: apply for_all_aux_m. refl. intros x y xy. subst y. refl.
        refl. refl. hyp.
      Qed.

    End for_all.

(***********************************************************************)
(* Properties of [filter]. *)

    Section filter.

      Variable f : X.t -> A -> bool.

      Definition filter_aux k x m := if f k x then add k x m else m.

      Global Instance filter_aux_m : PreOrder eq ->
        Proper (X.eq ==> eq ==> Logic.eq) f ->
        Proper (X.eq ==> eq ==> Equiv eq ==> Equiv eq) filter_aux.

      Proof.
        intros heq fm k k' kk' x x' xx' m m' mm'. unfold filter_aux.
        rewrite kk', xx'. destruct (f k' x'). rewrite kk', xx', mm'. refl. hyp.
      Qed.

      Lemma filter_aux_transp : Reflexive eq ->
        transpose_neqkey (Equiv eq) filter_aux.

      Proof.
        unfold transpose_neqkey. intros heq k k' x x' b n. unfold filter_aux.
        destruct (f k x); destruct (f k' x'); try refl.
        apply add_transp_Equiv; hyp.
      Qed.

      Lemma filter_eq : forall m, filter f m = fold filter_aux m empty.

      Proof. refl. Qed.

      (*TODO?

      Lemma filter_add : Reflexive eq ->
        Proper (X.eq ==> eq ==> Logic.eq) f -> forall k m, ~In k m ->
          forall x, filter f (add k x m) = f k x && filter f m.

      Proof.
        intros heq fm k m n x. rewrite filter_eq. rewrite fold_add; intuition.
        clear - heq fm. intros k k' kk' x x' xx' b b' bb'.
        apply filter_aux_m; intuition. subst x'. refl.
        apply filter_aux_transp.
      Qed.

      Global Instance filter_Equiv : PreOrder eq ->
        Proper (X.eq ==> eq ==> Logic.eq) f ->
        Proper (Equiv eq ==> Logic.eq) (filter f).

      Proof.
        intros heq fm m m' mm'. rewrite !filter_eq.
        apply fold_Equiv; intuition. apply filter_aux_transp.
      Qed.

      Global Instance filter_m : Reflexive eq ->
        Proper (X.eq ==> eq ==> Logic.eq) f ->
        Proper (Equal ==> Logic.eq) (filter f).

      Proof.
        intros heq fm m m' mm'. rewrite !filter_eq.
        apply fold_Equal; intuition. eapply Proper_inclusion_3.
        5: apply filter_aux_m. refl. intros x y xy. subst y. refl.
        refl. refl. hyp.
      Qed.*)

    End filter.

  End S.

  Implicit Arguments Equiv_find_Some [A eq0 m m' k x].
  Implicit Arguments Equiv_find_Some' [A eq0 m m' k x].

End Make.
