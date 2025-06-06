(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

Modular termination proof through SCC of an over DPGraph
*)

Set Implicit Arguments.

From Stdlib Require Import Permutation Multiset Setoid PermutSetoid.
From CoLoR Require Import SCCTopoOrdering AGraph ATrs RelUtil RelSub BoundNat
     AdjMat LogicUtil NatUtil SCC SCC_dec ListExtras SN VecUtil GDomainBij
     OptUtil Union SortUtil ListNodup ListPermutation.

Section S.

  Variable Sig : Signature.

  Notation rule := (rule Sig). Notation rules := (list rule).

  Variables (S : relation (term Sig)) (R : rules) (hyp : rules_preserve_vars R).

  Notation DPG := (hd_rules_graph S R).
  Notation rule_eq_dec := (@ATrs.eq_rule_dec Sig).
  Notation dim := (length R).

  Variables (ODPG : relation rule) (over_DPG : DPG << ODPG)
            (restriction : is_restricted ODPG R) (R_nodup : nodup R)
            (ODPG_dec : forall x y, {ODPG x y} + {~ODPG x y}).

  Definition hyps := mkSCC_dec_hyps rule_eq_dec restriction R_nodup ODPG_dec.

  Variables (M : matrix dim dim) (HM : M = SCC_mat_effective hyps) .

  Notation empty := (fun _ _ => False).

  Definition proj1_sig2 T P Q (e : @sig2 T P Q) :=
    match e with
    | exist2 _ _ a b c => a
    end.

  Definition s_SCC's := proj1_sig2 (sorted_SCC' hyps HM).

  Notation ODPGquo' := (Rquo' hyps HM).

(***********************************************************************)
(** s_SCC's properties *)

  Lemma s_SCC's_spec_cover i : i < dim -> In i s_SCC's.

  Proof.
    intros. unfold s_SCC's. destruct (sorted_SCC' hyps). unfold proj1_sig2.
    unfold permutation, meq in *. ded (p i).
    rewrite multiplicity_nats_decr_lt in H0.
    destruct (lt_ge_dec i (length (hyp_Dom hyps))); try lia.
    cut (exists j, j=i /\ In j x). intros; destruct H1. destruct H1.
    rewrite <- H1; auto.
    apply (multiplicity_in (@eq nat) eq_nat_dec). lia.
    assert (length (hyp_Dom hyps) = dim); intuition auto with *.
  Qed.

  Lemma s_SCC's_spec_bound i : In i s_SCC's -> i < dim.

  Proof.
    intros. unfold s_SCC's in H. destruct (sorted_SCC' hyps).
    unfold proj1_sig2 in *. gen p; intros. unfold permutation, meq in p.
    ded (p i). rewrite multiplicity_nats_decr_lt in H0.
    destruct (lt_ge_dec i (length (hyp_Dom hyps))); try lia.
    assert (dim = length (hyp_Dom hyps)). auto. rewrite H1 in *; auto.
    cut (exists j, j=i /\ In j (nats_decr_lt dim)).
    intros; destruct H1. destruct H1. 
    rewrite <- In_nats_decr_lt in H2. subst i; auto.
    eapply permutation_in. auto with typeclass_instances.
    apply permutation_sym. eauto. auto.
  Qed.

(***********************************************************************)
(** chain restricted to an SCC *)

  Notation SCC' := (SCC' hyps).
  Notation SCC'_tag := (SCC'_tag hyps).
  Notation SCC'_dec := (SCC'_dec hyps).

  Definition hd_red_SCC' i t1 t2 := exists l, exists r, exists s,
          SCC'_tag HM (mkRule l r) = Some i /\ t1 = sub s l /\ t2 = sub s r.

  Lemma hd_red_SCC'_cover t1 t2 : hd_red R t1 t2 ->
                                  exists i, hd_red_SCC' i t1 t2 /\ i<dim.

  Proof.
    intros. unfold hd_red in *. do 4 destruct H; destruct H0.
    cut (exists n, SCC'_tag HM (mkRule x x0) = Some n).
    intro. destruct H2 as [i]. exists i. split. exists x; exists x0; exists x1.
    split; try tauto.
    apply (find_first_Some_bound
             (SCC' (mkRule x x0)) (SCC'_dec HM (mkRule x x0))). intuition.
    ded (find_first_exist
           (SCC' (mkRule x x0)) (SCC'_dec HM (mkRule x x0)) _ R H).
    assert (SCC'_tag HM (mkRule x x0) <> None). apply H2.
    split; try tauto. left; auto.
    destruct (SCC'_tag HM (mkRule x x0)). exists n; auto. congruence.
  Qed.

  Definition hd_red_Mod_SCC' i :=  S @ hd_red_SCC' i.

(***********************************************************************)
(** union of chain_SCC' *)

  Notation union := Relation_Operators.union.

  Definition sorted_hd_red_Mod_SCC' := map hd_red_Mod_SCC' s_SCC's.

  Definition hd_red_Mod_SCC'_union :=
    fold_right (@union (term Sig)) empty sorted_hd_red_Mod_SCC'.

  Lemma union_list_spec : forall (A : Type) L (x y : A) (r : relation A),
      In r L -> r x y -> fold_right (@union A) empty L x y.

  Proof.
    intros. induction L. simpl in *; tauto.
    simpl in *. destruct H. destruct H. subst; left; auto. right; tauto.
  Qed.

  Lemma union_list_spec2 : forall (A : Type) L (x y : A),
      fold_right (@union A) empty L x y -> exists r, In r L /\ r x y.

  Proof.
    intros. induction L. simpl in *; tauto.
    simpl in *. destruct H. exists a; split; tauto.
    destruct (IHL H). exists x0. split; try tauto.
  Qed.

  Lemma hd_red_Mod_SCC'_cover : hd_red_Mod S R << hd_red_Mod_SCC'_union.

  Proof.
    unfold inclusion. intros. unfold hd_red_Mod_SCC'_union in H.
    unfold hd_red_Mod in H. do 2 destruct H. ded (hd_red_SCC'_cover H0).
    destruct H1 as [i]. assert (hd_red_Mod_SCC' i x y). exists x0; tauto.
    unfold hd_red_Mod_SCC'_union. eapply union_list_spec; eauto.
    unfold sorted_hd_red_Mod_SCC'. apply in_map.
    apply s_SCC's_spec_cover; tauto.
  Qed.

(***********************************************************************)
(** properties of the total order RT relatively to restricted chain *)

  Notation RT_ODPG := (RT hyps HM).

  Lemma compose_empty :
    forall i j, RT_ODPG i j -> hd_red_Mod_SCC' j @ hd_red_Mod_SCC' i << empty.

  Proof.
    intros. unfold inclusion. intros x y H0. destruct H0 as [z]. destruct H0.

    assert (~ODPGquo' j i). unfold RT in  *. destruct topo_sortable_Rquo'.
    simpl in *. intuition. ded (l (nats_decr_lt dim)). clear l.
    set (RTbis := fun x y : nat => x0 (nats_decr_lt dim) x y = true) in *.
    change (RTbis i j) in H.

    assert (RTbis j i). destruct H3. intuition. apply H5.
    ded (@Rquo_restricted hyps M HM j i).
    split; try split; try tauto; destruct H2; try tauto.

    unfold irreflexive in *. intuition. destruct H3; intuition. apply (H7 i).
    eapply H5; ehyp.

    assert (ODPGquo' j i). unfold Rquo'. intuition.
    unfold Rquo in *. unfold hd_red_Mod_SCC' in *.
    destruct H0 as [x']. destruct H0. destruct H1 as [z']. destruct H1.
    destruct H3 as [t1]. destruct H3 as [r1]. destruct H3 as [s1].
    exists (mkRule t1 r1); split; try tauto.
    destruct H4 as [t2]. destruct H4 as [r2]. destruct H4 as [s2].
    exists (mkRule t2 r2); split; try tauto.
    apply over_DPG. eapply hd_red_Mod_rule2_hd_rules_graph; intuition.
    unfold hd_red_Mod_rule. split.

    assert (SCC' (mkRule t1 r1) (mkRule t1 r1)).
    rewrite (SCC'_tag_exact hyps HM). split; try tauto. congruence.

    destruct H7. tauto.
    exists s1. subst x'. split; simpl; auto; eauto.
    intuition. split.

    assert (SCC' (mkRule t2 r2) (mkRule t2 r2)).
    rewrite (SCC'_tag_exact hyps HM). split; try tauto. congruence.

    destruct H7; tauto.
    exists s2. subst z. split; simpl; auto; eauto. congruence.

    subst j. unfold RT in *. destruct topo_sortable_Rquo'. simpl in *.
    ded (l (nats_decr_lt dim)). clear l. destruct H3. intuition.
    unfold irreflexive in H6. ded (H6 i). auto. tauto.
  Qed.

(***********************************************************************)
(** Proof of the modular termination criterion *)

  Lemma WF_SCC'_union_aux : forall L,
      (forall i, In i L -> WF (hd_red_Mod_SCC' i)) -> sort RT_ODPG L -> 
      WF (fold_right (@union _) empty (map hd_red_Mod_SCC' L)).

  Proof.
    intros. induction L; simpl in *.
    intro. apply SN_intro. intros; tauto.
    inversion H0. subst a0; subst l. eapply WF_incl. apply union_commut.
    apply WF_union_commut.

    apply IHL. intros. apply H. right; auto.
    destruct H0; auto. apply H. left; auto.

    unfold inclusion. intros. cut False; try tauto.
    destruct H1 as [z]. destruct H1. ded (union_list_spec2 _ _ _ H1).
    destruct H5 as [r]. destruct H5.

    assert (exists b, In b L /\ r = hd_red_Mod_SCC' b).
    apply in_map_elim; auto. destruct H7 as [b]. destruct H7; subst r.
    cut (RT_ODPG a b). intro. eapply (compose_empty H8). exists z; eauto.
    eapply sort_transitive. unfold RT; destruct topo_sortable_Rquo'.
    simpl in *. 
    ded (l (nats_decr_lt dim)). destruct H8. intuition. ehyp. auto.
  Qed.

  Lemma WF_SCC'_union :
    (forall i, i < dim -> WF (hd_red_Mod_SCC' i)) -> WF (hd_red_Mod S R).

  Proof.
    intros. eapply WF_incl. apply hd_red_Mod_SCC'_cover.
    unfold hd_red_Mod_SCC'_union, sorted_hd_red_Mod_SCC'.
    eapply WF_SCC'_union_aux. intros. apply H. apply s_SCC's_spec_bound. auto.
    unfold s_SCC's; destruct sorted_SCC'. simpl in *. auto.
  Qed.

  Fixpoint SCC'_list_aux i L :=
    match L with
    | nil => nil
    | x :: q =>
      match eq_opt_dec eq_nat_dec (SCC'_tag HM x) (Some i) with
      | left _ => x :: @SCC'_list_aux i q
      | right _ => @SCC'_list_aux i q
      end
    end.

  Lemma SCC'_list_aux_exact : forall i L r,
      In r (SCC'_list_aux i L) <-> In r L /\ SCC'_tag HM r = Some i.

  Proof.
    intros. induction L. simpl in *. tauto.
    split; intro. simpl in *.
    destruct (eq_opt_dec eq_nat_dec (SCC'_tag HM a) (Some i));
      destruct (rule_eq_dec a r); simpl in *; intuition.
    subst a; tauto.
    destruct H. simpl in *.
    destruct (eq_opt_dec eq_nat_dec (SCC'_tag HM a) (Some i));
      destruct H; simpl in *; try subst a; tauto.
  Qed.

  Lemma nodup_SCC'_list_aux : forall i L, nodup L -> nodup (SCC'_list_aux i L).

  Proof.
    induction L; intros; simpl. tauto.
    simpl in H. destruct H.
    destruct (eq_opt_dec eq_nat_dec (SCC'_tag HM a) (Some i)); try tauto.
    split. rewrite SCC'_list_aux_exact. tauto. tauto.
  Qed.

  Definition SCC'_list i := SCC'_list_aux i R.

  Lemma SCC'_list_exact : forall i r,
      In r (SCC'_list i) <-> SCC'_tag HM r = Some i.

  Proof.
    intros; split; intro.
    unfold SCC'_list in H. rewrite SCC'_list_aux_exact in H. tauto.
    unfold SCC'_list; rewrite SCC'_list_aux_exact; split; try tauto.
    assert (SCC' r r). rewrite (SCC'_tag_exact hyps HM).
    intuition. congruence. unfold SCCTopoOrdering.SCC' in H0. tauto.
  Qed.

  Lemma nodup_SCC'_list : forall i, nodup (SCC'_list i).

  Proof. unfold SCC'_list; intros. apply nodup_SCC'_list_aux. auto. Qed.
 
  Lemma chain_SCC'_red_Mod : forall i,
      hd_red_Mod_SCC' i << hd_red_Mod S (SCC'_list i).

  Proof.
    unfold inclusion; intros. do 2 destruct H. exists x0. split. auto.
    unfold hd_red_SCC' in H0. unfold hd_red. do 3 destruct H0.
    exists x1; exists x2; exists x3. rewrite SCC'_list_exact. intuition.
  Qed.

(***********************************************************************)
(** A faster way to compute SCC'_list but only half-certified *)

  Definition SCC_list_fast i (Hi : i < dim) :=
    listfilter R (list_of_vec (Vnth M Hi)).

  Lemma incl_SCC_list_fast i (Hi : i < dim) :
    Vnth (Vnth M Hi) Hi = true -> incl (SCC'_list i) (SCC_list_fast Hi).

  Proof.
    intros. assert(M[[i,i]] = true).
    unfold mat_unbound; destruct (le_gt_dec dim i). cut False; try tauto; lia.
    assert (g=Hi).
    unfold Peano.gt in *; apply lt_unique. subst; auto.
    unfold incl. intros. rewrite SCC'_list_exact in H1.
    unfold SCCTopoOrdering.SCC'_tag in H1. simpl in *.
    ded (find_first_exact _ _ _ H1).
    destruct H2 as [r]; destruct H2; destruct H3; destruct H3. 
    subst a. unfold SCC_list_fast. eapply listfilter_in. eauto.
    rewrite <- H. apply list_of_vec_exact.
    destruct H4; ded (eq_In_find_first rule_eq_dec H4); do 2 destruct H6.

    assert (x<dim). eapply find_first_Some_bound. eauto.

    unfold SCC_list_fast. eapply listfilter_in. eauto.

    assert ((M[[i,x]]) = true). rewrite HM.
    ded (SCC_sym H3). clear H3. rename H9 into H3.
    rewrite (SCC_effective_exact hyps HM) in H3.
    unfold SCC_effective in H3. simpl in H3.
    unfold rel_on_dom in H3. simpl in *. rewrite H6 in H3. 
    ded (eq_In_find_first rule_eq_dec H5).
    do 2 destruct H9. rewrite H9 in H3.

    assert (i=x0). eapply nodup_unique; eauto. subst x0.
    unfold GoM in H3. rewrite HM in H3. auto.

    unfold mat_unbound in H9; destruct (le_gt_dec dim i).
    cut False; try tauto; lia.
    destruct (le_gt_dec dim x). cut False; try tauto; lia.
    rewrite <- H9. unfold Peano.gt in *.
    assert (g=Hi). apply lt_unique. subst g; apply list_of_vec_exact.
  Qed.

  Lemma hd_red_Mod_SCC'_hd_red_Mod_fast : forall i (Hi : i < dim),
      Vnth (Vnth M Hi) Hi = true ->
      hd_red_Mod_SCC' i << hd_red_Mod S (SCC_list_fast Hi).

  Proof.
    intros. eapply incl_trans. apply chain_SCC'_red_Mod.
    ded (incl_SCC_list_fast Hi H). unfold inclusion; intros.
    destruct H1 as [z]; exists z. destruct H1; split; auto.
    do 4 destruct H2. destruct H3.
    exists x0; exists x1; exists x2; split; try split; try tauto.
    apply H0. auto.
  Qed.

(***********************************************************************)
(** Some lemma to prove trivial case of sub-problem termination *)

  Lemma red_Mod_SCC_trivial_empty : WF (hd_red_Mod S nil).

  Proof.
    unfold WF; intro; apply SN_intro; intros.
    do 2 destruct H. do 4 destruct H0. simpl in *; tauto.
  Qed.

  Lemma WF_chain_SCC_trivial : forall i,
      SCC'_list i = nil -> WF (hd_red_Mod_SCC' i).

  Proof.
    intros. eapply WF_incl. apply chain_SCC'_red_Mod.
    rewrite H. apply red_Mod_SCC_trivial_empty.
  Qed.

  Lemma red_Mod_SCC_trivial_singl : forall i r,
      SCC'_list i = r :: nil -> ~ODPG r r ->  WF (hd_red_Mod_SCC' i).

  Proof.
    intros i r H H0 x. apply SN_intro. intros y Hy. apply SN_intro. intros z Hz.
    cut (DPG r r). intro H1. assert False. apply H0. apply over_DPG. auto.
    tauto.
    assert (H1 : In r (SCC'_list i)). rewrite H. simpl. auto.
    unfold SCC'_list in H1. rewrite SCC'_list_aux_exact in H1.
    destruct H1 as [H1 H2]. destruct Hy as [x0 a]. destruct a as [s h].
    eapply hd_red_Mod_rule2_hd_rules_graph; auto; unfold red_mod in *;
    unfold hd_red_Mod_SCC' in *.
    unfold hd_red_Mod_rule. split. auto. destruct h as [x1 e].
    destruct e as [x2 e]. destruct e as [x3 a]. destruct a as [H3 H4].
    destruct H4 as [H4 H5]. exists x3. assert (h : r = mkRule x1 x2).
    rewrite <- SCC'_list_exact, H in H3; simpl in *; tauto.
    rewrite h; simpl. subst x0. split; eauto.
    unfold hd_red_Mod_rule. split. auto. destruct Hz as [x1 H3].
    destruct H3 as [H3 H4]. destruct H4 as [x2 H4]. destruct H4 as [x3 H4].
    destruct H4 as [x4 H4]. destruct H4 as [H4 H5]. destruct H5 as [H5 H6].
    exists x4. assert (r = mkRule x2 x3).
    rewrite <- SCC'_list_exact, H in H4; simpl in *; tauto.
    rewrite H7. simpl. subst x1. split; eauto.
  Qed.

  Lemma WF_hd_red_Mod_SCC_fast_trivial : forall i (Hi : i < dim),
      SCC_list_fast Hi = nil -> WF (hd_red_Mod_SCC' i).

  Proof.
    intros i Hi; intros. set (L := SCC'_list i). assert (L = SCC'_list i); auto.
    destruct L. apply WF_chain_SCC_trivial. auto.
    destruct L. destruct (ODPG_dec h h).
    assert (R [i] =Some h).
    assert (In h (SCC'_list i)). rewrite <- H0; simpl; auto.
    rewrite SCC'_list_exact in H1. gen H1; intro.
    unfold SCCTopoOrdering.SCC'_tag in H1. simpl in *.
    ded (find_first_exact _ _ _ H1). do 2 destruct H3.
    rewrite (SCC'_tag_exact hyps  HM) in H4. intuition.
    cut (x=h). intro; subst x; auto.
    rewrite H5, <- SCC'_list_exact, <- H0 in H2; simpl in *. intuition.

    cut (M[[i,i]] = true). intros. unfold mat_unbound in H2.
    destruct (le_gt_dec dim i); try discr.
    unfold Peano.gt in *; assert (g=Hi). apply lt_unique. subst g.
    ded (incl_SCC_list_fast Hi H2). rewrite H, <- H0 in *.
    unfold incl in H3. ded (H3 h). simpl in *. tauto.
    assert (SCC ODPG h h). split; apply t_step; auto.
    rewrite (SCC_effective_exact hyps HM) in H2.
    unfold SCC_effective in H2. simpl in *. unfold rel_on_dom in H2.
    ded (restriction o); intuition. ded (eq_In_find_first rule_eq_dec H4).
    do 2 destruct H3. ded(@nodup_unique rule R h R_nodup _ _ H1 H6).
    subst x. rewrite H3 in H2. intuition.

    eapply red_Mod_SCC_trivial_singl; eauto.

    ded (nodup_SCC'_list i).
    rewrite <-H0 in H1; simpl in H1; intuition. clear H1 H4 H5.
    assert(In h (SCC'_list i)); assert(In h0 (SCC'_list i)); try rewrite <- H0;
    simpl;auto.
    rewrite SCC'_list_exact in *. rewrite <- H2 in H1.
    assert (SCC' h h0). rewrite (SCC'_tag_exact hyps HM); auto.
    split; congruence.
    destruct H4. destruct H4. assert False; auto. tauto.
    rewrite H2 in H1. unfold SCCTopoOrdering.SCC'_tag in *. 
    ded (In_find_first2 H2). ded (In_find_first2 H1).
    do 2 destruct H6. do 2 destruct H7. simpl in *.
    assert (x=x0). congruence. subst x0.

    assert (SCC ODPG x x). destruct(rule_eq_dec x h). subst h.
    eapply SCC_trans. apply H4. apply SCC_sym. apply H4.
    do 2 destruct H9; try subst x; try tauto. simpl in *.
    eapply SCC_trans. apply SCC_sym. apply H9. apply H9.
    cut (M[[i,i]]=true). intros. unfold mat_unbound in H11.
    destruct (le_gt_dec dim i). cut False; try tauto; lia.
    unfold Peano.gt in *. assert (g=Hi). apply lt_unique. subst g.
    ded (incl_SCC_list_fast Hi H11). rewrite H, <- H0 in *.
    unfold incl in H12. ded (H12 h). simpl in *. tauto.

    rewrite (SCC_effective_exact hyps HM) in H10.
    unfold SCC_effective in H10. simpl in *. unfold rel_on_dom in H10.
    assert (In x R). eapply exists_element_at_in. exists i; auto.
    ded (eq_In_find_first rule_eq_dec H11). do 2 destruct H12.
    ded (nodup_unique R_nodup H13 H6). subst x0.
    rewrite H12 in H10. intuition.
  Qed.

End S.

Arguments WF_SCC'_union [Sig] _ [R] _ [ODPG] _ _ _ _ [M] _ _ _.

(***********************************************************************)
(** tactics *)

Ltac use_SCC_tag h M S R t :=
  let x := fresh in
    (set (x := SCC_tag_fast h M t); norm_in x (SCC_tag_fast h M t);
      match eval compute in x with
        | Some ?X1 =>
          let Hi := fresh in
            (assert (Hi : X1 < length R);
              [ norm (length R); lia
              | let L := fresh in
                (set (L := SCC_list_fast R M Hi);
                  norm_in L (SCC_list_fast R M Hi);
                  assert (WF (hd_red_Mod S L)); subst L; clear Hi; clear x)])
      end).

Ltac use_SCC_hyp M l := 
  let b := fresh "b" in
    (set (b := Vnth (Vnth M l) l);
      norm_in b (Vnth (Vnth M l) l);
      match eval compute in b with
        | false => apply WF_hd_red_Mod_SCC_fast_trivial with (Hi:=l); eauto
        | true => eapply WF_incl;
          [eapply hd_red_Mod_SCC'_hd_red_Mod_fast with (Hi:=l); auto | auto]
      end).

Ltac use_SCC_all_hyps M i Hi Hj :=
  let rec aux x :=
    match x with
      | 0 => lia
      | S ?y => destruct i; [use_SCC_hyp M Hi | aux y]
    end in	
    match type of Hj with
      | le _ ?Y => aux Y
    end.

Ltac SCC_name n1 n2 :=
  match goal with 
    | |- WF (chain ?R) => set (n1 := dp R); set (n2 := int_red R #)
    | |- WF (hd_red_mod ?E ?R) => set (n1 := R); set (n2 := red E #)
    | |- WF (?X @ hd_red ?R) => set (n1 := R); set (n2 := X)
    | |- WF (hd_red_Mod ?E ?R) => set (n1 := R); set (n2 := E)
  end.

