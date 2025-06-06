(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

We build here the quotient graph by the relation SCC, which is Topo Sortable.
We represent the quotient of the Domain by SCC with a function to nat.
*)

Set Implicit Arguments.

From Stdlib Require Import Permutation Multiset Heap PermutSetoid.
From CoLoR Require Import AdjMat RelUtil ListExtras LogicUtil VecUtil NatUtil
     RelSub Path SortUtil ListNodup OptUtil BoundNat SCC SCC_dec Total.

Section SCC_quotient.

  Variable hyps : SCC_dec_hyps.

  Notation A := (hyp_A hyps).
  Notation eq_dec := (hyp_eq_dec hyps).
  Notation Dom := (hyp_Dom hyps).
  Notation R := (hyp_R hyps).
  Notation restriction := (hyp_restriction hyps).
  Notation Dom_nodup := (hyp_nodup hyps).
  Notation R_dec := (hyp_R_dec hyps).
  Notation dim := (length Dom).

  Variables (M : matrix dim dim) (HM : M = SCC_mat_effective hyps).

  Notation SCC := (SCC R).
  Notation SCC_dec := (SCC_effective_dec hyps HM).

(***********************************************************************)
(** Reflexive closure of SCC:
isolated points are also considered as SCC *)

  Definition SCC' x y := (SCC%) x y /\ In x Dom /\ In y Dom.

  Lemma SCC'_dec : forall x y, {SCC' x y} + {~SCC' x y}.

  Proof.
    intros. unfold SCC', clos_refl, union. destruct (eq_dec x y); auto.
    subst; destruct (In_dec eq_dec y Dom). left; auto. right; tauto.
    destruct (SCC_dec x y);
      destruct (In_dec eq_dec y Dom); destruct (In_dec eq_dec x Dom);
      rewrite <- SCC_effective_exact in *; try tauto.
  Defined.

  Lemma SCC'_trans : forall x y z, SCC' x y -> SCC' y z -> SCC' x z.

  Proof.
    intros. unfold SCC' in *. destruct H; destruct H0.
    split; try split; try tauto. destruct H; destruct H0; subst; auto.
    left; auto. right; auto. right; auto. right; eapply SCC_trans. eauto. hyp.
  Qed.

  Lemma SCC'_sym : forall x y ,SCC' x y -> SCC' y x.

  Proof.
    intros; destruct H. split; try tauto.
    destruct H. left; auto. right; apply SCC_sym; auto.
  Qed.

(***********************************************************************)
(** SCC'_tag map each vertex of the graph to its SCC number *)

  Definition SCC'_tag x := find_first (SCC' x) (SCC'_dec x) Dom.

  Lemma SCC'_tag_exact : forall x y,
      SCC' x y <-> SCC'_tag x = SCC'_tag y /\ SCC'_tag x <> None.

  Proof.
    intros. split; intros. unfold SCC'_tag in *. split.

    apply find_first_indep. intros.
    split; intros; eapply SCC'_trans; auto; eauto.
    apply SCC'_sym; auto.

    eapply find_first_exist; unfold SCC' in *. 2: ehyp. tauto.

    destruct H. assert (exists n, SCC'_tag x = Some n).
    destruct (SCC'_tag x); try tauto. exists n; tauto.
    destruct H1. gen H1; intro. rewrite H in H2.
    unfold SCC'_tag in H1. unfold SCC'_tag in H2.
    ded (In_find_first2 H1). ded (In_find_first2 H2).
    do 2 (destruct H3; destruct H4). rewrite H3 in H4. inversion H4.
    subst x1. eapply SCC'_trans. ehyp. apply SCC'_sym. auto.
  Qed.

(***********************************************************************)
(** faster way to compute SCC'_tag but not certified *)

  Fixpoint bools_find_first n (v : vector bool n) :=
    match v with
    | Vnil => None
    | Vcons true w => Some 0
    | Vcons false w =>
      match bools_find_first w with 
      | None => None
      | Some r => Some (S r)
      end
    end.

  Definition SCC_tag_fast M t := 
    let oi := find_first (eq t) (eq_dec t) Dom in
    match oi with 
    | None => None
    | Some i =>
      match le_gt_dec dim i with
      | right Hi => @bools_find_first dim (Vnth M Hi)
      | left _ => None
      end
    end.

(***********************************************************************)
(** quotient relation *)

  Definition Rquo x y :=
    exists r, SCC'_tag r = Some x /\ exists s, SCC'_tag s = Some y /\ R r s.

  Lemma Rquo_restricted : is_restricted Rquo (nats_decr_lt dim).

  Proof.
    unfold is_restricted. intros. rewrite <- !In_nats_decr_lt.
    unfold Rquo in H.
    do 2 destruct H. do 2 destruct H0. unfold SCC'_tag in *.
    split; eapply find_first_Some_bound; eauto.
  Qed.

  Lemma Rquo_dec : forall x y, {Rquo x y} + {~Rquo x y}.

  Proof.
    intros; simpl in *. unfold Rquo.
    cut ({exists r, SCC'_tag r = Some x
                    /\ (exists s, SCC'_tag s = Some y /\ R r s) /\ In r Dom}
         + {~exists r, SCC'_tag r = Some x
                    /\ (exists s, SCC'_tag s = Some y /\ R r s) /\ In r Dom}).
    intro. destruct H.
    left; destruct e; exists x0; tauto.
    right. intuition. apply n. do 2 destruct H. exists x0; intuition.
    destruct H0; ded (restriction x0 x1). tauto.

    cut ({exists r, (fun t => SCC'_tag t = Some x
                   /\ exists s, SCC'_tag s = Some y /\ R t s) r /\ In r Dom}
         + {~exists r, (fun t => SCC'_tag t = Some x
                   /\ exists s, SCC'_tag s = Some y /\ R t s) r /\ In r Dom}).
    intro. destruct H.
    left; destruct e; auto. exists x0. intuition.
    right. intuition. apply n. destruct H. exists x0. intuition.

    apply exists_in_list_dec. intro r.
    destruct (eq_opt_dec eq_nat_dec (SCC'_tag r) (Some x)).

    2: { right. tauto. }
    cut ({exists s, SCC'_tag s = Some y /\ R r s}
         + {~exists s, SCC'_tag s = Some y /\ R r s}).
    intros. destruct H. left. intuition. right; intuition.
    change ({exists s, (fun t => SCC'_tag t = Some y /\ R r t) s}
            + {~exists s, (fun t => SCC'_tag t = Some y /\ R r t) s}).

    assert ({exists s, (fun t => SCC'_tag t = Some y /\ R r t) s /\ In s Dom}
         + {~exists s, (fun t => SCC'_tag t = Some y /\ R r t) s /\In s Dom}).
    apply exists_in_list_dec. intro r0.
    destruct (eq_opt_dec eq_nat_dec (SCC'_tag r0) (Some y));
      destruct (R_dec r r0).
    left; auto. right; tauto. right; tauto. right; tauto.

    destruct H. left; destruct e0; exists x0; tauto.
    right; intuition; apply n. destruct H. exists x0; intuition.
    ded (restriction r x0); tauto.
  Defined.

(***********************************************************************)
(** irreflexive version of Rquo *)

  Definition Rquo' x y := Rquo x y /\ x <> y.

  Lemma Rquo'_dec x y : {Rquo' x y} + {~Rquo' x y}.

  Proof.
    unfold Rquo'; intros; destruct (eq_nat_dec x y); destruct (Rquo_dec x y);
    auto; right; tauto.
  Defined.

  Lemma Rquo'_path : forall l x y, path Rquo' x y l -> 
    exists r, SCC'_tag r = Some x /\ exists s, SCC'_tag s = Some y /\ R! r s.

  Proof.
    induction l; intros; simpl in *.
    unfold Rquo', Rquo in H. do 2 destruct H. exists x0; intuition.
    destruct H2; exists x1; intuition auto with *.
    destruct H. unfold Rquo', Rquo in H. do 2 destruct H. exists x0; intuition.
    destruct H3; destruct H. ded (IHl _ _ H0). do 2 destruct H4.
    do 2 destruct H5; exists x3. intuition. eapply t_trans; eauto.
    destruct (eq_dec x1 x2). subst x1. apply t_step. auto.
    eapply t_trans. apply t_step. eauto. cut (SCC' x1 x2).
    intros. do 2 destruct H7; try tauto. destruct H7; auto.
    rewrite SCC'_tag_exact. intuition. congruence. rewrite H in H7. discr.
  Qed.

  Lemma irrefl_tc_Rquo' : irreflexive (Rquo'!).

  Proof.
    unfold irreflexive. intuition. ded (clos_trans_path H).
    destruct H0 as [l]. destruct l. simpl in H0; destruct H0; auto.
    simpl in H0; destruct H0. ded (Rquo'_path l n x H1).
    do 2 destruct H2. do 2 destruct H3.
    unfold Rquo' in H0. destruct H0. unfold Rquo in H0.
    do 2 destruct H0. do 2 destruct H6. cut (R! x3 x2).
    intro. cut (x=n). intuition. cut (SCC' x3 x2).
    intro. rewrite  SCC'_tag_exact in H9. destruct H9; congruence.
    unfold SCC'. intuition; ded (restriction x2 x3); try tauto.
    right. split; auto. apply t_step; auto. cut(R# x3 x2).
    intro. ded (rtc_split H8). destruct H9; try tauto. subst x3; congruence.
    assert (R# x3 x0). cut (SCC' x3 x0).
    intro. do 2 destruct H8. subst x3; intuition auto with *.
    destruct H8. apply tc_incl_rtc. intuition.
    rewrite SCC'_tag_exact. split. congruence. rewrite H6. discr.
    eapply rt_trans; eauto. assert (R# x0 x1). apply tc_incl_rtc. intuition.
    eapply rt_trans; eauto. cut (SCC' x1 x2).
    intro. do 2 destruct H10. subst x1; intuition auto with *. destruct H10.
    apply tc_incl_rtc. intuition.
    rewrite SCC'_tag_exact. split. congruence. rewrite H3. discr.
  Qed.

  Lemma topo_sortable_Rquo' : topo_sortable Rquo'.

  Proof.
    apply antisym_topo_sortable_topo_sortable.
    apply possible_antisym_topo_sort; auto.
    unfold RelMidex.eq_dec; apply eq_nat_dec.
    unfold rel_dec; apply Rquo'_dec. apply irrefl_tc_Rquo'.
  Qed.

(***********************************************************************)
(* total ordering on SCCs *)

  Definition RT x y :=
    proj1_sig topo_sortable_Rquo' (nats_decr_lt dim) x y = true.

  Lemma Rquo'_incl_RT : Rquo' << RT.

  Proof.
    unfold inclusion; intros. unfold RT. destruct topo_sortable_Rquo'. simpl.
    ded (l (nats_decr_lt dim)). destruct H0. intuition. apply H2. gen H; intro.
    unfold Rquo', Rquo, SCC'_tag in H; auto; do 3 destruct H; do 2 destruct H7.
    split; try split; try tauto; rewrite <- In_nats_decr_lt;
    eapply find_first_Some_bound; eauto.
  Qed.

(***********************************************************************)
(* SCCs sorting *)
  
  Lemma sorted_SCC' :
    {m : list nat | sort RT m & permutation eq_nat_dec (nats_decr_lt dim) m}.

  Proof.
    unfold RT. destruct topo_sortable_Rquo' as [F HF]; simpl.
    set (RTb := fun x y : N dim => F (nats_decr_lt dim) x y = true) in *.

    cut ({m : list (N dim) | sort RTb m & permutation N_eq_dec (L dim) m}).
    intro. destruct H as [mb]. exists (map N_val mb).
    apply sort_map_N_val. intuition.

    unfold permutation in *. unfold meq in *. intros.
    rewrite multiplicity_nats_decr_lt in *. destruct (lt_ge_dec a dim).
    ded (p (N_ l)). rewrite <- multiplicity_map_N_val, map_N_val_L,
                    multiplicity_nats_decr_lt in H.
    destruct (lt_ge_dec a dim); try lia.
    rewrite <- multiplicity_map_N_val in H; auto.
    erewrite <- multiplicity_map_N_val_notin; auto.

    cut({m : list (N dim) | sort (RTb %) m & permutation N_eq_dec (L dim) m}).
    intro. destruct H as [mb]. exists mb; auto. apply nodup_sort_strict; auto.
    eapply multiplicity_nodup. intros. unfold permutation in *.
    unfold meq in *. rewrite <- p, multiplicity_L. refl.

    apply treesort. ded (HF (nats_decr_lt dim)). destruct H; intuition auto with *.
    intros. unfold total in H4. destruct x as [x xdim]. destruct y as [y ydim].
    assert (trichotomy (fun x y => F (nats_decr_lt dim) x y = true) x y).
    apply H4; rewrite <- In_nats_decr_lt; auto.
    unfold trichotomy in H3. destruct (eq_nat_dec x y).
    left; left; subst x; auto.
    f_equal. apply lt_unique.
    assert ({F (nats_decr_lt dim) x y = true}
            +{~F (nats_decr_lt dim) x y = true}).
    destruct (F (nats_decr_lt dim) x y); auto.
    destruct H5. left; auto. right; auto. right; auto. right; tauto.

    apply rc_trans. intros x y z xy yz. unfold RTb in *.
    ded (HF (nats_decr_lt dim)).
    destruct H. intuition. unfold transitive in *. eapply H0; eauto.
  Qed.

End SCC_quotient.
