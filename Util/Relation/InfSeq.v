(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha, 2010-04-27
- Frederic Blanqui, 2011-05-11

Definitions and properties of infinite sequences, possibly modulo some
relation. Uses classical logic and the axiom of indefinite
description, and the axiom WF_notIS for WF_absorb *)

Set Implicit Arguments.

From CoLoR Require Import RelUtil NatUtil Path LeastNat LogicUtil ClassicUtil
     SN NotSN_IS SortUtil ListUtil.
From Stdlib Require Import IndefiniteDescription.

Section S.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

(*****************************************************************************)
(** given a sequence [f] having an infinite number of occurrences of
[a], returns the sub-sequence of those occurrences *)

  Section enum.

    Variables (f : nat -> A) (a : A)
      (H : forall i, exists j, j >= i /\ f j = a).

    Fixpoint g i :=
      match i with
        | 0 => proj1_sig (ch_min (H 0))
        | S i' => proj1_sig (ch_min (H (S (g i'))))
      end.

    Lemma g_mon : forall i, g i < g (S i).

    Proof.
      intro i. simpl. destruct (ch_min (H (S (g i)))). simpl. lia.
    Qed.

    Lemma g_correct : forall i, f (g i) = a.

    Proof.
      intro i. destruct i; simpl.
      destruct (ch_min (H 0)). simpl. intuition.
      destruct (ch_min (H (S (g i)))). simpl. intuition.
    Qed.

    Lemma g_ge_id : forall i, g i >= i.

    Proof.
      induction i. lia. simpl. destruct (ch_min (H (S (g i)))). simpl. lia.
    Qed.

    Lemma g_neq : forall i j, g i < j < g (S i) -> f j <> a.

    Proof.
      intros i j hj e. assert (g (S i) <= j). simpl.
      destruct (ch_min (H (S (g i)))). simpl. intuition. lia.
    Qed.

    Lemma g_complete : forall i, f i = a -> exists j, i = g j.

    Proof.
      intros i hi. assert (h : exists j, g j >= i). exists i. apply g_ge_id.
      exists (proj1_sig (ch_min h)). destruct (ch_min h). simpl. clear h.
      apply NNPP. intro. assert (h1 : i < g x). lia. destruct x.
      absurd (g 0 <= i). lia.
      simpl. destruct (ch_min (H 0)). simpl. intuition auto with *.
      assert (h2 : g x < i). apply NNPP. intro. cut (S x <= x). lia.
      intuition auto with *.
      absurd (f i = a). eapply g_neq. split. apply h2. hyp. hyp.
    Qed.

  End enum.

  Arguments g [f a] _ _.

(*****************************************************************************)
(** sorted list of indices [j] such that [f j = a /\ j < i] *)

  Section indices.

    Variables (f : nat -> A) (a : A).

    Fixpoint indices_aux acc i :=
      match i with
        | 0 => acc
        | S i' => indices_aux (if eq_dec (f i') a then i' :: acc else acc) i'
      end.

    Definition indices := indices_aux nil.

    Lemma In_indices_aux_elim : forall i x acc,
      In x (indices_aux acc i) -> In x acc \/ (f x = a /\ x < i).

    Proof.
      induction i; simpl; intros. auto.
      destruct (eq_dec (f i) a); destruct (IHi _ _ H); intuition.
      destruct H0. subst. auto. auto.
    Qed.

    Arguments In_indices_aux_elim [i x acc] _.

    Lemma indices_correct : forall i x, In x (indices i) -> f x = a /\ x < i.

    Proof.
      intros i x h. destruct (In_indices_aux_elim h). inversion H. hyp.
    Qed.

    Lemma In_indices_aux_intro : forall i x acc,
      In x acc -> In x (indices_aux acc i).

    Proof.
      induction i; simpl; intros. hyp. destruct (eq_dec (f i) a).
      apply IHi. simpl. auto. apply IHi. hyp.
    Qed.

    Lemma indices_aux_complete : forall i x acc,
      x < i -> f x = a -> In x (indices_aux acc i).

    Proof.
      induction i; simpl; intros. absurd (x<0); lia.
      destruct (lt_dec x i). apply IHi; hyp.
      assert (x=i). lia. subst x. destruct (eq_dec (f i) a). 2: cong.
      apply In_indices_aux_intro. simpl. auto.
    Qed.

    Lemma indices_complete : forall i x, x < i -> f x = a -> In x (indices i).

    Proof.
      intros i x xi e. apply indices_aux_complete; hyp.
    Qed.

    Lemma indices_aux_length : forall i acc,
      length (indices_aux acc i) <= i + length acc.

    Proof.
      induction i; simpl; intros. refl. destruct (eq_dec (f i) a).
      ded (IHi (i::acc)). simpl in H. lia. ded (IHi acc). lia.
    Qed.

    Lemma indices_length : forall i, length (indices i) <= i.

    Proof.
      intro i. ded (indices_aux_length i nil). unfold indices. simpl in H.
      lia.
    Qed.

    Lemma indices_aux_Sorted : forall i acc,
      Sorted lt acc -> HdRel le i acc -> Sorted lt (indices_aux acc i).

    Proof.
      induction i; simpl; intros. hyp. apply IHi.
      destruct (eq_dec (f i) a). 2: hyp. apply Sorted_cons. hyp.
      destruct acc. apply HdRel_nil. apply HdRel_cons. inversion H0. lia.
      destruct (eq_dec (f i) a). apply HdRel_cons. refl.
      inversion H0. apply HdRel_nil. apply HdRel_cons. lia.
    Qed.

    Lemma indices_Sorted : forall i, Sorted lt (indices i).

    Proof.
      intro i. apply indices_aux_Sorted. apply Sorted_nil. apply HdRel_nil.
    Qed.

  End indices.

  Arguments In_indices_aux_elim [f a i x acc] _.
  Arguments indices_complete [f a i x] _ _.

(*****************************************************************************)
(** given an infinite sub-sequence [g] of [f] for the indices [i>=i0]
such that [f i = a], returns a sub-sequence for the indices [i>=0]
such that [f i = a] *)

  Section prefix.

    Variables (f : nat -> A) (a : A) (i0 : nat) (g : nat -> nat).

    Notation indices := (indices f a).

    Let d := 0.

    Definition prefix i := let is := indices i0 in
      let n := length is in if lt_dec i n then nth i is d else i0 + g (i - n).

    Lemma prefix_correct :
      (forall i, f (i0 + g i) = a) -> (forall i, f (prefix i) = a).

    Proof.
      intros hg i. unfold prefix.
      destruct (lt_dec i (length (indices i0))).
      eapply indices_correct. apply nth_In. hyp.
      apply hg.
    Qed.

    Lemma prefix_mon :
      (forall i, g i < g (S i)) -> (forall i, prefix i < prefix (S i)).

    Proof.
      intros hg i. unfold prefix. set (is := indices i0).
      set (n := length is). destruct (lt_dec (S i) n); destruct (lt_dec i n).
      apply Sorted_nth. class. apply indices_Sorted. hyp. hyp. lia.
      lia. assert (n=S i). lia. subst. rewrite H, Nat.sub_diag.
      ded (nth_In d l). destruct (In_indices_aux_elim H0). inversion H1.
      lia. assert (e : S i - n = S (i-n)). lia. rewrite e.
      apply Nat.add_lt_mono_l. apply hg.
    Qed.

    Lemma prefix_complete :
      (forall i, i >= i0 -> f i = a -> exists j, i = i0 + g j) ->
      (forall i, f i = a -> exists j, i = prefix j).

    Proof.
      intros hg i e. set (is := indices i0). set (n := length is).
      assert (n <= i0). unfold n, is. apply indices_length.
      destruct (lt_ge_dec i i0).
      (* i < i0 *)
      ded (indices_complete l e). destruct (In_nth d H0) as [j [h1 h2]].
      exists j. unfold prefix. fold is. fold n. destruct (lt_dec j n).
      hyp. contr.
      (* i >= i0 *)
      destruct (hg _ g0 e) as [j hj]. exists (n+j). unfold prefix. fold is.
      fold n. destruct (lt_dec (n+j) n). lia.
      assert (s : n+j-n=j). lia. rewrite s. hyp.
    Qed.

  End prefix.

(*****************************************************************************)
(** building a constant infinite sub-sequence from an infinite
sequence on a finite codomain *)

  Lemma finite_codomain : forall As (f : nat -> A),
    (forall i, In (f i) As) -> exists a, exists g,
      (forall i, g i < g (S i)) /\ (forall i, f (g i) = a)
      /\ (forall i, f i = a -> exists j, i = g j).

  Proof.
    induction As; intros f fin.
    (* nil *)
    ded (fin 0). intuition auto with *.
    (* cons *)
    destruct (classic (forall i, exists j, j >= i /\ f j = a)).
    (* forall i, exists j, j >= i /\ f j = a *)
    exists a. exists (g H). intuition. apply g_mon. apply g_correct.
    apply g_complete. hyp.
    (* exists i0, forall j, j >= i0 -> f j <> a *)
    rewrite not_forall_eq in H. destruct H as [i0 hi0].
    rewrite not_exists_eq in hi0. set (f' := fun i => f(i0+i)).
    assert (forall i, In (f' i) As). intro i.
    ded (fin (i0+i)). simpl in H. destruct H. 2: hyp.
    ded (hi0 (i0+i)). rewrite not_and_eq in H0. destruct H0.
    absurd (i0+i>=i0). hyp. lia. subst. cong.
    destruct (IHAs f' H) as [b [g [h1 [h2 h3]]]]. exists b.
    exists (prefix f b i0 g). intuition.
    apply prefix_mon. hyp. apply prefix_correct. hyp.
    apply prefix_complete. intros j hj e. unfold f' in h3.
    assert (j = i0 + (j-i0)). lia. rewrite H1 in e.
    destruct (h3 _ e) as [k hk]. exists k. lia. hyp.
  Qed.

(*****************************************************************************)
(** build an infinite sequence by iterating a function *)

Section iter.

  Variables (a : A) (f : A -> A).

  Lemma IS_iter : forall R : relation A,
    (forall x, R x (f x)) -> IS R (iter a f).

  Proof.
    intros R hf. unfold IS. destruct i; simpl; apply hf.
  Qed.

End iter.

(***********************************************************************)
(** building an infinite E-sequence from an infinite E!-sequence *)

Section TransIS.

  Variables (E : relation A) (h : nat -> A) (HEh : IS (E!) h).

  Lemma IS_tc : exists h', IS E h' /\ h' 0 = h 0.

  Proof.
    assert (exPath : forall i, exists l, path E (h i) (h (S i)) l).
    intros i. apply clos_trans_path; auto.
    pose (li := fun i =>
      proj1_sig (constructive_indefinite_description _ (exPath i))).
    pose (F := fun i => length (cons (h i) (li i))).

    assert (HFi : forall i, exists y, F i = S y).
    intro i. exists (length (li i)). auto.
    pose (F0 := fun i => Interval_list F i).
    pose (P := fun i j => fst (F0 j) <= i /\ i < snd (F0 j)).

    assert (HinT : forall k, fst (F0 k) < snd (F0 k)).
    induction k. simpl. destruct (HFi 0) as [y Hy]; rewrite Hy; lia.
    simpl. destruct (HFi (S k)) as [y Hy]; rewrite Hy; lia.

    assert (HPeq : forall i j k, P k i /\ P k j -> i = j).
    intros i j k H; unfold P in H. destruct H as [H H0]. destruct H0 as [H1 H2].
    destruct H as [H H0]. gen (Nat.le_lt_trans H H2). intros H3.
    gen (Nat.le_lt_trans H1 H0). intros H4.
    destruct (Nat.le_gt_cases i j) as [H5 | H5]. case (NatCompat.le_lt_or_eq H5); try auto.
    clear H5 H1 H2 H3; intros H5. induction j. lia. simpl in H4.
    case (NatCompat.le_lt_or_eq (NatCompat.lt_n_Sm_le H5)); intros H1.
    rewrite (IHj (Nat.lt_trans (HinT j) H4) H1) in H1. lia.
    rewrite H1 in H4. lia.
    clear H1 H2 H4 H H0. induction i. lia. simpl in H3.
    case (NatCompat.le_lt_or_eq (NatCompat.lt_n_Sm_le H5)); intros H1.
    rewrite (IHi (Nat.lt_trans (HinT i) H3) H1) in H1. lia.
    rewrite H1 in H3; lia.

    assert (exP_F0 : forall i, exists j, P i j). intros i. apply int_exPi. auto.
    pose (F1 := fun i => proj1_sig (ch_min (exP_F0 i))).

    assert (HF0 : forall i, (snd (F0 i) - fst (F0 i) = F i)).
    induction i; auto. simpl. lia.
    pose (h' := fun i => let j := (F1 i) in let i' := i - (fst (F0 j)) in
      nth i' (h j :: li j) (h (S j))).

    assert (HT : forall i, F1 i <= F1 (S i) <= S (F1 i)). intros.

    assert (HSi : S i <= snd (F0 (F1 i))).
    gen (ch_minP _ (exP_F0 i)). unfold P. intuition.
    destruct (NatCompat.le_lt_or_eq HSi) as [H0 | H0].

    2: { assert (PSi : P (S i) (S (F1 i))). unfold P. simpl. rewrite H0.
    split; try lia. destruct (HFi (S (F1 i))) as [y Hy]. rewrite Hy; lia.

    cut (F1 (S i) = S (F1 i)). intros HT; rewrite HT. split; lia.

    destruct (proj2_sig (ch_min (exP_F0 (S i)))) as [_ H1]. apply H1.
    split; auto. intros k. unfold P. intros H2.
    rewrite (HPeq _ _ _ (conj PSi H2)). lia. }

    cut (F1 (S i) = F1 i). intros HT; rewrite HT. split; lia.

    assert (PSi : P (S i) (F1 i)). split; try lia.
    apply (@Nat.le_trans _ i); try lia. destruct (ch_minP _ (exP_F0 i)); hyp.
    destruct (proj2_sig (ch_min (exP_F0 (S i)))) as [_ H].
    apply H; split; try hyp.
    intros k Hk. rewrite (HPeq _ _ _ (conj PSi Hk)). lia.

    assert (DecFSi : forall i, F1 (S i) = F1 i \/ F1 (S i) = S (F1 i)).
    intros. destruct (HT i) as [Hi1 Hi2]. lia.

    assert (forall i, i - fst (F0 (F1 i)) < length (h (F1 i) :: li (F1 i))).
    intros i. destruct (ch_minP _ (exP_F0 i)) as [H1 H2].

    assert (H0 : i - fst (F0 (F1 i)) < snd (F0 (F1 i)) - fst (F0 (F1 i))).
    apply Nat.add_lt_mono_l with (p := fst (F0 (F1 i))).
    rewrite Nat.add_comm, Nat.sub_add; auto.
    rewrite Nat.add_comm, Nat.sub_add; auto.
    apply (Nat.le_trans H1 (@Nat.lt_le_incl _ _ H2)).
    apply (Nat.lt_le_trans H0). rewrite (HF0 (F1 i)). auto.

    exists h'; split; unfold h'.

    (* 1 *)
    intro i; destruct (DecFSi i) as [Hi | Hi]; rewrite Hi.

    assert (S (i - fst (F0 (F1 i))) < length (h (F1 i) :: li (F1 i))).
    gen (H (S i)). rewrite Hi, Nat.sub_succ_l. auto.
    destruct (ch_minP _ (exP_F0 i)). auto.

    rewrite Nat.sub_succ_l. 2: { apply (proj1 (ch_minP _ (exP_F0 i))). }
    gen H0. set (k := i - fst (F0 (F1 i))). destruct k. simpl.
    intros. apply path_headP.
    apply (proj2_sig (constructive_indefinite_description _ (exPath (F1 i)))).
    simpl. intros. apply path_nth_inP with (x := (h (F1 i))); try lia.
    apply (proj2_sig (constructive_indefinite_description _ (exPath (F1 i)))).
    rewrite <- Hi. assert (S i = snd (F0 (F1 i))).
    destruct (ch_minP _ (exP_F0 i)) as [_ HT0].
    destruct (NatCompat.le_lt_or_eq (NatCompat.lt_le_S HT0)); try auto.

    cut (F1 (S i) = F1 i). rewrite Hi. intros. symmetry in H1. lia.

    assert (PSi : P (S i) (F1 i)). split; try lia; auto.
    apply (@Nat.le_trans _ i); try lia. destruct (ch_minP _ (exP_F0 i)); hyp.
    destruct (proj2_sig (ch_min (exP_F0 (S i)))) as [_ H1].
    apply H1; split; try hyp.
    intros k Hk. rewrite (HPeq _ _ _ (conj PSi Hk)). lia.

    assert (nth (S i - fst (F0 (F1 (S i)))) (h (F1 (S i)) :: li (F1 (S i)))
      (h (S (F1 (S i)))) = h (F1 (S i))).

    cut (S i - fst (F0 (F1 (S i))) = 0). intros. rewrite H1. simpl; auto.

    rewrite Hi, H0. simpl. lia.
    rewrite H1. clear H1. gen (HF0 (F1 i)). unfold F. intros.

    cut (i - fst (F0 (F1 i)) = length (li (F1 i))).
    2: { rewrite <- H0, Nat.sub_succ_l in H1. simpl in H1.
    lia.
    apply (proj1 (ch_minP _ (exP_F0 i))). }
    set (k := i - fst (F0 (F1 i))).

    assert (path E (h (F1 i)) (h (S (F1 i))) (li (F1 i))).
    apply (proj2_sig (constructive_indefinite_description _ (exPath (F1 i)))).

    destruct k. intros. symmetry in H3.
    destruct (li (F1 i)). simpl. simpl in H3. rewrite Hi. auto.
    simpl in H3. lia. simpl. intros. 
    apply path_lastP with (x := (h (F1 i)));  auto. rewrite Hi. hyp.

    (* 2 *)
    cut ((F1 0) = 0). intro H0; rewrite H0; refl.
    assert (P00 : P 0 0). unfold P. simpl. split; try lia.
    destruct (HFi 0) as [k Hk]. rewrite Hk; lia.
    apply Nat.le_0_r. apply (is_min_ch (P 0) (exP_F0 0) 0 P00).
  Qed.

End TransIS.

(***********************************************************************)
(** building an infinite R-sequence modulo E from an infinite
E@R-sequence *)

Section ISCompSplit.

  Variables (E R : relation A) (f : nat -> A).

  Lemma ISComp_split : IS (E @ R) f -> exists g, ISMod E R f g.

  Proof.
    intros.
    assert (Hi : forall i, exists x, E (f i) x /\ R x (f (S i))).
    intro. destruct (H i). exists x. intuition.
    pose (Hgi := fun i => constructive_indefinite_description _ (Hi i)).
    exists (fun i => proj1_sig (Hgi i)). intro. apply (proj2_sig (Hgi i)).
  Qed.

End ISCompSplit.

(***********************************************************************)
(** building an infinite R-sequence from an infinite [E#@R]-sequence if
[R@E<<R] *)

Section absorb.

  Variables (E R : relation A) (ab : R @ E << R).

  Lemma IS_absorb : forall f, IS (E# @ R) f -> EIS R.

  Proof.
    intros f hf. destruct (ISComp_split hf) as [g H]. exists g.
    intro i. ded (H i). ded (H (S i)). eapply absorbs_right_rtc. apply ab.
    exists (f (S i)). intuition.
  Qed.

  Lemma WF_absorb : WF R -> WF (E# @ R).

  Proof.
    rewrite !WF_notIS_eq. intros wf f hf.
    destruct (IS_absorb hf) as [g hg]. fo.
  Qed.

End absorb.

Lemma WF_mod_rev2 : forall E S : relation A, WF (S @ E#) -> WF (E# @ S).

Proof.
  intros E S wf. apply (WF_incl ((E#@S)@E#)).
  intros x y xy. exists y. intuition auto with *.
  apply (WF_incl (E#@(S@E#))). apply comp_assoc.
  apply WF_absorb. 2: hyp. intros x z [y [xy yz]]. destruct xy as [t [xt ty]].
  exists t. intuition. apply rt_trans with y. hyp. apply rt_step. hyp.
Qed.

(***********************************************************************)
(** building an infinite R-sequence modulo E from an infinite
E@R-sequence modulo E if E is transitive *)

Section ISModComp.

  Variables (E R : relation A) (f g : nat -> A)
    (hyp1 : ISMod E (E @ R) f g) (TE : transitive E).

  Lemma ISMod_comp : exists g', ISMod E R f g'.

  Proof.
    assert (Hi : forall i, exists x, E (f i) x /\ R x (f (S i))).
    intro. destruct (hyp1 i). destruct H0. exists x. split; intuition.
    apply TE with (g i); auto.
    pose (Hgi := fun i => (constructive_indefinite_description _ (Hi i))).
    exists (fun i => proj1_sig (Hgi i)). intro. apply (proj2_sig (Hgi i)).
  Qed.

End ISModComp.

(***********************************************************************)
(** building an infinite R-sequence modulo E from an infinite
EUR-sequence modulo E with infinitely many R-steps *)

Section ISModUnion.

  Variables (E R : relation A) (f g : nat -> A)
    (hyp1 : ISMod E (E U R) f g)
    (hyp2 : forall i, exists j, i <= j /\ R (g j) (f (S j)))
    (TE : transitive E).

  Lemma ISMod_union : exists f', exists g', ISMod E R f' g'
    /\ forall i, (exists k, g' i = g k) /\ (exists k, f' i = f k).

  Proof.
    pose (reid := rec_ch_min _ hyp2).
    pose (g0 := fun i => (g (reid i))).
    pose (f0 := fun i => match i with 0 => f 0 | S j => (f (S (reid j))) end).
    pose (P := fun i j => i <= j /\ (R (g j) (f (S j)))).

    assert (E_gfi : forall i j, S (reid i) <= j -> j < (reid (S i)) ->
      E (g j) (f (S j))). intros i j le_Sij lt_jx.
    gen (is_min_ch (P (S (reid i))) (hyp2 (S (reid i)))). unfold P.
    intros Hproj. gen (Hproj j). intros HT. destruct (hyp1 j) as [_ ERj].
    destruct ERj; auto. destruct (NatCompat.lt_not_le lt_jx). apply HT. auto.

    assert (E_gf0 : forall j, j < (reid 0) -> E (g j) (f (S j))).
    intros j lt_jx. gen (is_min_ch (P 0) (hyp2 0)). unfold P. intro HP.
    gen (HP j). intro HPj. destruct (hyp1 j) as [_ ERj].
    destruct ERj; auto.
    destruct (NatCompat.lt_not_le lt_jx). apply HPj. split; auto. lia.

    assert (HEfgi : forall i j k,
      S (reid i) <= j -> j <= k  -> k <= reid (S i) -> E (f j) (g k)).
    intros i j k le_ij le_jk le_ki. induction k.
    rewrite (proj1 (Nat.le_0_r _) le_jk) in le_ij. destruct (Nat.nle_succ_0 _ le_ij).
    destruct (NatCompat.le_lt_or_eq le_jk) as [HT | HT]. 2: { rewrite HT.
    apply (proj1 (hyp1 (S k))). } apply TE with (g k).
    exact (IHk (NatCompat.lt_n_Sm_le HT) (Nat.le_trans (Nat.le_succ_diag_r k) le_ki)).
    apply TE with (f (S k)). apply (E_gfi i k); try lia.
    apply (proj1 (hyp1 (S k))).

    assert (HEfg0 : forall j k, j <= k -> k <= reid 0 -> E (f j) (g k)).
    intros j k le_jk le_k0. induction k. rewrite (proj1 (Nat.le_0_r _) le_jk).
    apply (proj1 (hyp1 0)). destruct (NatCompat.le_lt_or_eq le_jk) as [HT | HT].
    2: { rewrite HT. apply (proj1 (hyp1 (S k))). }
    apply TE with (g k). apply IHk; lia. apply TE with (f (S k)).
    apply (E_gf0 k); try lia. apply (proj1 (hyp1 (S k))).

    assert (Rgf : forall i, R (g (reid i)) (f (S (reid i)))).
    intro i. induction i. 2: { destruct (rec_ch_minP P hyp2 i). hyp. }
    simpl. destruct (ch_minP (P 0) (hyp2 0)). hyp.

    exists f0; exists g0. split. 2: { intro. split. exists (reid i). auto.
    destruct i. exists 0; auto. exists (S (reid i)). auto. }
    intro. split. 2: { apply Rgf. } destruct i. 2: { unfold f0, g0.
    apply (HEfgi i); auto.
    destruct (ch_minP (P (S (reid i))) (hyp2 (S (reid i)))) as [? _]. hyp. }
    unfold f0, g0. apply HEfg0; lia.
  Qed.

End ISModUnion.

(***********************************************************************)
(** building an infinite E-sequence from an infinite R-sequence modulo
E if [R@E<<E] *)

Section ISModCommute.

  Variables (E R : relation A) (f g : nat -> A)
    (hyp1 : ISMod E R f g) (hyp2 : R @ E @ R << E @ R).

  Lemma existEdom_proof :
    forall x i, R x (f (S i)) -> exists y, E x y /\ R y (f (S (S i))).

  Proof.
    intros. destruct (hyp1 (S i)). apply hyp2. exists (g (S i)).
    split; auto. exists (f (S i)). split; auto.
  Qed.

  Fixpoint ISOfISMod_rec n : { x : A * nat | R (fst x) (f (S (snd x))) } :=
    let P := fun x : A * nat => R (fst x) (f (S (snd x))) in
      match n with
        | S n' => let (t, Pt) := ISOfISMod_rec n' in
          let H := existEdom_proof Pt in 
            let s := constructive_indefinite_description _ H in 
              let (t', Pt') := s in (@exist _ P (t', (S (snd t))) (proj2 Pt'))
        | 0 => @exist _ P (g 0, 0) (proj2 (hyp1 0))
      end.

  Lemma ISOfISMod_rec_spec : forall i,
    E (fst (proj1_sig (ISOfISMod_rec i)))
    (fst (proj1_sig (ISOfISMod_rec (S i)))).

  Proof.
    induction i; simpl. destruct (constructive_indefinite_description
    _ (existEdom_proof (proj2 (hyp1 0)))) as [t Pt]. simpl. destruct Pt. auto.
    destruct (ISOfISMod_rec i) as [t Pt].
    destruct (constructive_indefinite_description
      _ (existEdom_proof Pt)) as [t' Pt']. simpl.
    destruct (constructive_indefinite_description
      _ (existEdom_proof (proj2 Pt'))) as [y Py]. simpl. exact (proj1 Py).
  Qed.

  Definition ISOfISMod n :=
    match n with
      | S n' => (fst (proj1_sig (ISOfISMod_rec n')))
      | 0 => f 0
    end.

  Lemma ISOfISMod_spec : IS E ISOfISMod.

  Proof.
    intro. case i. simpl. exact (proj1 (hyp1 O)).
    intros. unfold ISOfISMod. exact (ISOfISMod_rec_spec n).
  Qed.

End ISModCommute.

(***********************************************************************)
(** building an infinite R-sequence modulo E! from an infinite
R-sequence modulo [E#] *)

Section ISModTrans.

  Variables (E R : relation A) (f g : nat -> A)
    (hyp1 : ISMod (E #) R f g) (NISR : forall h, ~IS R h)
    (TrsR : transitive R).

  Lemma build_trs_proof : forall i, exists j, i <= j /\ E! (f j) (g j).

  Proof.
    intro i. apply not_all_not_ex. intro HTF. induction i.
    assert (HT : IS R g). intro k. gen (hyp1 (S k)).
    gen (HTF (S k)). rewrite not_and_eq. intro HT.
    destruct HT as [HT | HT]. destruct (HT (Nat.le_0_l (S k))). intro HT0.
    destruct (rtc_split (proj1 HT0)) as [HT1 | HT1]. rewrite <- HT1.
    apply (proj2 (hyp1 k)). tauto. apply (@NISR g). hyp.
    assert (HT : forall j, ~ ((E !) (f (S i + j)) (g (S i + j)))).
    intro j. gen (HTF (S i + j)). apply contraposee_inv. intro HT.
    split; try lia. hyp.
    assert (HT0 : forall j, (f (S i + j)) = (g (S i + j))).
    intro j. destruct (rtc_split (proj1 (hyp1 (S i + j)))); auto.
    destruct (HT j); auto.
    pose (h := fun j => g (S i + j)).
    assert (IS R h). intro j. unfold h. rewrite <- (HT0 (S j)).
    gen (proj2 (hyp1 (S i + j))). rewrite <-Nat.add_succ_r. simpl. auto.
    gen H. apply NISR.
  Qed.

  Lemma trc_ISMod : exists f', exists g', ISMod (E!) R f' g' /\
    (exists k, g' 0 = g k) /\ (f' 0 = f 0 \/ R (f 0) (f' 0)).

  Proof.
    set (HexP := build_trs_proof). pose (reid := rec_ch_min _ HexP).
    pose (f0 := fun i => f (reid i)). pose (g0 := fun i => g (reid i)).

    assert (eq_fg0 : forall j, j < reid 0 -> (f j) = (g j)).
    intros j lt_j0. gen (is_min_ch _ (HexP 0)). intros Hproj.
    gen (Hproj j). intros HT. cut (E # (f j) (g j)).
    intros HT0. destruct (rtc_split HT0) as [| HT1]; auto.
    destruct (NatCompat.le_not_lt (HT (conj (@le_0_n j) HT1))). hyp.
    apply (proj1 (hyp1 j)).

    assert (eq_fgi : forall i j,
      S (reid i) <= j -> j < (reid (S i)) -> (f j) = (g j)).
    intros i j. simpl. intros le_Sij lt_jx.
    gen (is_min_ch _ (HexP (S (reid i)))). intros Hproj.
    gen (Hproj j). intros HT. cut (E # (f j) (g j)).
    intros HT0. destruct (rtc_split HT0) as [| HT1]; auto.
    destruct (NatCompat.le_not_lt (HT (conj le_Sij HT1))). hyp.
    apply (proj1 (hyp1 j)).

    assert (HEfg : forall i, (E !) (f (reid i)) (g (reid i))).
    intro i. induction i. 2: { destruct (rec_ch_minP  _ HexP i); hyp. }
    destruct (ch_minP _ (HexP 0)); hyp.

    assert (HRfg : forall i j k, (reid i) <= j -> j < k  -> k <= reid (S i) ->
      R (g j) (f k)).
    intros i j k le_ij lt_jk le_ki. induction k. destruct (Nat.nlt_0_r lt_jk).
    destruct (NatCompat.le_lt_or_eq (NatCompat.lt_n_Sm_le lt_jk)) as [HT | HT].
    2: { rewrite HT. apply (proj2 (hyp1 k)). }
    apply (@TrsR _ (f k)). apply IHk; try lia.
    rewrite (eq_fgi i k); try lia.
    apply (proj2 (hyp1 k)).

    assert (HRfg0 : forall j k, j < k  -> k <= reid 0 -> R (g j) (f k)).
    intros j k lt_jk le_k0. induction k. destruct (Nat.nlt_0_r lt_jk).
    destruct (NatCompat.le_lt_or_eq (NatCompat.lt_n_Sm_le lt_jk)) as [HT | HT].
    2: { rewrite HT. apply (proj2 (hyp1 k)). }
    apply (@TrsR _ (f k)). apply IHk; try lia. rewrite (eq_fg0 k); try lia.
    apply (proj2 (hyp1 k)).

    exists f0; exists g0. split. intro i. simpl. unfold f0, g0. split.
    apply HEfg.
    apply (HRfg i); auto. destruct (rec_ch_minP _ HexP i) as [HT _].
    apply (@Nat.lt_le_trans (reid i) (S (reid i)) (reid (S i))); auto.
    split. exists (reid 0). simpl. auto.
    unfold f0. case_eq (reid 0); intros. left; refl. right.
    rewrite eq_fg0; try lia. apply HRfg0; lia.
  Qed.

End ISModTrans.

End S.

Arguments finite_codomain [A] _ [As f] _.
