(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sidi Ould-Biha, 2010-04-27
- Frederic Blanqui, 2011-05-11

Definitions and properties of infinite sequences, possibly modulo some
relation. Uses classical logic and the axiom of indefinite
description, and the axiom WF_notIS for WF_absorb *)

Set Implicit Arguments.

Require Import RelUtil NatUtil List Path NatLeast LogicUtil ClassicUtil
  IndefiniteDescription.

Section S.

  Variable A : Type.

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
      intro i. simpl. destruct (ch_min (H (S (g i)))). simpl. omega.
    Qed.

    Lemma g_correct : forall i, f (g i) = a.

    Proof.
      intro i. destruct i; simpl.
      destruct (ch_min (H 0)). simpl. intuition.
      destruct (ch_min (H (S (g i)))). simpl. intuition.
    Qed.

    Lemma g_ge_id : forall i, g i >= i.

    Proof.
      induction i. omega. simpl. destruct (ch_min (H (S (g i)))). simpl. omega.
    Qed.

    Lemma g_neq : forall i j, g i < j < g (S i) -> f j <> a.

    Proof.
      intros i j hj e. assert (g (S i) <= j). simpl.
      destruct (ch_min (H (S (g i)))). simpl. intuition. omega.
    Qed.

    Lemma g_complete : forall i, f i = a -> exists j, i = g j.

    Proof.
      intros i hi. assert (h : exists j, g j >= i). exists i. apply g_ge_id.
      exists (proj1_sig (ch_min h)). destruct (ch_min h). simpl. clear h.
      apply NNPP. intro. assert (h1 : i < g x). omega. destruct x.
      absurd (g 0 <= i). omega.
      simpl. destruct (ch_min (H 0)). simpl. intuition.
      assert (h2 : g x < i). apply NNPP. intro. cut (S x <= x). omega.
      intuition.
      absurd (f i = a). eapply g_neq. split. apply h2. hyp. hyp.
    Qed.

  End enum.

  Implicit Arguments g [f a].

(*****************************************************************************)
(** sorted list of indices [j] such that [f j = a /\ j < i] *)

  Section indices.

    Variables (eq_dec : forall x y : A, {x=y}+{~x=y}) (f : nat -> A) (a : A).

    Fixpoint indices_aux acc i :=
      match i with
        | 0 => acc
        | S i' => indices_aux (if eq_dec (f i') a then i' :: acc else acc) i'
      end.

    Definition indices := indices_aux nil.

    Lemma In_indices_aux_elim : forall i x acc,
      In x (indices_aux acc i) -> In x acc \/ f x = a.

    Proof.
      induction i; simpl; intros. auto. destruct (eq_dec (f i) a ).
      destruct (IHi _ _ H). destruct H0. subst. auto. auto. auto.
      apply IHi. hyp.
    Qed.

    Implicit Arguments In_indices_aux_elim [i x acc].

    Lemma indices_correct : forall i x, In x (indices i) -> f x = a.

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
      induction i; simpl; intros. absurd (x<0); omega.
      destruct (lt_dec x i). apply IHi; hyp.
      assert (x=i). omega. subst. destruct (eq_dec (f i) (f i)). 2: irrefl.
      apply In_indices_aux_intro. simpl. auto.
    Qed.

    Lemma indices_complete : forall i x, x < i -> f x = a -> In x (indices i).

    Proof.
      intros i x xi e. apply indices_aux_complete; hyp.
    Qed.

    Require Import Sorted.

    Lemma indices_aux_Sorted : forall i acc,
      Sorted lt acc -> HdRel le i acc -> Sorted lt (indices_aux acc i).

    Proof.
      induction i; simpl; intros. hyp. apply IHi.
      destruct (eq_dec (f i) a). 2: hyp. apply Sorted_cons. hyp.
      destruct acc. apply HdRel_nil. apply HdRel_cons. inversion H0. omega.
      destruct (eq_dec (f i) a). apply HdRel_cons. refl.
      inversion H0. apply HdRel_nil. apply HdRel_cons. omega.
    Qed.

    Lemma indices_Sorted : forall i, Sorted lt (indices i).

    Proof.
      intro i. apply indices_aux_Sorted. apply Sorted_nil. apply HdRel_nil.
    Qed.

    Variable d : nat.

    Lemma Sorted_nth_S : forall l i, Sorted lt l ->
      i < length l -> S i < length l -> nth i l d < nth (S i) l d.

    Proof.
      induction l; destruct i; simpl; intros. omega. omega.
      inversion H. subst. destruct l. simpl in H1. absurd_arith.
      inversion H5. hyp.
      inversion H. apply IHl. hyp. omega. omega.
    Qed.

    Lemma HdRel_nth : forall l i n, Sorted lt l ->
      HdRel lt n l -> i < length l -> n < nth i l d.

    Proof.
      induction l; destruct i; simpl; intros.
      absurd_arith. absurd_arith. inversion H0. hyp.
      apply IHl. inversion H. hyp.
      destruct l. apply HdRel_nil. apply HdRel_cons.
      inversion H0. inversion H. inversion H8. subst. omega.
      omega.
    Qed.

    Lemma Sorted_nth : forall j l i, Sorted lt l ->
      i < length l -> j < length l -> i < j -> nth i l d < nth j l d.

    Proof.
      induction j; intros. absurd_arith.
      destruct l; simpl in *. absurd_arith.
      inversion H. subst. destruct i; simpl.
      apply HdRel_nth. hyp. hyp. omega.
      apply IHj. hyp. omega. omega. omega.
    Qed.

  End indices.

(*****************************************************************************)
(** sorted list of indices [j] such that [f j = a /\ j < i] *)

  Section prefix.

    Variables (eq_dec : forall x y : A, {x=y}+{~x=y}) (f : nat -> A) (a : A)
      (i0 : nat) (g : nat -> nat) (d : nat).

    Notation indices := (indices eq_dec f a).

    Definition prefix i := let is := indices i0 in
      let n := length is in if lt_dec i n then nth i is d else g (i - n).

    Lemma prefix_correct :
      (forall i, f (g i) = a) -> (forall i, f (prefix i) = a).

    Proof.
      intros hg i. unfold prefix.
      destruct (lt_dec i (length (indices i0))).
      eapply indices_correct. apply nth_In. hyp.
      apply hg.
    Qed.

    Require Import ListUtil.

    Lemma prefix_mon :
      (length (indices i0) > 0 -> last (indices i0) d < g 0) ->
      (forall i, g i < g (S i)) -> (forall i, prefix i < prefix (S i)).

    Proof.
      intros hyp hg i. unfold prefix. set (is := indices i0).
      set (n := length is). destruct (lt_dec (S i) n); destruct (lt_dec i n).
      apply Sorted_nth. apply indices_Sorted. hyp. hyp. omega.
      absurd_arith. assert (n=S i). omega. subst. rewrite H, minus_diag.
      assert (h : length (indices i0) > 0). fold is. omega.
      generalize (hyp h). rewrite last_nth. fold is. rewrite H. simpl.
      rewrite <- minus_n_O. auto.
      assert (e : S i - n = S (i-n)). omega. rewrite e. apply hg.
    Qed.

  End prefix.

(*****************************************************************************)
(** building a constant infinite sub-sequence from an infinite
sequence on a finite codomain *)

  Lemma finite_codomain : forall As (f : nat -> A),
    (forall i, In (f i) As) -> exists a, exists g,
      (forall i, g i < g (S i)) /\ (forall i, f (g i) = a)
      (*/\ (forall i, f i = a -> exists j, i = g j)*).

  Proof.
    induction As; intros f fin.
    (* nil *)
    ded (fin 0). intuition.
    (* cons *)
    destruct (classic (forall i, exists j, j >= i /\ f j = a)).
    (* forall i, exists j, j >= i /\ f j = a *)
    exists a. exists (g H). intuition. apply g_mon. apply g_correct.
    (*apply g_complete. hyp.*)
    (* exists i0, forall j, j >= i0 -> f j <> a *)
    rewrite not_forall_eq in H. destruct H as [i0 hi0].
    rewrite not_exists_eq in hi0. set (f' := fun i => f(i+i0)).
    assert (forall i, In (f' i) As). intro i.
    ded (fin (i+i0)). simpl in H. destruct H. 2: hyp.
    ded (hi0 (i+i0)). rewrite not_and_eq in H0. destruct H0.
    absurd (i+i0>=i0). hyp. omega. subst. irrefl.
    destruct (IHAs f' H) as [b [g [h1 (*[*)h2 (*h3]*)]]]. exists b.
    exists (fun i => g i + i0). intuition.
  Qed.

(*****************************************************************************)
(** build an infinite sequence by iterating a function *)

Section iter.

  Variables (a : A) (f : A -> A).

  Fixpoint iter i :=
    match i with
      | 0 => a
      | S i' => f (iter i')
    end.

  Lemma IS_iter : forall R : relation A, (forall x, R x (f x)) -> IS R iter.

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
      projT1 (constructive_indefinite_description _ (exPath i))).
    pose (F := fun i => length (cons (h i) (li i))).

    assert (HFi : forall i, exists y, F i = S y).
    intro i. exists (length (li i)). auto.
    pose (F0 := fun i => Interval_list F i).
    pose (P := fun i j => fst (F0 j) <= i /\ i < snd (F0 j)).

    assert (HinT : forall k, fst (F0 k) < snd (F0 k)).
    induction k. simpl. destruct (HFi 0) as [y Hy]; rewrite Hy; omega.
    simpl. destruct (HFi (S k)) as [y Hy]; rewrite Hy; omega.

    assert (HPeq : forall i j k, P k i /\ P k j -> i = j).
    intros i j k H; unfold P in H. destruct H as [H H0]. destruct H0 as [H1 H2].
    destruct H as [H H0]. generalize (le_lt_trans _ _ _ H H2). intros H3.
    generalize (le_lt_trans _ _ _ H1 H0). intros H4.
    destruct (le_or_lt i j) as [H5 | H5]. case (le_lt_or_eq _ _ H5); try auto.
    clear H5 H1 H2 H3; intros H5. induction j. omega. simpl in H4.
    case (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)); intros H1.
    rewrite (IHj (lt_trans _ _ _ (HinT j) H4) H1) in H1. omega.
    rewrite H1 in H4. omega.
    clear H1 H2 H4 H H0. induction i. omega. simpl in H3.
    case (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H5)); intros H1.
    rewrite (IHi (lt_trans _ _ _ (HinT i) H3) H1) in H1. omega.
    rewrite H1 in H3; omega.

    assert (exP_F0 : forall i, exists j, P i j). intros i. apply int_exPi. auto.
    pose (F1 := fun i => projT1 (ch_min (exP_F0 i))).

    assert (HF0 : forall i, (snd (F0 i) - fst (F0 i) = F i)).
    induction i; auto. simpl. omega.
    pose (h' := fun i => let j := (F1 i) in let i' := i - (fst (F0 j)) in
      nth i' (h j :: li j) (h (S j))).

    assert (HT : forall i, F1 i <= F1 (S i) <= S (F1 i)). intros.

    assert (HSi : S i <= snd (F0 (F1 i))).
    generalize (ch_minP _ (exP_F0 i)). unfold P. intuition.
    destruct (le_lt_or_eq _ _ HSi) as [H0 | H0]. Focus 2.

    assert (PSi : P (S i) (S (F1 i))). unfold P. simpl. rewrite H0.
    split; try omega. destruct (HFi (S (F1 i))) as [y Hy]. rewrite Hy; omega.

    cut (F1 (S i) = S (F1 i)). intros HT; rewrite HT. split; omega.

    destruct (projT2 (ch_min (exP_F0 (S i)))) as [_ H1]. apply H1.
    split; auto. intros k. unfold P. intros H2.
    rewrite (HPeq _ _ _ (conj PSi H2)). omega.

    cut (F1 (S i) = F1 i). intros HT; rewrite HT. split; omega.

    assert (PSi : P (S i) (F1 i)). split; try omega.
    apply (@le_trans _ i); try omega. destruct (ch_minP _ (exP_F0 i)); hyp.
    destruct (projT2 (ch_min (exP_F0 (S i)))) as [_ H].
    apply H; split; try hyp.
    intros k Hk. rewrite (HPeq _ _ _ (conj PSi Hk)). omega.

    assert (DecFSi : forall i, F1 (S i) = F1 i \/ F1 (S i) = S (F1 i)).
    intros. destruct (HT i) as [Hi1 Hi2]. omega.

    assert (forall i, i - fst (F0 (F1 i)) < length (h (F1 i) :: li (F1 i))).
    intros i. destruct (ch_minP _ (exP_F0 i)) as [H1 H2].

    assert (H0 : i - fst (F0 (F1 i)) < snd (F0 (F1 i)) - fst (F0 (F1 i))).
    apply plus_lt_reg_l with (p := fst (F0 (F1 i))).
    rewrite le_plus_minus_r; auto.
    rewrite le_plus_minus_r; auto.
    apply (@le_trans _ _ _ H1 (@lt_le_weak _ _ H2)).
    apply (lt_le_trans _ _ _ H0). rewrite (HF0 (F1 i)). auto.

    exists h'; split; unfold h'.

    (* 1 *)
    intro i; destruct (DecFSi i) as [Hi | Hi]; rewrite Hi.

    assert (S (i - fst (F0 (F1 i))) < length (h (F1 i) :: li (F1 i))).
    generalize (H (S i)). rewrite Hi. rewrite <- minus_Sn_m. auto.
    destruct (ch_minP _ (exP_F0 i)). auto.

    rewrite <- minus_Sn_m. Focus 2. apply (proj1 (ch_minP _ (exP_F0 i))).
    generalize H0. set (k := i - fst (F0 (F1 i))). destruct k. simpl.
    intros. apply path_headP.
    apply (projT2 (constructive_indefinite_description _ (exPath (F1 i)))).
    simpl. intros. apply path_nth_inP with (x := (h (F1 i))); try omega.
    apply (projT2 (constructive_indefinite_description _ (exPath (F1 i)))).
    rewrite <- Hi. assert (S i = snd (F0 (F1 i))).
    destruct (ch_minP _ (exP_F0 i)) as [_ HT0].
    destruct (le_lt_or_eq _ _ (lt_le_S _ _ HT0)); try auto.

    cut (F1 (S i) = F1 i). rewrite Hi. intros. symmetry in H1. omega.

    assert (PSi : P (S i) (F1 i)). split; try omega; auto.
    apply (@le_trans _ i); try omega. destruct (ch_minP _ (exP_F0 i)); hyp.
    destruct (projT2 (ch_min (exP_F0 (S i)))) as [_ H1].
    apply H1; split; try hyp.
    intros k Hk. rewrite (HPeq _ _ _ (conj PSi Hk)). omega.

    assert (nth (S i - fst (F0 (F1 (S i)))) (h (F1 (S i)) :: li (F1 (S i)))
      (h (S (F1 (S i)))) = h (F1 (S i))).

    cut (S i - fst (F0 (F1 (S i))) = 0). intros. rewrite H1. simpl; auto.

    rewrite Hi, H0. simpl. omega.
    rewrite H1. clear H1. generalize (HF0 (F1 i)). unfold F. intros.

    cut (i - fst (F0 (F1 i)) = length (li (F1 i))).
    Focus 2. rewrite <- H0 in H1. rewrite <- minus_Sn_m in H1. simpl in H1.
    omega.
    apply (proj1 (ch_minP _ (exP_F0 i))).
    set (k := i - fst (F0 (F1 i))).

    assert (path E (h (F1 i)) (h (S (F1 i))) (li (F1 i))).
    apply (projT2 (constructive_indefinite_description _ (exPath (F1 i)))).

    destruct k. intros.  symmetry in H3.
    destruct (li (F1 i)). simpl. simpl in H3. rewrite Hi. auto.
    simpl in H3. absurd_arith. simpl. intros. 
    apply path_lastP with (x := (h (F1 i)));  auto. rewrite Hi. hyp.

    (* 2 *)
    cut ((F1 0) = 0). intro H0; rewrite H0; refl.
    assert (P00 : P 0 0). unfold P. simpl. split; try omega.
    destruct (HFi 0) as [k Hk]. rewrite Hk; omega.
    symmetry. apply le_n_O_eq. apply (is_min_ch (P 0) (exP_F0 0) 0 P00).
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
    exists (fun i => projT1 (Hgi i)). intro. apply (projT2 (Hgi i)).
  Qed.

End ISCompSplit.

(***********************************************************************)
(** building an infinite R-sequence from an infinite E#R-sequence if
R@E<<R *)

Section absorb.

  Variables (E R : relation A) (ab : R @ E << R).

  Lemma IS_absorb : forall f, IS (E# @ R) f -> EIS R.

  Proof.
    intros f hf. destruct (ISComp_split hf) as [g H]. exists g.
    intro i. ded (H i). ded (H (S i)). eapply incl_comp_rtc. apply ab.
    exists (f (S i)). intuition.
  Qed.

  Require Import SN IS_NotSN.

  Lemma WF_absorb : WF R -> WF (E# @ R).

  Proof.
    repeat rewrite WF_notIS. intros wf f hf.
    destruct (IS_absorb hf) as [g hg]. firstorder.
  Qed.

End absorb.

Lemma WF_mod_rev2 : forall E S : relation A, WF (S @ E#) -> WF (E# @ S).

Proof.
  intros E S wf. apply WF_incl with (S:=(E#@S)@E#).
  intros x y xy. exists y. intuition.
  apply WF_incl with (S:=E#@(S@E#)). apply comp_assoc.
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
    exists (fun i => projT1 (Hgi i)). intro. apply (projT2 (Hgi i)).
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
    generalize (is_min_ch (P (S (reid i))) (hyp2 (S (reid i)))). unfold P.
    intros Hproj. generalize (Hproj j). intros HT. destruct (hyp1 j) as [_ ERj].
    destruct ERj; auto. destruct (lt_not_le _ _ lt_jx). apply HT. auto.

    assert (E_gf0 : forall j, j < (reid 0) -> E (g j) (f (S j))).
    intros j lt_jx. generalize (is_min_ch (P 0) (hyp2 0)). unfold P. intro HP.
    generalize (HP j). intro HPj. destruct (hyp1 j) as [_ ERj].
    destruct ERj; auto.
    destruct (lt_not_le _ _ lt_jx). apply HPj. split; auto. omega.

    assert (HEfgi : forall i j k,
      S (reid i) <= j -> j <= k  -> k <= reid (S i) -> E (f j) (g k)).
    intros i j k le_ij le_jk le_ki. induction k.
    rewrite <- (le_n_O_eq _ le_jk) in le_ij. destruct (le_Sn_O _ le_ij).
    destruct (le_lt_or_eq _ _ le_jk) as [HT | HT]. Focus 2. rewrite HT.
    apply (proj1 (hyp1 (S k))). apply TE with (g k).
    exact (IHk (lt_n_Sm_le _ _ HT) (@le_trans _ _ _ (le_n_Sn k) le_ki)).
    apply TE with (f (S k)). apply (E_gfi i k); try omega.
    apply (proj1 (hyp1 (S k))).

    assert (HEfg0 : forall j k, j <= k -> k <= reid 0 -> E (f j) (g k)).
    intros j k le_jk le_k0. induction k. rewrite <- (le_n_O_eq _ le_jk).
    apply (proj1 (hyp1 0)). destruct (le_lt_or_eq _ _ le_jk) as [HT | HT].
    Focus 2. rewrite HT. apply (proj1 (hyp1 (S k))).
    apply TE with (g k). apply IHk; omega. apply TE with (f (S k)).
    apply (E_gf0 k); try omega. apply (proj1 (hyp1 (S k))).

    assert (Rgf : forall i, R (g (reid i)) (f (S (reid i)))).
    intro i. induction i. Focus 2. destruct (rec_ch_minP P hyp2 i). hyp.
    simpl. destruct (ch_minP (P 0) (hyp2 0)). hyp.

    exists f0; exists g0. split. Focus 2. intro. split. exists (reid i). auto.
    destruct i. exists 0; auto. exists (S (reid i)). auto.
    intro. split. Focus 2. apply Rgf. destruct i. Focus 2. unfold f0, g0.
    apply (HEfgi i); auto.
    destruct (ch_minP (P (S (reid i))) (hyp2 (S (reid i)))) as [? _]. hyp.
    unfold f0, g0. apply HEfg0; omega.
  Qed.

End ISModUnion.

(***********************************************************************)
(** building an infinite E-sequence from an infinite R-sequence modulo
E if R@E << E *)

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
              let (t', Pt') := s in (exist P (t', (S (snd t))) (proj2 Pt'))
        | 0 => (exist P (g 0, 0) (proj2 (hyp1 0)))
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
R-sequence modulo E# *)

Section ISModTrans.

  Variables (E R : relation A) (f g : nat -> A)
    (hyp1 : ISMod (E #) R f g) (NISR : forall h, ~IS R h)
    (TrsR : transitive R).

  Lemma build_trs_proof : forall i, exists j, i <= j /\ E! (f j) (g j).

  Proof.
    intro i. apply not_all_not_ex. intro HTF. induction i.
    assert (HT : IS R g). intro k. generalize (hyp1 (S k)).
    generalize (HTF (S k)). rewrite not_and_eq. intro HT.
    destruct HT as [HT | HT]. destruct (HT (le_O_n (S k))). intro HT0.
    destruct (rtc_split (proj1 HT0)) as [HT1 | HT1]. rewrite <- HT1.
    apply (proj2 (hyp1 k)). tauto. apply (@NISR g). hyp.
    assert (HT : forall j, ~ ((E !) (f (S i + j)) (g (S i + j)))).
    intro j. generalize (HTF (S i + j)). apply contraposee_inv. intro HT.
    split; try omega. hyp.
    assert (HT0 : forall j, (f (S i + j)) = (g (S i + j))).
    intro j. destruct (rtc_split (proj1 (hyp1 (S i + j)))); auto.
    destruct (HT j); auto.
    pose (h := fun j => g (S i + j)).
    assert (IS R h). intro j. unfold h. rewrite <- (HT0 (S j)).
    generalize (proj2 (hyp1 (S i + j))). rewrite <- plus_Snm_nSm. simpl. auto.
    generalize H. apply NISR.
  Qed.

  Lemma trc_ISMod : exists f', exists g', ISMod (E!) R f' g' /\
    (exists k, g' 0 = g k) /\ (f' 0 = f 0 \/ R (f 0) (f' 0)).

  Proof.
    set (HexP := build_trs_proof). pose (reid := rec_ch_min _ HexP).
    pose (f0 := fun i => f (reid i)). pose (g0 := fun i => g (reid i)).

    assert (eq_fg0 : forall j, j < reid 0 -> (f j) = (g j)).
    intros j lt_j0. generalize (is_min_ch _ (HexP 0)). intros Hproj.
    generalize (Hproj j). intros HT. cut (E # (f j) (g j)).
    intros HT0. destruct (rtc_split HT0) as [| HT1]; auto.
    destruct (le_not_lt _ _ (HT (conj (le_O_n j) HT1))). hyp.
    apply (proj1 (hyp1 j)).

    assert (eq_fgi : forall i j,
      S (reid i) <= j -> j < (reid (S i)) -> (f j) = (g j)).
    intros i j. simpl. intros le_Sij lt_jx.
    generalize (is_min_ch _ (HexP (S (reid i)))). intros Hproj.
    generalize (Hproj j). intros HT. cut (E # (f j) (g j)).
    intros HT0. destruct (rtc_split HT0) as [| HT1]; auto.
    destruct (le_not_lt _ _ (HT (conj le_Sij HT1))). hyp.
    apply (proj1 (hyp1 j)).

    assert (HEfg : forall i, (E !) (f (reid i)) (g (reid i))).
    intro i. induction i. Focus 2. destruct (rec_ch_minP  _ HexP i); hyp.
    destruct (ch_minP _ (HexP 0)); hyp.

    assert (HRfg : forall i j k, (reid i) <= j -> j < k  -> k <= reid (S i) ->
      R (g j) (f k)).
    intros i j k le_ij lt_jk le_ki. induction k. destruct (lt_n_O _ lt_jk).
    destruct (le_lt_or_eq _ _ (lt_n_Sm_le _ _ lt_jk)) as [HT | HT]. Focus 2.
    rewrite HT. apply (proj2 (hyp1 k)).
    apply (@TrsR _ (f k)). apply IHk; try omega.
    rewrite (eq_fgi i k); try omega.
    apply (proj2 (hyp1 k)).

    assert (HRfg0 : forall j k, j < k  -> k <= reid 0 -> R (g j) (f k)).
    intros j k lt_jk le_k0. induction k. destruct (lt_n_O _ lt_jk).
    destruct (le_lt_or_eq _ _ (lt_n_Sm_le _ _ lt_jk)) as [HT | HT]. Focus 2.
    rewrite HT. apply (proj2 (hyp1 k)).
    apply (@TrsR _ (f k)). apply IHk; try omega. rewrite (eq_fg0 k); try omega.
    apply (proj2 (hyp1 k)).

    exists f0; exists g0. split. intro i. simpl. unfold f0, g0. split.
    apply HEfg.
    apply (HRfg i); auto. destruct (rec_ch_minP _ HexP i) as [HT _].
    apply (lt_le_trans (reid i) (S (reid i)) (reid (S i))); auto.
    split. exists (reid 0). simpl. auto.
    unfold f0. case_eq (reid 0). left; refl. right.
    rewrite eq_fg0; try omega. apply HRfg0; omega.
  Qed.

End ISModTrans.

End S.
