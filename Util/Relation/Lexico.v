(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-25

lexicographic ordering
*)

Set Implicit Arguments.

From Stdlib Require Import Morphisms Basics.
From CoLoR Require Import SN LogicUtil NatUtil VecUtil VecOrd ListUtil RelUtil.

(****************************************************************************)
(** ** Lexicographic quasi-ordering on pairs. *)

Section lex.

  (** We assume given a set [A] equipped with two relations [gtA] and
  [eqA] satisfying some compatibility condition, and a set [B]
  equipped with a relation [gtB]. *)

  Variables (A B : Type) (gtA eqA : relation A) (gtB : relation B).

  (** Definition of the lexicographic relation. *)

  Inductive lex : relation (prod A B) :=
  | lex1 a a' b b' : gtA a a' -> lex (a,b) (a',b')
  | lex2 a a' b b' : eqA a a' -> gtB b b' -> lex (a,b) (a',b').

  Lemma lex_intro : forall a a' b b',
    gtA a a' \/ (eqA a a' /\ gtB b b') -> lex (a,b) (a',b').

  Proof.
    intros. destruct H. apply lex1. exact H. destruct H. apply lex2.
    exact H. exact H0.
  Qed.

  (** We now prove that [lex] is wellfounded if both [gtA] and [gtB]
  are wellfounded, [eqA] is transitive and [gtA] absorbs [eqA]. *)

  Variables (WF_gtA : WF gtA) (WF_gtB : WF gtB)
    (eqA_trans : Transitive eqA) (Hcomp : eqA @ gtA << gtA).

  Lemma SN_compat : forall a, SN gtA a -> forall a', eqA a a' -> SN gtA a'.

  Proof.
    intros a SN_a a' eqaa'. apply SN_intro. intros a'' gta'a''.
    inversion SN_a. apply H. apply (incl_elim Hcomp). exists a'. auto.
  Qed.

  Lemma lex_SN_eq : forall a b,
    SN lex (a,b) -> forall a', eqA a a' -> SN lex (a',b).

  Proof.
    intros a b SN_ab a' eqaa'. inversion SN_ab. apply SN_intro.
    destruct y as (a'',b'). intro H'.
    inversion H'; subst a'0 b'0 a0 b0; apply H.
    apply lex1. apply (incl_elim Hcomp). exists a'. auto.
    apply lex2. apply (eqA_trans eqaa' H3). exact H5.
  Qed.

  Lemma lex_SN :
    forall a, SN gtA a -> forall b, SN gtB b -> SN lex (a, b).

  Proof.
    induction 1 as [a Ha1 Ha2]. induction 1 as [b Hb1 Hb2]. apply SN_intro.
    destruct y as (a'',b'). intro H. inversion H; subst a'' b'0 a0 b0.
    (* gtA a a' *)
    apply Ha2. exact H1. apply WF_gtB.
    (* eqA a a' /\ gtB b b' *)
    apply (@lex_SN_eq a). 2: exact H3. apply Hb2. exact H5.
  Qed.

  Lemma WF_lex : WF lex.

  Proof.
    unfold WF. destruct x as (a,b). apply lex_SN. apply WF_gtA. apply WF_gtB.
  Qed.

End lex.

(** [symprod] is included in [lex]. *)

Lemma symprod_lex A (gtA : relation A) :
  symprod gtA gtA << lex gtA Logic.eq gtA.

Proof.
  intros t u tu. inversion tu; clear tu; subst.
  apply lex1. hyp. apply lex2. refl. hyp.
Qed.

(** [lex] is monotone wrt inclusion. *)

Global Instance lex_incl A B : Proper (incl ==> incl ==> incl ==> incl) (@lex A B).

Proof.
  intros gtA gtA' gtAgtA' eqA eqA' eqAeqA' gtB gtB' gtBgtB' t u tu.
  inversion tu; clear tu; subst. apply lex1. fo. apply lex2; fo.
Qed.

Global Instance lex_same A B : Proper (same ==> same ==> same ==> same) (@lex A B).

Proof.
  intros gtA1 gtA' [gtAgtA' gtA'gtA] eqA eqA' [eqAeqA' eqA'eqA]
    gtB gtB' [gtBgtB' gtB'gtB]. split; apply lex_incl; fo.
Qed.

(****************************************************************************)
(** ** Type of n-tuples of elements of [A]. *)

Fixpoint prodn n A : Type :=
  match n with
    | 0 => unit
    | S n' => prod A (prodn n' A)
  end.

Fixpoint projn n {A} : prodn n A -> forall i, i<n -> A :=
  match n as n return prodn n A -> forall i, i<n -> A with
    | 0 => fun xs i (hi : i<0) => False_rect _ (Nat.nlt_0_r hi)
    | S n' => fun xs i =>
      match i as i return i<S n' -> A with
        | 0 => fun _ => fst xs
        | S i' => fun hi => projn (snd xs) (NatCompat.lt_S_n hi)
      end
  end.

(****************************************************************************)
(** ** Lexicographic order on tuples. *)

Fixpoint lexn {n A} (eqA gtA : relation A) :=
  match n as n return relation (prodn n A) with
    | 0 => empty_rel
    | S n' => lex gtA eqA (lexn eqA gtA)
  end.

Section lexn.

  Variables (A : Type) (eqA gt : relation A).

  (** Equivalent definition. *)
 
  Lemma lexn_eq : forall n (xs ys : prodn n A), lexn eqA gt xs ys <->
    (exists i (hi : i<n), gt (projn xs hi) (projn ys hi)
      /\ forall j, j<i -> forall hj : j<n, eqA (projn xs hj) (projn ys hj)).

  Proof.
    induction n; simpl prodn.
    (* 0 *)
    intuition auto with *. destruct H as [i [hi _]]. lia.
    (* S *)
    intros [x xs] [y ys]. simpl lexn. split; intro h.
    (* -> *)
    inversion h; clear h; subst.
    ex 0 (Nat.lt_0_succ n). split. simpl projn. hyp. intros. lia.
    rewrite IHn in H4. destruct H4 as [i [hi [h1 h2]]].
    ex (S i) (NatCompat.lt_n_S hi). split.
    simpl. rewrite lt_unique with (h1 := NatCompat.lt_S_n (NatCompat.lt_n_S hi)) (h2:=hi). hyp.
    intros [|j] k hj; simpl. hyp. apply h2. lia.
    (* <- *)
    destruct h as [i [hi [h1 h2]]]. destruct i as [|i].
    apply lex1. hyp. 
    apply lex2. gen (h2 _ (Nat.lt_0_succ i) (Nat.lt_0_succ n)). simpl. auto.
    rewrite IHn. ex i (NatCompat.lt_S_n hi). split. fo.
    intros j ji jn. gen (h2 _ (NatCompat.lt_n_S ji) (NatCompat.lt_n_S jn)). simpl.
    rewrite lt_unique with (h1 := NatCompat.lt_S_n (NatCompat.lt_n_S jn)) (h2:=jn). auto.
  Qed.

  (** Wellfoundedness. *)

  Variables (gt_wf : WF gt) (eqA_trans : Transitive eqA)
    (Hcomp : eqA @ gt << gt).

  Lemma lexn_wf n : WF (lexn (n:=n) eqA gt).

  Proof. induction n; simpl. apply WF_empty_rel. apply WF_lex; hyp. Qed.

End lexn.

(** Monotony wrt incl. *)

Global Instance lexn_incl A : forall n, Proper (incl ==> incl ==> incl) (@lexn n A). 

Proof.
  induction n; simpl. fo.
  intros eqA eqA' eqAeqA' gt gt' gtgt'. apply lex_incl; auto.
  apply IHn; hyp.
Qed.

(****************************************************************************)
(** ** Convert of vector of size [n] into an [n]-tuple. *)

Fixpoint prod_of_vec n A (v : vector A n) :=
  match v in vector _ n return prodn n A with
    | Vnil => tt
    | Vcons x v' => (x, prod_of_vec v')
  end.

Lemma projn_prod_of_vec : forall A n (xs : vector A n) i (hi : i<n),
  projn (prod_of_vec xs) hi = Vnth xs hi.

Proof.
  intro A. induction xs; intros i hi. lia. simpl. destruct i as [|i]; fo.
Qed.

(****************************************************************************)
(** ** Lexicographic order on vectors of fixed length. *)

Definition lexv {n A} (eq gt : relation A) : relation (vector A n) :=
  fun v w => lexn eq gt (prod_of_vec v) (prod_of_vec w).

Section lexv.

  Variables (A : Type) (eq gt : relation A).

  (** Equivalent definition. *)

  Lemma lexv_eq : forall n (xs ys : vector A n), lexv eq gt xs ys <->
    (exists i (hi : i<n), gt (Vnth xs hi) (Vnth ys hi)
      /\ forall j, j<i -> forall hj : j<n, eq (Vnth xs hj) (Vnth ys hj)).

  Proof.
    intros n xs ys. unfold lexv. rewrite lexn_eq.
    split; intros [i [hi [h1 h2]]]; ex i hi; split.
    rewrite !projn_prod_of_vec in h1. hyp.
    intros j ji hj. gen (h2 _ ji hj). rewrite !projn_prod_of_vec. auto.
    rewrite !projn_prod_of_vec. hyp.
    intros j ji hj. rewrite !projn_prod_of_vec. fo.
  Qed.

  (** Wellfoundedness. *)

  Section wf.

    Variables (gt_wf : WF gt) (eq_trans : Transitive eq)
      (Hcomp : eq @ gt << gt).

    Lemma lexv_wf n : WF (lexv (n:=n) eq gt).

    Proof. apply WF_inverse. apply lexn_wf; hyp. Qed.

  End wf.

  (** [lexv eq gt] absorbs [Vforall2 eq]. *)

  Lemma lexv_forall2_l : eq @ gt << gt -> Transitive eq ->
    forall n, Vforall2 eq (n:=n) @ lexv eq gt << lexv eq gt.

  Proof.
    intros gt_eq eq_trans n ts vs [us [tsus usvs]].
    revert usvs. rewrite !lexv_eq. intros [i [hi [h1 h2]]]. ex i hi. split.
    apply gt_eq. exists (Vnth us hi). split.
    apply Vforall2_elim_nth. hyp. hyp.
    intros j ji jn. trans (Vnth us jn). apply Vforall2_elim_nth. hyp. fo.
  Qed.

  Lemma lexv_forall2_r : gt @ eq << gt -> Transitive eq ->
    forall n, lexv eq gt @ Vforall2 eq (n:=n) << lexv eq gt.

  Proof.
    intros gt_eq eq_trans n ts vs [us [tsus usvs]].
    revert tsus. rewrite !lexv_eq. intros [i [hi [h1 h2]]]. ex i hi. split.
    apply gt_eq. exists (Vnth us hi). split.
    hyp. apply Vforall2_elim_nth. hyp.
    intros j ji jn. trans (Vnth us jn). fo. apply Vforall2_elim_nth. hyp.
  Qed.

  (** [lexv eq gt] is invariant by [Vforall2 eq]. *)

  Global Instance lexv_forall2 n : Transitive eq -> Symmetric eq ->
    Proper (eq ==> eq ==> impl) gt ->
    Proper (Vforall2 eq ==> Vforall2 eq ==> impl) (lexv (n:=n) eq gt).

  Proof.
    intros eq_trans eq_sym gt_eq ts ts' tsts' us us' usus'; unfold impl.
    rewrite !lexv_eq. intros [i [i1 [i2 i3]]]. ex i i1. split.
    eapply gt_eq. eapply Vforall2_elim_nth. apply tsts'.
    eapply Vforall2_elim_nth. apply usus'. hyp.
    intros j ji jn.
    rewrite <- (Vforall2_elim_nth _ tsts'), <- (Vforall2_elim_nth _ usus'). fo.
  Qed.

  (** Transitivity. *)

  Lemma lexv_trans n : Transitive eq -> Transitive gt ->
    gt @ eq << gt -> eq @ gt << gt ->
    Transitive (lexv (n:=n) eq gt).

  Proof.
    intros eq_trans gt_trans gt_eq_r gt_eq_l ts us vs. rewrite !lexv_eq.
    intros [i [i1 [i2 i3]]] [j [j1 [j2 j3]]]. destruct (lt_dec i j).
    (* i < j *)
    ex i i1. split. apply gt_eq_r. exists (Vnth us i1). fo.
    intros k ki kn. trans (Vnth us kn). fo. apply j3. lia.
    destruct (eq_nat_dec i j).
    (* i = j *)
    subst j. ex i i1. split.
    trans (Vnth us i1). hyp. rewrite !(Vnth_eq _ i1 j1); auto.
    intros k ki kn. trans (Vnth us kn); fo.
    (* i > j *)
    ex j j1. split. apply gt_eq_l. exists (Vnth us j1). split. firstorder auto with zarith. hyp.
    intros k kj kn. trans (Vnth us kn). apply i3. lia. fo.
  Qed.

End lexv.

(** Monotony wrt incl. *)

Global Instance lexv_incl n A : Proper (incl ==> incl ==> incl) (@lexv n A). 

Proof. intros eq eq' eqeq' gt gt' gtgt' t u. apply lexn_incl; hyp. Qed.

(** [Vrel1] is included in [lexv]. *)

Lemma Vrel1_lexv n A (gt : relation A) :
  Vrel1 (n:=n) gt << lexv Logic.eq gt.

Proof.
  intros t u. rewrite Vrel1_nth_iff, lexv_eq. intros [i [hi [h1 h2]]].
  ex i hi. firstorder auto with zarith.
Qed.

(** [lexv (opt eq) (opt gt)] absorbs [Vforall2_opt eq]. *)

Section Vforall2_opt.

  Variables (A : Type) (eq gt : relation A).

  Lemma lexv_forall2_opt_l : eq @ gt << gt -> Transitive eq -> forall n,
    Vforall2_opt (n:=n) eq @ lexv (opt eq) (opt gt)
    << lexv (opt eq) (opt gt).

  Proof.
    intros gt_eq eq_trans n ts vs [us [tsus usvs]].
    revert usvs. rewrite !lexv_eq. intros [i [hi [h1 h2]]]. ex i hi.
    destruct tsus as [k [k1 [k2 k3]]]. inversion h1; clear h1; subst.
    destruct (le_dec k i).
    (* k <= i *)
    exfalso. assert (a : i - k < n - k). lia.
    gen (Vforall2_elim_nth a k3). rewrite !Vnth_sub, Vnth_eq with (h2:=hi),
      Vnth_eq with (v:=us) (h2:=hi), <- H; try lia.
    intro e; inversion e; clear e; subst. fo.
    (* k >= i *)
    split.
    (* i-th argument is decreasing *)
    assert (a : i < k). lia.
    gen (Vforall2_elim_nth a k2). rewrite !Vnth_sub, Vnth_eq with (h2:=hi),
      Vnth_eq with (v:=us) (h2:=hi), <- H; auto.
    intro e; inversion e; clear e; subst.
    apply opt_intro. apply gt_eq. exists x. fo.
    (* forall j<i, j-th arguments are equivalent *)
    intros j ji jn. gen (h2 _ ji jn). intro e; inversion e; clear e; subst.
    assert (a : j < k). lia.
    gen (Vforall2_elim_nth a k2). rewrite !Vnth_sub, Vnth_eq with (h2:=jn),
      Vnth_eq with (v:=us) (h2:=jn), <- H2; auto.
    intro e; inversion e; clear e; subst.
    apply opt_intro. trans x0; hyp.
  Qed.

  Lemma lexv_forall2_opt_r : gt @ eq << gt -> Transitive eq -> forall n,
    lexv (opt eq) (opt gt) @ Vforall2_opt (n:=n) eq
    << lexv (opt eq) (opt gt).

  Proof.
    intros gt_eq eq_trans n ts vs [us [tsus usvs]].
    revert tsus. rewrite !lexv_eq. intros [i [hi [h1 h2]]]. ex i hi.
    destruct usvs as [k [k1 [k2 k3]]]. inversion h1; clear h1; subst.
    destruct (le_dec k i).
    (* k <= i *)
    exfalso. assert (a : i - k < n - k). lia.
    gen (Vforall2_elim_nth a k3). rewrite !Vnth_sub, Vnth_eq with (h2:=hi),
      Vnth_eq with (v:=vs) (h2:=hi), <- H0; try lia.
    intro e; inversion e; clear e; subst. fo.
    (* k >= i *)
    split.
    (* i-th argument is decreasing *)
    assert (a : i < k). lia.
    gen (Vforall2_elim_nth a k2). rewrite !Vnth_sub, Vnth_eq with (h2:=hi),
      Vnth_eq with (v:=vs) (h2:=hi), <- H0; auto.
    intro e; inversion e; clear e; subst.
    apply opt_intro. apply gt_eq. exists y. fo.
    (* forall j<i, j-th arguments are equivalent *)
    intros j ji jn. gen (h2 _ ji jn). intro e; inversion e; clear e; subst.
    assert (a : j < k). lia.
    gen (Vforall2_elim_nth a k2). rewrite !Vnth_sub, Vnth_eq with (h2:=jn),
      Vnth_eq with (v:=vs) (h2:=jn), <- H3; auto.
    intro e; inversion e; clear e; subst.
    apply opt_intro. trans y0; hyp.
  Qed.

End Vforall2_opt.

(** Monotony of [lexv] wrt arguments. *)

Lemma lexv_mon_arg A (eq gt : relation A) n (ts us : vector A n)
  p (ts' us' : vector A p) :
  lexv eq gt ts us -> lexv eq gt (Vapp ts ts') (Vapp us us').

Proof.
  rewrite !lexv_eq. intros [i [i1 [i2 i3]]].
  assert (hi : i < n + p). lia. ex i hi. split.
  (* i-th argument *)
  rewrite !Vnth_app. destruct (le_gt_dec n i). lia.
  rewrite !Vnth_eq with (h1:=g) (h2:=i1); auto.
  (* arguments before i-th *)
  intros j ji hj. rewrite !Vnth_app. destruct (le_gt_dec n j). lia. fo.
Qed.

(** Monotony of [Rof lexv (Vopt_filter M)] when [M] is sorted. *)

Lemma lexv_opt_filter_sorted_mon_arg A (eq gt : relation A)
  n (ks : vector nat n) (ks_sorted : sorted ks) p (ts : vector A p)
  q (us : vector A q) p' (ts' : vector A p') q' (us' : vector A q') :
  lexv (opt eq) (opt gt) (Vopt_filter ks ts) (Vopt_filter ks us) ->
  lexv (opt eq) (opt gt) (Vopt_filter ks (Vapp ts ts'))
                           (Vopt_filter ks (Vapp us us')).

Proof.
  rewrite !lexv_eq. intros [i [i1 [i2 i3]]]. ex i i1. split.
  (* i-th argument *)
  revert i2. rewrite !Vnth_opt_filter.
  destruct (lt_dec (Vnth ks i1) p); destruct (lt_dec (Vnth ks i1) q);
    destruct (lt_dec (Vnth ks i1) (p+p'));
      destruct (lt_dec (Vnth ks i1) (q+q'));
        try (refl || (exfalso; lia) || by (intro h; inversion h)).
  rewrite !Vnth_app.
  destruct (le_gt_dec p (Vnth ks i1)); destruct (le_gt_dec q (Vnth ks i1));
    try (refl || (exfalso; lia) || by (intro h; inversion h)).
  rewrite Vnth_eq with (h1:=l) (h2:=g), Vnth_eq with (h1:=l0) (h2:=g0); auto.
  (* arguments before i-th *)
  intros j ji hj. gen (i3 _ ji hj). rewrite !Vnth_opt_filter.
  destruct (lt_dec (Vnth ks hj) p); destruct (lt_dec (Vnth ks hj) q);
    destruct (lt_dec (Vnth ks hj) (p+p'));
      destruct (lt_dec (Vnth ks hj) (q+q'));
        try (refl || (exfalso; lia) || by (intro h; inversion h)).
  rewrite !Vnth_app.
  destruct (le_gt_dec p (Vnth ks hj)); destruct (le_gt_dec q (Vnth ks hj));
    try (refl || (exfalso; lia) || by (intro h; inversion h)).
  rewrite Vnth_eq with (h1:=l) (h2:=g), Vnth_eq with (h1:=l0) (h2:=g0); auto.
Qed.

(****************************************************************************)
(** ** Lexicographic order on lists of bounded length. *)

Section lexl.

  Variables (m : nat) (A : Type) (eq gt : relation A).

  Inductive lexl : relation (list A) :=
  | lexl_intro : forall (xs ys : list A) i
                        (im : i < m) (ix : i < length xs) (iy : i < length ys),
      gt (ith ix) (ith iy)
      -> (forall j (ji : j < i) (jx : j < length xs) (jy : j < length ys),
             eq (ith jx) (ith jy))
      -> lexl xs ys.

  Variables (gt_wf : WF gt) (eq_trans : Transitive eq)
            (Hcomp : eq @ gt << gt).

  Lemma lexl_wf : WF lexl.

  Proof.
    assert (e : lexl << Rof (lexv (opt eq) (opt gt)) (vec_opt_of_list m)).
    intros x y xy. unfold Rof. rewrite lexv_eq. inversion xy; subst. ex i im.
    split. rewrite Vnth_vec_opt_of_list with (il:=ix),
      Vnth_vec_opt_of_list with (il:=iy). apply opt_intro. hyp.
    intros j ji jm. assert (jx : j < length x). lia.
    assert (jy : j < length y). lia.
    rewrite Vnth_vec_opt_of_list with (il:=jx),
      Vnth_vec_opt_of_list with (il:=jy). apply opt_intro.
    apply H0; hyp.
    rewrite e. apply WF_inverse. apply lexv_wf. apply wf_opt. hyp.
    class. apply opt_absorbs_left. hyp.
  Qed.

End lexl.

Global Instance lexl_incl m A : Proper (incl ==> incl ==> incl) (@lexl m A). 

Proof.
  intros eq eq' eqeq' gt gt' gtgt' xs ys h. destruct h.
  eapply lexl_intro. apply im. apply gtgt'. apply H.
  intros j ji jx jy. apply eqeq'. apply H0. hyp.
Qed.

(****************************************************************************)
(** ** Lexicographic ordering on dependent pairs. *)

Section lexd.

  Variables (A : Type) (B : A -> Type).

  Section def.

    Variables (gtA : relation A) (gtB : forall a : A, relation (B a)).

    Inductive lexd : relation (sigT B) :=
    | lexdl a a' (b : B a) (b' : B a') : gtA a a' -> lexd (existT b) (existT b')
    | lexdr a (b b' : B a) : gtB b b' -> lexd (existT b) (existT b').

  End def.

  Lemma lexd_incl : forall gt1 gt1', gt1 << gt1'
    -> forall gt2 gt2', (forall a, gt2 a << gt2' a)
    -> lexd gt1 gt2 << lexd gt1' gt2'.

  Proof.
    intros gt1 gt1' h1 gt2 gt2' h2 a a'.
    intro aa'. inversion aa'; subst.
    apply lexdl. apply h1. hyp.
    apply lexdr. apply h2. hyp.
  Qed.

End lexd.
