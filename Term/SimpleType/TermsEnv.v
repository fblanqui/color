(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-27

Operations on environments of terms of simply typed
lambda-calculus are introduced in this file.
*)

Set Implicit Arguments.

From CoLoR Require Import RelExtras ListExtras TermsLifting LogicUtil OptUtil.
From Coq Require Import Arith Setoid Morphisms Lia.

Module TermsEnv (Sig : TermsSig.Signature).

  Module Export TL := TermsLifting.TermsLifting Sig.

  Definition emptyEnv E := forall p, E |= p :! .

  Lemma varD_tail : forall E A i, E |= S i := A -> tail E |= i := A.

  Proof. intros; destruct E; trivial. inversion H. Qed.

  Lemma varD_tail_rev : forall E A i, tail E |= i := A -> E |= S i := A.

  Proof. intros; destruct E; trivial. destruct i; trivial. Qed.

  Lemma varUD_tail : forall E i, E |= S i :! -> tail E |= i :! .

  Proof. intros; destruct E; trivial. inversion H; destruct i; trivial. Qed.

  Lemma varUD_tail_rev : forall E i, tail E |= i :! -> E |= S i :! .

  Proof. intros; destruct E; trivial. destruct i; trivial. Qed.

  Lemma varD_UD_absurd : forall E p A, E |= p := A -> E |= p :! -> False.

  Proof. intros E p A EpA Ep. destruct Ep; unfold VarD in *; try_solve. Qed.

  Definition equiv E x E' x' :=
    (forall A, E |= x := A <-> E' |= x' := A) /\ (E |= x :! <-> E' |= x' :!).

  Lemma split_beyond : forall E k n p, p < k -> length E <= p ->
    (initialSeg E k ++ copy n None ++ finalSeg E k) |= p :! .

  Proof.
    intros; unfold VarUD.
    rewrite nth_app_right; autorewrite with datatypes.
    destruct (le_gt_dec n (p - Min.min k (length E))).
    rewrite nth_app_right; autorewrite with datatypes; trivial.
    left; apply nth_beyond; autorewrite with datatypes; trivial.
    simpl; lia.
    rewrite nth_app_left; autorewrite with datatypes; try_solve.
    set (w := Min.le_min_r k (length E)); lia.
  Qed.

  Lemma equiv_copy_split_l : forall E k p n, p < k ->
    equiv E p (initialSeg E k ++ copy n None ++ finalSeg E k) p.

  Proof.
    intros; unfold equiv.
    destruct (le_gt_dec (length E) p).
    set (w := split_beyond E n H l).
    split; split; intro; trivial.
    set (ww := nth_some E p H0); lia.
    exfalso; apply varD_UD_absurd with 
      (initialSeg E k ++ copy n None ++ finalSeg E k) p A; trivial.
    left; apply nth_beyond; trivial.
    unfold VarD, VarUD. rewrite !nth_app_left, initialSeg_nth; fo.
    autorewrite with datatypes.
    apply Min.min_case2; trivial.
  Qed.

  Lemma copy_split_l_varD : forall E k p n A, p < k -> E |= p := A ->
    (initialSeg E k ++ copy n None ++ finalSeg E k) |= p := A.

  Proof.
    intros. apply (proj1 (proj1 (equiv_copy_split_l E n H) A)); trivial.
  Qed.

  Lemma copy_split_l_varUD : forall E k p n, p < k -> E |= p :! ->
    (initialSeg E k ++ copy n None ++ finalSeg E k) |= p :! .

  Proof.
    intros. apply (proj1 (proj2 (equiv_copy_split_l E n H))); trivial.
  Qed.

  Lemma copy_split_l_rev_varD : forall E k p n A, p < k ->
    (initialSeg E k ++ copy n None ++ finalSeg E k) |= p := A -> E |= p := A.

  Proof.
    intros. apply (proj2 (proj1 (equiv_copy_split_l E n H) A)); trivial.
  Qed.

  Lemma copy_split_l_rev_varUD : forall E k p n, p < k ->
    (initialSeg E k ++ copy n None ++ finalSeg E k) |= p :! -> E |= p :! .

  Proof.
    intros. apply (proj2 (proj2 (equiv_copy_split_l E n H))); trivial.
  Qed.

  Lemma equiv_copy_split_r : forall E k n p p', p >= k -> p' = p + n ->
    equiv E p (initialSeg E k ++ copy n None ++ finalSeg E k) p'.

  Proof.
    intros; unfold equiv, VarD, VarUD; rewrite H0.
    rewrite !nth_app_right; autorewrite with datatypes.
    destruct (le_gt_dec k (length E)).
    replace (p + n - Min.min k (length E) - n) with (p - k).
    split; split; intro; solve
      [ replace (k + (p - k)) with p; [trivial | lia]
      | replace p with (k + (p - k)); [trivial | lia]
      ].
    rewrite Min.min_l; lia.
    replace (p + n - Min.min k (length E) - n) with (p - length E).
    split; split; intro; try solve 
      [ left; apply nth_beyond; lia
      | set (w := nth_some E _ H1); lia ].
    rewrite Min.min_r; lia.
    set (w := Min.le_min_l k (length E)); lia.
    set (w := Min.le_min_l k (length E)); lia.
  Qed.

  Lemma copy_split_r_varD : forall E k n p p' A, p >= k -> p' = p + n ->
    E |= p := A -> (initialSeg E k ++ copy n None ++ finalSeg E k) |= p' := A.

  Proof.
    intros. apply (proj1 (proj1 (equiv_copy_split_r E n H H0) A)); trivial.
  Qed.

  Lemma copy_split_r_varUD : forall E k n p p', p >= k -> p' = p + n ->
    E |= p :! -> (initialSeg E k ++ copy n None ++ finalSeg E k) |= p' :! .

  Proof.
    intros. apply (proj1 (proj2 (equiv_copy_split_r E n H H0))); trivial.
  Qed.

  Lemma copy_split_r_rev_varD : forall E k n p p' A, p >= k -> p' = p + n ->
    (initialSeg E k ++ copy n None ++ finalSeg E k) |= p' := A -> E |= p := A.

  Proof.
    intros. apply (proj2 (proj1 (equiv_copy_split_r E n H H0) A)); trivial.
  Qed.

  Lemma copy_split_r_rev_varUD : forall E k n p p', p >= k -> p' = p + n ->
    (initialSeg E k ++ copy n None ++ finalSeg E k) |= p' :! -> E |= p :! .

  Proof.
    intros. apply (proj2 (proj2 (equiv_copy_split_r E n H H0))); trivial.
  Qed.

  Lemma equiv_hole_l : forall E k p, p < k ->
    equiv E p (initialSeg E k ++ finalSeg E (S k)) p.

  Proof.
    intros; unfold equiv, VarD, VarUD.
    destruct (le_gt_dec (length E) p).
    assert (p >= length (initialSeg E k ++ finalSeg E (S k))).
    autorewrite with datatypes using simpl.
    lia.
    split; split; intro; try solve [left; apply nth_beyond; trivial].
    set (ww := nth_some E p H1); lia.
    exfalso; apply varD_UD_absurd with 
      (initialSeg E k ++ finalSeg E (S k)) p A; trivial.
    left; apply nth_beyond; trivial.
    unfold VarD, VarUD. rewrite !nth_app_left, initialSeg_nth; fo.
    autorewrite with datatypes.
    apply Min.min_case2; trivial.
  Qed.

  Lemma hole_l_varD : forall E k p A, p < k -> E |= p := A ->
    (initialSeg E k ++ finalSeg E (S k)) |= p := A.

  Proof. intros. apply (proj1 (proj1 (equiv_hole_l E H) A)); trivial. Qed.

  Lemma hole_l_varUD : forall E k p, p < k -> E |= p :! ->
    (initialSeg E k ++ finalSeg E (S k)) |= p :! .

  Proof. intros. apply (proj1 (proj2 (equiv_hole_l E H))); trivial. Qed.

  Lemma hole_l_rev_varD : forall E k p A, p < k ->
    (initialSeg E k ++ finalSeg E (S k)) |= p := A -> E |= p := A.

  Proof. intros. apply (proj2 (proj1 (equiv_hole_l E H) A)); trivial. Qed.

  Lemma hole_l_rev_varUD : forall E k p, p < k ->
    (initialSeg E k ++ finalSeg E (S k)) |= p :! -> E |= p :! .

  Proof. intros. apply (proj2 (proj2 (equiv_hole_l E H))); trivial. Qed.

  Lemma equiv_hole_r : forall E k p p', p > k -> p = S p' ->
    equiv E p (initialSeg E k ++ finalSeg E (S k)) p'.

  Proof.
    intros; unfold equiv, VarD, VarUD; rewrite H0.
    rewrite nth_app_right; autorewrite with datatypes.
    destruct (le_gt_dec k (length E)).
    replace (p' - Min.min k (length E)) with (p' - k).
    split; split; intro; solve
      [ replace (S k + (p' - k)) with (S p'); [trivial | lia]
      | replace (S p') with (S k + (p' - k)); [trivial | lia]
      ].
    rewrite Min.min_l; lia.
    replace (p' - Min.min k (length E)) with (p' - (length E)).
    split; split; intro; solve
      [ left; apply nth_beyond; lia
      | set (w := nth_some E _ H1); lia
      ].
    rewrite Min.min_r; lia.
    set (w := Min.le_min_l k (length E)); lia.
  Qed.

  Lemma hole_r_varD : forall E k p p' A, p > k -> p = S p' -> E |= p := A ->
    (initialSeg E k ++ finalSeg E (S k)) |= p' := A.

  Proof. intros. apply (proj1 (proj1 (equiv_hole_r E H H0) A)); trivial. Qed.

  Lemma hole_r_varUD : forall E k p p', p > k -> p = S p' -> E |= p :! ->
    (initialSeg E k ++ finalSeg E (S k)) |= p' :! .

  Proof. intros. apply (proj1 (proj2 (equiv_hole_r E H H0))); trivial. Qed.

  Lemma hole_r_rev_varD : forall E k p p' A, p > k -> p = S p' ->
    (initialSeg E k ++ finalSeg E (S k)) |= p' := A -> E |= p := A.

  Proof. intros. apply (proj2 (proj1 (equiv_hole_r E H H0) A)); trivial. Qed.

  Lemma hole_r_rev_varUD : forall E k p p', p > k -> p = S p' ->
    (initialSeg E k ++ finalSeg E (S k)) |= p' :! -> E |= p :! .

  Proof. intros. apply (proj2 (proj2 (equiv_hole_r E H H0))); trivial. Qed.

  Lemma emptyEnv_empty : emptyEnv EmptyEnv.

  Proof. intro p; destruct p; try_solve. Qed.

  Lemma emptyEnv_tail : forall E, emptyEnv (None :: E) -> emptyEnv E.

  Proof. intros; intro p. apply (H (S p)). Qed.

  Lemma tail_emptyEnv : forall E, emptyEnv E -> emptyEnv (tail E).

  Proof. intros; intro p. destruct (H (S p)); destruct E; try_solve. Qed.

  Lemma emptyEnv_cons : forall E, emptyEnv E -> emptyEnv (None :: E).

  Proof. intros. intro p; destruct p. right; try_solve. apply (H p). Qed.

  Lemma emptyEnv_copyNone : forall k, emptyEnv (copy k None).

  Proof.
    intros; intro p. destruct (le_gt_dec k p).
    left; apply nth_beyond; autorewrite with datatypes using trivial.
    right; apply nth_copy_in; trivial.
  Qed.

  Lemma emptyEnv_absurd : forall a E P, emptyEnv (Some a :: E) -> P.

  Proof.
    intros. exfalso.
    assert ((Some a :: E) |= 0 := a). auto with terms.
    destruct (H 0); try_solve.
  Qed.

  Definition isNotEmpty (e: option SimpleType) := e <> None.

  Lemma isNotEmpty_dec : forall e, {isNotEmpty e} + {~isNotEmpty e}.

  Proof. intro e; destruct e. left; try_solve. right; try_solve. Qed.

  Definition dropEmptySuffix (E: Env) : Env :=
    match find_last isNotEmpty isNotEmpty_dec E with
    | None => EmptyEnv
    | Some i => initialSeg E (S i)
    end.

  Lemma dropSuffix_decl : forall E x A,
    E |= x := A -> dropEmptySuffix E |= x := A.

  Proof.
    intros. destruct (find_last_last isNotEmpty isNotEmpty_dec E x H)
      as [q [Eq qx]]; try_solve.
    unfold dropEmptySuffix. rewrite Eq.
    unfold VarD; rewrite initialSeg_nth; trivial. lia.
  Qed.

  Lemma dropSuffix_decl_rev : forall E x A,
    dropEmptySuffix E |= x := A -> E |= x := A.

  Proof.
    intros. unfold dropEmptySuffix in H.
    destruct (option_dec (find_last isNotEmpty isNotEmpty_dec E))
      as [Ee | [p Ep]].
    rewrite Ee in H.
    destruct x; try_solve.
    rewrite Ep in H. unfold VarD; apply initialSeg_prefix with (S p); trivial.
  Qed.

  Lemma dropSuffix_last : forall E (E' := dropEmptySuffix E), 
    length E' = 0 \/ exists A, E' |= pred (length E') := A.

  Proof.
    intro E. unfold dropEmptySuffix.
    destruct (option_dec (find_last isNotEmpty isNotEmpty_dec E))
      as [Ee | [p Ep]].
    rewrite Ee; left; trivial.
    rewrite Ep; right.
    destruct (find_last_ok isNotEmpty isNotEmpty_dec E Ep) as [w [pEpw wSome]].
    destruct w.
    exists s.
    autorewrite with datatypes.
    rewrite Min.min_l.    
    unfold VarD.
    rewrite initialSeg_nth; trivial.
    auto with arith.
    assert (nth_error E p <> None); try_solve.
    set (w := proj1 (nth_in E p) H).
    lia.
    destruct wSome; trivial.
  Qed.

  Fixpoint env_compose (E F: Env) : Env :=
    match E, F with
    | nil, nil => EmptyEnv
    | L, nil => L
    | nil, L => L
    | _::E', Some a::F' => Some a :: env_compose E' F'
    | e1::E', None::F' => e1 :: env_compose E' F'
    end.

  Notation "E [+] F" := (env_compose E F) (at level 50, left associativity).

  Lemma env_sum_empty_l : forall E, EmptyEnv [+] E = E.

  Proof. induction E; auto. Qed.

  Lemma env_sum_empty_r : forall E, E [+] EmptyEnv = E.

  Proof. induction E; auto. Qed.

  #[global] Hint Rewrite env_sum_empty_l env_sum_empty_r : terms.

  Lemma env_sum_assoc : forall (E1 E2 E3: Env),
    E1 [+] E2 [+] E3 = E1 [+] (E2 [+] E3).

  Proof.
    induction E1; intros. 
    autorewrite with terms using trivial.
    destruct E2; destruct E3; autorewrite with terms using trivial.
    destruct o; destruct o0; simpl; rewrite IHE1; trivial.
  Qed.

  Lemma tail_distr_sum : forall E1 E2, tail (E1 [+] E2) = tail E1 [+] tail E2.

  Proof.
    intros.
    destruct E1; destruct E2; try destruct E2; try destruct o0; try_solve.
    rewrite env_sum_empty_r; trivial.
  Qed.

  Lemma env_sum_ln_rn : forall E1 E2 x,
    E1 |= x :! -> E2 |= x :! -> E1 [+] E2 |= x :!.

  Proof.
    induction E1; destruct E2 as [|a' E2]; trivial.
    destruct x.
    inversion 1; inversion 1; destruct a'; auto.
    unfold VarUD; inversion 1; inversion 1; destruct a'; 
      simpl in *; apply IHE1; trivial.
  Qed.

  Lemma env_sumn_ln : forall x E1 E2, E1 [+] E2 |= x :! -> E1 |= x :! .

  Proof.
    induction x.
    destruct E1; destruct E2; try destruct o0; try_solve.
    inversion 1; try_solve.
    destruct E1; destruct E2; try destruct o0; try_solve;
      revert IHx; unfold VarUD; simpl; intro IHx; gen (IHx E1 E2); tauto.
  Qed.

  Lemma env_sumn_rn : forall x E1 E2, E1 [+] E2 |= x :! -> E2 |= x :! .

  Proof.
    induction x.
    destruct E1; destruct E2; try destruct o0; try_solve.
    destruct E1; destruct E2; try destruct o0; try_solve;
      revert IHx; unfold VarUD; simpl; intro IHx; gen (IHx E1 E2); tauto.
  Qed.

  Lemma env_sum_ry : forall E1 E2 x A, E2 |= x := A -> E1 [+] E2 |= x := A.

  Proof.
    induction E1; destruct E2; intros x A E_comp;
      try solve [unfold VarD; destruct x; simpl; intros; discr]. 
    auto.
    unfold VarD; simpl.
    destruct o; destruct x; simpl; intros; 
      solve [trivial | discr | apply IHE1; trivial].
  Qed.

  Lemma env_sum_right : forall E1 E2 x A1 A2,
    E1 |= x := A1 -> E2 [+] E1 |= x := A2 -> A1 = A2.

  Proof.
    induction E1; destruct E2; destruct x; unfold VarD; try_solve;
      try congruence.
    intros A1 A2 aA1.
    inversion aA1; congruence.
    intros A1 A2 E1x.
    destruct a; intro H; apply IHE1 with E2 x; trivial.
  Qed.

  Lemma env_sum_ly_rn : forall E1 E2 x A,
    E1 |= x := A -> E2 |= x :! -> E1 [+] E2 |= x := A.

  Proof.
    induction E1; destruct E2 as [|a' E2]; trivial.
    inversion 1; destruct x; discr.
    inversion 1; inversion 1; destruct a'; destruct x; unfold VarD; 
      simpl in *; solve [trivial | discr | apply IHE1; trivial].
  Qed.

  Lemma env_sum_length : forall El Er,
    length (El [+] Er) = Max.max (length El) (length Er).

  Proof.
    induction El; intros.
    simpl; destruct Er; trivial.
    simpl; destruct Er; trivial.
    destruct o; simpl; rewrite IHEl; trivial.
  Qed.

  Definition env_comp_on E F x : Prop :=
    forall A B, E |= x := A -> F |= x := B -> A = B.

  Lemma env_comp_on_sym : forall E1 E2 x,
    env_comp_on E1 E2 x -> env_comp_on E2 E1 x.

  Proof. fo. Qed.

  Definition env_comp E F : Prop := forall x, env_comp_on E F x.

  Notation "E [<->] F" := (env_comp E F) (at level 70).

  Lemma env_comp_refl : forall E, E [<->] E.

  Proof. intros E x A B. unfold VarD; congruence. Qed.

  Lemma env_comp_sym : forall E1 E2, E1 [<->] E2 -> E2 [<->] E1.

  Proof. intros E1 E2 E1E2 x A B E2x E1x. sym; apply (E1E2 x); trivial. Qed.

  Lemma env_comp_empty : forall E, E [<->] EmptyEnv.

  Proof. intros E x A B. destruct x; try_solve. Qed.

  Lemma env_comp_empty_r : forall E, EmptyEnv [<->] E.

  Proof. intros; apply env_comp_sym; apply env_comp_empty. Qed.

  Lemma env_comp_dropSuffix : forall E1 E2,
    E1 [<->] dropEmptySuffix E2 -> E1 [<->] E2.

  Proof.
    intros; intros p A B Dl Dr. apply (H p); trivial.
    apply dropSuffix_decl; trivial.
  Qed.

  #[global] Hint Immediate env_comp_refl env_comp_empty env_comp_empty_r : terms.

  Lemma env_comp_tail : forall e1 e2 E1 E2,
    (e1::E1) [<->] (e2::E2) -> E1 [<->] E2.

  Proof.
    unfold env_comp. intros e1 e2 E1 E2 E_comp x A B E1_x E2_x.
    apply (E_comp (S x) A B); trivial.
  Qed.

  Lemma env_comp_cons : forall e1 e2 E1 E2, E1 [<->] E2 ->
    (e1 = e2 \/ e1 = None \/ e2 = None) -> (e1::E1) [<->] (e2::E2).

  Proof.
    unfold env_comp.
    intros e1 e2 E1 E2 E_comp e1e2 x A B E1_x E2_x.
    destruct e1e2 as [e1e2 | [e1e2 | e1e2]];
      first [rewrite e1e2 in E1_x | rewrite e1e2 in E2_x];
      destruct x; unfold VarD in *; simpl in *;
      solve [congruence | discr | apply E_comp with x; trivial].
  Qed.

  Lemma env_comp_single : forall A x E, (E |= x :! \/ E |= x := A) ->
    (copy x None ++ A [#] EmptyEnv) [<->] E.

  Proof.
    intros; intros p B C Dl Dr.
    destruct (lt_eq_lt_dec p x) as [[p_x | p_x] | p_x].
    exfalso; apply (varD_UD_absurd Dl).
    right; unfold VarUD.
    rewrite nth_app_left.
    apply nth_copy_in; trivial.
    autorewrite with datatypes using trivial.
    inversion H.
    exfalso; apply (varD_UD_absurd Dr).
    rewrite p_x; trivial.
    rewrite <- p_x in H0.
    inversion Dl.
    assert (A = B).
    cut ((copy x None ++ A[#]EmptyEnv) |= p := B); trivial.
    unfold VarD.
    rewrite nth_app_right; autorewrite with datatypes using try lia.
    rewrite p_x; rewrite <- minus_n_n.
    intro D; inversion D; trivial.
    inversion Dr; inversion H0; try_solve.
    exfalso; apply (varD_UD_absurd Dl).
    left; unfold VarUD.
    rewrite nth_app_right; autorewrite with datatypes.
    cut (p - x > 0); try lia.
    destruct (p - x); intro; try solve [lia].
    destruct n; trivial.
    lia.
  Qed.

  #[global] Hint Resolve env_comp_cons : terms.

  Lemma env_sum_ly : forall E1 E2 x A, env_comp_on E1 E2 x ->
    E1 |= x := A ->  E1 [+] E2 |= x := A.

  Proof.
    intros; destruct (isVarDecl_dec E2 x) as [[B E2x] | E2xn].
    unfold VarD; rewrite (env_sum_ry E1 E2x).
    assert (A = B); [apply H; trivial | congruence].
    apply env_sum_ly_rn; trivial.
  Qed.

  Lemma typing_ext_env_l : forall Pt E E' A,
    E |- Pt := A ->  E' [+] E |- Pt := A.

  Proof.
    induction Pt.
     (* variable *)
    intros E E' A Ex.
    constructor.
    inversion Ex.
    apply env_sum_ry; trivial.
     (* function symbol *)
    inversion 1; constructor.
     (* abstraction *)
    intros E E' a TypAbs.
    inversion TypAbs.
    constructor.
    change (decl A (E'[+]E)) with (decl A E' [+] decl A E).
    apply IHPt; trivial.
     (* application *)
    intros E E' A TypApp.
    inversion TypApp.
    constructor 4 with A0.
    apply IHPt1; trivial.
    apply IHPt2; trivial.
  Qed.

  Lemma typing_ext_env_r : forall Pt E E' A,
    E [<->] E' -> E |- Pt := A -> E [+] E' |- Pt := A.

  Proof.
    induction Pt.
     (* variable *)
    intros E E' A envC Ex.
    constructor.
    inversion Ex.
    apply env_sum_ly; trivial.
     (* function symbol *)
    inversion 2; constructor.
     (* abstraction *)
    intros E E' a EE' TypAbs.
    inversion TypAbs.
    constructor.
    change (decl A (E [+] E')) with (decl A E [+] decl A E').
    apply IHPt; trivial.
    unfold decl; apply env_comp_cons; auto.
     (* application *)
    intros E E' A EE' TypApp.
    inversion TypApp.
    constructor 4 with A0.
    apply IHPt1; trivial.
    apply IHPt2; trivial.
  Qed.

  Fixpoint env_subtract (E F: Env) : Env :=
  match E, F with
  | nil, _ => EmptyEnv
  | E, nil => E
  | None :: E', _ :: F' => None :: env_subtract E' F'
  | Some e :: E', None :: F' => Some e :: env_subtract E' F'
  | Some e :: E', Some f :: F' => None :: env_subtract E' F'
  end.

  Notation "E [-] F" := (env_subtract E F) (at level 50, left associativity).

  Lemma env_sub_empty : forall E, E [-] EmptyEnv = E.

  Proof. destruct E; trivial. destruct o; trivial. Qed.

  #[global] Hint Rewrite env_sub_empty : terms.

  Lemma env_sub_Empty : forall E1 E2, emptyEnv E2 -> E1 [-] E2 = E1.

  Proof.
    induction E1; trivial.
    intros E2 E2_empty; simpl.
    destruct a; destruct E2; try destruct o; trivial; try solve [
      rewrite IHE1; [trivial | apply emptyEnv_tail; trivial]
    | eapply emptyEnv_absurd; eauto
    ].
  Qed.

  Lemma env_sub_ln : forall E E' x, E |= x :! -> E [-] E'  |= x :!.

  Proof.
    induction E; destruct E' as [|a' E']; intros; trivial.
    destruct a; trivial.
    inversion H; destruct x; destruct a; destruct a'; simpl in *; 
      solve [ discr 
            | auto 
	    | unfold VarUD; destruct (IHE E' x); auto ].
  Qed.

  Lemma env_sub_ry : forall E E' x A, E' |= x := A -> E [-] E' |= x :!.

  Proof.
    induction E; destruct E' as [|a' E']; intros; 
      try solve [inversion H; destruct x; simpl in *; discr].
    destruct x; unfold VarUD; auto.
    destruct x.
    destruct a; destruct a'; unfold VarUD; simpl; auto.
    inversion H.
    unfold VarD in H; simpl in H.
    simpl; destruct a; destruct a'; unfold VarUD;
      destruct (IHE E' x A); auto.
  Qed.

  Lemma env_sub_ly_rn : forall E E' x A,
    E |= x := A -> E' |= x :! -> E [-] E' |= x := A.

  Proof.
    induction E; destruct E' as [|a' E']; intros;
      try solve [inversion H; destruct x; simpl in *; discr].
    simpl; destruct a; trivial.
    destruct x.
    destruct a; destruct a'; unfold VarD in *; inversion H0; 
      simpl in *; solve [discr | trivial].
    inversion H.
    simpl; destruct a; destruct a'; unfold VarD;
      simpl; apply IHE; trivial.
  Qed.

  Lemma env_sub_suby_rn : forall E E' x A, E [-] E' |= x := A -> E' |= x :! .

  Proof.
    intros E E' x A EE'x.
    destruct (isVarDecl_dec E' x) as [[C E'x] | E'n]; trivial.
    exfalso; apply varD_UD_absurd with (E [-] E') x A; trivial.
    apply env_sub_ry with C; trivial.
  Qed.

  Lemma env_sub_suby_ly : forall E E' x A, E [-] E' |= x := A -> E |= x := A.

  Proof.
    intros E E' x A EE'x.
    destruct (isVarDecl_dec E x) as [[B Ex] | En].
    set (E'n := env_sub_suby_rn E E' EE'x).
    set (w := env_sub_ly_rn Ex E'n).
    assert (A = B).
    unfold VarD in *; congruence.
    rewrite H; trivial.
    set (w := env_sub_ln E' En).
    inversion w; unfold VarD in EE'x; congruence.
  Qed.

  Lemma env_sum_double : forall E, E [+] E = E.

  Proof. induction E; auto. destruct a; simpl; congruence. Qed.

  #[global] Hint Rewrite env_sum_double : terms.

  Lemma env_comp_sum_comp_right : forall E1 E2 E3,
    E1 [<->] E2 [+] E3 -> E1 [<->] E3.

  Proof.
    intros E1 E2 E3 E1_23 p A B E1_pA E3_pB.
    exact (E1_23 p A B E1_pA (env_sum_ry E2 E3_pB)).
  Qed.

  Lemma env_comp_ext_l : forall E1 E2, E1 [+] E2 [<->] E2.

  Proof.
    intros E1 E2 p A B E1E2_pA E2_pB.
    set (hint := env_sum_ry E1 E2_pB).
    inversion E1E2_pA.
    inversion hint.
    try_solve.
  Qed.

  Lemma env_comp_sub : forall E1 E2 E3, E1 [<->] E2 -> E1 [-] E3 [<->] E2.

  Proof.
    induction E1; auto.
    intros E2 E3 E12 p A B.
    destruct p; unfold VarD.
    destruct a; destruct E3; destruct E2; 
      try destruct o; try destruct o0; solve 
    [
      try_solve 
    | intros sA sB;
      inversion sA as [s_A]; rewrite <- s_A;
      inversion sB as [s_B]; rewrite <- s_B;
      apply (E12 0); unfold VarD; trivial
    ].
    destruct a; destruct E3; destruct E2;
      try destruct o; try destruct o0; try solve 
    [
      try_solve 
    | apply (E12 (S p) A B)
    | apply (IHE1 E2 E3 (env_comp_tail E12) p A B)
    ].
  Qed.

  Lemma env_sub_varDecl : forall E1 E2 p A,
    E1 [-] E2 |= p := A -> E1 |= p := A /\ E2 |= p :!.

  Proof.
    intros E F p A EFp.
    destruct (isVarDecl_dec F p) as [[B Fp] | Fp].
    assert (EFn: E [-] F |= p :!).
    apply env_sub_ry with B; trivial.
    unfold VarD in *.
    inversion EFn; congruence.
    split; trivial.
    apply env_sub_suby_ly with F; trivial.
  Qed.

  Lemma env_sum_varDecl : forall E1 E2 p A, E1 [+] E2 |= p := A ->
    {E1 |= p := A /\ E2 |= p :!} + {E2 |= p := A}.

  Proof.
    intros E F p A EFp.
    destruct (isVarDecl_dec F p) as [[B Fp] | Fn].
    right.
    set (w := env_sum_ry E Fp).
    assert (A = B).
    unfold VarD in *; congruence.
    rewrite H; trivial.
    left; split; trivial.
    destruct (isVarDecl_dec E p) as [[B Ep] | En].
    set (w := env_sum_ly_rn Ep Fn).
    assert (A = B).
    unfold VarD in *; congruence.
    rewrite H; trivial.
    set (w := env_sum_ln_rn En Fn).
    inversion w; unfold VarD in EFp; congruence.
  Qed.

  Lemma env_comp_sum_comm : forall E1 E2, E1 [<->] E2 -> E1 [+] E2 = E2 [+] E1.

  Proof.
    induction E1.
    destruct E2; try_solve.
    destruct E2.
    destruct E1; try_solve.
    intro E12c.
    set (IH := IHE1 E2 (env_comp_tail E12c)).
    destruct a; destruct o; simpl; try rewrite IH; trivial.
    rewrite (E12c 0 s s0); unfold VarD; trivial.
  Qed. 

  Lemma env_comp_sum : forall E1 E2 E3,
    E1 [<->] E2 -> E1 [<->] E3 -> E1 [<->] E2 [+] E3.

  Proof.
    induction E1.
    intros; apply env_comp_sym; apply env_comp_empty.
    intros E2 E3 E12 E13.
    destruct E2.
    rewrite env_sum_empty_l; trivial.
    destruct E3.
    rewrite env_sum_empty_r; trivial.
    destruct o0; simpl.
    apply env_comp_cons.
    apply IHE1; eapply env_comp_tail; eauto.
    destruct a; try_solve.
    left; rewrite (E13 0 s0 s); try_solve.
    apply env_comp_cons.
    apply IHE1; eapply env_comp_tail; eauto.
    destruct a; destruct o; try_solve.
    left; rewrite (E12 0 s s0); try_solve.
  Qed.

  Lemma env_sum_disjoint : forall E1 E2,
    (copy (length E1) None ++ E2) [+] E1 = E1 ++ E2.

  Proof.
    induction E1; simpl; intros.
    rewrite env_sum_empty_r; trivial.
    destruct a; rewrite IHE1; trivial.
  Qed.

  Lemma env_sub_sub_sum : forall E1 E2 E3,
    E1 [-] E2 [-] E3 = E1 [-] (E2 [+] E3).

  Proof.
    induction E1.
    induction E2; trivial.
    destruct E2; destruct E3; destruct a; simpl; trivial.
    rewrite env_sub_empty; trivial.
    destruct o; destruct o0; simpl; rewrite IHE1; congruence.
    destruct o0; rewrite IHE1; trivial.
  Qed.

  Lemma env_sub_disjoint : forall E F,
    (forall p, E |= p :! \/ F |= p :!) -> E [-] F = E.

  Proof.
    induction E; auto.
    intros F H.
    simpl.
    destruct a; destruct F; trivial.
    destruct o; trivial.
    destruct (H 0); destruct H0; try_solve.
    rewrite IHE; trivial.
    intro p; exact (H (S p)).
    rewrite IHE; trivial.
    intro p; exact (H (S p)).
  Qed.

  Lemma env_sum_sub : forall E1 E2 E3, (forall p, E2 |= p :! \/ E3 |= p :!) ->
    E1 [+] E2 [-] E3 = E1 [-] E3 [+] E2.

  Proof.
    induction E1; intros F G H.
    rewrite env_sub_disjoint; trivial.
    rewrite env_sum_empty_l; trivial.
    destruct F; destruct G; destruct a; repeat rewrite env_sum_empty_r;
      repeat rewrite env_sub_empty; simpl; trivial.
    destruct o; destruct o0; try_solve;
      try solve
	[ rewrite (IHE1 F G); [trivial | intro p; exact (H (S p))]
	| destruct (H 0); destruct H0; try_solve
        ].
    destruct o; destruct o0;
      try solve
	[ simpl; rewrite (IHE1 F G); [trivial | intro p; exact (H (S p))]
	| destruct (H 0); destruct H0; try_solve
	].
  Qed.

  Lemma env_extend : forall M A,
    (copy (length M) None ++ A [#] EmptyEnv) [+] M = M ++ A [#] EmptyEnv.

  Proof.
    induction M; trivial. intro A. destruct a; simpl; rewrite IHM; trivial.
  Qed.

(* x-man reduntant, check env_comp_ext_l *)
  Lemma env_comp_sum_l : forall M N, M [<->] N [+] M.

  Proof.
    intros. intros p A B Mp NMp. set (w := env_sum_ry N Mp).
    inversion NMp; inversion w; try_solve.
  Qed.

  Lemma env_sum_remove_double : forall E1 E2, E1 [+] E2 [+] E1 = E2 [+] E1.

  Proof.
    induction E1; intros.
    destruct E2; trivial.
    destruct E2; simpl.
    destruct a; rewrite env_sum_double; trivial.
    destruct o; destruct a; rewrite <- IHE1; trivial.
  Qed.

  Lemma env_sub_move : forall E1 E2 E3,
    (E1 [-] E2) [+] (E3 [-] E2) = E1 [+] E3 [-] E2.

  Proof.
    induction E1; intros.
    destruct E3; destruct E2; try destruct o; try destruct o0; trivial.
    destruct E2; destruct E3; destruct a; try destruct o; try destruct o0; 
      simpl; trivial; rewrite IHE1; trivial.
  Qed.

  Definition envSubset E F := forall x A, E |= x := A -> F |= x := A.

  Lemma env_subset_empty : forall E, envSubset EmptyEnv E.

  Proof. intros; intros p A D. inversion D; destruct p; try_solve. Qed.

  Lemma env_subset_refl : forall E, envSubset E E.

  Proof. fo. Qed.

  Lemma env_subset_trans : forall E1 E2 E3,
    envSubset E1 E2 -> envSubset E2 E3 -> envSubset E1 E3.

  Proof. fo. Qed.

  Lemma env_subset_cons : forall a E E',
    envSubset E' E -> envSubset (a [#] E') (a [#] E).

  Proof. intros; intros p A. destruct p; fo. Qed.

  Lemma env_subset_cons_none : forall E E',
    envSubset E' E -> envSubset (None :: E') (None :: E).

  Proof. intros; intros p A. destruct p; fo. Qed.

  Lemma env_subset_cons_rev : forall a b E E',
    envSubset (a :: E') (b :: E) -> envSubset E' E.

  Proof. intros; intros p A D. set (w := H (S p) A D); trivial. Qed.

  Lemma env_subset_tail : forall E' E,
    envSubset E' E -> envSubset (tail E') (tail E).

  Proof.
    intros; intros p A D. apply varD_tail. apply H.
    apply varD_tail_rev; trivial.
  Qed.

  Lemma env_subset_lowered : forall E E' n, envSubset E E' ->
    envSubset (loweredEnv E n) (loweredEnv E' n).

  Proof.
    intros; unfold loweredEnv; intros w A D.
    destruct (nth_app (initialSeg E n) (finalSeg E (S n)) w D) as
      [[ED w_len] | [ED w_len]]; 
      rewrite initialSeg_length in w_len; try rewrite initialSeg_length in ED.
    assert (E' |= w := A).
    apply H; unfold VarD.
    apply initialSeg_prefix with n; trivial.
    assert (w < n).
    set (h := Min.le_min_l n (length E)).
    lia.
    unfold VarD; rewrite nth_app_left; autorewrite with datatypes; trivial.
    apply Min.min_case2; trivial.
    apply nth_some with (Some A); trivial.

    assert (Min.min n (length E) = n).
    apply Min.min_l.
    set (h := finalSeg_nth_idx E (S n) (w - Min.min n (length E)) ED).
    lia.
    rewrite H0 in ED.
    assert (ED': nth_error E (S n + (w - n)) = Some (Some A)).
    rewrite <- nth_finalSeg_nth; trivial.
    set (E'D := H (S n + (w - n)) A ED').
    replace (S n + (w - n)) with (S w) in E'D.
    assert (Min.min n (length E') = n).
    set (ww := nth_some E' (S w) E'D).
    apply Min.min_l.
    lia.
    unfold VarD; rewrite nth_app_right.
    autorewrite with datatypes; rewrite H1.
    replace (S n + (w - n)) with (S w); trivial.
    lia.
    autorewrite with datatypes.
    rewrite H1; rewrite <- H0; trivial.
    lia.
  Qed.

  Lemma env_subset_comp : forall E E', envSubset E E' -> E [<->] E'.

  Proof.
    intros; intros x A B D1 D2. set (w := H x A D1).
    inversion D2; inversion w; try_solve.
  Qed.

  Lemma env_subset_as_sum_l : forall E E',
    length E' <= length E -> envSubset E' E -> E = E' [+] E.

  Proof.
    induction E.
    intros; inversion H; destruct E'; try_solve.
    intros.
    destruct E'; trivial.
    assert (E = E' [+] E).
    apply (IHE E').
    simpl in H; lia.
    apply env_subset_cons_rev with o a; trivial.
    assert (forall E E', E = E' -> a :: E = a :: E').
    intros; replace E0 with E'0; trivial.
    destruct a; destruct o; simpl; try solve [apply H2; trivial].
    exfalso; apply varD_UD_absurd with (None::E) 0 s.
    apply H0; constructor.
    right; trivial.
  Qed.

  Lemma env_subset_as_sum_r : forall E E',
    length E' <= length E -> envSubset E' E -> E = E [+] E'.

  Proof.
    induction E.
    intros; inversion H; destruct E'; try_solve.
    intros.
    destruct E'; trivial.
    assert (E = E [+] E').
    apply (IHE E').
    simpl in H; lia.
    apply env_subset_cons_rev with o a; trivial.
    assert (forall E E' (a: option SimpleType), E = E' -> a :: E = a :: E').
    intros; replace E0 with E'0; trivial.
    destruct a; destruct o; simpl; try solve [apply H2; trivial].
    replace s with s0.
    apply H2; trivial.
    assert ((Some s0 :: E') |= 0 := s0).
    constructor.
    set (w := H0 0 s0 H3); inversion w; trivial.
    exfalso; apply varD_UD_absurd with (None::E) 0 s.
    apply H0; constructor.
    right; trivial.
  Qed.

  Lemma env_comp_on_subset : forall El El' Er Er' i,
    env_comp_on El Er i -> envSubset El' El ->
    envSubset Er' Er -> env_comp_on El' Er' i.

  Proof. fo. Qed.

  Lemma env_comp_subset : forall El Er El' Er', El [<->] Er ->
    envSubset El' El -> envSubset Er' Er -> El' [<->] Er'.

  Proof. fo. Qed.

  Lemma env_subset_sum_l : forall E El Er, El [<->] Er ->
    envSubset E El -> envSubset E (El [+] Er).

  Proof.
    intros; intros x A D. apply env_sum_ly. exact (H x). apply H0; trivial.
  Qed.

  Lemma env_subset_sum_r : forall E El Er,
    envSubset E Er -> envSubset E (El [+] Er).

  Proof. intros; intros x A D. apply env_sum_ry. apply H; trivial. Qed.

  Lemma env_subset_sum : forall El El' Er Er', El' [<->] Er' ->
    envSubset El El' -> envSubset Er Er' ->
    envSubset (El [+] Er) (El' [+] Er').

  Proof.
    intros; intros p A D.
    destruct (env_sum_varDecl El Er D) as [[Elp Ern] | Erp].
    apply env_sum_ly.
    exact (H p).
    apply H0; trivial.
    apply env_sum_ry.
    apply H1; trivial.
  Qed.

  Lemma env_subset_lsum : forall El Er E,
    envSubset El E -> envSubset Er E -> envSubset (El [+] Er) E.

  Proof.
    intros; intros p A D.
    destruct (env_sum_varDecl El Er D) as [[Elp _] | Erp].
    apply H; trivial.
    apply H0; trivial.
  Qed.

  Lemma env_subset_sum_req : forall El El' Er,
    envSubset El El' -> envSubset (El [+] Er) (El' [+] Er).

  Proof.
    intros; intros p A D.
    destruct (env_sum_varDecl El Er D) as [[Elp Ern] | Erp].
    apply env_sum_ly_rn; trivial.
    apply H; trivial.
    apply env_sum_ry; trivial.
  Qed.

  Lemma env_subset_sum_leq : forall El Er Er', El [<->] Er' ->
    envSubset Er Er' -> envSubset (El [+] Er) (El [+] Er').

  Proof. intros. apply env_subset_sum; trivial. apply env_subset_refl. Qed.

  Lemma varDecl_single : forall x A B w,
    (copy x None ++ A[#]EmptyEnv) |= w := B -> A = B /\ x = w.

  Proof.
    intros.
    destruct (lt_eq_lt_dec x w) as [[xw | xw] | xw].
    exfalso; apply (varD_UD_absurd H).
    left; apply nth_beyond; autorewrite with datatypes using simpl; try lia.
    rewrite xw; split; trivial.
    rewrite xw in H.
    unfold VarD in H.
    rewrite
      (@nth_app_right (option SimpleType) (copy w None) (A[#]EmptyEnv) w) in H;
      autorewrite with datatypes using auto.
    rewrite copy_length in H.
    replace (w - w) with 0 in H; [inversion H; trivial | lia].
    exfalso; apply (varD_UD_absurd H).
    right; rewrite nth_app_left; autorewrite with datatypes using trivial.
  Qed.

  Lemma env_subset_single : forall A x E,
    E |= x := A -> envSubset (copy x None ++ A [#] EmptyEnv) E.

  Proof.
    intros; intros w B D. destruct (varDecl_single x A D).
    rewrite <- H0; rewrite <- H1; trivial.
  Qed.

  Lemma typing_ext_env : forall Pt E E' A,
    envSubset E' E -> E' |- Pt := A -> E |- Pt := A.

  Proof.
    induction Pt.
     (* variable *)
    intros E E' A envC Ex.
    constructor.
    inversion Ex.
    apply envC; trivial.
     (* function symbol *)
    inversion 2; constructor.
     (* abstraction *)
    intros E E' a EE' TypAbs.
    inversion TypAbs.
    constructor.
    apply IHPt with (A [#] E'); trivial.
    apply env_subset_cons; trivial.
     (* application *)
    intros E E' A EE' TypApp.
    inversion TypApp.
    constructor 4 with A0.
    apply IHPt1 with E'; trivial.
    apply IHPt2 with E'; trivial.
  Qed.

  Lemma env_subset_dropSuffix_length : forall E E', envSubset E' E ->
    length (dropEmptySuffix E') <= length E.

  Proof.
    intros.
    destruct (dropSuffix_last E') as [E'e | [A E'A]].
    rewrite E'e; lia.
    set (E'd := dropSuffix_decl_rev E' E'A).
    set (w := H (pred (length (dropEmptySuffix E'))) A E'd).
    assert (Ed: nth_error E (pred (length (dropEmptySuffix E'))) <> None).
    inversion w; try_solve.
    set (x := proj1 (nth_in E (pred (length (dropEmptySuffix E')))) Ed).
    lia.
  Qed.

  Lemma varUD_hole : forall E i,
    (initialSeg E i ++ None :: finalSeg E (S i)) |= i :!.

  Proof.
    intros.
    destruct (lt_eq_lt_dec (length E) i) as [[iE | iE] | iE].
    left.
    apply nth_beyond.
    autorewrite with datatypes using simpl; try lia.
    right.
    rewrite nth_app_right; autorewrite with datatypes; rewrite iE.
    apply Min.min_case2; replace (i - i) with 0; solve [trivial | lia].
    auto with arith.
    right.
    rewrite nth_app_right; autorewrite with datatypes; auto with arith.
    replace (i - Min.min i (length E)) with 0; trivial.
    rewrite Min.min_l; lia.
  Qed.

  Lemma varD_hole : forall E i j A, i <> j -> E |= j := A ->
    (initialSeg E i ++ None :: finalSeg E (S i)) |= j := A.

  Proof.
    unfold VarD; intros.
    set (iE := nth_some E j H0).
    destruct (lt_eq_lt_dec i j) as [[ij | ij] | ij].
    rewrite nth_app_right; autorewrite with datatypes; rewrite Min.min_l;
      try lia.
    replace (j - i) with (S (j - S i)); try lia.
    simpl; rewrite nth_finalSeg_nth.
    replace (S i + (j - S i)) with j; [trivial | lia].
    lia.
    rewrite nth_app_left; autorewrite with datatypes; trivial.
    apply Min.min_case2; trivial.
  Qed.

  Lemma varD_hole_env_length : forall E i j A,
    (initialSeg E i ++ None :: finalSeg E (S i)) |= j := A -> length E > j.

  Proof.
    unfold VarD; intros.
    destruct (le_lt_dec (Min.min i (length E)) j).
    rewrite (@nth_app_right (option SimpleType) (initialSeg E i) 
      (None :: finalSeg E (S i)) j) in H.
    rewrite initialSeg_length in H.
    destruct (le_gt_dec (length E) i); trivial.
    rewrite Min.min_r in H; trivial.
    rewrite (finalSeg_empty E (k := S i)) in H.
    destruct (j - length E); try destruct n; try_solve.
    lia.
    assert (forall (A : Type) l (a: A) i,
      i > 0 -> nth_error (a::l) i = nth_error l (pred i)).
    intros; destruct i0; try_solve.
    lia.
    rewrite H0 in H.
    set (w := finalSeg_nth_idx E (S i) (pred (j - Min.min i (length E))) H).
    rewrite Min.min_l in w; lia.
    destruct (j - Min.min i (length E)); try_solve.
    lia.
    autorewrite with datatypes; trivial.
    rewrite nth_app_left in H; autorewrite with datatypes; trivial.
    set (w := Min.le_min_r i (length E)); lia.
  Qed.

  Lemma varD_hole_env_length_j_ge_i : forall E i j A, j >= i ->
    (initialSeg E i ++ None :: finalSeg E (S i)) |= j := A -> length E > i.

  Proof. intros; set (w := varD_hole_env_length E i H0); lia. Qed.

  Lemma varD_hole_rev : forall E i j A, i <> j ->
    (initialSeg E i ++ None :: finalSeg E (S i)) |= j := A -> E |= j := A.

  Proof.
    unfold VarD; intros.
    destruct (lt_eq_lt_dec i j) as [[ij | ij] | ij].
    assert (length E > i).
    apply varD_hole_env_length_j_ge_i with j A; auto with arith.
    rewrite nth_app_right in H0; autorewrite with datatypes.
    replace (length (initialSeg E i)) with i in H0.
    assert (forall (A : Type) l (a: A) i,
      i > 0 -> nth_error (a::l) i = nth_error l (pred i)).
    intros; destruct i0; try_solve.
    lia.
    rewrite (H2 (option SimpleType) (finalSeg E (S i)) None (j - i)) in H0.
    replace j with (S i + pred (j - i)).
    rewrite <- nth_finalSeg_nth; trivial.
    lia.
    lia.
    autorewrite with datatypes; rewrite Min.min_l; trivial; lia.
    rewrite Min.min_l; trivial; lia.
    lia.
    rewrite nth_app_left in H0; autorewrite with datatypes.
    apply initialSeg_prefix with i; trivial.
    assert (Min.min i (length E) > j).
    rewrite Min.min_comm.
    apply Min.min_case2; trivial.
    apply varD_hole_env_length with i A; trivial.
    lia.
  Qed.

  Lemma env_hole_subset : forall E i,
    envSubset (initialSeg E i ++ None :: finalSeg E (S i)) E.

  Proof.
    intros; intros j A D.
    destruct (eq_nat_dec i j).
    rewrite e in D.
    assert (length (initialSeg E j) = j).
    autorewrite with datatypes.
    apply Min.min_l.
    assert (length E > j).
    apply varD_hole_env_length_j_ge_i with j A; trivial.
    lia.
    lia.
    unfold VarD in D.
    rewrite nth_app_right in D.
    replace (j - length (initialSeg E j)) with 0 in D.
    inversion D.
    rewrite H; lia.
    lia.
    apply varD_hole_rev with i; trivial.
  Qed.

  Definition env_eq E1 E2 := envSubset E1 E2 /\ envSubset E2 E1.

  Notation "E1 [=] E2" := (env_eq E1 E2) (at level 70).

  Lemma env_eq_refl : forall E, E [=] E.

  Proof. fo. Qed.

  Lemma env_eq_sym : forall E E', E [=] E' -> E' [=] E.

  Proof. fo. Qed.

  Lemma env_eq_trans : forall E1 E2 E3, E1 [=] E2 -> E2 [=] E3 -> E1 [=] E3.

  Proof. fo. Qed.

  Lemma env_eq_some_none_absurd : forall E1 E2 A,
    Some A :: E1 [=] None :: E2 -> False.

  Proof.
    intros. set (w := (proj1 H) 0 A); compute in w.
    set (p := w (eq_refl (Some (Some A)))); inversion p.
  Qed.

  Lemma env_eq_some_nil_absurd : forall E1 A,
    Some A :: E1 [=] EmptyEnv -> False.

  Proof.
    intros. set (w := (proj1 H) 0 A); compute in w.
    set (p := w (eq_refl (Some (Some A)))); inversion p.
  Qed.

  Lemma env_eq_tail : forall E1 E2, E1 [=] E2 -> tail E1 [=] tail E2.

  Proof. intros. split; destruct H; apply env_subset_tail; trivial. Qed.

  Lemma env_eq_cons : forall a b E E', a = b -> E [=] E' -> a :: E [=] b :: E'.

  Proof.
    intros; split; rewrite H.
    inversion H0.
    destruct b.    
    fold (s [#] E); fold (s [#] E'); apply env_subset_cons; trivial.
    apply env_subset_cons_none; trivial.
    inversion H0.
    destruct b.    
    fold (s [#] E); fold (s [#] E'); apply env_subset_cons; trivial.
    apply env_subset_cons_none; trivial.
  Qed.

  Lemma env_eq_cons_inv : forall a b E E', (a :: E) [=] (b :: E') -> E [=] E'.

  Proof.
    intros. change E with (tail (a :: E)). change E' with (tail (b :: E')).
    apply env_eq_tail; trivial.
  Qed.

  Lemma env_eq_cons_inv_hd : forall a b E E', (a :: E) [=] (b :: E') -> a = b.

  Proof.
    intros. destruct a; destruct b; trivial.
    set (hint := (proj1 H) 0 s).
    fo; inversion H0; trivial.
    set (hint := (proj1 H) 0 s).
    fo; inversion H0; trivial.
    set (hint := (proj2 H) 0 s).
    fo; inversion H0; trivial.
  Qed.

  Lemma env_eq_comp : forall E1 E2, E1 [=] E2 -> E1 [<->] E2.

  Proof.
    intros. intros p A B D1 D2. set (D2' := proj1 H p A D1).
    inversion D2; inversion D2'; try_solve.
  Qed.

  Lemma env_eq_empty_none_empty : EmptyEnv [=] None :: EmptyEnv.

  Proof.
    intros; split.
    apply env_subset_empty.
    intros w A wA.
    destruct w; try_solve.
    destruct w; try_solve.
  Qed.

  Lemma env_eq_empty_cons : forall E, None :: E [=] EmptyEnv -> E [=] EmptyEnv.

  Proof.
    intros. split.
    intros p A Ep.
    set (w := proj1 H (S p) A).
    unfold VarD in w; simpl in w.
    set (ww := w Ep); try_solve.
    apply env_subset_empty.
  Qed.

  Lemma env_eq_empty_cons_rev : forall E,
    E [=] EmptyEnv -> None :: E [=] EmptyEnv.

  Proof.
    intros. split.
    intros p A Ep. destruct p; try_solve.
    set (w := proj1 H p A Ep); destruct p; try_solve.
    apply env_subset_empty.
  Qed.

  Lemma env_eq_empty_tail : forall E n, E [=] E ++ copy n None.

  Proof.
    intros; split; intros p A D.
    unfold VarD; rewrite nth_app_left; trivial.
    apply nth_some with (Some A); trivial.
    destruct (nth_app E (copy n None) p D) as [[Dl _] | [Dr _]].
    trivial.
    destruct (le_gt_dec n (p - length E)).
    assert (p - length E >= length (copy n (None (A:=SimpleType)))).
    autorewrite with datatypes using lia.
    set (w := nth_beyond (copy n None) H).
    try_solve.
    set (w := nth_copy_in (None (A:=SimpleType)) g).
    try_solve.
  Qed.

  Lemma env_eq_empty : forall E, emptyEnv E -> E [=] EmptyEnv.

  Proof.
    intros; split.
    intros w A wA.
    exfalso; apply (varD_UD_absurd wA).
    apply H.
    apply env_subset_empty.
  Qed.

  Lemma env_eq_empty_empty : forall E E', emptyEnv E -> emptyEnv E' -> E [=] E'.

  Proof.
    intros; split; intros p A D.
    destruct (H p); inversion D; try_solve.
    destruct (H0 p); inversion D; try_solve.
  Qed.

  Lemma env_eq_empty_subset : forall E E', E [=] EmptyEnv -> envSubset E E'.

  Proof.
    intros. intros w A wA. set (x := (proj1 H) w A wA). destruct w; try_solve.
  Qed.

  Lemma env_eq_def : forall E1 E2,
    (forall i A, E1 |= i := A <-> E2 |= i := A) ->  E1 [=] E2.

  Proof.
    induction E1.
     (* base *)
    induction E2.
    intros; apply env_eq_refl.
    intros.    
    destruct a.
    set (w := proj2 (H 0 s)); compute in w.
    set (p := w (eq_refl (Some (Some s)))); try_solve.
    apply env_eq_sym; apply env_eq_empty_cons_rev; apply env_eq_sym.
    apply IHE2; intros.
    split.
    destruct i; try_solve.
    intro D.
    set (w := proj2 (H (S i) A) D); try_solve.
     (* step *)
    destruct E2; intros.
    apply env_eq_empty.
    intro j.
    destruct (isVarDecl_dec (a :: E1) j) as [[B D] | X]; trivial.
    set (w := proj1 (H j B) D).
    destruct j; try_solve.
    apply env_eq_cons.
    destruct a; destruct o; trivial.
    set (w := proj1 (H 0 s)); compute in w.
    set (p := w (eq_refl (Some (Some s)))); inversion p; trivial.
    set (w := proj1 (H 0 s)); compute in w.
    set (p := w (eq_refl (Some (Some s)))); inversion p.
    set (w := proj2 (H 0 s)); compute in w.
    set (p := w (eq_refl (Some (Some s)))); inversion p.
    apply IHE1.
    intros.
    set (hint := H (S i) A); trivial.
  Qed.

  Lemma env_equiv_eq : forall E E', E [=] E' -> length E = length E' -> E = E'.

  Proof.
    induction E; destruct E'; intros; try_solve.
    rewrite (IHE E').
    rewrite (env_eq_cons_inv_hd H); trivial.
    apply env_eq_cons_inv with a o; trivial.
    try_solve.
  Qed.

  #[global] Hint Immediate env_eq_refl env_eq_sym env_eq_empty_none_empty : terms.

  #[global] Instance env_eq_Equivalence : Equivalence env_eq.

  Proof.
    split.
    intro x. apply env_eq_refl.
    intros x y. apply env_eq_sym.
    intros x y z. apply env_eq_trans.
  Qed.

  #[global] Instance envSubset_morph : Proper (env_eq ==> env_eq ==> iff) envSubset.

  Proof. fo. Qed.

  #[global] Instance loweredEnv_morph : Proper (env_eq ==> eq ==> env_eq) loweredEnv.

  Proof.
    intros E F [EF FE] x y xy. subst y. split.
    apply env_subset_lowered; trivial.
    apply env_subset_lowered; trivial.
  Qed.

  #[global] Instance env_comp_morph : Proper (env_eq ==> env_eq ==> iff) env_comp.

  Proof. fo. Qed.

  #[global] Instance VarD_morph : Proper (env_eq ==> eq ==> eq ==> iff) VarD.

  Proof. intros E F EF x y xy t u tu. subst y u. fo. Qed.

  #[global] Instance VarUD_morph : Proper (env_eq ==> eq ==> iff) VarUD.

  Proof.
    intros e e0 H n m nm. subst m. split; intro H0.
    destruct (isVarDecl_dec e0 n) as [[A e0n] | e0n]; trivial.
    set (en := proj2 H n A e0n).
    exfalso; apply varD_UD_absurd with e n A; trivial.
    destruct (isVarDecl_dec e n) as [[A e0n] | e0n]; trivial.
    set (en := proj1 H n A e0n).
    exfalso; apply varD_UD_absurd with e0 n A; trivial.
  Qed.

  Lemma env_compose_morph_aux0 : forall El Er El' Er',
    (forall El El' Er', El [=] El' -> Er [=] Er' ->
      envSubset (El [+] Er) (El' [+] Er')) ->
    El [=] El' -> None :: Er [=] Er' ->
    envSubset (El [+] (None :: Er)) (El' [+] Er').

  Proof.
    set (env_subset_cons' := env_subset_cons); unfold decl in env_subset_cons'.
    intros.
    destruct Er'; destruct El; destruct El'; 
      try destruct o; try destruct o0; try destruct o1; 
      simpl; try solve
      [ exfalso; eapply env_eq_some_nil_absurd; eauto with terms
      | exfalso; eapply env_eq_some_none_absurd; eauto with terms 
      | destruct H1; trivial
      ]; try apply env_subset_cons_none; trivial.
    rewrite (env_eq_empty_cons H1).
    rewrite <- (env_eq_empty_cons (env_eq_sym H0)).
    apply env_subset_refl.
    assert (None :: El[+]Er [=] EmptyEnv).
    apply env_eq_empty_cons_rev.
    split.
    change EmptyEnv with (EmptyEnv [+] EmptyEnv).
    apply H; apply env_eq_empty_cons; trivial.
    apply env_subset_empty.
    fold EmptyEnv; rewrite <- H2; apply env_subset_refl.
    rewrite (env_eq_cons_inv_hd H0).
    apply env_subset_cons'.
    replace El' with (El' [+] EmptyEnv).
    apply H; trivial.
    apply (env_eq_cons_inv H0).
    apply env_eq_empty_cons; trivial.
    rewrite env_sum_empty_r; trivial.
    replace El' with (El' [+] EmptyEnv).
    apply H; trivial.
    apply (env_eq_cons_inv H0).
    apply env_eq_empty_cons; trivial.
    rewrite env_sum_empty_r; trivial.
    apply env_subset_sum_r; destruct (env_eq_cons_inv H1); trivial.
    replace Er' with (nil [+] Er').
    apply H; trivial.
    change (nil (A:=option SimpleType))
      with (tail (None (A:=SimpleType) :: nil)) in H0.
    set (w := env_eq_tail H0); trivial.
    apply (env_eq_cons_inv H1).
    rewrite env_sum_empty_l; trivial.
    rewrite (env_eq_cons_inv_hd H0).
    apply env_subset_cons'.
    apply H.
    destruct (env_eq_cons_inv H0); fo.
    destruct (env_eq_cons_inv H1); fo.
    apply H.
    destruct (env_eq_cons_inv H0); fo.
    destruct (env_eq_cons_inv H1); fo.
  Qed.

  Lemma env_compose_morph_aux : forall El Er El' Er',
    El [=] El' -> Er [=] Er' -> envSubset (El [+] Er) (El' [+] Er').

  Proof.
    set (env_subset_cons' := env_subset_cons); unfold decl in env_subset_cons'.
    intros El Er; gen El; induction Er; clear El.
    intros.
    rewrite env_sum_empty_r.
    apply env_subset_sum_l.
    rewrite <- H0.
    apply env_comp_empty.
    destruct H; trivial.

    intros; destruct a; destruct Er'.
    exfalso; eapply env_eq_some_nil_absurd; eauto.
    destruct o.
    rewrite (env_eq_cons_inv_hd H0); rewrite (env_eq_cons_inv_hd H0) in H0.
    destruct (env_eq_cons_inv H0).
    destruct El; destruct El'; try destruct o; try destruct o0;
      simpl; apply env_subset_cons'; try solve 
	[ exfalso; eapply env_eq_some_nil_absurd; eauto with terms
	| apply IHEr; eapply env_eq_cons_inv; eauto
	| exfalso; eapply env_eq_some_none_absurd; eauto with terms
	| trivial
	].
    apply env_subset_sum_r; destruct (env_eq_cons_inv H0); trivial.
    replace Er' with (nil [+] Er').
    apply IHEr; trivial.
    change (nil (A:=option SimpleType))
      with (tail (None (A:=SimpleType) :: nil)) in H.
    set (w := env_eq_tail H); trivial.
    fo.
    rewrite env_sum_empty_l; trivial.
    exfalso; eapply env_eq_some_none_absurd; eauto with terms.
    apply env_compose_morph_aux0; trivial.
    apply env_compose_morph_aux0; trivial.
  Qed.

  #[global] Instance env_compose_morph :
    Proper (env_eq ==> env_eq ==> env_eq) env_compose.

  Proof.
    intros; split.
    apply env_compose_morph_aux; trivial.
    apply env_compose_morph_aux; auto with terms.
  Qed.

  Lemma env_eq_sum : forall El El' Er Er',
    El [=] El' -> Er [=] Er' -> El [+] Er [=] El' [+] Er'.

  Proof. intros. rewrite H; rewrite H0. apply env_eq_refl. Qed.

  Lemma env_eq_subset_sum_l : forall E E', envSubset E' E -> E [=] E' [+] E.

  Proof.
    intros; split.    
    apply env_subset_sum_r; apply env_subset_refl.
    intros w A D.
    destruct (env_sum_varDecl E' E D) as [[E'w _] | Ew]; trivial.
    apply H; trivial.
  Qed.

  Lemma env_subset_dropSuffix_eq : forall E, env_eq (dropEmptySuffix E) E.

  Proof.
    split; intros; intros p A D.
    apply dropSuffix_decl_rev; trivial.
    apply dropSuffix_decl; trivial.
  Qed.

  Lemma typing_drop_suffix : forall E Pt A,
    E |- Pt := A -> dropEmptySuffix E |- Pt := A.

  Proof.
    intros. apply typing_ext_env with E; trivial.
    apply (proj2 (env_subset_dropSuffix_eq E)).
  Qed.

  Lemma liftedEnv_empty : forall E n k,
    emptyEnv E -> liftedEnv n E k [=] EmptyEnv.

  Proof.
    intros; split; intros p A D.
    unfold liftedEnv in D.
    destruct (nth_app (initialSeg E k) (copy n None ++ finalSeg E k) p D)
      as [[dec cond] | [dec cond]].
    set (w := initialSeg_prefix E k p dec).
    destruct (H p); try_solve.
    destruct
      (nth_app (copy n None) (finalSeg E k) (p - length (initialSeg E k)) dec)
      as [[dec' cond'] | [dec' cond']].
    destruct (emptyEnv_copyNone n (p - length (initialSeg E k))); try_solve.
    set (w := nth_finalSeg_nth E k (p - length (initialSeg E k)
      - length (copy n (A:=option SimpleType) None))).
    destruct (H (k + (p - length (initialSeg E k)
      - length (copy n (None (A:=SimpleType)))))); try_solve.
    destruct p; try_solve.
  Qed.

  Lemma liftedEnv_distr_sum_equiv : forall El Er n k,
    liftedEnv n (El [+] Er) k [=] liftedEnv n El k [+] liftedEnv n Er k.

  Proof.
    unfold liftedEnv; intros; split; intros p A D.
    destruct (nth_app _ _ _ D) as [[Dl cond] | [Dr cond]].
    assert (p < k).
    rewrite initialSeg_length in cond.
    set (w := Min.le_min_l k (length (El[+]Er))); lia.
    set (ElErD := initialSeg_prefix (El[+]Er) k p Dl).
    destruct (env_sum_varDecl El Er ElErD) as [[ElD ErND] | ErD].
    apply env_sum_ly_rn.
    apply copy_split_l_varD; trivial.
    apply copy_split_l_varUD; trivial.
    apply env_sum_ry.
    apply copy_split_l_varD; trivial.
    destruct (nth_app _ _ _ Dr) as [[Drl cond'] | [Drr cond']];
      rewrite copy_length in cond'.
    rewrite (@nth_copy_in (option SimpleType) n None
      (p - length (initialSeg (El[+]Er) k))) in Drl; try_solve.
    rewrite copy_length in Drr.
    set (ElErD := Drr); rewrite nth_finalSeg_nth in ElErD.
    assert (length (initialSeg (El[+]Er) k) = k).
    autorewrite with datatypes.
    destruct (le_gt_dec (length (El[+]Er)) k).
    rewrite finalSeg_empty in Drr; trivial.
    destruct (p - length (initialSeg (El[+]Er) k) - n); try_solve.
    apply Min.min_l; lia.
    destruct (env_sum_varDecl El Er ElErD) as [[ElD ErND] | ErD].
    apply env_sum_ly_rn.
    apply copy_split_r_varD
      with (k + (p - length (initialSeg (El[+]Er) k) - n)); trivial; try lia.
    apply copy_split_r_varUD
      with (k + (p - length (initialSeg (El[+]Er) k) - n)); trivial; try lia.
    apply env_sum_ry.
    apply copy_split_r_varD
      with (k + (p - length (initialSeg (El[+]Er) k) - n)); trivial; try lia.

    destruct (env_sum_varDecl _ _ D) as [[DL DRN] | DR].
    destruct (nth_app _ _ _ DL) as [[DLl cond] | [DLr cond]].
    assert (p < k).
    rewrite initialSeg_length in cond.
    set (w := Min.le_min_l k (length El)).
    lia.
    apply copy_split_l_varD; trivial.
    apply env_sum_ly_rn.
    rewrite initialSeg_nth in DLl; trivial.
    apply copy_split_l_rev_varUD with k n; trivial.
    destruct (nth_app _ _ _ DLr) as [[DLrl cond'] | [DLrr cond']]; 
      rewrite copy_length in cond'.
    rewrite (@nth_copy_in (option SimpleType) n None
      (p - length (initialSeg El k))) in DLrl; try_solve.
    assert (length (initialSeg El k) = k).
    autorewrite with datatypes.
    destruct (le_gt_dec (length El) k).
    rewrite finalSeg_empty in DLrr; trivial.
    rewrite copy_length in DLrr.
    destruct (p - length (initialSeg El k) - n); try_solve.
    apply Min.min_l; lia.
    rewrite copy_length in DLrr.
    set (w := DLrr); rewrite nth_finalSeg_nth in w.
    apply copy_split_r_varD with (k + (p - length (initialSeg El k) - n));
      trivial; try lia.
    apply env_sum_ly_rn; trivial.
    apply copy_split_r_rev_varUD with k n p; trivial; try lia.
    destruct (nth_app _ _ _ DR) as [[DRl cond] | [DRr cond]].
    apply copy_split_l_varD; trivial.
    rewrite initialSeg_length in cond.
    set (w := Min.le_min_l k (length Er)); lia.
    apply env_sum_ry.
    unfold VarD; apply initialSeg_prefix with k; trivial.
    destruct (nth_app _ _ _ DRr) as [[DRrl cond'] | [DRrr cond']];
      rewrite copy_length in cond'.
    rewrite (@nth_copy_in (option SimpleType) n None
      (p - length (initialSeg Er k))) in DRrl; try_solve.
    rewrite copy_length in DRrr.
    set (w := DRrr); rewrite nth_finalSeg_nth in w.
    assert (length (initialSeg Er k) = k).
    autorewrite with datatypes.
    destruct (le_gt_dec (length Er) k).
    clear w.
    rewrite finalSeg_empty in DRrr; trivial.
    destruct (p - length (initialSeg Er k) - n); try_solve.
    apply Min.min_l; lia.
    apply copy_split_r_varD with (k + (p - length (initialSeg Er k) - n));
      trivial; try lia.
    apply env_sum_ry; trivial.
  Qed.

  Lemma liftedEnv_distr_sum : forall El Er n k,
    liftedEnv n (El [+] Er) k = liftedEnv n El k [+] liftedEnv n Er k.

  Proof.
    intros. apply env_equiv_eq.
    apply liftedEnv_distr_sum_equiv.
    unfold liftedEnv.
    autorewrite with datatypes.
    rewrite !env_sum_length.
    autorewrite with datatypes.
    destruct (le_gt_dec (length El) (length Er)); lia.
  Qed.

  Lemma loweredEnv_distr_sum_equiv : forall El Er n,
    loweredEnv (El [+] Er) n [=] loweredEnv El n [+] loweredEnv Er n.

  Proof.
    unfold loweredEnv; intros; split; intros p A D.
    destruct (nth_app _ _ _ D) as [[Dl cond] | [Dr cond]].
    assert (p < n).
    rewrite initialSeg_length in cond.
    set (w := Min.le_min_l n (length (El[+]Er))); lia.
    set (ElErD := initialSeg_prefix (El[+]Er) n p Dl).
    destruct (env_sum_varDecl El Er ElErD) as [[ElD ErND] | ErD].
    apply env_sum_ly_rn.
    apply hole_l_varD; trivial.
    apply hole_l_varUD; trivial.
    apply env_sum_ry.
    apply hole_l_varD; trivial.
    set (ElErD := Dr); rewrite nth_finalSeg_nth in ElErD.
    assert (length (initialSeg (El[+]Er) n) = n).
    autorewrite with datatypes.
    destruct (le_gt_dec (length (El[+]Er)) n).
    clear ElErD.
    rewrite finalSeg_empty in Dr; trivial.
    destruct (p - length (initialSeg (El[+]Er) n)); try_solve.
    lia.
    apply Min.min_l; lia.
    destruct (env_sum_varDecl El Er ElErD) as [[ElD ErND] | ErD].
    apply env_sum_ly_rn.
    apply hole_r_varD with (S n + (p - length (initialSeg (El[+]Er) n))); 
      trivial; try lia.
    apply hole_r_varUD with (S n + (p - length (initialSeg (El[+]Er) n))); 
      trivial; try lia.
    apply env_sum_ry.
    apply hole_r_varD with (S n + (p - length (initialSeg (El[+]Er) n))); 
      trivial; try lia.

    destruct (env_sum_varDecl _ _ D) as [[DL DRN] | DR].
    destruct (nth_app _ _ _ DL) as [[DLl cond] | [DLr cond]].
    assert (p < n).
    rewrite initialSeg_length in cond.
    set (w := Min.le_min_l n (length El)).
    lia.
    apply hole_l_varD; trivial.
    apply env_sum_ly_rn.
    rewrite initialSeg_nth in DLl; trivial.
    apply hole_l_rev_varUD with n; trivial.
    assert (length (initialSeg El n) = n).
    autorewrite with datatypes.
    destruct (le_gt_dec (length El) n).
    rewrite finalSeg_empty in DLr; trivial.
    destruct (p - length (initialSeg El n)); try_solve.
    lia.
    apply Min.min_l; lia.
    rewrite nth_finalSeg_nth in DLr.
    apply hole_r_varD with (S n + (p - length (initialSeg El n))); trivial;
      try lia.
    apply env_sum_ly_rn; trivial.
    apply hole_r_rev_varUD with n p; trivial; try lia.
    destruct (nth_app _ _ _ DR) as [[DRl cond] | [DRr cond]].
    apply hole_l_varD.
    rewrite initialSeg_length in cond.
    set (w := Min.le_min_l n (length Er)); lia.
    apply env_sum_ry.
    unfold VarD; apply initialSeg_prefix with n; trivial.
    set (w := DRr); rewrite nth_finalSeg_nth in w.
    assert (length (initialSeg Er n) = n).
    autorewrite with datatypes.
    destruct (le_gt_dec (length Er) n).
    rewrite finalSeg_empty in DRr; trivial.
    destruct (p - length (initialSeg Er n)); try_solve.
    lia.
    apply Min.min_l; lia.
    apply hole_r_varD with (S n + (p - length (initialSeg Er n))); trivial;
      try lia.
    apply env_sum_ry; trivial.
  Qed.

  Lemma loweredEnv_distr_sum : forall El Er n,
    loweredEnv (El [+] Er) n = loweredEnv El n [+] loweredEnv Er n.

  Proof.
    intros.
    apply env_equiv_eq.
    apply loweredEnv_distr_sum_equiv.
    unfold loweredEnv.
    autorewrite with datatypes.
    rewrite !env_sum_length.
    autorewrite with datatypes.
    destruct (le_gt_dec (length El) (length Er)); lia.
  Qed.

  Lemma lift_tail : forall E n k,
    liftedEnv n (tail E) k [=] tail (liftedEnv n E (S k)).

  Proof.
    induction E; intros.
    unfold liftedEnv, finalSeg; destruct k; simpl; rewrite <- 1app_nil_end.
    apply env_eq_empty_empty.
    apply emptyEnv_copyNone.
    apply tail_emptyEnv.
    apply emptyEnv_copyNone.
    apply env_eq_empty_empty.
    apply emptyEnv_copyNone.
    apply tail_emptyEnv.
    apply emptyEnv_copyNone.
    unfold liftedEnv; simpl.
    change (finalSeg (a::E) (S k)) with (finalSeg E k).
    apply env_eq_refl.
  Qed.

  Lemma lower_tail : forall E n,
    loweredEnv (tail E) n = tail (loweredEnv E (S n)).

  Proof.
    induction E; intros.
    destruct n; trivial.
    unfold loweredEnv; simpl.
    change (finalSeg (a::E) (S (S n))) with (finalSeg E (S n)); trivial.
  Qed.

End TermsEnv.
