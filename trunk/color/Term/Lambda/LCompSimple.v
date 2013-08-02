(**

CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05


* Termination of beta-reduction for simply-typed lambda-terms
*)

Set Implicit Arguments.

Require Import Morphisms Basics SN VecUtil LogicUtil.
Require Export LSimple LComp.

(****************************************************************************)
(** * Functor providing a termination proof for any CP structure

assuming that every type constant is interpreted by a computability
predicate, and every function symbol is computable. *)

Module Make (Export ST : ST_Struct)
  (Export CP : CP_Struct with Module L := ST.L).

  Module Export C := LComp.Make CP.
  Module Export T := LSimple.Make ST.

  Section int.

    Variables (I : So -> Te -> Prop) (cp_I : forall b, cp (I b)).

    (** ** Interpretation of simple types *)

    Fixpoint int T :=
      match T with
        | Base b => I b
        | Arr A B => arr (int A) (int B)
      end.

    Lemma int_base b t : I b t <-> int (Base b) t.

    Proof. refl. Qed.

    (** The interpretation of a type is a computability predicate. *)

    Lemma cp_int : forall T, cp (int T).

    Proof. induction T; simpl. apply cp_I. apply cp_arr; hyp. Qed.

    Global Instance int_aeq : Proper (Logic.eq ==> aeq ==> iff) int.

    Proof.
      intros T U TU. subst U. destruct (cp_int T) as [h _ _ _].
      intros t u tu. split; intro i. rewrite <- tu. hyp. rewrite tu. hyp.
    Qed.

    Lemma int_sn : forall T t, int T t -> SN R_aeq t.

    Proof. intros T t h. gen (cp_int T). intros [_ T2 _ _]. auto. Qed.

    Lemma int_var : forall T x, int T (Var x).

    Proof.
      intros T x. gen (cp_int T). intros [T1 _ _ T4]. apply cp_var; auto.
    Qed.

    (** A substitution is valid wrt an environment [E] if, for every
       mapping [(x,T) in E], [s x] is in the interpretation of [T]. *)

    Definition valid E s := forall x T, MapsTo x T E -> int T (s x).

    Lemma valid_id : forall E, valid E id.

    Proof.
      intros E x T hx. gen (cp_int T). intros [T1 _ _ T4]. apply cp_var; hyp.
    Qed.

(****************************************************************************)
(** Termination proof assuming that function symbols are computable. *)

    Variable comp_fun : forall f, int (typ f) (Fun f).

    Lemma tr_int : forall v E V, E |- v ~: V ->
      forall s, valid E s -> int V (subs s v).

    Proof.
      (* We proceed by induction on the size of [v]. *)
      ind_size1 v; intros E V ht s hs; inversion ht; subst.
      (* var *)
      apply hs. hyp.
      (* fun *)
      apply comp_fun.
      (* app *)
      simpl. gen (hu _ _ H2 _ hs); intro h1. simpl in h1. apply h1.
      eapply hv. apply H4. hyp.
      (* lam *)
      rename X0 into A. rename V0 into V.
      (* First note that [A] and [V] are computability predicates. *)
      gen (cp_int A). intros [A1 A2 A3 A4].
      gen (cp_int V). intros [V1 V2 V3 V4].
      (* We first replace [s] by its restriction [s0] on [fv (Lam x v)]. *)
      rewrite subs_seq_restrict. set (s0 := S.restrict (fv (Lam x v)) s).
      (* We simplify. *)
      simpl. set (x' := var x v s0). set (s' := S.update x (Var x') s0).
      intros a ha.
      (* We check that [s0] is valid wrt [E]. *)
      assert (hs0 : valid E s0). intros z B hz. unfold s0. unfold_restrict.
      destruct (XSet.mem z (fv (Lam x v))). apply hs. hyp. apply int_var.
      (* We check that [s'] is valid wrt [add x A E]. *)
      assert (hs' : valid (add x A E) s'). intros z B.
      rewrite add_mapsto_iff. unfold s'. intros [[h1 h2]|[h1 h2]].
      subst z B. rewrite update_eq. apply int_var.
      rewrite update_neq. 2: hyp. apply hs0. hyp.
      (* We apply lemma [cp_beta]. *)
      apply cp_beta; auto.
      (* Proof that [SN R_aeq (Lam x' (subs s' v))]. *)
      apply sn_lam. eapply int_sn. eapply hu. refl. apply H3. hyp.
      (* Proof that [int V (subs (single x' a) (subs s' v))]. *)
      rewrite subs_comp.
      (* We first prove that [comp (single x' a) s'] is equal to
        [update x a s0]. *)
      assert (k : seq (fv v) (comp (single x' a) s') (S.update x a s0)).
      intros z hz. unfold comp, s'. unfold_update. eq_dec z x.
      (* z = x *)
      subst. simpl. rewrite single_eq. refl.
      (* z <> x *)
      unfold s0. unfold_restrict. case_eq (XSet.mem z (fv (Lam x v))).
      (* ~In z (fv (Lam x v)) *)
      Focus 2. rewrite <- not_mem_iff. simpl. set_iff. intuition.
      (* In z (fv (Lam x v)) *)
      intro k. gen (var_notin_fv_subs s0 hz n). fold x'.
      unfold s0. unfold_restrict. rewrite k. intuition.
      rewrite single_notin_fv. refl. hyp.
      (* We can now apply the induction hypothesis. *)
      rewrite (subs_seq k). eapply hu. refl. apply H3. intros z B.
      rewrite add_mapsto_iff. intros [[h1 h2]|[h1 h2]].
      subst z B. rewrite update_eq. hyp.
      rewrite update_neq. 2: hyp. unfold s0. unfold_restrict.
      destruct (XSet.mem z (fv (Lam x v))). apply hs. hyp. apply int_var.
    Qed.

    Lemma tr_sn : forall E v V, E |- v ~: V -> SN R_aeq v.

    Proof.
      intros E v V ht. eapply int_sn. rewrite <- subs_id. eapply tr_int.
      apply ht. apply valid_id.
    Qed.

(****************************************************************************)
(** ** Computability of vectors of terms.

[vint] is defined in such a way that as much types [Ts] as there are
terms [ts] must be given, but [Ts] can contain more types than
necessary (i.e. the length [n] of [Ts] can be bigger than the length
[p] of [ts]). However, the result does not depend on these extras
types. *)

    Fixpoint vint n (Ts : Tys n) p (ts : Tes p) :=
      match Ts, ts with
        | _, Vnil => True
        | Vcons T _ Ts', Vcons t _ ts' => int T t /\ vint Ts' ts'
        | _, _ => False
      end.

    (*COQ: [Functional Scheme vint] does not seem to end. *)

   (** Basic properties of [vint]. *)

    Lemma vint_le : forall n (Ts : Tys n) p (ts : Tes p),
      vint Ts ts -> p <= n.

    Proof.
      induction Ts; destruct ts; simpl; try omega.
      intros [h1 h2]. gen (IHTs _ _ h2). omega.
    Qed.

    Arguments vint_le [n Ts p ts] _.

    Lemma vint_int_Vnth : forall n (Ts : Tys n) p (ts : Tes p), vint Ts ts ->
      forall j (jn : j<n) (jp : j<p), int (Vnth Ts jn) (Vnth ts jp).

    Proof.
      induction Ts; destruct ts; simpl vint; intros i j jn jp; intuition.
      destruct j; simpl. hyp. apply IHTs. hyp.
    Qed.

    Lemma int_Vnth_vint : forall n (Ts : Tys n) p (ts : Tes p), p <= n ->
      (forall j (jn : j<n) (jp : j<p), int (Vnth Ts jn) (Vnth ts jp))
      -> vint Ts ts.

    Proof.
      induction Ts; destruct ts; intros a b; simpl; auto. omega. split.
      assert (p: 0<S n). omega. assert (q:0<S n0). omega. gen (b _ p q). auto.
      apply IHTs. omega. intros j p q.
      assert (p': S j<S n). omega. assert (q':S j<S n0). omega. gen (b _ p' q').
      rewrite 2!Vnth_cons. destruct (NatUtil.lt_ge_dec 0 (S j)). 2: omega.
      assert (c : Vnth Ts (Vnth_cons_tail_aux p' l) = Vnth Ts p).
      apply Vnth_eq. omega.
      assert (d : Vnth ts (Vnth_cons_tail_aux q' l) = Vnth ts q).
      apply Vnth_eq. omega.
      rewrite c, d. auto.
    Qed.

    Lemma vint_sub_intro : forall n (Ts : Tys n) p (ts : Tes p), vint Ts ts ->
      forall i k (h : i+k<=n) k' (h' : i+k'<= p), k'<=k ->
        vint (Vsub Ts h) (Vsub ts h').

    Proof.
      intros n Ts p ts a i k h k' h' b. apply int_Vnth_vint. hyp.
      intros j jk jk'. rewrite 2!Vnth_sub. apply vint_int_Vnth. hyp.
    Qed.

    Lemma vint_sub_elim : forall n (Ts : Tys n) p (ts : Tes p) (h : 0+p<=n),
      vint Ts ts -> vint (Vsub Ts h) ts.

    Proof.
      intros n Ts p ts h i. apply int_Vnth_vint. refl.
      intros j j1 j2. rewrite Vnth_sub. apply vint_int_Vnth. hyp.
    Qed.

    Lemma vint_typ_cast : forall n (Ts : Tys n) n' (h : n=n') p (ts : Tes p),
      vint (Vcast Ts h) ts <-> vint Ts ts.

    Proof.
      induction Ts; intros n' e p ts.
      subst. rewrite Vcast_refl. refl.
      destruct n'. discr. simpl. destruct ts. refl. rewrite IHTs. refl.
    Qed.

    Lemma vint_term_cast : forall n (Ts : Tys n) p (ts : Tes p) p' (h : p=p'),
      vint Ts (Vcast ts h) <-> vint Ts ts.

    Proof. intros n Ts p ts p' e. subst. rewrite Vcast_refl. refl. Qed.

    Lemma vint_term_app_l : forall n (Ts : Tys n) p (ts : Tes p) q (us : Tes q),
      vint Ts (Vapp ts us) -> vint Ts ts.

    Proof.
      intros n Ts p ts q us; revert p ts q us n Ts.
      induction ts; intros q us m Ts; simpl; destruct Ts; fo.
    Qed.

    Lemma vint_term_app_r : forall n (Ts : Tys n) p (ts : Tes p) q (us : Tes q)
      (h : vint Ts (Vapp ts us)), vint (Vsub Ts (vint_le h)) us.

    Proof.
      intros n Ts p ts q us h.
      assert (a : p+q<=p+q). omega. rewrite <- Vsub_app_r with (v1:=ts) (h:=a).
      apply vint_sub_intro. hyp. refl.
    Qed.

    Lemma vint_sn : forall n (Ts : Tys n) p (ts : Tes p),
      vint Ts ts -> Vforall (SN R_aeq) ts.

    Proof.
      induction Ts; destruct ts; simpl; auto. fo.
      intros [h1 h2]. split.
      eapply int_sn. apply h1.
      apply IHTs. hyp.
    Qed.

    Global Instance vint_vaeq n (Ts : Tys n) p :
      Proper (@vaeq p ==> impl) (@vint n Ts p).

    Proof.
      revert n Ts p. induction Ts; intros p us vs usvs; unfold impl; simpl.
      (* nil *)
      destruct us. VOtac. auto. fo.
      (* cons *)
      rename h into T.
      destruct us. VOtac. auto. revert usvs. VSntac vs. rewrite vaeq_cons.
      gen (cp_int T). intros [T1 _ _ _].
      intros [h1 h2] [i1 i2]. rewrite <- h1, <- h2. intuition.
    Qed.

    (** [v] is computable if, for every vector [vs] computable wrt
      the input types of [v], [apps v vs] is computable. *)

    Lemma int_arrow : forall V v n, n <= arity V ->
      (forall vs : Tes n, vint (inputs V) vs -> int (output V n) (apps v vs))
      -> int V v.

    Proof.
      induction V; simpl; intros v n hn hv.
      (* base *)
      assert (n=0). omega. subst n.
      change (I s (apps v Vnil)). apply hv. auto.
      (* arrow *)
      destruct n. gen (hv Vnil). fo.
      intros v1 h1. apply IHV2 with (n:=n). omega. intros vs hvs.
      change (int (output V2 n) (apps v (Vcons v1 vs))). apply hv. fo.
    Qed.

    (** [apps v vs] is computable if [v] and [vs] so are. *)

    Lemma int_apps : forall n (vs : Tes n) v (Vs : Tys n) U,
      vint Vs vs -> int (arrow Vs U) v -> int U (apps v vs).

    Proof.
      induction vs; simpl; intros v Vs U.
      VOtac. simpl. auto.
      VSntac Vs. simpl. intros [h1 h2] h3.
      eapply IHvs. apply h2. apply h3. hyp.
    Qed.

    (** Computability of vectors of terms is preserved by reduction. *)

    Infix "==>R" := (vaeq_prod R) (at level 70).

    Global Instance vint_vaeq_prod n (Ts : Tys n) p :
      Proper (vaeq_prod R ==> impl) (@vint n Ts p).

    Proof.
      revert n Ts p. induction Ts; intros p us vs usvs; unfold impl; simpl.
      (* nil *)
      destruct us. VOtac. auto. fo.
      (* cons *)
      rename h into T.
      destruct us. VOtac. auto. revert usvs. VSntac vs.
      rewrite vaeq_prod_cons.
      gen (cp_int T). intros [T1 _ T3 _].
      intros [[h1 h2]|[h1 h2]] [i1 i2]; split.
      eapply T3. apply h1. hyp.
      rewrite <- h2. hyp.
      rewrite <- h1. hyp.
      eapply IHTs. apply h2. hyp.
    Qed.

  End int.

  Arguments cp_int [I] _ T.
  Arguments vint_term_app_l [I n Ts p ts q us] _.
  Arguments vint_term_app_r [I n Ts p ts q us] _.

(****************************************************************************)
(** * Monotony properties of [int] and [vint]. *)

  Require Import SetUtil.

  Lemma int_equiv : forall I J T,
    (forall a, occurs a T -> I a [=] J a) -> int I T [=] int J T.

  Proof.
    intros I J. induction T; simpl. fo. intro h.
    rewrite IHT1, IHT2. refl. intuition. intuition.
  Qed.

  Lemma int_equiv' : forall I J T,
    (forall a, occurs a T -> I a [=] J a) -> int I T [= int J T.

  Proof. intros I J T IJ. rewrite (int_equiv _ _ T IJ). refl. Qed.

  Section mon.

    Variables (eq_dec : forall x y : So, {x=y}+{~x=y})
      (I J : So -> set Te) (a : So) (IJa : I a [= J a)
      (IJna : forall b, b <> a -> I b [=] J b).

    Lemma int_mon : forall T,
      (pos a T -> int I T [= int J T) /\ (neg a T -> int J T [= int I T).

    Proof.
      induction T; simpl_pos.
      destruct (eq_dec s a). subst s. fo. fo.
      destruct IHT1 as [i1 i2]. destruct IHT2 as [j1 j2].
      split; intros [h1 h2]; apply arr_incl; fo.
    Qed.

    Lemma int_pos : forall T, pos a T -> int I T [= int J T.

    Proof. intros T h. destruct (int_mon T) as [i _]. fo. Qed.

    Lemma int_neg : forall T, neg a T -> int J T [= int I T.

    Proof. intros T h. destruct (int_mon T) as [_ i]. fo. Qed.

    Lemma vint_mon : forall n (Ts : Tys n) p (ts : Tes p),
      (Vforall (pos a) Ts -> vint I Ts ts -> vint J Ts ts)
      /\ (Vforall (neg a) Ts -> vint J Ts ts -> vint I Ts ts).

    Proof.
      induction Ts; intro p; destruct ts; simpl. fo. fo. fo.
      destruct (IHTs _ ts) as [a1 a2]. split; intros [h1 h2] [i1 i2].
      split. apply int_pos; hyp. apply a1; hyp.
      split. apply int_neg; hyp. apply a2; hyp.
    Qed.

    Lemma vint_pos : forall n (Ts : Tys n) p (ts : Tes p),
      Vforall (pos a) Ts -> vint I Ts ts -> vint J Ts ts.

    Proof. intros n Ts p ts h. destruct (vint_mon Ts ts) as [i _]. fo. Qed.

    Lemma vint_neg : forall n (Ts : Tys n) p (ts : Tes p),
      Vforall (neg a) Ts -> vint J Ts ts -> vint I Ts ts.

    Proof. intros n Ts p ts h. destruct (vint_mon Ts ts) as [_ i]. fo. Qed.

  End mon.

End Make.

(****************************************************************************)
(** * Termination of beta-reduction. *)

Module SN_beta (Export ST : ST_Struct).

  Module Import CP := CP_beta ST.L.
  Module Import SN := Make ST CP.

  Lemma neutral_apps_fun : forall f n (us : Tes n), neutral (apps (Fun f) us).

  Proof. intros f n us. apply neutral_apps. fo. Qed.

  Lemma tr_sn_beta_aeq : forall E v V, E |- v ~: V -> SN beta_aeq v.

  Proof.
    (* The interpretation [I := fun (_ : B) => SN beta_aeq] is valid. *)
    set (I := fun (_ : So) => SN beta_aeq).
    assert (cp_I : forall b, cp (I b)). intro b. apply cp_SN.
    (* We apply [tr_sn] by using [I] as interpretation. *)
    apply tr_sn with (I:=I). hyp.
    (* We now prove that every symbol [f] is computable. *)
    intro f. set (n := arity (typ f)).
    (* [f] is computable if for every vector [ts] of [n] computable terms,
    [apps (Fun f) ts] is computable. *)
    apply int_arrow with (n:=n). refl. intros vs hvs.
    (* The interpretation of [output_base (typ f)] is a computability
      predicate. *)
    rewrite output_arity. simpl. set (b := output_base (typ f)).
    gen (cp_I b). intros [b1 b2 b3 b4].
    (* [vs] are strongly normalizing. *)
    cut (SN (vaeq_prod beta) vs).
    Focus 2. apply sn_vaeq_prod. eapply vint_sn. apply cp_I. apply hvs.
    (* We can therefore proceed by induction on [vs]. *)
    induction 1.
    (* Since [apps (Fun f) x] is neutral, it suffices to prove that all its
    reducts are computable. *)
    apply b4. apply neutral_apps_fun.
    intros y r. assert (k : not_lam (Fun f)). discr.
    destruct (beta_aeq_apps_no_lam k r) as [u [z [h1 h2]]]; subst.
    rewrite vaeq_prod_cons in h2. destruct h2 as [[i1 i2]|[i1 i2]].
    inversion i1; subst. simpl_aeq; subst. inversion H3; subst. inversion H1.
    simpl_aeq; subst. apply H0. hyp. rewrite <- i2. hyp.
  Qed.

End SN_beta.