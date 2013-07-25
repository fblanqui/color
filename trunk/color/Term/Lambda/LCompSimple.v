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

    Variables (Bint : So -> Te -> Prop) (cp_Bint : forall b, cp (Bint b)).

    (** Interpretation of simple types *)

    Fixpoint int T :=
      match T with
        | Base b => Bint b
        | Arr A B => arr (int A) (int B)
      end.

    Lemma int_base b t : Bint b t <-> int (Base b) t.

    Proof. refl. Qed.

    Lemma cp_int : forall T, cp (int T).

    Proof. induction T; simpl. apply cp_Bint. apply cp_arr; hyp. Qed.

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

    (** Termination proof assuming that function symbols are
      computable. *)

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

    (** Computability of vectors of terms.

It is defined in such a way that [Ts] can contain more types than
necessary (i.e. the length [n] of [Ts] can be bigger than or equal to
the length [p] of [ts]), but the result does not depend on these
extras types. *)

    Fixpoint vint n (Ts : Tys n) p (ts : Tes p) :=
      match Ts, ts with
        | _, Vnil => True
        | Vcons T _ Ts', Vcons t _ ts' => int T t /\ vint Ts' ts'
        | _, _ => False
      end.

    (*COQ: [Functional Scheme vint] does not seem to end. *)

    Lemma int_Vnth : forall n (Ts : Tys n) p (ts : Tes p)
      j (jn : j<n) (jp : j<p), vint Ts ts -> int (Vnth Ts jn) (Vnth ts jp).

    Proof.
      induction Ts; destruct ts; simpl vint; intros j jn jp; intuition.
      destruct j; simpl. hyp. apply IHTs. hyp.
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

    Lemma vint_term_app_l : forall p (ts : Tes p) q (us : Tes q) n (Ts : Tys n),
      vint Ts (Vapp ts us) -> vint Ts ts.

    Proof. induction ts; intros q us m Ts; simpl; destruct Ts; fo. Qed.

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
      change (Bint s (apps v Vnil)). apply hv. auto.
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

  Arguments cp_int [Bint] _ T.

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
    (* The interpretation [Bint := fun (_ : B) => SN beta_aeq] is valid. *)
    set (Bint := fun (_ : So) => SN beta_aeq).
    assert (cp_Bint : forall b, cp (Bint b)). intro b. apply cp_SN.
    (* We apply [tr_sn] by using [Bint] as interpretation. *)
    apply tr_sn with (Bint:=Bint). hyp.
    (* We now prove that every symbol [f] is computable. *)
    intro f. set (n := arity_typ f).
    (* [f] is computable if for every vector [ts] of [n] computable terms,
    [apps (Fun f) ts] is computable. *)
    apply int_arrow with (n:=n). refl. intros vs hvs.
    (* The interpretation of [output_base (typ f)] is a computability
      predicate. *)
    rewrite output_arity. simpl. set (b := output_base (typ f)).
    gen (cp_Bint b). intros [b1 b2 b3 b4].
    (* [vs] are strongly normalizing. *)
    cut (SN (vaeq_prod beta) vs).
    Focus 2. apply sn_vaeq_prod. eapply vint_sn. apply cp_Bint. apply hvs.
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
