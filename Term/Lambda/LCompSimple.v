(**

CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05


* Termination of beta-reduction for simply-typed lambda-terms
*)

Set Implicit Arguments.

Require Import Morphisms Basics SN VecUtil LogicUtil LSimple.
Require LTerm.

Module Make (Export ST : LSimple.ST_Struct).

  Module Export S := LSimple.Make ST.

(****************************************************************************)
(** ** Functor providing a termination proof for any CP structure

assuming that every type constant is interpreted by a computability
predicate, and every function symbol is computable. *)

  Module SN (Import CP : CP_Struct).

    Module Export P := Props CP.

    Section int.

      Variables (Bint : So -> pred) (cp_Bint : forall b, cp (Bint b)).

      (** Interpretation of simple types *)

      Fixpoint int T :=
        match T with
          | Base b => Bint b
          | Arr A B => arr (int A) (int B)
        end.

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
        assert (hs0 : valid E s0). intros z B hz. unfold s0, S.restrict.
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
        (* We first prove that [comp s' (single x' a)] is equal to
        [update x a s0]. *)
        assert (k : seq (fv v) (comp s' (single x' a)) (S.update x a s0)).
        intros z hz. unfold comp, s', S.update. eq_dec z x.
        (* z = x *)
        subst. simpl. rewrite single_eq. refl.
        (* z <> x *)
        unfold s0, S.restrict. case_eq (XSet.mem z (fv (Lam x v))).
        (* ~In z (fv (Lam x v)) *)
        Focus 2. rewrite <- not_mem_iff. simpl. set_iff. intuition.
        (* In z (fv (Lam x v)) *)
        intro k. gen (var_notin_fv_subs s0 hz n). fold x'.
        unfold s0, S.restrict. rewrite k. intuition. rewrite single_notin_fv.
        refl. hyp.
        (* We can now apply the induction hypothesis. *)
        rewrite (subs_seq k). eapply hu. refl. apply H3. intros z B.
        rewrite add_mapsto_iff. intros [[h1 h2]|[h1 h2]].
        subst z B. rewrite update_eq. hyp.
        rewrite update_neq. 2: hyp. unfold s0, S.restrict.
        destruct (XSet.mem z (fv (Lam x v))). apply hs. hyp. apply int_var.
      Qed.

      Lemma tr_sn : forall E v V, E |- v ~: V -> SN R_aeq v.

      Proof.
        intros E v V ht. eapply int_sn. rewrite <- subs_id. eapply tr_int.
        apply ht. apply valid_id.
      Qed.

      (** Computability of vectors of terms. *)

      Fixpoint vint n (Ts : Tys n) p (ts : Tes p) :=
        match Ts, ts with
          | _, Vnil => True
          | Vcons T _ Ts', Vcons t _ ts' => int T t /\ vint Ts' ts'
          | _, _ => False
        end.

      (*COQ: [Functional Scheme vint] does not seem to end. *)

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

      Lemma int_base : forall V v,
        (forall n (vs : Tes n),
          vint (inputs V) vs -> int (Base (output V)) (apps v vs)) ->
        int V v.

      Proof.
        induction V; simpl; intros v hv.
        (* base *)
        change (Bint s (apps v Vnil)). apply hv. fo.
        (* arrow *)
        intros v1 h1. apply IHV2. intros n vs hvs.
        change (int (Base (output V2)) (apps v (Vcons v1 vs))). apply hv. fo.
      Qed.

      (** Computability of vectors of terms is preserved by reduction. *)

      Infix "==>R" := (vaeq_prod R) (at level 70).

      Global Instance vint_vaeq_prod n (Ts : Tys n) p :
        Proper (@vaeq_prod R p ==> impl) (@vint n Ts p).

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

  End SN.

(****************************************************************************)
(** ** Termination of beta-reduction. *)

  Import CP_beta.

  Module Import SN_beta := SN CP_beta.

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
    intro f. set (n:=arity(typ f)).
    (* [f] is computable if for every vector [ts] of [n] computable terms,
    [apps (Fun f) ts] is computable. *)
    apply int_base. intros p vs hvs.
    (* The interpretation of [output (typ f)] is a computability predicate. *)
    set (b := output (typ f)). gen (cp_Bint b). intros [b1 b2 b3 b4].
    (* [vs] are strongly normalizing. *)
    cut (SN (@vaeq_prod beta p) vs).
    Focus 2. apply sn_vaeq_prod. eapply vint_sn. apply cp_Bint. apply hvs.
    (* We can therefore proceed by induction on [vs]. *)
    induction 1.
    (* Since [apps (Fun f) x] is neutral, it suffices to prove that all its
    reducts are computable. *)
    apply b4. apply neutral_apps_fun.
    intros y r. assert (k : not_lam (Fun f)). discr.
    destruct (beta_aeq_apps_no_lam k r) as [u [z [h1 h2]]]; subst.
    rewrite vaeq_prod_cons in h2. destruct h2 as [[i1 i2]|[i1 i2]].
    inversion i1; subst. inv_aeq H1; subst. inversion H3; subst. inversion H1.
    inv_aeq i1; subst. apply H0. hyp. rewrite <- i2. hyp.
  Qed.

End Make.
