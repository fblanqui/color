(**

CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2012-04-05

* Termination of beta-reduction for simply-typed lambda-terms
*)

Set Implicit Arguments.

From Stdlib Require Import Morphisms Basics Lia. 
From CoLoR Require Import SN VecUtil LogicUtil SetUtil.
From CoLoR Require Export LSimple LComp.

(****************************************************************************)
(** ** Interpretation of simple types as computability predicates. *)

Module Export Def.

  Section int.

    Variables F X So : Type.

    Notation Te := (@Te F X).

    Variable I : So -> set Te.

    Fixpoint int T :=
      match T with
        | Base b => I b
        | Arr A B => arr (int A) (int B)
      end.

    (** Computability of vectors of terms.

[vint] is defined in such a way that as much types [Ts] as there are
terms [ts] must be given, but [Ts] can contain more types than
necessary (i.e. the length [n] of [Ts] can be bigger than the length
[p] of [ts]). However, the result does not depend on these extras
types. *)

    Notation Tes := (vector Te).
    Notation Ty := (@Ty So).
    Notation Tys := (vector Ty).

    Fixpoint vint {n} (Ts : Tys n) {p} (ts : Tes p) :=
      match Ts, ts with
        | _, Vnil => True
        | Vcons T Ts', Vcons t ts' => int T t /\ vint Ts' ts'
        | _, _ => False
      end.

    (*COQ: [Functional Scheme vint] does not seem to end. *)

  End int.

End Def.

(****************************************************************************)
(** * Functor providing a termination proof for any CP structure

assuming that every type constant is interpreted by a computability
predicate, and every function symbol is computable. *)

Module Make (Export ST : ST_Struct)
  (Export CP : CP_Struct with Module L := ST.L).

  Module Export C := LComp.Make CP.
  Module Export T := LSimple.Make ST.

  Notation int := (@int F X So).
  Notation vint := (@vint F X So).

  Section int.

    Variables (I : So -> Te -> Prop) (cp_I : forall b, cp (I b)).

(****************************************************************************)
(** ** Properties of the interpretation of simple types *)

    Notation int := (int I).

    Lemma int_base b t : I b t <-> int (Base b) t.

    Proof. refl. Qed.

    (** The interpretation of a type is a computability predicate. *)

    Global Instance cp_int : forall T, cp (int T).

    Proof. induction T; simpl. apply cp_I. apply cp_arr; hyp. Qed.

    Global Instance int_aeq : Proper (Logic.eq ==> aeq ==> impl) int.

    Proof.
      intros T V TV. subst V. destruct (cp_int T) as [h _ _ _].
      intros t u tu i. rewrite <- tu. hyp.
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
(** ** Termination proof assuming that function symbols are computable. *)

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
      try rename X into X0. (* compat: variable is X0 before coq 8.15 but X after *)
      rename X0 into A; rename V0 into V.
      simpl. set (x' := var x v s). set (s' := S.update x (Var x') s).
      gen (cp_int A). intros [A1 A2 A3 A4].
      gen (cp_int V). intros [V1 V2 V3 V4]. apply cp_lam; class.
      intros a ha. unfold s', x'. rewrite subs_comp, single_update_var.
      eapply hu. refl. apply H3.
      intros z B. env. rewrite add_mapsto_iff. intros [[h1 h2]|[h1 h2]]; subst.
      rewrite update_eq. hyp.
      rewrite update_neq. apply hs. hyp. hyp.
    Qed.

    Lemma tr_sn : forall E v V, E |- v ~: V -> SN R_aeq v.

    Proof.
      intros E v V ht. eapply int_sn. rewrite <- subs_id. eapply tr_int.
      apply ht. apply valid_id.
    Qed.

(****************************************************************************)
(** ** Properties of [vint]. *)

    Notation vint := (vint I).

   (** Basic properties of [vint]. *)

    Lemma vint_le : forall n (Ts : Tys n) p (ts : Tes p),
      vint Ts ts -> p <= n.

    Proof.
      induction Ts; destruct ts; simpl; try lia.
      intros [h1 h2]. gen (IHTs _ _ h2). lia.
    Qed.

    Arguments vint_le [n Ts p ts] _.

    Lemma vint_le' : forall n (Ts : Tys n) p (ts : Tes p),
      vint Ts ts -> 0+p <= n.

    Proof. simpl. apply vint_le. Qed.

    Lemma vint_typs_eq : forall n (Ts Us : Tys n) p (ts : Tes p),
      vint Us ts -> Us = Ts -> vint Ts ts.

    Proof. intros n Ts Us p ts h e. subst. hyp. Qed.

    Lemma vint_typs_eq_cast : forall n (Ts : Tys n) m (Us : Tys m)
      (h : n=m) p (ts : Tes p), vint Us ts -> Us = Vcast Ts h -> vint Ts ts.

    Proof.
      intros n Ts m Us h p ts i. subst. rewrite Vcast_refl. intro; subst. hyp.
    Qed.

    Lemma vint_elim_nth : forall n (Ts : Tys n) p (ts : Tes p),
      vint Ts ts ->
      forall j (jn : j<n) (jp : j<p), int (Vnth Ts jn) (Vnth ts jp).

    Proof.
      induction Ts; destruct ts; simpl Def.vint; intros hts j jn jp; intuition auto with *.
      destruct j; simpl. hyp. apply IHTs. hyp.
    Qed.

    Lemma vint_intro_nth : forall n (Ts : Tys n) p (ts : Tes p), p <= n ->
      (forall j (jn : j<n) (jp : j<p), int (Vnth Ts jn) (Vnth ts jp))
      -> vint Ts ts.

    Proof.
      induction Ts; destruct ts; intros a b; simpl; auto. lia. split.
      assert (p: 0<S n). lia. assert (q:0<S n0). lia. gen (b _ p q). auto.
      apply IHTs. lia. intros j p q.
      assert (p': S j<S n). lia. assert (q':S j<S n0). lia. gen (b _ p' q').
      rewrite 2!Vnth_cons. destruct (NatUtil.lt_ge_dec 0 (S j)). 2: lia.
      assert (c : Vnth Ts (Vnth_cons_tail_aux p' l) = Vnth Ts p).
      apply Vnth_eq. lia.
      assert (d : Vnth ts (Vnth_cons_tail_aux q' l) = Vnth ts q).
      apply Vnth_eq. lia.
      rewrite c, d. auto.
    Qed.

    Lemma vint_eq : forall n (Ts : Tys n) p (ts : Tes p), p <= n ->
      (vint Ts ts
        <-> (forall j (jn : j<n) (jp : j<p), int (Vnth Ts jn) (Vnth ts jp))).

    Proof.
      intros n Ts p ts pn. split. apply vint_elim_nth.
      apply vint_intro_nth. hyp.
    Qed.

    Lemma vint_sub_intro : forall n (Ts : Tys n) p (ts : Tes p),
      vint Ts ts -> forall i k (h : i+k<=n) k' (h' : i+k'<= p), k'<=k ->
        vint (Vsub Ts h) (Vsub ts h').

    Proof.
      intros n Ts p ts a i k h k' h' b. apply vint_intro_nth. hyp.
      intros j jk jk'. rewrite 2!Vnth_sub. apply vint_elim_nth. hyp.
    Qed.

    Lemma vint_sub_typ_elim : forall n (Ts : Tys n) p (ts : Tes p) (h : 0+p<=n),
      vint (Vsub Ts h) ts -> vint Ts ts.

    Proof.
      intros n Ts p ts h. rewrite 2!vint_eq; try lia. intuition.
      gen (H _ jp jp). rewrite Vnth_sub. erewrite Vnth_eq. intro i; apply i.
      refl.
    Qed.

    Lemma vint_sub_typ_intro : forall n (Ts : Tys n) p (ts : Tes p)
      (h : 0+p<=n), vint Ts ts -> vint (Vsub Ts h) ts.

    Proof.
      intros n Ts p ts h i. apply vint_intro_nth. refl.
      intros j j1 j2. rewrite Vnth_sub. apply vint_elim_nth. hyp.
    Qed.

    Lemma vint_sub_term_intro : forall n (Ts : Tys n) p (ts : Tes p)
      q (h : 0+q<=p), vint Ts ts -> vint Ts (Vsub ts h).

    Proof.
      intros n Ts p ts q h hts. apply vint_intro_nth. gen (vint_le hts). lia.
      intros j jn jq. rewrite Vnth_sub. apply vint_elim_nth. hyp.
    Qed.

    Lemma vint_cast_typ : forall n (Ts : Tys n) n' (h : n=n') p (ts : Tes p),
      vint (Vcast Ts h) ts <-> vint Ts ts.

    Proof.
      induction Ts; intros n' e p ts.
      subst. rewrite Vcast_refl. refl.
      destruct n'. discr. rewrite Vcast_cons. simpl. destruct ts.
      refl. rewrite IHTs. refl.
    Qed.

    Lemma vint_cast_term : forall n (Ts : Tys n) p (ts : Tes p) p' (h : p=p'),
      vint Ts (Vcast ts h) <-> vint Ts ts.

    Proof. intros n Ts p ts p' e. subst. rewrite Vcast_refl. refl. Qed.

    Lemma vint_app_term_elim_l : forall n (Ts : Tys n) p (ts : Tes p)
      q (us : Tes q), vint Ts (Vapp ts us) -> vint Ts ts.

    Proof.
      intros n Ts p ts q us; revert p ts q us n Ts.
      induction ts; intros q us m Ts; simpl; destruct Ts; fo.
    Qed.

    Lemma vint_app_term_elim_r : forall n (Ts : Tys n) p (ts : Tes p)
      q (us : Tes q) (h : vint Ts (Vapp ts us)), vint (Vsub Ts (vint_le h)) us.

    Proof.
      intros n Ts p ts q us h.
      assert (a : p+q<=p+q). lia. rewrite <- Vsub_app_r with (v1:=ts) (h:=a).
      apply vint_sub_intro. hyp. refl.
    Qed.

    Lemma vint_app_intro : forall n (Ts : Tys n) p (ts : Tes p)
      q (us : Tes q) (h : p+q <= n), vint Ts ts -> vint (Vsub Ts h) us ->
      vint Ts (Vapp ts us).

    Proof.
      induction Ts; simpl.
      destruct ts; simpl; intros q us i.
      assert (q=0). lia. subst. VOtac. fo.
      lia.
      destruct ts; simpl; intros q us i.
      destruct us; simpl. fo. rewrite Vsub_cons. intuition.
      eapply vint_sub_typ_elim. apply H2.
      rewrite Vsub_cons. intuition. eapply IHTs. hyp. apply H0.
    Qed.

    Lemma vint_forall_sn : forall n (Ts : Tys n) p (ts : Tes p),
      vint Ts ts -> Vforall (SN R_aeq) ts.

    Proof.
      induction Ts; destruct ts; simpl; auto. fo.
      intros [h1 h2]. split.
      eapply int_sn. apply h1.
      apply IHTs. hyp.
    Qed.

    Global Instance vint_vaeq n (Ts : Tys n) p :
      Proper (vaeq ==> impl) (vint Ts (p:=p)).

    Proof.
      revert n Ts p. induction Ts; intros p us vs usvs; unfold impl; simpl.
      (* nil *)
      destruct us. VOtac. auto. fo.
      (* cons *)
      rename h into T.
      destruct us. VOtac. auto. revert usvs. VSntac vs.
      rewrite Vforall2_cons_eq. gen (cp_int T). intros [T1 _ _ _].
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
      assert (n=0). lia. subst n.
      change (I s (apps v Vnil)). apply hv. auto.
      (* arrow *)
      destruct n. gen (hv Vnil). fo.
      intros v1 h1. apply IHV2 with (n:=n). lia. intros vs hvs.
      change (int (output V2 n) (apps v (Vcons v1 vs))). apply hv. fo.
    Qed.

    (** [apps v vs] is computable if [v] and [vs] so are. *)

    Lemma int_apps : forall n (vs : Tes n) v (Vs : Tys n) A,
      vint Vs vs -> int (arrow Vs A) v -> int A (apps v vs).

    Proof.
      induction vs; simpl; intros v Vs V.
      VOtac. simpl. auto.
      VSntac Vs. simpl. intros [h1 h2] h3.
      eapply IHvs. apply h2. apply h3. hyp.
    Qed.

    (** Computability of vectors of terms is preserved by reduction. *)

    Global Instance vint_clos_vaeq n (Ts : Tys n) p :
      Proper (clos_vaeq R ==> impl) (vint Ts (p:=p)).

    Proof.
      revert n Ts p. induction Ts; intros p us vs usvs; unfold impl; simpl.
      (* nil *)
      destruct us. VOtac. auto. fo.
      (* cons *)
      rename h into T.
      destruct us. VOtac. auto. revert usvs. VSntac vs.
      rewrite clos_vaeq_cons.
      gen (cp_int T); intros [T1 _ T3 _].
      intros [[h1 h2]|[h1 h2]] [i1 i2]; split.
      eapply T3. apply h1. hyp.
      rewrite <- h2. hyp.
      rewrite <- h1. hyp.
      eapply IHTs. apply h2. hyp.
    Qed.

  End int.

  Arguments cp_int [I] _ T.
  Arguments vint_app_term_elim_l [I n Ts p ts q us] _.
  Arguments vint_app_term_elim_r [I n Ts p ts q us] _.
  Arguments vint_le [I n Ts p ts] _.
  Arguments vint_le' [I n Ts p ts] _.
  Arguments vint_elim_nth [I n Ts p ts] _ [j] _ _.

(****************************************************************************)
(** ** Monotony properties of [int] and [vint]. *)

  Import SetUtil.

  Lemma int_equiv : forall I J T,
    (forall a, occurs a T -> I a [=] J a) -> int I T [=] int J T.

  Proof.
    intros I J. induction T; simpl. fo. intro h.
    rewrite IHT1, IHT2. refl. intuition. intuition.
  Qed.

  Lemma int_equiv' : forall I J T,
    (forall a, occurs a T -> I a [=] J a) -> int I T [<=] int J T.

  Proof. intros I J T IJ. rewrite (int_equiv _ _ T IJ). refl. Qed.

  Section mon.

    Variables (eq_dec : forall x y : So, {x=y}+{~x=y})
      (I J : So -> set Te) (a : So) (IJa : I a [<=] J a)
      (IJna : forall b, b <> a -> I b [=] J b).

    Lemma int_mon : forall T,
      (pos a T -> int I T [<=] int J T) /\ (neg a T -> int J T [<=] int I T).

    Proof.
      induction T; simpl_pos.
      destruct (eq_dec s a). subst s. fo. fo.
      destruct IHT1 as [i1 i2]. destruct IHT2 as [j1 j2].
      split; intros [h1 h2]; apply arr_incl; fo.
    Qed.

    Lemma int_pos : forall T, pos a T -> int I T [<=] int J T.

    Proof. intros T h. destruct (int_mon T) as [i _]. fo. Qed.

    Lemma int_neg : forall T, neg a T -> int J T [<=] int I T.

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
(** * Termination of beta-eta-reduction. *)

Module SN_beta_eta (Export ST : ST_Struct).

  Module Import CP := CP_beta_eta ST.L.
  Module Import SN := Make ST CP.

  Lemma neutral_apps_fun : forall f n (us : Tes n), neutral (apps (Fun f) us).

  Proof. intros f n us. apply neutral_apps. fo. Qed.

  Lemma tr_sn_beta_aeq : forall E v V, E |- v ~: V -> SN R_aeq v.

  Proof.
    (* The interpretation [I := fun (_ : B) => SN R_aeq] is valid. *)
    set (I := fun (_ : So) => SN R_aeq).
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
    cut (SN (clos_vaeq R) vs).
    2:{ apply sn_clos_vaeq_intro. eapply vint_forall_sn. apply cp_I.
        apply hvs. }
    (* We can therefore proceed by induction on [vs]. *)
    induction 1.
    (* Since [apps (Fun f) x] is neutral, it suffices to prove that all its
    reducts are computable. *)
    apply b4. apply neutral_apps_fun.
    intros y r. 
    destruct (R_aeq_apps_fun r) as [vs [h1 h2]]; clear r; subst.
    apply H0. hyp. rewrite <- h2. hyp.
  Qed.

  Arguments R_aeq_apps_fun [f n us t0] _ : rename.
End SN_beta_eta.
