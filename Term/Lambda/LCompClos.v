(**
CoLoR, a Coq library on rewriting and termination.

See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2013-05-02

* Computability closure

and proof that it enforces termination of higher-order rewrite systems.

After "Inductive-data-type Systems", F. Blanqui, J.-P. Jouannaud and
  M. Okada, Theoretical Computer Science 272, p. 41-68, 2002,
  http://dx.doi.org/10.1016/S0304-3975(00)00347-9. *)

Set Implicit Arguments.

From Coq Require Import Morphisms Basics.
From CoLoR Require Import LogicUtil LCompSimple VecUtil RelUtil LCall LCompInt
     SetUtil SN NatUtil LCompRewrite EqUtil.
From Coq Require Lexicographic_Product.
From CoLoR Require Union Lexico.


Module Export Def.

(****************************************************************************)
(** * Abstract definition of the computability closure. *)

  Section cc.

    (** We assume given a set [F] for function symbols, a set [X] for
       variables, and a set [So] for type constants. *)

    Variables F X : Type.

    Notation Te := (@Te F X).
    Notation Var := (@Var F X).
    Notation Fun := (@Fun F X).
    Notation Tes := (vector Te).
    Notation call := (@call F X).

    Variable So : Type.

    Notation Ty := (@Ty So).
    Notation Tys := (vector Ty).

    (** We assume given a structure for finite sets on [X]. *)

    Variable ens_X : Ens X.

    Notation In := (Ens_In ens_X).
    Notation fvs := (@fvs F X ens_X).

    (** We assume given a set [En] for typing environments equipped with
       the following functions: *)

    Variable env : Env X So.

    Notation En := (Env_type env).
    Notation MapsTo := (Env_MapsTo env).
    Notation add := (Env_add env).

    (** We assume given a type for each function symbol. *)

    Variable typ : F -> Ty.

    Notation TypArgs := (@TypArgs F X So typ).

    (** For each symbol [f], we assume given a finite number of
       accessible arguments. *)

    Variables (Acc : F -> nat -> Prop)
      (Acc_arity : forall g i, Acc g i -> i < arity (typ g)).

    (** We assume given an environment-indexed family of relations on calls. *)

    Variable gt1 : En -> relation call.

(****************************************************************************)
(** ** Definition of the computability closure for a call [mk_call f ls]. *)

    Section cc_def.

      Variables (f : F) (n : nat) (ls : Tes n).

      Inductive cc : En -> Te -> Ty -> Prop :=

      | cc_arg : forall E i (i1 : i < n) (i2 : i < arity (typ f)),
        cc E (Vnth ls i1) (Vnth (inputs (typ f)) i2)

      | cc_var : forall E x T,
        MapsTo x T E -> ~In x (fvs ls) -> cc E (Var x) T
      (* The assumption [~In x (fvs ls)] is derivable since it is assumed in
         [cc_lam], unique rule adding a variable. *)

      | cc_app : forall E t u A B,
        cc E t (A ~~> B) -> cc E u A -> cc E (App t u) B

      | cc_lam : forall E x A v B,
        ~In x (fvs ls) -> cc (add x A E) v B -> cc E (Lam x v) (A ~~> B)

      | cc_acc : forall E g (us : TypArgs g) i (hi : Acc g i),
        cc E (apps (Fun g) us) (Base (output_base (typ g))) ->
        cc E (Vnth us (Acc_arity hi)) (Vnth (inputs (typ g)) (Acc_arity hi))

      | cc_call : forall E g p (us : Tes p),
        0+p <= arity (typ g) -> gt1 E (mk_call f ls) (mk_call g us) ->
        (forall i (i1 : i < p) (i2 : i < arity (typ g)),
          cc E (Vnth us i1) (Vnth (inputs (typ g)) i2)) ->
        cc E (apps (Fun g) us) (output (typ g) p).

(****************************************************************************)
(** Variants of [cc] constructors for proving that some term is in [cc]. *)

     Lemma cc_arg' E v V i (i1 : i < n) (i2 : i < arity (typ f)) :
        v = Vnth ls i1 -> V = Vnth (inputs (typ f)) i2 -> cc E v V.

     Proof. intros hv hV. subst. apply cc_arg. Qed.

     Lemma cc_acc' E v V g (us : TypArgs g) i (hi : Acc g i) :
        cc E (apps (Fun g) us) (Base (output_base (typ g))) ->
        v = Vnth us (Acc_arity hi) ->
        V = Vnth (inputs (typ g)) (Acc_arity hi) -> cc E v V.

     Proof. intros h hv hV. subst. apply cc_acc. hyp. Qed.

     Lemma cc_call' E v V g p (us : Tes p) :
        0+p <= arity (typ g) -> gt1 E (mk_call f ls) (mk_call g us) ->
        (forall i (i1 : i < p) (i2 : i < arity (typ g)),
          cc E (Vnth us i1) (Vnth (inputs (typ g)) i2)) ->
        v = apps (Fun g) us -> V = output (typ g) p -> cc E v V.

     Proof. intros h1 h2 h3 hv hV. subst. apply cc_call; hyp. Qed.

(****************************************************************************)
(** Inversion lemma and tactic for [cc]. *)

      Lemma inv_cc : forall E t T, cc E t T ->
        (exists i (i1 : i < n) (i2 : i < arity (typ f)),
          t = Vnth ls i1 /\ T = Vnth (inputs (typ f)) i2)
        \/ (exists x, t = Var x /\ MapsTo x T E /\ ~In x (fvs ls))
        \/ (exists v V u, t = App u v /\ cc E u (V ~~> T) /\ cc E v V)
        \/ (exists x v A B, t = Lam x v /\ T = A ~~> B /\ ~In x (fvs ls)
          /\ cc (add x A E) v B)
        \/ (exists g (us : TypArgs g) i (hi : Acc g i),
          t = Vnth us (Acc_arity hi) /\ T = Vnth (inputs (typ g)) (Acc_arity hi)
          /\ cc E (apps (Fun g) us) (Base (output_base (typ g))))
        \/ (exists g p (us : Tes p),
          t = apps (Fun g) us /\ T = output (typ g) p
          /\ 0+p <= arity (typ g) /\ gt1 E (mk_call f ls) (mk_call g us)).

      Proof.
        intros E t T h. inversion h.
        left. ex i i1 i2. intuition.
        right. left. exists x. intuition.
        do 2 right. left. ex u A t0. intuition.
        do 3 right. left. ex x v A B. intuition.
        do 4 right. left. ex g us i hi. intuition.
        do 5 right. ex g p us. intuition.
      Qed.

    End cc_def.

    Lemma cc_cast : forall f n (ls : Tes n) p (h : n=p) E v V,
      cc f (Vcast ls h) E v V <-> cc f ls E v V.

    Proof. intros f n ls p h E v V. subst p. rewrite Vcast_refl. refl. Qed.

  End cc.

  Arguments cc [F X So] ens_X [env] typ [Acc] Acc_arity gt1 f [n] ls _ _ _.

  Ltac inv_cc h := apply inv_cc in h;
    let i := fresh "i" in let g := fresh "g" in let us := fresh "us" in
      let x := fresh "x" in let u := fresh "u" in let v := fresh "v" in
        let A := fresh "A" in let B := fresh "B" in let p := fresh "p" in
          let h1 := fresh "h" in let h2 := fresh "h" in
            let h3 := fresh "h" in let h4 := fresh "h" in
              destruct h as
                [[i [h1 [h2 [h3 h4]]]]
                  |[[x [h1 [h2 h3]]]
                    |[[v [A [u [h1 [h2 h3]]]]]
                      |[[x [v [A [B [h1 [h2 [h3 h4]]]]]]]
                        |[[g [us [i [h1 [h2 [h3 h4]]]]]]
                          |[g [p [us [h1 [h2 [h3 h4]]]]]]]]]]].

End Def.

(****************************************************************************)
(** * Ingredients of a computability closure. *)

Module Type CC_Struct.

  (** We assume given a BI structure. *)

  Declare Module Export BI : BI_Struct.

  (** Some notations. *)

  Notation caeq := (@caeq F X FOrd.eq_dec XOrd.eq_dec ens_X var_notin).
  Notation cc := (@cc F X So ens_X env typ Acc Acc_arity).

End CC_Struct.

(****************************************************************************)
(** * Axiomatic proof of correctness of the computability closure. *)

Module Comp (Export CC : CC_Struct)
  (Export CP : CP_Struct with Module L := CC.BI.ST.L).

  Module Export CS := LCompSimple.Make CC.BI.ST CP.
  Module Export C := LCall.Make CC.BI.ST.

  Section comp.

    Variables

      (** We assume given an interpretation of base types as
         computability predicates. *)

      (I : So -> set Te) (I_cp : forall b, cp (I b))

      (** We assume that the accessible arguments of a computable term of
         the form [apps (Fun g) ts] are computable. *)

      (comp_acc : forall g (ts : Tes (arity (typ g))),
        int I (Base (output_base (typ g))) (apps (Fun g) ts) ->
        forall i (hi : Acc g i),
          int I (Vnth (inputs (typ g)) (Acc_arity hi)) (Vnth ts (Acc_arity hi)))

      (** We assume given an environment-indexed family of relations
      on calls. *)

      (gt1 : En -> relation call)

      (** We assume given a relation [gt2] on max calls that is
      wellfounded, compatible with [mcaeq] and decreases whenever [gt1]
      decreases. *)

      (gt2 : relation max_call) (gt2_wf : WF gt2)
      (gt2_mcaeq : Proper (mcaeq ==> mcaeq ==> impl) gt2)
      (gt2_gt1 : forall E f n (ls : Tes n) g p (us : Tes p),
        n <= arity (typ f) -> p <= arity (typ g) ->
        gt1 E (mk_call f ls) (mk_call g us) ->
        forall s (ts' : Tes (arity (typ f) - n)) (us' : Tes (arity (typ g) - p))
          (nf : n + (arity (typ f) - n) = arity (typ f))
          (pg : p + (arity (typ g) - p) = arity (typ g)),
          vint I (inputs (typ f)) (Vapp (Vmap (subs s) ls) ts') ->
          (forall x A, MapsTo x A E -> ~XSet.In x (fvs ls) -> int I A (s x)) ->
          gt2 (mk_max_call f (Vcast (Vapp (Vmap (subs s) ls) ts') nf))
              (mk_max_call g (Vcast (Vapp (Vmap (subs s) us) us') pg)))

      (** Induction hypothesis: we assume that, given a [mk_max_call f
         ts] such that [ts] are computable, every call [mk_max_call g
         us] smaller in [gt2], is computable whenever [us] are
         computable. *)

      (f : F) (ts : TypArgs f) (hts : vint I (inputs (typ f)) ts)
      (IH : forall g (us : TypArgs g),
          gt2 (mk_max_call f ts) (mk_max_call g us) ->
        vint I (inputs (typ g)) us ->
        int I (output (typ g) (arity (typ g))) (apps (Fun g) us))

      (** We assume given some terms [ls] and some substitution [s0]
      such that [Vmap (subs s0) ls] is alpha-equivalent to a prefix of
      [ts]. *)

      (n : nat) (ls : Tes n) (s0 : X -> Te) (h : 0+n <= arity (typ f))
      (hls : Vmap (subs s0) ls ~~~ Vsub ts h).

(****************************************************************************)
(** ** Correctness proof:

we prove that, if [v] is in the closure of [mk_call f ls] and [E], and
[s] is a substitution equal to [s0] on [fvs ls] and computable on
variables of [E] not in [fvs ls], then [subs s v] is computable. *)

    Lemma cc_comp : forall E v V, cc gt1 f ls E v V -> forall s,
      (forall x, XSet.In x (fvs ls) -> s x = s0 x) ->
      (forall x A, MapsTo x A E -> ~XSet.In x (fvs ls) -> int I A (s x)) ->
      int I V (subs s v).

    Proof.
      (* We proceed by induction on [cc]. *)
      induction 1; intros s hs1 hs2.

      (* cc_arg *)
      rewrite <- Vnth_map with (f:=subs s). apply vint_elim_nth.
      (* We prove that [s] is equal to [s0] on [ls]. *)
      assert (a : Vmap (subs s) ls = Vmap (subs s0) ls).
      apply Vmap_eq. apply Vforall_intro. intros lj hj.
      destruct (Vin_nth hj) as [j [j1 j2]]. subst lj.
      apply subs_seq. intros x hx. apply hs1. eapply In_fvs_Vnth. apply hx.
      rewrite a, hls. apply vint_sub_term_intro. hyp.

      (* cc_var *)
      apply hs2; hyp.

      (* cc_app *)
      simpl. apply IHcc1. hyp. hyp. apply IHcc2. hyp. hyp.

      (* cc_lam *)
      gen (cp_int I_cp A). intros [A1 A2 A3 A4].
      gen (cp_int I_cp B). intros [B1 B2 B3 B4]. simpl. apply cp_lam; class.
      intros a ha. rewrite subs_comp, single_update_var.
      eapply IHcc. intros y hy. unfold Def.update. eq_dec y x.
      subst. contr. apply hs1. hyp.
      intros z Z. simpl. rewrite add_mapsto_iff.
      intros [[h1 h2]|[h1 h2]] i; subst.
      rewrite update_eq. hyp.
      rewrite update_neq. apply hs2; hyp. hyp.

      (* cc_acc *)
      rewrite <- Vnth_map with (f:=subs s). apply comp_acc.
      replace (Fun g) with (subs s (Fun g)). 2: refl.
      rewrite <- subs_apps. apply IHcc; hyp.

      (* cc_call *)
      rewrite subs_apps. simpl.
      (* We prove that [Vmap (subs s0) ls = Vmap (subs s) ls]. *)
      assert (e : Vmap (subs s0) ls = Vmap (subs s) ls).
      apply Vmap_eq. apply Vforall_intro. intros y hy.
      destruct (Vin_nth hy) as [i [i1 i2]]. subst y.
      apply subs_seq. intros z hz. sym. apply hs1. eapply In_fvs_Vnth. apply hz.
      (* Proof that [t = apps (Fun g) (Vmap (subs s) us)] is computable:
         we prove that for all computable [vs], [apps t vs] is computable. *)
      apply int_arrow with (n := arity (typ g) - p). rewrite arity_output. refl.
      intros vs hvs. rewrite output_output.
      assert (pg : p + (arity (typ g) - p) = arity (typ g)). lia.
      rewrite pg, apps_apps, <- apps_cast with (h:=pg).
      (* We now use the induction hypothesis [IH]. *)
      apply IH.
      (* Proof that [gt2 (mk_max_call f ts)
         (mk_max_call g (Vcast (Vapp (Vmap (subs s) us) vs) pg))]. *)
      rewrite (Veq_app ts h).
      assert (nf : n + (arity (typ f) - (0 + n)) = arity (typ f)). lia.
      eapply gt2_mcaeq with (x := mk_max_call f
        (Vcast (Vapp (Vmap (subs s) ls) (Vsub ts (Veq_app_aux2 h))) nf)).
      2: refl. apply caeq_intro. rewrite Vforall2_cast.
      apply Vforall2_intro_nth.
      intros i hi. rewrite !Vnth_app. simpl. destruct (le_gt_dec n i). refl.
      apply Vforall2_elim_nth. rewrite <- e, (Vsub_pi h). hyp.
      eapply gt2_gt1; auto. apply H0.
      apply vint_app_intro with (h := Veq_app_aux2 h).
      rewrite <- e, hls. apply vint_sub_term_intro. hyp.
      apply vint_sub_intro. hyp. refl. hyp.
      (* Proof that [Vapp (Vmap (subs s) us) vs] are computable. *)
      rewrite vint_cast_term. clear pg.
      assert (pg : p + (arity (typ g) - p) <= arity (typ g)). lia.
      apply vint_app_intro with (h := pg).
      (* Proof that [Vmap (sub s) us] are computable. *)
      apply vint_intro_nth. lia.
      intros j jn jp. rewrite Vnth_map. apply H2; hyp.
      (* Proof that [vs] are computable. *)
      apply vint_eq. refl. intros j jn jp. rewrite Vnth_sub.
      assert (k : j < arity (output (typ g) p)). rewrite arity_output. hyp.
      assert (a : Vnth (inputs (typ g)) (Vnth_sub_aux p pg jn)
                  = Vnth (inputs (output (typ g) p)) k). sym. simpl in H.
      rewrite inputs_output with (h:=H), Vnth_sub. apply Vnth_eq. refl.
      setoid_rewrite a. apply vint_elim_nth. hyp.
    Qed.

  End comp.

End Comp.

(****************************************************************************)
(** * Axiomatic proof of the termination of a rewrite system

whose right hand-sides are in the computability closure of their
corresponding left hand-sides. *)

Module Termin (Export CC : CC_Struct)
  (Export RS : RS_Struct with Module L := CC.BI.ST.L).

  Module Export CR := LCompRewrite.Make RS.

  (** We use the CP structure for the union of beta-reduction and
  rewriting defined in LCompRewrite. *)

  Module CP := CP_beta_eta_rewrite RS.

  Module Export C := Comp CC CP.

  Section termin.

    Variables

      (** We assume given an interpretation of base types as
         computability predicates. *)

      (I : So -> set Te) (I_cp : forall b, cp (I b))

      (** We assume that the accessible arguments of a computable term of
         the form [apps (Fun g) ts] are computable. *)

      (comp_acc : forall g (ts : TypArgs g),
        int I (Base (output_base (typ g))) (apps (Fun g) ts) ->
        forall i (hi : Acc g i),
          int I (Vnth (inputs (typ g)) (Acc_arity hi)) (Vnth ts (Acc_arity hi)))

      (** We assume that [apps (Fun f) ts] is computable if all its
         reducts and arguments [ts] are computable. *)

      (comp_fun : forall f (ts : TypArgs f),
        vint I (inputs (typ f)) ts ->
        (forall u, apps (Fun f) ts =>R u -> I (output_base (typ f)) u) ->
        I (output_base (typ f)) (apps (Fun f) ts))

      (** We assume given an environment-indexed family of relations
         on calls. *)

      (gt1 : En -> relation call)

      (** We assume given a relation [gt2] on max calls that is
      wellfounded, compatible with [mcaeq] and [clos_vaeq], and
      decreases whenever [gt1] decreases. *)

      (gt2 : relation max_call) (gt2_wf : WF gt2)
      (gt2_mcaeq : Proper (mcaeq ==> mcaeq ==> impl) gt2)
      (gt2_gt1 : forall E f n (ls : Tes n) g p (us : Tes p),
        n <= arity (typ f) -> p <= arity (typ g) ->
        gt1 E (mk_call f ls) (mk_call g us) ->
        forall s (ts' : Tes (arity (typ f) - n)) (us' : Tes (arity (typ g) - p))
          (nf : n + (arity (typ f) - n) = arity (typ f))
          (pg : p + (arity (typ g) - p) = arity (typ g)),
          vint I (inputs (typ f)) (Vapp (Vmap (subs s) ls) ts') ->
          (forall x A, MapsTo x A E -> ~XSet.In x (fvs ls) -> int I A (s x)) ->
          gt2 (mk_max_call f (Vcast (Vapp (Vmap (subs s) ls) ts') nf))
              (mk_max_call g (Vcast (Vapp (Vmap (subs s) us) us') pg)))
      (gt2_clos_vaeq : forall f ts us, vint I (inputs (typ f)) ts ->
        ts ==>R us -> gt2 (mk_max_call f ts) (mk_max_call f us))

      (** We assume that, for every rule, the right hand-side is in
         the computability closure of the left hand-side. *)

      (lhs_cc_rhs : forall l r (h : rule l r),
        cc gt1 (lhs_fun h) (lhs_args h) XMap.empty r
        (output (typ (lhs_fun h)) (lhs_nb_args h))).

(****************************************************************************)
(** ** Termination proof. *)

    Lemma tr_sn_cc : forall E v V, E |- v ~: V -> SN R_aeq v.

    Proof.
      (* [v] is SN since every function symbol is computable. *)
      apply tr_sn with (I:=I). hyp.
      (* [f] is computable if, for every max call [c], [c] is computable. *)
      cut (forall c, SN gt2 c ->
        vint I (inputs (typ (call_fun c))) (call_args c) ->
        int I (output (typ (call_fun c)) (arity (typ (call_fun c))))
              (apps (Fun (call_fun c)) (call_args c))).
      intros h f. apply int_arrow with (n:=arity(typ f)). refl.
      intros vs hvs. apply (h (mk_max_call f vs)).
      apply WF_inverse. apply gt2_wf. hyp.
      (* We prove that every max call [c] is computable when its arguments
         so are, by induction on [gt2]. *)
      induction 1; clear H. destruct x as [[f n ts] e]; simpl; simpl in e.
      subst n. intro hts.
      (* The interpretation of [output_base_typ f] is a computability
      predicate. *)
      rewrite output_arity. set (b := output_base (typ f)).
      gen (I_cp b); intros [b1 b2 b3 b4].
      (* We now use the assumption [comp_fun] and prove that every
         reduct of [apps (fun f) (Vapp ts vs)] is computable. *)
      apply comp_fun. hyp. intros t' h.
      destruct (beta_eta_rewrite_aeq_apps_fun h) as [[vs [j1 j2]]
        |[m [ls [r [s [q [vs [h1 [h2 [h3 h4]]]]]]]]]]; clear h.
      (* Reduction in one argument. *)
      subst t'. rewrite int_base, <- output_arity.
      apply (H0 (mk_max_call f vs)).
      apply gt2_clos_vaeq. hyp. hyp. simpl. rewrite <- j2. hyp.
      (* Rewrite step at the top. *)
      rewrite h4; clear h4. rewrite h3, vint_cast_term in hts.
      (* By assumption, [r] is in the computability closure of
        [apps (Fun l) ls]. *)
      gen (lhs_cc_rhs h2).
      rewrite lhs_fun_eq, lhs_args_eq, cc_cast, lhs_nb_args_eq. intro hc.
      (* Proof that [apps (subs s r) vs] is computable: we prove that
         [subs s r] and [vs] are computable. *)
      rewrite int_base. eapply int_apps.
      (* Proof that [vs] are computable. *)
      gen (vint_app_term_elim_r hts); intro hvs. apply hvs.
      (* Proof that [subs s r] is computable: we use [cc_comp]. *)
      assert (hm : 0 + m <= arity (typ f)). lia.
      eapply cc_comp with (ts:=ts) (gt1:=gt1) (gt2:=gt2) (ls:=ls) (h:=hm)
        (E:=XMap.empty); auto.
      (* Proof that [ts] is computable. *)
      rewrite h3, vint_cast_term. hyp.
      (* Proof that calls smaller than [mk_call f ts] are computable. *)
      intros g us h. apply (H0 _ h).
      (* Proof that [Vmap (subs s) ls ~~~ Vsubs ts hm]. *)
      sym. gen (Vforall2_sub hm h3). rewrite Vsub_cast, Vsub_app_l. auto.
      lia.
      (* Proof that [r] is in the computability closure of [mk_call f ls]. *)
      rewrite <- output_arity. setoid_rewrite <- h1 at 3. rewrite arrow_output. hyp.
      (* Proof that [s] is valid on the empty environment. *)
      intros z T. rewrite empty_mapsto_iff. fo.
    Qed.

  End termin.

End Termin.

(****************************************************************************)
(** * Termination proof of a rewrite system

whose right hand-sides are in the computability closure of their
corresponding left hand-sides, using the interpretation of types as
computability predicates defined in LCompInt, and a DLQO based on the
accessible supterm ordering for comparing function calls. *)

Module SN_rewrite (Export CC : CC_Struct)
  (Export RS : RS_Struct with Module L := CC.BI.ST.L)
  (Export CO : DLQO_Struct with Module ST := CC.BI.ST).

  Module Import T := Termin CC RS.

  Module Export CI := LCompInt.Make CC.BI.ST CP BI.

  Module Import L := LCall.Lex CO.

  (** For [gt1], i.e. for comparing function calls in the
  computability closure, we use [gt_call (gt_args_lex gt)] where [gt] is
  the alpha-closure of the accessibility subterm ordering. *)

  Definition gt := clos_aeq (supterm_acc!).

  Definition gt1 (E : En) := gt_call (gt_args_lex gt).

  Lemma gt1_wf E : WF (gt1 E).

  Proof.
    apply gt_call_wf. apply gt_args_lex_wf. unfold gt. class.
    apply clos_aeq_tc_supterm_acc_wf.
  Qed.

  #[global] Instance gt1_aeq E : Proper (caeq ==> caeq ==> impl) (gt1 E).

  Proof. unfold gt1, gt. class. Qed.

  (** For [gt2], i.e. for the termination proof, we use a variant of
  [gt1] that is compatible with [==>R]: we use [gt_call] on the union
  of [gt_args_lex (gt0)!] and [gt_red R], where [gt0] is the
  restriction on wellfounded terms of [gt U R_aeq]. *)

  Definition gt0 := RelUtil.restrict (SN R_aeq) (gt U R_aeq).

  Definition gt2c := gt_call (fun r => gt_args_lex (gt0!) r U gt_red R).

  Definition gt2 := Rof gt2c max_call_call.

  (** Properties of [gt0]. *)

  Lemma gt0_wf : WF gt0.

  Proof. apply restrict_SN_clos_aeq_tc_supterm_acc_R_mon_wf; class. Qed.

  #[global] Instance gt0_aeq : Proper (aeq ==> aeq ==> impl) gt0.

  Proof.
    eapply restrict_prop with (E:=aeq). class.
    unfold gt. rewrite <- clos_aeq_union. class.
  Qed.

  (** We check that [gt2] is invariant by [mcaeq]. *)

  #[global] Instance gt2c_caeq : Proper (caeq ==> caeq ==> impl) gt2c.

  Proof.
    intros [f n ts] [f' n' ts'] e [g p us] [g' p' us'] e'.
    inv_caeq e f' n'. inv_caeq e' g' p'.
    unfold impl, gt2c, Def.gt_call, Rof, transp; simpl.
    intro l; inversion l; clear l; subst.
    apply left_lex. hyp.
    apply right_lex. destruct H0 as [H0|H0].
    left. rewrite <- h, <- h0. hyp.
    right. rewrite <- h, <- h0. hyp.
  Qed.

  #[global] Instance gt2_mcaeq : Proper (mcaeq ==> mcaeq ==> impl) gt2.

  Proof. intros [f ts] [f' ts'] e [g us] [g' us'] e'. apply gt2c_caeq; hyp. Qed.

  (** We prove that [gt2] is wellfounded. *)

  Import Lexicographic_Product.
  Import Union.

  Lemma gt2_wf : WF gt2.

  Proof.
    apply WF_inverse. apply WF_inverse. apply wf_WF_transp.
    apply wf_lexprod. apply WF_wf_transp. apply gtC_wf.
    intro r. apply WF_wf_transp. apply wf_union_absorb.
    apply gt_args_lex_wf. class. apply WF_tc. apply gt0_wf. apply gt_red_wf.
    apply gt_args_lex_absorbs_gt_red. class. class.
    apply incl_tc. unfold gt0. rewrite restrict_union. fo.
  Qed.

  (** We check that [gt2] is compatible with [==>R]. *)

  Lemma gt2_clos_vaeq : forall f (ts us : TypArgs f),
    vint I (inputs (typ f)) ts -> ts ==>R us ->
    gt2 (mk_max_call f ts) (mk_max_call f us).

  Proof.
    intros f ts us hts tsus. unfold gt2, gt2c, Def.gt_call, Rof, transp.
    apply right_lex. unfold Def.gt_args_lex, Rof. red. simpl.
    right. apply gt_red_intro. fo. apply sn_clos_vaeq_intro.
    eapply vint_forall_sn. apply I_cp. apply not_neutral_apps_fun. apply hts.
  Qed.

  (** We check that [gt1] makes [gt2] decrease. *)

  Import Lexico.

  Lemma gt2_gt1 : forall E f n (ls : Tes n) g p (us : Tes p),
      n <= arity (typ f) -> p <= arity (typ g) ->
      gt1 E (mk_call f ls) (mk_call g us) ->
      forall s (ts' : Tes (arity (typ f) - n)) (us' : Tes (arity (typ g) - p))
        (nf : n + (arity (typ f) - n) = arity (typ f))
        (pg : p + (arity (typ g) - p) = arity (typ g)),
        vint I (inputs (typ f)) (Vapp (Vmap (subs s) ls) ts') ->
        (forall x A, MapsTo x A E -> ~XSet.In x (fvs ls) -> int I A (s x)) ->
        gt2 (mk_max_call f (Vcast (Vapp (Vmap (subs s) ls) ts') nf))
            (mk_max_call g (Vcast (Vapp (Vmap (subs s) us) us') pg)).

  Proof.
    intros E f n ls g p us hn hp hgt1 s ts' us' nf pg hlsts' hs. revert hgt1.
    unfold gt1, gt2, gt2c, Def.gt_call, Rof, transp; simpl. intro hgt1.
    inversion hgt1; clear hgt1; subst.
    (* code f >C code g *)
    apply left_lex. hyp.
    (* code f = code g *)
    apply right_lex. left.
    revert H0. unfold Def.gt_args_lex, Rof. set (M := CO.filter (code g)).
    rewrite !lexv_eq. simpl. intros [i [i1 [i2 i3]]]. ex i i1. split.
    (* decrease in i-th argument *)
    eapply opt_incl
      with (x := RelUtil.restrict (SN R_aeq) (clos_aeq (supterm_acc!))).
    apply incl_tc. unfold gt0. rewrite restrict_union. fo.
    inversion i2; clear i2. rewrite !Vopt_filter_cast,
      Vopt_filter_app with (x:=subs s x), Vopt_filter_app with (x:=subs s y).
    apply opt_intro. split.
    symmetry in H. destruct (Vnth_opt_filter_Some_elim H) as [a e].
    rewrite e, <- Vnth_map. apply Vforall_nth. eapply vint_forall_sn.
    apply I_cp. apply not_neutral_apps_fun. eapply vint_app_term_elim_l.
    apply hlsts'. apply clos_aeq_tc_supterm_acc_subs. hyp.
    rewrite Vopt_filter_map, Vnth_map, <- H0. refl.
    rewrite Vopt_filter_map, Vnth_map, <- H. refl.
    (* for all j<i, the j-th arguments are equivalent *)
    intros j ji jg. rewrite !Vopt_filter_cast.
    gen (i3 _ ji jg); intro h. inversion h; clear h; subst.
    rewrite Vopt_filter_app with (x:=subs s x),
      Vopt_filter_app with (x:=subs s y).
    apply opt_intro. rewrite H1. refl.
    rewrite Vopt_filter_map, Vnth_map, <- H0. refl.
    rewrite Vopt_filter_map, Vnth_map, <- H. refl.
  Qed.

  (** Termination theorem. *)

  Section termin.

    Variables
      (lhs_cc_rhs : forall l r (h : rule l r),
        cc gt1 (lhs_fun h) (lhs_args h)
        XMap.empty r (output (typ (lhs_fun h)) (lhs_nb_args h))).

    Lemma tr_sn_beta_eta_rewrite_aeq : forall E v V, E |- v ~: V -> SN R_aeq v.

    Proof.
      eapply tr_sn_cc. apply I_cp. apply not_neutral_apps_fun.
      apply comp_acc. apply comp_fun. apply not_neutral_apps_fun.
      apply gt2_wf. apply gt2_mcaeq. apply gt2_gt1.
      apply gt2_clos_vaeq. apply lhs_cc_rhs.
    Qed.

  End termin.

End SN_rewrite.
