(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Pierre-Yves Strub, 2009-04-09
- Frederic Blanqui, 2009-11-02 (matches_dom)

Matching algorithm for ATerms.
*)

(**********************************************************************)
From Stdlib Require Import Peano_dec Bool.
From Stdlib Require OrderedTypeEx FMapAVL.
From CoLoR Require Import LogicUtil EqUtil NatUtil VecUtil ATerm ASubstitution
  FSetUtil FMapUtil ListUtil.
From CoLoR Require AVariables.

Module VSF := AVariables.VarSetUtil.XSetFacts.
Module VS  := AVariables.XSet.

Module VM := FMapAVL.Make (OrderedTypeEx.Nat_as_OT).
Module VMU := FMapUtil.Make VM.
Module VMF := VMU.XMapFacts.

(**********************************************************************)
Set   Implicit Arguments.
Unset Strict Implicit.

(**********************************************************************)
Section Matching.
  Variable Sig : Signature.

  Notation term      := (@ATerm.term Sig).
  Notation terms     := (@vector term).
  Notation vars      := (@AVariables.vars Sig).
  Notation vars_list := (@AVariables.vars_list Sig).
  Notation vars_vec  := (@AVariables.vars_vec Sig _).

  Notation matching  := (VM.t term) (only parsing).

  Notation beq_term  := (@beq_term Sig).
  Notation beq_terms := (fun x y => beq_vec beq_term x y).

  Notation "x =X y"   := (NatUtil.beq_nat x y) (at level 70, no associativity).
  Notation "f =S g"   := (@beq_symb Sig f g)   (at level 70, no associativity).
  Notation "t =T u"   := (beq_term t u)        (at level 70, no associativity).
  Notation "ts =V us" := (beq_terms ts us)     (at level 70, no associativity).

  Local Coercion is_true b := b = true.
  Local Hint Unfold is_true : core.

  Definition exmatch (m : matching) (x : variable) (t : term) :=
  match VM.find x m with
  | None   => Some (VM.add x t m)
  | Some u => if t =T u then Some m else None
  end.

  Fixpoint matches_r (u t : term) (m : matching) : option matching :=
  match u, t with
  | Var y   , _        => exmatch m y t
  | Fun g us, Fun f ts => if f =S g then Vfold2 m matches_r us ts else None
  | _       , _        => None
  end.

  Notation "\unopt_ ( x ) v" :=
    (match v with Some v' => v' | None => x end)
    (at level 8, v at level 36, x at level 50, format "\unopt_ ( x )  v").

  Definition subst_of_matching (m : matching) :=
    fun (x : variable) => \unopt_(Var x) (VM.find x m).

  Notation "\S ( θ )" := (subst_of_matching θ) (format "\S ( θ )").

  Definition matches (u t : term) :=
  match matches_r u t VM.empty with
  | None   => None
  | Some m => Some \S(m)
  end.

  Notation "t ! θ" := (@sub Sig θ t) (at level 15).

  (********************************************************************)
  Lemma subst_of_matchingE :
    forall x m v, VM.find x m = Some v -> \S(m) x = v.
  Proof.
    by intros x m v H; unfold subst_of_matching; rewrite H.
  Qed.

  (********************************************************************)
  Lemma vmap_eqb : forall x y, VMF.eqb x y = (x =X y).
  Proof.
    intros x y; unfold VMF.eqb; unfold VMF.eq_dec.
    case_eq (eq_nat_dec x y); intros Hxy Hxydep.
      by sym; apply (proj2 (beq_nat_ok x y)).
      case_eq (x =X y); intros Hxyb.
        by elim (Hxy (proj1 (beq_nat_ok x y) Hxyb)).
        refl.
  Qed.

  (********************************************************************)
  (** Induction principle for [matches_r] when result is [Some _] **)
  Section MatchInd.
    Variable P  : term -> term -> matching -> matching -> Prop.
    Variable Ps : forall nt nu,
      terms nt -> terms nu -> matching -> matching -> Prop.

    Hypothesis Hvar :
      forall x t θ θ', exmatch θ x t = Some θ' -> P (Var x) t θ θ'.

    Hypothesis Hfun :
      forall f g ts us θ θ',
           Vfold2 θ matches_r ts us = Some θ'
        -> Ps ts us θ θ'
        -> f = g
        -> P (Fun f ts) (Fun g us) θ θ'.

    Hypothesis Hnil :
      forall θ, Ps Vnil Vnil θ θ.

    Hypothesis Hcns :
      forall t nt (ts : terms nt) u nu (us : terms nu) θ θ' Ω,
           matches_r t u Ω = Some θ'
        -> P t u Ω θ'
        -> Vfold2 θ matches_r ts us = Some Ω
        -> Ps ts us θ Ω
        -> Ps (Vcons t ts) (Vcons u us) θ θ'.

    Notation "\matchesP" :=
      (forall u t θ θ', matches_r u t θ = Some θ' -> P u t θ θ').
    Notation "\matchesPs" :=
      (forall nu (us : terms nu) nt (ts : terms nt) θ θ',
        Vfold2 θ matches_r us ts = Some θ' -> Ps us ts θ θ').

    Lemma matches_some_ind : \matchesP /\ \matchesPs.
    Proof.
      apply term_ind_comb.
      (* var *)
      hyp.
      (* fun *)
      intros g us Hus t θ θ' Hθθ'; destruct t as [y|f ts]; try discr.
      simpl in Hθθ'; case_eq (f =S g); intros Hfg; rewrite Hfg in Hθθ';
        try discr.
      by apply Hfun; auto; rewrite (proj1 beq_symb_ok Hfg).
      (* nil *)
      intros nt ts θ θ'; destruct ts as [|t nt ts]; try discr.
      by inversion_clear 1; apply Hnil.
      (* cons *)
      intros u nu us Hu Hus nt ts θ θ'.
      destruct ts as [|t nt ts]; try discr; simpl Vfold2.
      case_eq (Vfold2 θ matches_r us ts); try discr; intros Ω HθΩ HΩθ'.
      by apply Hcns with Ω; auto.
    Qed.
  End MatchInd.

  (********************************************************************)
  Section VarMin.
    Lemma exmatches_var_min :
      forall y t θ θ', exmatch θ y t = Some θ' ->
        forall x, VM.mem x θ' = VM.mem x θ || (y =X x).
    Proof.
      intros y t θ θ'; unfold exmatch; case_eq (VM.find y θ).
        intros v H; case (t =T v); intros Htu; try discr.
        inversion_clear Htu in H; intros x; case_eq (y =X x); intros Hxy.
          by rewrite <- (proj1 (beq_nat_ok _ _) Hxy), VMF.mem_find_b, H.
          by rewrite orb_false_r.

        intros Hymem H x; inversion_clear H in Hymem; case_eq (y =X x).
          intros Hxy; rewrite (proj1 (beq_nat_ok _ _) Hxy),
            VMF.add_b, orb_comm; unfold VMF.eqb; unfold VMF.eq_dec.
          by rewrite (eq_nat_dec_refl x).
          intros Hxy; rewrite VMF.add_b.
          by rewrite orb_comm, vmap_eqb, Hxy.
    Qed.

    Notation "\matches_var_min" :=
      (forall u t θ θ', matches_r u t θ = Some θ' ->
        forall x, VM.mem x θ' = VM.mem x θ || VS.mem x (vars u)).

    Notation "\nmatches_var_min" :=
      (forall nu (us : terms nu) nt (ts : terms nt) θ θ',
        Vfold2 θ matches_r us ts = Some θ'
        -> forall x, VM.mem x θ' = VM.mem x θ || VS.mem x (vars_vec us)).

    Lemma matches_var_min_comb :  \matches_var_min /\ \nmatches_var_min.
    Proof.
      apply matches_some_ind.
      (* var *)
      simpl; intros y t θ θ' H x.
      by rewrite VSF.singleton_b, vmap_eqb; eapply exmatches_var_min; eauto.
      (* fun *)
      by intros f _ ts _ θ θ' _ H _ x; rewrite AVariables.vars_fun.
      (* nil *)
      by intros θ x; simpl; rewrite VSF.empty_b, orb_false_r.
      (* cons *)
      intros u nu us _ _ _ θ θ' Ω _ HΩθ' _ HθΩ x.
      simpl; rewrite VSF.union_b, (HΩθ' x), (HθΩ x).
      by case (VM.mem x θ); simpl; try rewrite orb_comm.
    Qed.

    Lemma matches_var_minP : \matches_var_min.
    Proof. exact (proj1 matches_var_min_comb). Qed.

    Lemma nmatches_var_minP : \nmatches_var_min.
    Proof. exact (proj2 matches_var_min_comb). Qed.
  End VarMin.

  Lemma matches_var_minadded :
    forall u t m m', matches_r u t m = Some m' ->
      forall x, VM.mem x m = false -> VM.mem x m' -> VS.mem x (vars u).
  Proof.
    intros u t m m' H x Hmem₁ Hmem₂.
    by rewrite (matches_var_minP H) in Hmem₂; rewrite Hmem₁ in Hmem₂.
  Qed.

  (********************************************************************)
  Section MatchMon.
    Lemma exmatch_mon :
      forall θ θ' x t, exmatch θ x t = Some θ' ->
        forall y, VM.mem y θ -> VM.find y θ = VM.find y θ'.
    Proof.
      intros θ θ' x t; unfold exmatch; case_eq (VM.find x θ).
        by intros u H; case (t =T u); intros I; inversion_clear I.

        intros H I; inversion_clear I; intros y Hyθ.
        sym; apply VMF.add_neq_o; intros Hxy; subst y.
        rewrite VMF.mem_find_b in Hyθ; rewrite H in Hyθ.
        discr.
    Qed.

    Notation "\matches_mon" :=
      (forall u t θ θ', matches_r u t θ = Some θ' ->
        forall x, VM.mem x θ -> VM.find x θ = VM.find x θ').

    Notation "\nmatches_mon" :=
      (forall nu (us : terms nu) nt (ts : terms nt) θ θ',
        Vfold2 θ matches_r us ts = Some θ'
        -> forall x, VM.mem x θ -> VM.find x θ = VM.find x θ').

    Lemma matches_mon_comb : \matches_mon /\ \nmatches_mon.
    Proof.
      apply matches_some_ind; auto.
        by intros x t θ θ'; apply exmatch_mon.

        intros _ _ _ _ _ _ θ θ' Ω _ HΩθ' _ HθΩ x Hx.
        trans (VM.find x Ω); [by apply HθΩ | idtac].
        apply HΩθ'; unfold is_true; rewrite <- Hx;
          rewrite !VMF.mem_find_b.
        by rewrite (HθΩ x Hx).
    Qed.

    Lemma matches_monP : \matches_mon.
    Proof. exact (proj1 matches_mon_comb). Qed.

    Lemma nmatches_monP : \nmatches_mon.
    Proof. exact (proj2 matches_mon_comb). Qed.
  End MatchMon.

  (********************************************************************)
  Lemma matches_submon :
    forall u t θ,
      u ! \S(θ) = t ->
      (forall x, VS.mem x (vars u) -> VM.mem x θ) ->
      forall u' t' θ', matches_r u' t' θ = Some θ' -> u ! \S(θ') = t.
  Proof.
    intros u t θ Hsub Hdom u' t' θ' Hθθ'; subst t.
    apply sub_eq; intros x Hx; unfold subst_of_matching.
    rewrite (matches_monP Hθθ'); try refl.
    by apply Hdom; unfold is_true; apply (proj1 (AVariables.in_vars_mem _ _)).
  Qed.

  Lemma nmatches_submon :
    forall nu (us : terms nu) nt (ts : terms nt) θ,
      (Vmap (sub \S(θ)) us) =V ts ->
      (forall x, VS.mem x (vars_vec us) -> VM.mem x θ) ->
      forall u t θ', matches_r u t θ = Some θ' ->
        (Vmap (sub \S(θ')) us) =V ts.
  Proof.
    induction us as [|u nu us IH]; destruct ts as [|t nt ts]; try discr.
    (* nil *)
    intros; refl.
    (* cons *)
    intros θ Heq Hmem u' t' θ' Hθθ'; simpl in Heq |- *.
    elim (proj1 (andb_true_iff _ _) Heq); intros Htu Hts_uts.
    unfold is_true; apply (proj2 (andb_true_iff _ _)); split.
      apply (proj2 (beq_term_ok _ _)); apply matches_submon with θ u' t'.
        by apply (proj1 (beq_term_ok _ _)).
        by intros x Hx; apply Hmem; simpl; rewrite VSF.union_b, Hx, orb_true_l.
        hyp.

      apply IH with θ u' t'; try hyp.
        by intros x Hx; apply Hmem; simpl; rewrite VSF.union_b, Hx, orb_true_r.
  Qed.

  (********************************************************************)
  Section MatchCorrectness.
    Notation "\matches_correct" :=
      (forall u t θ θ', matches_r u t θ = Some θ' -> u ! \S(θ') = t).

    Notation "\nmatches_correct" :=
      (forall nu (us : terms nu) nt (ts : terms nt) θ θ',
        Vfold2 θ matches_r us ts = Some θ' -> (Vmap (sub \S(θ')) us) =V ts).

    Lemma matches_r_correct : \matches_correct /\ \nmatches_correct.
    Proof.
      apply matches_some_ind.
      (* var *)
      intros y u θ θ'; simpl; unfold exmatch; case_eq (VM.find y θ).
        intros v Hv; case_eq (u =T v); intros Htv I;
          inversion_clear I in Hv.
        unfold subst_of_matching; rewrite Hv; simpl.
        by sym; apply (proj1 (beq_term_ok _ _)).
        intros _ I; inversion I as [Hadd]; clear I.
        by unfold subst_of_matching; rewrite VMF.add_eq_o.
      (* fun *)
      intros f g ts us _ θ _ Hveq Hfg.
      apply (proj1 (beq_term_ok _ _)); rewrite sub_fun, beq_fun.
      by rewrite Hveq, andb_true_r; apply (proj2 beq_symb_ok).
      (* nil *)
      intros θ; simpl; refl.
      (* cons *)
      intros t nt ts u nu us θ θ' Ω HΩθ IHΩθ HθΩ IHθΩ; simpl.
      rewrite <- IHΩθ, (beq_refl (@beq_term_ok Sig)), andb_true_l.
      eapply nmatches_submon with Ω t u; try hyp; intros x Hx.
      by unfold is_true; rewrite (nmatches_var_minP HθΩ), Hx, orb_true_r.
    Qed.

    Lemma matches_correct : forall u t θ, matches u t = Some θ -> u ! θ = t.
    Proof.
      intros u t θ; unfold matches.
      case_eq (matches_r u t VM.empty); try discr; intros Ω HΩ.
      inversion_clear 1; apply (proj1 matches_r_correct) with VM.empty.
      hyp.
    Qed.
  End MatchCorrectness.

  (********************************************************************)
  Section MatchCompletness.
    Definition compose (m : matching) (θ : variable -> term) :=
      fun (x : variable) => \unopt_(θ x) (VM.find x m).

    Notation "m ⊕ θ" := (compose m θ) (at level 40, no associativity).

    Lemma composeI : forall x m θ, VM.find x m = None -> (m ⊕ θ) x = θ x.
    Proof.
      by intros x m θ H; unfold compose; rewrite H.
    Qed.

    Lemma composeE : forall x m v θ, VM.find x m = Some v -> (m ⊕ θ) x = v.
    Proof.
      by intros x m v θ Hfind; unfold compose; rewrite Hfind.
    Qed.

    Notation "\matches_complete" :=
      (forall u t m, (exists θ, u ! (m ⊕ θ) = t) -> matches_r u t m <> None).

    Notation "\nmatches_complete" :=
      (forall nu (us : terms nu) nt (ts : terms nt) m,
        (exists θ, (Vmap (sub (m ⊕ θ)) us) =V ts) ->
        Vfold2 m matches_r us ts <> None).

    Lemma matches_extend_compatP :
      forall u t m m', matches_r u t m = Some m' ->
        forall θ, u ! (m ⊕ θ) = t -> forall x, (m ⊕ θ) x = (m' ⊕ θ) x.
    Proof.
      intros u t m m' H θ Hθ x; unfold compose.
      case_eq (VM.find x m); case_eq (VM.find x m').
        (* some/some*)
        intros v₂ Hv₂ v₁ Hv₁; rewrite <- (matches_monP H) in Hv₂.
        congruence. by rewrite VMF.mem_find_b, Hv₁.
        (* none/some *)
        intros Hm' v Hv; rewrite <- (matches_monP H) in Hm'.
        congruence. by rewrite VMF.mem_find_b, Hv.
        (* some/none *)
        intros v Hv Hm; rewrite <- (composeI θ Hm).
        rewrite <- (subst_of_matchingE Hv).
        apply subeq_inversion with u.
          by rewrite (proj1 matches_r_correct _ _ _ _ H).
          apply (proj2 (AVariables.in_vars_mem _ _)).
          apply (matches_var_minadded H); rewrite VMF.mem_find_b.
          by rewrite Hm. by rewrite Hv.
        (* none/none *)
        refl.
    Qed.

    Lemma nmatches_extend_compatP :
      forall nu (us : terms nu) nt (ts : terms nt) m m',
        Vfold2 m matches_r us ts = Some m' ->
        forall θ, Vmap (sub (m ⊕ θ)) us =V ts ->
          forall x, (m ⊕ θ) x = (m' ⊕ θ) x.
    Proof.
      induction us as [|u nu us IH]; destruct ts as [|t nt ts];
        intros m₁ m₂; try discr.
        (* nil/nil *)
        by simpl; intros H; inversion_clear H.
        (* some/some *)
        simpl; case_eq (Vfold2 m₁ matches_r us ts); try discr.
        intros m H₁ H₂ θ H x; elim (proj1 (andb_true_iff _ _) H).
        intros Hu Hus; trans ((m ⊕ θ) x).
          by apply (IH _ _ _ _ H₁).

          apply (matches_extend_compatP H₂).
          rewrite <- (proj1 (beq_term_ok _ _) Hu).
          by apply sub_eq; intros y _; sym; apply (IH _ _ _ _ H₁).
    Qed.

    Lemma matches_r_complete : \matches_complete /\ \nmatches_complete.
    Proof.
      apply term_ind_comb.
        (* var *)
        intros x t m H; elim H; simpl; unfold compose.
        case_eq (VM.find x m);
          [intros mx Hfind _ Ht | intros Hfind _ _];
          unfold exmatch; rewrite Hfind; try done.
        by rewrite (proj2 (beq_term_ok _ _) (sym_eq Ht)); discr.

        (* fun *)
        intros g us IH t m H; destruct t as [x|f nt];
          elim H; intros θ Hθ; rewrite sub_fun in Hθ; try discr.
        inversion_clear Hθ; simpl; rewrite (beq_refl (@beq_symb_ok Sig)).
        apply IH; exists θ; rewrite beq_vec_refl; try done.
        by apply beq_term_ok.

        (* nil *)
        destruct ts as [|t nt ts]; intros m H; simpl.
          by discr.
          by elim H; intros θ Hθ; simpl in Hθ.

        (* cons *)
        intros u nu us IH IHs; destruct ts as [|t nt ts]; intros m H.
          by elim H; intros θ Hθ; simpl in Hθ.

          elim H; intros θ Hθ; simpl in Hθ.
          case (proj1 (andb_true_iff _ _) Hθ); intros Hu Hus.
          simpl; case_eq (Vfold2 m matches_r us ts).
            intros m' Hm'; apply IH; exists θ.
            rewrite <- (proj1 (beq_term_ok _ _) Hu).
            apply sub_eq; intros x _; sym.
            by apply nmatches_extend_compatP with _ us _ ts.

            intros Hfold _; eapply IHs; [idtac | ehyp].
            by exists θ.
    Qed.

    Lemma matches_complete :
      forall u t θ, u!θ = t -> matches u t <> None.
    Proof.
      intros u t θ H; unfold matches.
      case_eq (matches_r u t VM.empty).
        by intros; discr.
        intros Habd _; eapply (proj1 matches_r_complete); [idtac|ehyp].
        exists θ; rewrite <- H; apply sub_eq; intros x _.
        by unfold compose; rewrite VMF.empty_o.
    Qed.

    Lemma matches_complete_ext :
      forall u t θ, u!θ = t ->
        exists Ω,
          (  matches u t = Some Ω
          /\ forall x, VS.mem x (vars u) -> θ x = Ω x).
    Proof.
      intros u t θ H; case_eq (matches u t).
        intros Ω HΩ; exists Ω; split; [refl | idtac].
        intros x Hxu; apply subeq_inversion with u.
          by rewrite H; sym; apply matches_correct.
          by apply (proj2 (AVariables.in_vars_mem _ _)).
        intros Habs; elim (matches_complete H Habs).
    Qed.
  End MatchCompletness.

  (********************************************************************)

  Lemma matches_r_dom : forall u t m m' x, matches_r u t m = Some m' ->
    ~In x (ATerm.vars u) -> VM.mem x m' = VM.mem x m.
  Proof.
    cut ((forall u t m m', matches_r u t m = Some m' ->
    forall x, ~In x (ATerm.vars u) -> VM.mem x m' = VM.mem x m)
    /\ (forall nu (us : terms nu) nt (ts : terms nt) m m',
      Vfold2 m matches_r us ts = Some m' ->
      forall x, ~In x (ATerm.vars_vec us) -> VM.mem x m' = VM.mem x m)).
    intuition. eapply H0. apply H. hyp. apply matches_some_ind.
    (* Var *)
    simpl. intuition. unfold exmatch in H.
    destruct (VM.find (elt:=term) x θ).
    revert H. case (beq_term t t0); intro. inversion H. refl. discr.
    inversion H. rewrite VMF.add_b. rewrite vmap_eqb. change (x<>x0) in H1.
    rewrite <- (beq_ko beq_nat_ok) in H1. rewrite H1. refl.
    (* Fun *)
    intros. apply H0. rewrite vars_fun in H2. hyp.
    (* Vnil *)
    refl.
    (* Vcons *)
    simpl. intros. rewrite notin_app in H3. destruct H3.
    trans (VM.mem (elt:=term) x Ω). apply H0. hyp. apply H2. hyp.
  Qed.

  Lemma matches_dom : forall u t s x,
    matches u t = Some s -> ~In x (ATerm.vars u) -> s x = Var x.
  Proof.
    intros u t s x. unfold matches.
    case_eq (matches_r u t VM.empty).
    intros t0 H H0 H1. inversion H0.
    ded (matches_r_dom H H1). rewrite VMF.empty_a in H2.
    unfold subst_of_matching. revert H2. rewrite VMF.mem_find_b.
    destruct (VM.find x t0). discr. refl. discr.
  Qed.

End Matching.
