(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Pierre-Yves Strub, 2009-04-09

Matching algorithm for ATerms .
*)

(**********************************************************************)
Require Import Peano_dec .

Require Import LogicUtil .
Require Import EqUtil .
Require Import NatUtil .
Require Import VecUtil .
Require Import ATerm .
Require (****) AVariables .
Require Import ASubstitution .

Require OrderedTypeEx FSetUtil FMapUtil .

Module VSF := AVariables.VarSetUtil.XSetFacts .
Module VS  := AVariables.VarSetUtil.XSet .

Module VMU := FMapUtil.Make (OrderedTypeEx.Nat_as_OT) .
Module VMF := VMU.XMapFacts .
Module VM  := VMU.XMap .

(**********************************************************************)
Set   Implicit Arguments .
Unset Strict Implicit .

(**********************************************************************)
Section Matching .
  Variable Sig : Signature .

  Notation term      := (@ATerm.term Sig) .
  Notation terms     := (@vector term) .
  Notation vars      := (@AVariables.vars Sig) .
  Notation vars_list := (@AVariables.vars_list Sig) .
  Notation vars_vec  := (@AVariables.vars_vec Sig _) .

  Notation matching  := (VM.t term) (only parsing) .

  Notation beq_term  := (@beq_term Sig) .
  Notation beq_terms := (fun x y => beq_vec beq_term x y) .

  Notation "x =X y" := (NatUtil.beq_nat x y) (at level 70, no associativity) .
  Notation "f =S g" := (@beq_symb Sig f g)   (at level 70, no associativity) .
  Notation "t =T u" := (beq_term t u)        (at level 70, no associativity) .

  Local Coercion is_true b := b = true .
  Local Hint Unfold is_true .

  Definition exmatch (m : matching) (x : variable) (t : term) :=
  match VM.find x m with
  | None   => Some (VM.add x t m)
  | Some u => if t =T u then Some m else None
  end .

  Fixpoint matches_r (u t : term) (m : matching) {struct u} : option matching :=
  match u, t with
  | Var y   , _        => exmatch m y t
  | Fun g us, Fun f ts => if f =S g then Vfold2 m matches_r us ts else None
  | _       , _        => None
  end .

  Notation "\unopt_ ( x ) v" :=
    (match v with Some v' => v' | None => x end)
    (at level 8, v at level 36, x at level 50) .

  Definition subst_of_matching (m : matching) :=
    fun (x : variable) => \unopt_(Var x) (VM.find x m) .

  Notation "\S ( θ )" := (subst_of_matching θ) (format "\S ( θ )") .

  Definition matches (u t : term) :=
  match matches_r u t (VM.empty _) with
  | None   => None
  | Some m => Some \S(m)
  end .

  Notation "t ! θ" := (sub (θ : @substitution Sig) t) (at level 15) .

  (********************************************************************)
  Lemma vmap_eqb : forall x y, VMF.eqb x y = (x =X y) .
  Proof .
    intros x y; unfold VMF.eqb; unfold VMF.eq_dec .
    coq_case_eq (eq_nat_dec x y); intros Hxy Hxydep .
      by symmetry; apply (proj2 (beq_nat_ok x y)) .
      coq_case_eq (x =X y); intros Hxyb .
        by elim (Hxy (proj1 (beq_nat_ok x y) Hxyb)) .
        reflexivity .
  Qed .

  (********************************************************************)
  (** Induction principle for [matches_r] when result is [Some _] **)
  Section MatchInd .
    Variable P  : term -> term -> matching -> matching -> Prop .
    Variable Ps : forall nt nu, terms nt -> terms nu -> matching -> matching -> Prop .

    Hypothesis Hvar :
      forall x t θ θ', exmatch θ x t = Some θ' -> P (Var x) t θ θ' .

    Hypothesis Hfun :
      forall f g ts us θ θ',
           Vfold2 θ matches_r ts us = Some θ'
        -> Ps ts us θ θ'
        -> f = g
        -> P (Fun f ts) (Fun g us) θ θ' .

    Hypothesis Hnil :
      forall θ, Ps Vnil Vnil θ θ .

    Hypothesis Hcns :
      forall t nt (ts : terms nt) u nu (us : terms nu) θ θ' Ω,
           matches_r t u Ω = Some θ'
        -> P t u Ω θ'
        -> Vfold2 θ matches_r ts us = Some Ω
        -> Ps ts us θ Ω
        -> Ps (Vcons t ts) (Vcons u us) θ θ' .

    Notation "\matchesP" :=
      (forall u t θ θ', matches_r u t θ = Some θ' -> P u t θ θ') .
    Notation "\matchesPs" :=
      (forall nu (us : terms nu) nt (ts : terms nt) θ θ',
        Vfold2 θ matches_r us ts = Some θ' -> Ps us ts θ θ') .

    Lemma matches_some_ind : \matchesP /\ \matchesPs .
    Proof .
      apply term_ind_comb .
      (* var *)
      assumption .
      (* fun *)
      intros g us Hus t θ θ' Hθθ'; destruct t as [y|f ts]; try discr .
      simpl in Hθθ'; coq_case_eq (f =S g); intros Hfg; rewrite Hfg in Hθθ'; try discr .
      by apply Hfun; auto; rewrite (proj1 beq_symb_ok Hfg) .
      (* nil *)
      intros nt ts θ θ'; destruct ts as [x|t nt ts]; try discr .
      by inversion_clear 1; apply Hnil .
      (* cons *)
      intros u nu us Hu Hus nt ts θ θ' .
      destruct ts as [|t nt ts]; try discr; simpl Vfold2 .
      coq_case_eq (Vfold2 θ matches_r us ts); try discr; intros Ω HθΩ HΩθ' .
      by apply Hcns with Ω; auto .
    Qed .
  End MatchInd .

  (********************************************************************)
  Section VarMin .
    Lemma exmatches_var_min :
      forall y t θ θ', exmatch θ y t = Some θ' ->
        forall x, VM.mem x θ' = VM.mem x θ || (y =X x) .
    Proof .
      intros y t θ θ'; unfold exmatch; coq_case_eq (VM.find y θ) .
        intros v H; case (t =T v); intros Htu; try discr .
        inversion_clear Htu in H; intros x; coq_case_eq (y =X x); intros Hxy .
          by rewrite <- (proj1 (beq_nat_ok _ _) Hxy); rwn VMF.mem_find_b H .
          by rewrite orb_false_r .

        intros Hymem H x; inversion_clear H in Hymem; coq_case_eq (y =X x) .
          intros Hxy; rewrite (proj1 (beq_nat_ok _ _) Hxy) .
          rwn VMF.add_b orb_comm; unfold VMF.eqb; unfold VMF.eq_dec .
          by rewrite (eq_nat_dec_refl x) .
          intros Hxy; rwn VMF.add_b orb_comm .
          by rwn vmap_eqb Hxy .
    Qed .

    Notation "\matches_var_min" :=
      (forall u t θ θ', matches_r u t θ = Some θ' ->
        forall x, VM.mem x θ' = VM.mem x θ || VS.mem x (vars u)) .

    Notation "\nmatches_var_min" :=
      (forall nu (us : terms nu) nt (ts : terms nt) θ θ',
        Vfold2 θ matches_r us ts = Some θ'
        -> forall x, VM.mem x θ' = VM.mem x θ || VS.mem x (vars_vec us)) .

    Lemma matches_var_min_comb :  \matches_var_min /\ \nmatches_var_min .
    Proof .
      apply matches_some_ind .
      (* var *)
      simpl; intros y t θ θ' H x .
      by rwn VSF.singleton_b vmap_eqb; eapply exmatches_var_min; eauto .
      (* fun *)
      by intros f _ ts _ θ θ' _ H _ x; rewrite AVariables.vars_fun .
      (* nil *)
      by intros θ x; simpl; rwn VSF.empty_b orb_false_r .
      (* cons *)
      intros u nu us _ _ _ θ θ' Ω _ HΩθ' _ HθΩ x .
      simpl; rwn VSF.union_b (HΩθ' x) (HθΩ x) .
      by case (VM.mem x θ); simpl; try rewrite orb_comm .
    Qed .

    Lemma matches_var_minP : \matches_var_min .
    Proof . exact (proj1 matches_var_min_comb) . Qed .

    Lemma nmatches_var_minP : \nmatches_var_min .
    Proof . exact (proj2 matches_var_min_comb) . Qed .
  End VarMin .

  (********************************************************************)
  Section MatchMon .
    Lemma exmatch_mon :
      forall θ θ' x t, exmatch θ x t = Some θ' ->
        forall y, VM.mem y θ -> VM.find y θ = VM.find y θ' .
    Proof .
      intros θ θ' x t; unfold exmatch; coq_case_eq (VM.find x θ) .
        by intros u H; case (t =T u); intros I; inversion_clear I .

        intros H I; inversion_clear I; intros y Hyθ .
        symmetry; apply VMF.add_neq_o; intros Hxy; subst y .
        rewrite VMF.mem_find_b in Hyθ; rewrite H in Hyθ .
        discriminate .
    Qed .

    Notation "\matches_mon" :=
      (forall u t θ θ', matches_r u t θ = Some θ' ->
        forall x, VM.mem x θ -> VM.find x θ = VM.find x θ') .

    Notation "\nmatches_mon" :=
      (forall nu (us : terms nu) nt (ts : terms nt) θ θ',
        Vfold2 θ matches_r us ts = Some θ'
        -> forall x, VM.mem x θ -> VM.find x θ = VM.find x θ') .

    Lemma matches_mon_comb : \matches_mon /\ \nmatches_mon .
    Proof .
      apply matches_some_ind; auto .
        by intros x t θ θ'; apply exmatch_mon .

        intros _ _ _ _ _ _ θ θ' Ω _ HΩθ' _ HθΩ x Hx .
        transitivity (VM.find x Ω); [by apply HθΩ | idtac] .
        apply HΩθ'; unfold is_true; rewrite <- Hx; repeat rewrite VMF.mem_find_b .
        by rewrite (HθΩ x Hx) .
    Qed .

    Lemma matches_monP : \matches_mon .
    Proof . exact (proj1 matches_mon_comb) . Qed .

    Lemma nmatches_monP : \nmatches_mon .
    Proof . exact (proj2 matches_mon_comb) . Qed .
  End MatchMon .

  (********************************************************************)
  Lemma matches_submon :
    forall u t θ,
      u ! \S(θ) = t ->
      (forall x, VS.mem x (vars u) -> VM.mem x θ) ->
      forall u' t' θ', matches_r u' t' θ = Some θ' -> u ! \S(θ') = t .
  Proof .
    intros u t θ Hsub Hdom u' t' θ' Hθθ'; subst t .
    apply sub_eq; intros x Hx; unfold subst_of_matching .
    rewrite (matches_monP Hθθ'); try reflexivity .
    by apply Hdom; unfold is_true; apply (proj1 (AVariables.in_vars_mem _ _)) .
  Qed .

  Lemma nmatches_submon :
    forall nu (us : terms nu) nt (ts : terms nt) θ,
      beq_terms (Vmap (sub \S(θ)) us) ts ->
      (forall x, VS.mem x (vars_vec us) -> VM.mem x θ) ->
      forall u t θ', matches_r u t θ = Some θ' ->
        beq_terms (Vmap (sub \S(θ')) us) ts .
  Proof .
    induction us as [|u nu us IH]; destruct ts as [|t nt ts]; try discr .
    (* nil *)
    intros; reflexivity .
    (* cons *)
    intros θ Heq Hmem u' t' θ' Hθθ'; simpl in Heq |- * .
    elim (proj1 (andb_true_iff _ _) Heq); intros Htu Hts_uts .
    unfold is_true; apply (proj2 (andb_true_iff _ _)); split .
      apply (proj2 (beq_term_ok _ _)); apply matches_submon with θ u' t' .
        by apply (proj1 (beq_term_ok _ _)) .
        by intros x Hx; apply Hmem; simpl; rwn VSF.union_b Hx orb_true_l .
        assumption .

      apply IH with θ u' t'; try assumption .
        by intros x Hx; apply Hmem; simpl; rwn VSF.union_b Hx orb_true_r .
  Qed .

  (********************************************************************)
  Section MatchCorrectness .
    Notation "\matches_correct" :=
      (forall u t θ θ', matches_r u t θ = Some θ' -> u ! \S(θ') = t) .

    Notation "\nmatches_correct" :=
      (forall nu (us : terms nu) nt (ts : terms nt) θ θ',
        Vfold2 θ matches_r us ts = Some θ' -> beq_terms (Vmap (sub \S(θ')) us) ts) .

    Lemma matches_r_correct : \matches_correct /\ \nmatches_correct .
    Proof .
      apply matches_some_ind .
      (* var *)
      intros y u θ θ'; simpl; unfold exmatch; coq_case_eq (VM.find y θ) .
        intros v Hv; coq_case_eq (u =T v); intros Htv I; inversion_clear I in Hv .
        unfold subst_of_matching; rewrite Hv; simpl .
        by symmetry; apply (proj1 (beq_term_ok _ _)) .
        intros _ I; inversion I as [Hadd]; clear I .
        by unfold subst_of_matching; rewrite VMF.add_eq_o .
      (* fun *)
      intros f g ts us _ θ _ Hveq Hfg .
      apply (proj1 (beq_term_ok _ _)); rwn sub_fun beq_fun .
      by rwn Hveq andb_true_r; apply (proj2 beq_symb_ok) .
      (* nil *)
      intros θ; simpl; reflexivity .
      (* cons *)
      intros t nt ts u nu us θ θ' Ω HΩθ IHΩθ HθΩ IHθΩ; simpl .
      rewrite <- IHΩθ; rwn (beq_refl (@beq_term_ok Sig)) andb_true_l .
      eapply nmatches_submon with Ω t u; try assumption; intros x Hx .
      by unfold is_true; rwn (nmatches_var_minP HθΩ) Hx orb_true_r .
    Qed .

    Lemma matches_correct : forall u t θ, matches u t = Some θ -> u ! θ = t .
    Proof .
      intros u t θ; unfold matches .
      coq_case_eq (matches_r u t (VM.empty _)); try discr; intros Ω HΩ .
      inversion_clear 1; apply (proj1 matches_r_correct) with (VM.empty _) .
      assumption .
    Qed .
  End MatchCorrectness .
End Matching .
