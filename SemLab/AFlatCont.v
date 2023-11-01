(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-07-02

flat context closure (Sternagel & Middeldorp, RTA'08)
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs NatUtil LogicUtil ListUtil SN EqUtil VecUtil
     RelUtil BoundNat.

(***********************************************************************)
(** flat context closure of a rule *)

Section S.

  Variable Sig : Signature.

  Notation term := (term Sig). Notation terms := (vector term).
  Notation rule := (rule Sig). Notation rules := (rules Sig).

  Lemma flat_cont_aux : forall n i, i < n -> i + S (n - S i) = n.

  Proof. lia. Qed.

  Definition flat_cont_symb n (f : Sig) i (h : i < arity f) :=
    Cont f (flat_cont_aux h) (fresh n i) Hole (fresh (n+i) (arity f - S i)).

  Arguments flat_cont_symb _ [f i] _.

  Variables (some_symbol : Sig) (arity_some_symbol : arity some_symbol > 0)
            (n : nat).

  Definition one_flat_cont := flat_cont_symb n arity_some_symbol.

  Definition flat_conts_symb n f :=
    map (fun x => flat_cont_symb n (N_prf x)) (L (arity f)).

  Variables (Fs : list Sig) (Fs_ok : forall x : Sig, In x Fs).

  Definition flat_conts n := flat_map (flat_conts_symb n) Fs.

  Definition flat_cont_rule (a : rule) c :=
    let (l,r) := a in mkRule (fill c l) (fill c r).

  Definition is_root_preserving (a : rule) := let (l,r) := a in
    match l, r with
      | Fun f _, Fun g _ => beq_symb f g
      | _, _ => true
    end.

  Definition flat_rule n (a : rule) :=
    if is_root_preserving a then a :: nil
      else map (flat_cont_rule a) (flat_conts n).

  Definition flat_rules R := flat_map (flat_rule (S n)) R.

  Lemma root_preserving : forall R a,
    is_root_preserving a = true -> In a R -> In a (flat_rules R).

  Proof.
    intros. unfold flat_rules. rewrite in_flat_map. exists a. split_all.
    unfold flat_rule. rewrite H. simpl. auto.
  Qed.

(***********************************************************************)
(** main theorem for standard rewriting *)

  Section red.

    Variables (R : rules) (hyp : n >= maxvar_rules R).

    Lemma red_flat : red (flat_rules R) << red R.

    Proof.
      intros t u h. redtac. unfold flat_rules in lr. rewrite in_flat_map in lr.
      destruct lr as [[a b] [h1 h2]]. unfold flat_rule in h2. simpl in h2.
      destruct a. simpl in h2. split_all. inversion H. subst. apply red_rule.
      hyp.
      destruct b. simpl in h2. split_all. inversion H. subst. apply red_rule.
      hyp.
      revert h2. case_beq_symb Sig f f0; intro. simpl in h2. split_all.
      inversion H. subst. apply red_rule. hyp.
      rewrite in_map_iff in h2.
      destruct h2 as [d [h3 h4]]. unfold flat_cont_rule in h3. inversion h3.
      clear h3. subst. unfold flat_conts in h4. rewrite in_flat_map in h4.
      destruct h4 as [g [h5 h6]]. unfold flat_conts_symb in h6.
      rewrite in_map_iff in h6. destruct h6 as [x [h3 h4]]. subst.
      unfold flat_cont_symb. simpl. rewrite !Vmap_cast, !Vmap_app. simpl.
      set (v1 := Vmap (sub s) (fresh (S n) x)).
      set (v2 := Vmap (sub s) (fresh (S(n+x)) (arity g - S x))).
      set (e := flat_cont_aux x). set (d' := Cont g e v1 Hole v2).
      set (v' := Vmap (sub s) t0). set (v0' := Vmap (sub s) t1).
      change (red R (fill c (fill d' (sub s (Fun f t0))))
        (fill c (fill d' (sub s (Fun f0 t1))))). rewrite !fill_fill.
      apply red_rule. hyp.
    Qed.

    Definition red_flat_cont := Rof (red (flat_rules R)) (fill one_flat_cont).

    Lemma red_one_flat_cont_intro : red R << red_flat_cont.

    Proof.
      intros t u h. redtac. subst. unfold red_flat_cont, Rof.
      rewrite !fill_fill.
      case_eq (is_root_preserving (mkRule l r)); intros.
      apply red_rule. unfold flat_rules. rewrite in_flat_map.
      exists (mkRule l r). split_all. unfold flat_rule. rewrite H. simpl. auto.
      destruct l. discr. destruct r. discr.
      destruct (cont_case (comp one_flat_cont c)). discr.
      destruct H0 as [d [g [i [vi [j [vj [e]]]]]]]. rewrite !H0, <- !fill_fill.
      set (l := Fun f t). set (r := Fun f0 t0).
      apply context_closed_red.
      assert (m : maxvar_rule (mkRule l r) < S n). eapply maxvar_rules_elim.
      apply lr. lia.
      rewrite !fill_sub with (n:=n).
      set (s' := maxvar_union (S n) s (fsub n (Vapp vi vj))).
      apply hd_red_incl_red. apply hd_red_rule. unfold flat_rules.
      rewrite in_flat_map. exists (mkRule l r). split_all. unfold flat_rule.
      unfold l, r. rewrite H, in_map_iff. assert (h : i < arity g). lia.
      exists (flat_cont_symb (S n) h). split_all. simpl.
      gen (flat_cont_aux h). assert (arity g - S i = j). lia.
      rewrite H1.
      intro. assert (e0=e). apply eq_unique. subst. refl.
      unfold flat_conts. rewrite in_flat_map. exists g. split. apply Fs_ok.
      unfold flat_conts_symb. rewrite in_map_iff. exists (N_ h). split_all.
      apply In_L.
      trans (maxvar_rule (mkRule l r)). lia. apply Nat.le_max_r.
      trans (maxvar_rule (mkRule l r)). lia. apply Nat.le_max_l.
    Qed.

    Lemma rtc_red_one_flat_cont_intro : forall t u, red R # t u ->
      red (flat_rules R) # (fill one_flat_cont t) (fill one_flat_cont u).

    Proof.
      induction 1. apply rt_step. apply red_one_flat_cont_intro. hyp.
      apply rt_refl. apply rt_trans with (fill one_flat_cont y); hyp.
    Qed.

    Lemma WF_red_flat : WF (red R) <-> WF (red (flat_rules R)).

    Proof.
      split; intro.
      (* -> *)
      intro t. gen (H t). induction 1. apply SN_intro; intros. apply H1.
      apply red_flat. hyp.
      (* <- *)
      intro t. geneq H t (fill one_flat_cont t). induction 1. intros. subst.
      apply SN_intro; intros. apply H0 with (fill one_flat_cont y). 2: refl.
      apply red_one_flat_cont_intro. hyp.
    Qed.

  End red.

(***********************************************************************)
(** main theorem for rewriting modulo *)

  Section red_mod.

    Variables E R : rules.
    Variable hypE : n >= maxvar_rules E.
    Variable hypR : n >= maxvar_rules R.

    Lemma WF_red_mod_flat :
      WF (red_mod E R) <-> WF (red_mod (flat_rules E) (flat_rules R)).

    Proof.
      split; intro.
      (* -> *)
      intro t. gen (H t). induction 1. apply SN_intro; intros. apply H1.
      do 2 destruct H2. exists x0. split.
      (* rewrite red_flat in H2. hyp. *) eapply incl_elim.
      eapply rtc_incl. apply red_flat. hyp.
      apply red_flat. hyp.
      (* <- *)
      intro t. geneq H t (fill one_flat_cont t). induction 1. intros. subst.
      apply SN_intro; intros. apply H0 with (fill one_flat_cont y). 2: refl.
      do 2 destruct H1. exists (fill one_flat_cont x). split.
      apply rtc_red_one_flat_cont_intro; hyp.
      apply red_one_flat_cont_intro; hyp.
    Qed.

  End red_mod.

End S.

(***********************************************************************)
(** functorization *)

Module Type FlatCC.
  Parameter Sig : Signature.
  Parameter Fs : list Sig.
  Parameter Fs_ok : forall x : Sig, In x Fs.
  Parameter some_symbol : Sig.
  Parameter arity_some_symbol : arity some_symbol > 0.
End FlatCC.

Module FlatCCProps (Import F : FlatCC).

  Notation rules := (rules Sig).

  Section red_mod.

    Variables E R : rules.

    Let n := max (maxvar_rules E) (maxvar_rules R).

    Definition flat_mod_rules := flat_rules n Fs.

    Lemma WF_red_mod_flat :
      WF (red_mod E R) <-> WF (red_mod (flat_mod_rules E) (flat_mod_rules R)).

    Proof.
      eapply WF_red_mod_flat. apply arity_some_symbol. apply Fs_ok.
      apply Nat.le_max_l. apply Nat.le_max_r.
    Qed.

  End red_mod.

  Section red.

    Variable R : rules.

    Let n := maxvar_rules R.

    Definition flat_rules := flat_rules n Fs R.

    Lemma WF_red_flat : WF (red R) <-> WF (red flat_rules).

    Proof.
      eapply WF_red_flat. apply arity_some_symbol. apply Fs_ok. apply Nat.le_refl.
    Qed.

  End red.

  Ltac flat_cc :=
    match goal with
      | |- WF (red_mod _ _) => rewrite WF_red_mod_flat
      | |- WF (red _) => rewrite WF_red_flat
    end.

End FlatCCProps.
