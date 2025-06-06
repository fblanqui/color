From Stdlib Require Import Setoid List Relations Wellfounded PeanoNat.
From CoLoR Require Import weaved_relation list_permut terminaison.
From CoLoR Require equational_theory equational_extension term subterm_dp.

Module MakeMarkedEqTh (EqtT : equational_theory_spec.EqTh).

  Module F <: term_spec.Signature.
    Module Symb.
      Definition A := (bool * EqtT.T.symbol)%type.
      Definition eq_A := @eq A.

      Lemma eq_proof : equivalence A eq_A.
      Proof.
        constructor; red.
        reflexivity.
        intros; transitivity y; assumption.
        intros; symmetry; assumption.
      Qed.

      Add Relation A eq_A
        reflexivity proved by (@equiv_refl _ _ eq_proof)
        symmetry proved by (@equiv_sym _ _ eq_proof)
        transitivity proved by (@equiv_trans _ _ eq_proof) as EQA.

      Definition eq_bool (t1 t2 : A) : bool :=
        match t1, t2 with
        | (true, _), (false, _) => false
        | (false, _), (true, _) => false
        | (_, t1), (_, t2) => EqtT.T.F.Symb.eq_bool t1 t2
        end.

      Lemma eq_bool_ok : forall (t1 t2 : A),
        if eq_bool t1 t2 then t1 = t2 else t1 <> t2.
      Proof.
        intros [b1 t1] [b2 t2];
        destruct b1; destruct b2; simpl;
        try solve [intros H; inversion H];
        case_eq (EqtT.T.eq_symb_bool t1 t2); intros H;
        generalize (EqtT.T.eq_symb_bool_ok t1 t2);
        rewrite H; intros H0; try (f_equal; exact H0);
        intros G; inversion G as [H1]; elim H0; exact H1.
      Qed.
    End Symb.

    Definition arity (f : Symb.A) := EqtT.T.F.arity (snd f).
  End F.

  Module T := term.Make'(F)(EqtT.T.X).
  Module EQT := equational_theory.Make(T).

  Definition inject_symb (f : EqtT.T.symbol) : T.symbol := (false, f).
  Definition mark_symb (f : T.symbol) : T.symbol := (true, snd f).
End MakeMarkedEqTh.

Module OrderingPair (Eqt : equational_theory_spec.EqTh).

  Module M := Eqt.T.

  Definition Trel_stable (R1 R2 : relation M.term) :=
    forall (t1 t2 : M.term) (sigma : M.substitution),
      R1 t1 t2 -> R2 (M.apply_subst sigma t1) (M.apply_subst sigma t2).

  Definition Trel_monotone (R : relation M.term) :=
    forall (f : M.symbol) (l1 l2 : list M.term),
      one_step_list R l1 l2 -> R (M.Term f l1) (M.Term f l2).

  Definition Trel_compat (R1 R2 : relation M.term) :=
    forall (t1 t2 t3 : M.term), R1 t1 t2 -> R2 t2 t3 -> R1 t1 t3.

  Section S.
    Variable R O : relation M.term.
    Hypothesis R_stable : Trel_stable R O.
    Hypothesis O_monotone : Trel_monotone O.

    Lemma stable_monotone_R_list :
      inclusion _ (one_step_list (Eqt.one_step R)) (one_step_list O).
    Proof.
      set (P2 := fun t1 t2 => Eqt.one_step R t1 t2 -> O t1 t2);
      set (Pl2 := fun l1 l2 => one_step_list (Eqt.one_step R) l1 l2
                            -> one_step_list O l1 l2);
      change (forall l1 l2, Pl2 l1 l2);
      apply M.term_rec8 with P2;
      unfold P2 in *; unfold Pl2 in *; clear P2 Pl2.

      intros v t H; inversion H; subst;
      destruct H0; apply R_stable; assumption.

      intros t v H; inversion H; subst;
      destruct H0; apply R_stable; assumption.

      intros f1 f2 l1 l2 H H0; inversion H0; subst;
      [ destruct H1; apply R_stable; assumption
      | apply O_monotone; apply H; assumption ].

      induction l1; intros l2 H H0; inversion H0; subst;
      [ constructor 1; apply H; [| | assumption ];
        left; reflexivity
      | constructor 2; apply IHl1; [| assumption ];
        intros; apply H; try right; assumption ].
    Qed.

    Lemma stable_monotone_R_term : inclusion _ (Eqt.one_step R) O.
    Proof.
      intros t1 t2 H; inversion H; subst;
      [ inversion H0; subst; apply R_stable
      | apply O_monotone; apply stable_monotone_R_list ];
      assumption.
    Qed.
  End S.
End OrderingPair.

Module OrdAFS (Eqt : equational_theory_spec.EqTh).

  Module M := Eqt.T.
  Module Import op := OrderingPair(Eqt).

  Inductive afs_val :=
    | AFS_id : M.symbol -> afs_val
    | AFS_arg : nat -> afs_val
    | AFS_filt : M.symbol -> list nat -> afs_val.

  Fixpoint afs_filt (l : list M.term) (ns : list nat) : list M.term :=
    match ns with
    | n::ns =>
      match nth_error l n with
      | Some t => t :: afs_filt l ns
      | _ => afs_filt l ns
      end
    | _ => nil
    end.

  Fixpoint afs_term (afs_symb : M.symbol -> afs_val) (t : M.term) : M.term :=
    match t with
    | M.Var _ => t
    | M.Term f l =>
      let l' := map (afs_term afs_symb) l in
      match afs_symb f with
      | AFS_id f => M.Term f l'
      | AFS_arg n => nth n l' (M.Term f nil)
      | AFS_filt f ns => M.Term f (afs_filt l' ns)
      end
    end.

  Lemma nth_map : forall (A : Type) (F : A -> A)
                  (d : A) (l : list A) (i : nat),
    i < length l -> nth i (map F l) d = F (nth i l d).
  Proof.
    intros; revert i H; induction l;
    intros; [ inversion H |];
    destruct i; simpl; [ reflexivity |];
    apply IHl; apply Nat.succ_lt_mono in H; assumption.
  Qed.

  Section S.
    Variables Tle Tlt : relation M.term.
    Hypothesis Tlt_wf : well_founded Tlt.
    Hypothesis Tle_mono : Trel_monotone Tle.
    Hypothesis Tlt_Tle_compat : Trel_compat Tlt Tle.

    Hypothesis Tle_refl : reflexive _ Tle.
    Hypothesis Tle_trans : transitive _ Tle.

    Variable afs_symb : M.symbol -> afs_val.

    Let afs := afs_term afs_symb.
    Let Tlt_afs (t1 t2 : M.term) := Tlt (afs t1) (afs t2).
    Let Tle_afs (t1 t2 : M.term) := Tle (afs t1) (afs t2).

    Lemma Tlt_Tle_compat_afs : Trel_compat Tlt_afs Tle_afs.
    Proof.
      intros t1 t2 t3;
      apply (Tlt_Tle_compat (afs t1) (afs t2) (afs t3)).
    Qed.

    Lemma Tle_monotone_afs : Trel_monotone Tle_afs.
    Proof.
      intros f l1 l2 H.

      unfold Tle_afs; unfold afs; simpl;
      destruct (afs_symb f) as [g|i|g ns]; simpl.

      apply Tle_mono;
      induction H; [ left | right ]; assumption.

      generalize (Nat.le_gt_cases (length l1) i); intros [Hi|Hi].

      rewrite nth_overflow; [| rewrite length_map; assumption ];
      rewrite nth_overflow; [| rewrite length_map;
        apply one_step_list_length_eq in H; rewrite <- H; assumption ].
      apply Tle_refl.

      revert i Hi; induction H; destruct i; simpl; intros;
      [ assumption
      | apply Tle_refl
      | apply Tle_refl
      | apply IHone_step_list; apply (proj2 (Nat.succ_lt_mono _ _) Hi) ].

      cut (refl_trans_clos (one_step_list Tle)
        (afs_filt (map afs l1) ns) (afs_filt (map afs l2) ns));
      [ unfold afs; intros [Hr|x y Htc];
        [ apply Tle_refl |]; induction Htc;
        [| apply Tle_trans with (M.Term g y); [| assumption ]];
        apply Tle_mono; assumption |].

      revert l1 l2 H; induction ns; intros; [ constructor |].

      cut (
        (nth_error (map afs l1) a = None /\
         nth_error (map afs l2) a = None) \/
        (exists t1, exists t2,
         nth_error (map afs l1) a = Some t1 /\
         nth_error (map afs l2) a = Some t2 /\
         Tle t1 t2));
      [ intros [[H0 H1]|[t1 [t2 [H0 [H1 H2]]]]]; simpl;
        rewrite H0; rewrite H1; [ exact (IHns _ _ H) | right ];
        right with (t2 :: afs_filt (map afs l1) ns);
        [ left; assumption |]; apply IHns in H; destruct H;
        [ left; left; apply Tle_refl
        | induction H; [ left; right; assumption |];
          right with (t2::y); [ right |]; assumption ] |].

      revert l1 l2 H; induction a.

      intros; inversion H; subst; right;
      [ exists (afs t1); exists (afs t2)
      | exists (afs t); exists (afs t) ];
      split; try reflexivity;
      split; try reflexivity;
      [ assumption | apply Tle_refl ].

      intros; inversion H; subst; simpl; [| exact (IHa _ _ H0) ];
      destruct (nth_error (map afs l) a);
      [ right; exists t; exists t;
        split; try reflexivity;
        split; try reflexivity;
        apply Tle_refl
      | left; split; reflexivity ].
    Qed.

    Definition sigma_afs (sigma : M.substitution) :=
      map (fun p => (fst p, afs (snd p))) sigma.

    Lemma afs_subst : forall t sigma,
      afs (M.apply_subst sigma t) = M.apply_subst (sigma_afs sigma) (afs t).
    Proof.
      intros; pattern t; apply M.term_rec3; intros.

      induction sigma as [|[v0 t0] sigma]; [ reflexivity |];
      simpl; case (M.eq_var_bool v v0); [ reflexivity | assumption ].

      unfold afs; simpl; destruct (afs_symb f) as [g|i|g ns]; simpl.

      f_equal; revert H; clear; induction l; simpl; intros;
      [ reflexivity |]; f_equal; [ apply H; left; reflexivity |];
      apply IHl; intros; apply H; right; assumption.

      generalize (Nat.le_gt_cases (length l) i); intros [Hi|Hi].

      rewrite nth_overflow;
      [| rewrite length_map; rewrite length_map; assumption ];
      rewrite nth_overflow;
      [| rewrite length_map; assumption ];
      reflexivity.

      rewrite nth_map; [| rewrite length_map; assumption ];
      rewrite nth_map; [| assumption ];
      rewrite nth_map; [| assumption ];
      rewrite <- H; [ reflexivity |];
      apply nth_In; assumption.

      f_equal; clear f g; revert l H; induction ns as [|i ns];
      [ intros; reflexivity |]; intros.

      cut(
        (nth_error (map afs (map (M.apply_subst sigma) l)) i = None /\
         nth_error (map afs l) i = None) \/
        (exists t0, exists t1,
         nth_error (map afs (map (M.apply_subst sigma) l)) i = Some t0 /\
         nth_error (map afs l) i = Some t1 /\
         t0 = M.apply_subst (sigma_afs sigma) t1));
      [ intros [[H0 H1]|[t0 [t1 [H0 [H1 H2]]]]]; simpl; unfold afs in *;
        rewrite H0; rewrite H1; [| simpl; f_equal; [ assumption |]];
        apply IHns; assumption |].

      revert i; induction l as [|s l];
      [ left; destruct i; split; reflexivity | destruct i ];
      [| simpl; apply IHl; intros; apply H; right; assumption ];
      right; exists (afs (M.apply_subst sigma s)); exists (afs s);
      split; [ reflexivity |]; split; [ reflexivity |];
      apply H; left; reflexivity.
    Qed.
  End S.
End OrdAFS.

Module OrdSafeAFS (Eqt : equational_theory_spec.EqTh).

  Module M := Eqt.T.
  Module Import op := OrderingPair(Eqt).

  Inductive afs_val :=
    | AFS_perm : M.symbol -> list nat -> afs_val.

  Fixpoint afs_rest (ns ac : list nat) (l : nat) :=
    match l with
    | S l => if existsb (Nat.eqb l) ns
             then afs_rest ns ac l
             else afs_rest ns (l::ac) l
    | _ => ac
    end.

  Fixpoint afs_filt (l : list M.term) (ns : list nat) : list M.term :=
    match ns with
    | n::ns =>
      match nth_error l n with
      | Some t => t :: afs_filt l ns
      | _ => afs_filt l ns
      end
    | _ => nil
    end.

  Fixpoint afs_term (afs_symb : M.symbol -> afs_val) (t : M.term) : M.term :=
    match t with
    | M.Var _ => t
    | M.Term f l =>
      let l' := map (afs_term afs_symb) l in
      match afs_symb f with
      | AFS_perm f ns =>
        M.Term f (afs_filt l' (afs_rest ns ns (length l')))
      end
    end.

  Lemma rest_safe : forall ns l i, i < l -> In i (afs_rest ns ns l).
  Proof.
    intros ns;
    cut (forall l i, i < l ->
         forall ac, (forall x, In x ns -> In x ac) ->
         In i (afs_rest ns ac l));
    [ intros; apply H; try intros; assumption |].
      induction l; intros; simpl; [ inversion H |];
    apply Nat.lt_eq_cases in H; destruct H;
    [ destruct (existsb (Nat.eqb l)); apply IHl;
      try apply Nat.succ_lt_mono; try assumption;
      intros; right; apply H0; assumption |].
    assert (Hk : forall k ac, In i ac -> In i (afs_rest ns ac k));
    [ induction k; intros; simpl; [ assumption |];
      destruct (existsb (Nat.eqb k) ns);
      apply IHk; [| right ]; assumption |].

    apply eq_add_S in H; rewrite <- H; clear H IHl;
    case_eq (existsb (Nat.eqb i) ns); intros;
    [| apply Hk; left; reflexivity ].

    apply existsb_exists in H; destruct H as [j [Hi H]];
    apply Nat.eqb_eq in H; rewrite <- H in Hi; clear H;
    apply Hk; apply H0; assumption.
  Qed.

  Fixpoint intersperse (a : M.term) (ls : list (list M.term)) : list M.term :=
    match ls with
    | l :: nil => l
    | l :: tl => l ++ a :: intersperse a tl
    | _ => nil
    end.

  Fixpoint dissect (n : nat) (l : list nat) : list (list nat) :=
    match l with
    | m :: tl =>
      let ls := dissect n tl in
      if Nat.eqb n m then (nil :: ls)
      else match ls with
      | (r::ls) => ((m::r) :: ls)
      | _ => ((m::nil) :: nil)
      end
    | _ => (nil :: nil)
    end.

  Lemma dissect_not_nil : forall n l, dissect n l <> nil.
  Proof.
    intros n; destruct l as [|i l];
    intros Heq; simpl in Heq;
    [| destruct (Nat.eqb n i);
    [| destruct (dissect n l) ]];
    discriminate Heq.
  Qed.

  Lemma dissect_in : forall l i, In i l ->
    exists m1 : list nat, exists m2 : list nat,
    exists mm : list (list nat), m1 :: m2 :: mm = dissect i l.
  Proof.
    induction l; simpl; intros;
    [ contradiction H | destruct H ];
    [ rewrite H; rewrite Nat.eqb_refl;
      destruct l; simpl;
      [| destruct (Nat.eqb i n);
      [| destruct (dissect i l) ]]
    | destruct (IHl i H) as [m1 [m2 [mm Hm]]];
      rewrite <- Hm; destruct (Nat.eqb i a) ];
    eexists; eexists; eexists; eauto.
  Qed.

  Lemma nth_in : forall (A : Type) (s : A) (lh lt : list A),
    nth_error (lh ++ s :: lt) (length lh) = Some s.
  Proof.
    intros; induction lh; simpl; [ reflexivity | assumption ].
  Qed.

  Lemma inter_diss : forall x l lh lt s,
    afs_filt (lh ++ s :: lt) l = intersperse s
    (map (afs_filt (lh ++ x :: lt)) (dissect (length lh) l)).
  Proof.
    clear; intros;
    set (ds := dissect (length lh) l);
    assert (Heq: dissect (length lh) l = ds);
    [ reflexivity | clearbody ds ].

    revert l Heq; induction ds; intros;
    [ apply dissect_not_nil in Heq; contradiction Heq |].

    revert a l Heq; induction a; intros.

    destruct l; simpl in Heq;
    [ injection Heq; intros; subst; reflexivity |];
    case_eq (Nat.eqb (length lh) n);
    intros Hn; rewrite Hn in Heq;
    [| destruct (dissect (length lh) l); discriminate Heq ];
    injection Heq; clear Heq; intros Heq; destruct ds;
    [ apply dissect_not_nil in Heq; contradiction Heq |];
    apply Nat.eqb_eq in Hn; rewrite <- Hn; clear Hn;
    simpl; rewrite nth_in; f_equal; apply IHds; assumption.

    destruct l; simpl in Heq; [ discriminate Heq |];
    case_eq (Nat.eqb (length lh) n);
    intros Hn; rewrite Hn in Heq;
    [ discriminate Heq | apply Nat.eqb_neq in Hn ];
    case_eq (dissect (length lh) l);
    [ intros G; apply dissect_not_nil in G; contradiction G |];
    intros; rewrite H in Heq; injection Heq; intros; subst;
    apply IHa in H; clear IHds IHa Heq.

    assert (nth_error (lh ++ s :: lt) a = nth_error (lh ++ x :: lt) a);
    [ revert a Hn; clear; induction lh; simpl; intros;
      [ destruct a; [ contradiction Hn |]; reflexivity
      | destruct a0; [ reflexivity |]; apply IHlh;
        intros H; contradiction Hn; rewrite H; reflexivity ]|];
    simpl; rewrite H0; destruct ds; [| destruct a0 ];
    rewrite H; destruct (nth_error (lh ++ x :: lt) a);
    reflexivity.
  Qed.

  Section S.
    Variables Tle Tlt : relation M.term.
    Hypothesis Tlt_wf : well_founded Tlt.
    Hypothesis Tle_mono : Trel_monotone Tle.
    Hypothesis Tlt_mono : Trel_monotone Tlt.
    Hypothesis Tlt_Tle_compat : Trel_compat Tlt Tle.

    Hypothesis Tle_trans : transitive _ Tle.
    Hypothesis Tlt_trans : transitive _ Tlt.

    Variable afs_symb : M.symbol -> afs_val.

    Let afs := afs_term afs_symb.
    Let Tlt_afs (t1 t2 : M.term) := Tlt (afs t1) (afs t2).
    Let Tle_afs (t1 t2 : M.term) := Tle (afs t1) (afs t2).

    Lemma Tlt_Tle_compat_afs : Trel_compat Tlt_afs Tle_afs.
    Proof.
      intros t1 t2 t3;
      apply (Tlt_Tle_compat (afs t1) (afs t2) (afs t3)).
    Qed.

    Lemma gen_monotone_afs : forall (R : relation M.term),
      transitive _ R -> Trel_monotone R ->
      Trel_monotone (fun x y => R (afs x) (afs y)).
    Proof.
      intros R HtransR HmonoR f l1 l2 H.

      unfold afs.

      simpl; destruct (afs_symb f) as [g ns].

      assert (Hl : one_step_list R (map afs l1) (map afs l2));
      [ induction H; [ left | right ]; assumption |]; unfold afs in Hl;
      set (ll1 := map (afs_term afs_symb) l1) in *; clearbody ll1;
      set (ll2 := map (afs_term afs_symb) l2) in *; clearbody ll2;
      clear l1 l2 H; revert ll1 ll2 Hl; intros l1 l2 H.

      cut (trans_clos (one_step_list R)
        (afs_filt l1 (afs_rest ns ns (length l1)))
        (afs_filt l2 (afs_rest ns ns (length l2))));
      [ intros Htc; induction Htc;
        [| apply HtransR with (M.Term g y); [| assumption ]];
        apply HmonoR; assumption | clear f g ].

      generalize (rest_safe ns (length l1)); intros Hin.

      assert (Hl : length l1 = length l2);
      [ apply one_step_list_length_eq in H; assumption |];
      rewrite <- Hl; set (l := afs_rest ns ns (length l1)) in *;
      clearbody l; clear ns Hl.

      apply one_step_in_list in H;
      destruct H as [s [t [lh [lt [Rts [Hs Ht]]]]]]; subst.

      rewrite (inter_diss s l lh lt s);
      rewrite (inter_diss s l lh lt t);
      set (f:= afs_filt (lh ++ s :: lt)); clearbody f.

      cut (exists m1, exists m2, exists mm,
        m1 :: m2 :: mm = dissect (length lh) l);
      [| apply dissect_in; apply Hin; rewrite length_app;
         simpl; pattern (length lh) at 1; rewrite <- Nat.add_0_r;
         apply Nat.add_lt_mono_l; apply Nat.lt_0_succ ].

      set (ll := dissect (length lh) l); clearbody ll;
      induction ll; intros [m1 [m2 [mm Hm]]]; rewrite <- Hm;
      [ discriminate Hm | destruct ll; [ discriminate Hm |]];
      rewrite rwr_list_expand_strong;
      exists s; exists t; exists (f m1);
      exists (intersperse s (map f (m2::mm)));
      exists (intersperse t (map f (m2::mm)));
      split; [ reflexivity |];
      split; [ reflexivity |];
      split; [ left; assumption |];
      destruct mm; [ left | right ];
      injection Hm; intros; subst; apply IHll;
      exists l0; exists l1; exists mm; reflexivity.
    Qed.

    Lemma Tlt_monotone_afs : Trel_monotone Tlt_afs.
    Proof.
      apply gen_monotone_afs;
      [ apply Tlt_trans | apply Tlt_mono ].
    Qed.

    Lemma Tle_monotone_afs : Trel_monotone Tle_afs.
    Proof.
      apply gen_monotone_afs;
      [ apply Tle_trans | apply Tle_mono ].
    Qed.

    Definition sigma_afs (sigma : M.substitution) :=
      map (fun p => (fst p, afs (snd p))) sigma.

    Lemma afs_subst : forall t sigma,
      afs (M.apply_subst sigma t) = M.apply_subst (sigma_afs sigma) (afs t).
    Proof.
      intros; pattern t; apply M.term_rec3; intros.

      induction sigma as [|[v0 t0] sigma]; [ reflexivity |];
      simpl; case (M.eq_var_bool v v0); [ reflexivity | assumption ].

      unfold afs; simpl; destruct (afs_symb f) as [g ns]; simpl;
      f_equal; clear f g.

      rewrite length_map; rewrite length_map; rewrite length_map;
      set (ns0 := afs_rest ns ns (length l)); clearbody ns0; clear ns.

      revert l H; induction ns0 as [|i ns];
      intros; [ reflexivity |].

      cut(
        (nth_error (map afs (map (M.apply_subst sigma) l)) i = None /\
         nth_error (map afs l) i = None) \/
        (exists t0, exists t1,
         nth_error (map afs (map (M.apply_subst sigma) l)) i = Some t0 /\
         nth_error (map afs l) i = Some t1 /\
         t0 = M.apply_subst (sigma_afs sigma) t1));
      [ intros [[H0 H1]|[t0 [t1 [H0 [H1 H2]]]]]; simpl; unfold afs in *;
        rewrite H0; rewrite H1; [| simpl; f_equal; [ assumption |]];
        apply IHns; assumption |].

      revert i; induction l as [|s l];
      [ left; destruct i; split; reflexivity | destruct i ];
      [| simpl; apply IHl; intros; apply H; right; assumption ];
      right; exists (afs (M.apply_subst sigma s)); exists (afs s);
      split; [ reflexivity |]; split; [ reflexivity |];
      apply H; left; reflexivity.
    Qed.
  End S.
End OrdSafeAFS.

Module MakeSDP (Eqt : equational_theory_spec.EqTh).

  Module M := Eqt.T.
  Module sdp := subterm_dp.MakeSubDP(Eqt).
  Module Import op := OrderingPair(Eqt).

  Section S.
    Variables Tle Tlt : relation M.term.
    Hypothesis Tlt_wf : well_founded Tlt.
    Hypothesis Tle_mono : Trel_monotone Tle.
    Hypothesis Tlt_Tle_compat : Trel_compat Tlt Tle.

    Variables R_rules dps : relation M.term.
    Hypothesis rules_decrease : Trel_stable R_rules Tle.
    Hypothesis dps_strictly_decrease : Trel_stable dps Tlt.

    Lemma rtc_R_step : forall t f l1 l2, Tlt t (M.Term f l1) ->
      refl_trans_clos (one_step_list (Eqt.one_step R_rules)) l1 l2 ->
      Tlt t (M.Term f l2).
    Proof.
      intros t f l1 l H H0;
      destruct H0; [ assumption |];
      induction H0; [| apply IHtrans_clos ];
      apply Tlt_Tle_compat with (M.Term f x);
      try assumption; apply Tle_mono;
      apply stable_monotone_R_list with R_rules;
      assumption.
    Qed.

    Lemma wf_Rcdp : well_founded (sdp.Rcdp R_rules dps).
    Proof.
      apply wf_incl with Tlt; [| assumption ];
      intros x y H; inversion H; inversion H1; subst;
      apply rtc_R_step with l2; [| assumption ];
      rewrite <- H4; apply dps_strictly_decrease;
      assumption.
    Qed.

    Variable P_rest : M.term -> Prop.
    Let Rcdp_rest d := rest P_rest (sdp.Rcdp R_rules d).

    Lemma wf_Rcdp_rest : well_founded (Rcdp_rest dps).
    Proof.
      apply wf_incl with (sdp.Rcdp R_rules dps);
      [ intros x y [H H0]; assumption | apply wf_Rcdp ].
    Qed.

    Variables dps_large dps_union : relation M.term.
    Hypothesis dps_large_decrease : Trel_stable dps_large Tle.
    Hypothesis dps_large_wf : well_founded (Rcdp_rest dps_large).
    Hypothesis dps_union_def : forall (t1 t2 : M.term),
      dps_union t1 t2 -> dps t1 t2 \/ dps_large t1 t2.

    Lemma wf_union_Rcdp_rest : well_founded (Rcdp_rest dps_union).
    Proof.
      intros t;
      apply well_founded_ind with (R:=Tlt);
      [ apply Tlt_wf |]; clear t.

      intros t; pattern t;
      apply well_founded_ind with (R:=Rcdp_rest dps_large);
      [ apply dps_large_wf |]; clear t.

      intros t IH2 IH1; constructor; intros s [H Hrest];
      destruct H as [f l1 l2 t Hl1_l2 Ht];
      inversion Ht; clear Ht; subst.

      destruct (dps_union_def _ _ H1).

      apply IH1; apply rtc_R_step with l2; [| assumption ];
      rewrite <- H; apply dps_strictly_decrease; assumption.

      apply IH2.

      split; [| assumption ];
      split with (l2:=l2); [ assumption |];
      rewrite <- H; constructor; assumption.

      intros x Hx; apply IH1;
      apply rtc_R_step with l2; [| assumption ];
      apply Tlt_Tle_compat
        with (M.apply_subst sigma t1); [ assumption |];
      rewrite <- H; apply dps_large_decrease; assumption.
    Qed.
  End S.
End MakeSDP.

Module MakeMarkedSDP
  (EqtT : equational_theory_spec.EqTh)
  (EqtM : equational_theory_spec.EqTh with Module T.X := EqtT.T.X).

  Module T := EqtT.T.
  Module M := EqtM.T.
  Module opT := OrderingPair(EqtT).
  Module opM := OrderingPair(EqtM).

  Module sdp := subterm_dp.MakeSubDP(EqtT).

  Section S.
    Variables Tle Tlt : relation M.term.
    Hypothesis Tlt_wf : well_founded Tlt.
    Hypothesis Tle_mono : opM.Trel_monotone Tle.
    Hypothesis Tlt_Tle_compat : opM.Trel_compat Tlt Tle.

    Variable inject_symb : T.symbol -> M.symbol.

    Fixpoint inject_term (t : T.term) : M.term :=
      match t with
      | T.Term f ts => M.Term (inject_symb f) (List.map inject_term ts)
      | T.Var i => M.Var i
      end.

    Variable mark_symb : M.symbol -> M.symbol.

    Definition mark_term (t : M.term) : M.term :=
      match t with
      | M.Term f ts => M.Term (mark_symb f) ts
      | _ => t
      end.

    Definition sigma_inject (sigma : T.substitution) : M.substitution :=
      map (fun p => (fst p, inject_term (snd p))) sigma.

    Lemma inject_subst : forall t sigma,
      inject_term (T.apply_subst sigma t) = M.apply_subst (sigma_inject sigma) (inject_term t).
    Proof.
      intros; pattern t; apply T.term_rec3; intros.

      induction sigma as [|[v0 t0] sigma]; [ reflexivity |];
      simpl; case (M.eq_var_bool v v0); [ reflexivity | assumption ].

      simpl; f_equal; revert H; induction l; simpl; intros;
      [ reflexivity | f_equal; [ apply H; left; reflexivity |]];
      apply IHl; intros; apply H; right; assumption.
    Qed.

    Definition is_fapp (t : T.term) : Prop :=
      match t with
      | T.Term _ _ => True
      | _ => False
      end.

    Lemma mark_inject_subst : forall t sigma, is_fapp t ->
      mark_term (inject_term (T.apply_subst sigma t)) =
      M.apply_subst (sigma_inject sigma) (mark_term (inject_term t)).
    Proof.
      intros; destruct t; [ contradiction H | clear H ].
      simpl; f_equal; induction l; [ reflexivity |];
      simpl; f_equal; [ apply inject_subst | assumption ].
    Qed.

    Let Tlt_mark (t1 t2 : T.term) :=
      Tlt (mark_term (inject_term t1)) (mark_term (inject_term t2)).

    Let Tle_mark (t1 t2 : T.term) :=
      Tle (mark_term (inject_term t1)) (mark_term (inject_term t2)).

    Let Tle_inject (t1 t2 : T.term) :=
      Tle (inject_term t1) (inject_term t2).

    Variables R_rules dps : relation T.term.
    Hypothesis rules_decrease : opT.Trel_stable R_rules Tle_inject.
    Hypothesis dps_strictly_decrease : opT.Trel_stable dps Tlt_mark.

    Lemma Tle_inject_mono : opT.Trel_monotone Tle_inject.
    Proof.
      unfold Tle_inject; intros f l1 l2 H; simpl; apply Tle_mono;
      induction H; [ left | right ]; assumption.
    Qed.

    Lemma R_stable_list : forall l1 l2,
      one_step_list (EqtT.one_step R_rules) l1 l2 ->
      one_step_list Tle (map inject_term l1) (map inject_term l2).
    Proof.
      intros l1 l2 H; induction H; [ left | right; assumption ];
      apply opT.stable_monotone_R_term with (O:=Tle_inject) in H;
      try assumption; apply Tle_inject_mono.
    Qed.

    Lemma rtc_R_step : forall t f l1 l2, Tlt_mark t (T.Term f l1) ->
      refl_trans_clos (one_step_list (EqtT.one_step R_rules)) l1 l2 ->
      Tlt_mark t (T.Term f l2).
    Proof.
      intros t f l1 l H H0;
      destruct H0; [ assumption |];
      induction H0; [| apply IHtrans_clos ];
      apply Tlt_Tle_compat with (mark_term (inject_term (T.Term f x)));
      try assumption; simpl; apply Tle_mono; apply R_stable_list;
      assumption.
    Qed.

    Lemma wf_Rcdp : well_founded (sdp.Rcdp R_rules dps).
    Proof.
      apply wf_incl with Tlt_mark;
      [| unfold Tlt_mark; apply Inverse_Image.wf_inverse_image; assumption ];
      intros x y H; inversion H; inversion H1; subst;
      apply rtc_R_step with l2; [| assumption ];
      rewrite <- H4; apply dps_strictly_decrease;
      assumption.
    Qed.

    Variable P_rest : T.term -> Prop.
    Let Rcdp_rest d := rest P_rest (sdp.Rcdp R_rules d).

    Lemma wf_Rcdp_rest : well_founded (Rcdp_rest dps).
    Proof.
      apply wf_incl with (sdp.Rcdp R_rules dps);
      [ intros x y [H H0]; assumption | apply wf_Rcdp ].
    Qed.

    Variables dps_large dps_union : relation T.term.
    Hypothesis dps_large_decrease : opT.Trel_stable dps_large Tle_mark.
    Hypothesis dps_large_wf : well_founded (Rcdp_rest dps_large).
    Hypothesis dps_union_def : forall (t1 t2 : T.term),
      dps_union t1 t2 -> dps t1 t2 \/ dps_large t1 t2.

    Lemma wf_union_Rcdp_rest : well_founded (Rcdp_rest dps_union).
    Proof.
      intros t;
      apply well_founded_ind with (R:=Tlt_mark);
      [ unfold Tlt_mark; apply Inverse_Image.wf_inverse_image; assumption |];
      clear t.

      intros t; pattern t;
      apply well_founded_ind with (R:=Rcdp_rest dps_large);
      [ apply dps_large_wf |]; clear t.

      intros t IH2 IH1; constructor; intros s [H Hrest];
      destruct H as [f l1 l2 t Hl1_l2 Ht];
      inversion Ht; clear Ht; subst.

      destruct (dps_union_def _ _ H1).

      apply IH1; apply rtc_R_step with l2; [| assumption ];
      rewrite <- H; apply dps_strictly_decrease; assumption.

      apply IH2.

      split; [| assumption ];
      split with (l2:=l2); [ assumption |];
      rewrite <- H; constructor; assumption.

      intros x Hx; apply IH1;
      apply rtc_R_step with l2; [| assumption ];
      apply Tlt_Tle_compat
        with (mark_term (inject_term (T.apply_subst sigma t1)));
      [| rewrite <- H; apply dps_large_decrease ]; assumption.
    Qed.
  End S.
End MakeMarkedSDP.

Module MakeLEX (Eqt : equational_theory_spec.EqTh).

  Module M := Eqt.T.
  Module Import op := OrderingPair(Eqt).

  Section S.
    Variables Tle Tlt : relation M.term.
    Hypothesis Tlt_wf : well_founded Tlt.
    Hypothesis Tle_mono : Trel_monotone Tle.
    Hypothesis Tlt_mono : Trel_monotone Tlt.
    Hypothesis Tlt_Tle_compat : Trel_compat Tlt Tle.

    Variables R_rules : relation M.term.
    Hypothesis rules_decrease : Trel_stable R_rules Tlt.

    Lemma wf_R : well_founded (Eqt.one_step R_rules).
    Proof.
      apply wf_incl with Tlt; [| assumption ];
      intros x y H;
      apply stable_monotone_R_term with R_rules;
      assumption.
    Qed.

    Variables R_large R_union : relation M.term.
    Hypothesis rules_large_decrease : Trel_stable R_large Tle.
    Hypothesis rules_large_wf : well_founded (Eqt.one_step R_large).
    Hypothesis rules_union_def : forall (t1 t2 : M.term),
      R_union t1 t2 -> R_rules t1 t2 \/ R_large t1 t2.

    Lemma wf_union_R : well_founded (Eqt.one_step R_union).
    Proof.
      intros t;
      apply well_founded_ind with (R:=Tlt);
      [ apply Tlt_wf |]; clear t.

      intros t; pattern t;
      apply well_founded_ind with (R:=Eqt.one_step R_large);
      [ apply rules_large_wf |]; clear t.

      intros t H H0; constructor; intros s Hst.
      assert (Eqt.one_step R_rules s t \/ Eqt.one_step R_large s t).

      revert Hst; clear H H0; revert s t;
      set (P2 := fun s t => Eqt.one_step R_union s t ->
        Eqt.one_step R_rules s t \/ Eqt.one_step R_large s t);
      change (forall t1 t2, P2 t1 t2);
      apply M.term_rec7 with (Pl2 := fun l1 l2 =>
        one_step_list (Eqt.one_step R_union) l1 l2 ->
        one_step_list (Eqt.one_step R_rules) l1 l2 \/
        one_step_list (Eqt.one_step R_large) l1 l2);
      unfold P2 in *; clear P2.

      intros v t H; inversion H; subst;
      inversion H0; subst; rewrite H1;
      inversion H0; subst;
      apply rules_union_def in H5;
      destruct H5; [ left | right ];
      constructor; constructor; assumption.

      intros t v H; inversion H; subst;
      inversion H0; subst; rewrite H1;
      inversion H0; subst;
      apply rules_union_def in H5;
      destruct H5; [ left | right ];
      constructor; constructor; assumption.

      intros f1 f2 l1 l2 H H0;
      inversion H0; subst;
      [ inversion H1; subst;
        apply rules_union_def in H4;
        destruct H4; [ left | right ];
        constructor; constructor; assumption
      | apply H in H2; destruct H2; [ left | right ];
        apply Eqt.in_context; assumption ].

      induction l1; intros l2 H H0;
      inversion H0; subst.

      apply H in H4; try (left; reflexivity);
      destruct H4; [ left | right ];
      constructor; assumption.

      apply IHl1 in H4;
      [ destruct H4; [ left | right ]
      | intros; apply H ];
      try right; assumption.

      destruct H1.

      apply H0; apply stable_monotone_R_term with R_rules;
      assumption.

      apply H in H1; [ assumption |]; intros; apply H0;
      apply Tlt_Tle_compat with s; [ assumption |];
      apply stable_monotone_R_term with R_large;
      assumption.
    Qed.
  End S.
End MakeLEX.
