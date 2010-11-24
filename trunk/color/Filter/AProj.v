(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-05-13

arguments filtering with projections only
*)

Set Implicit Arguments.

Require Import ATrs VecUtil LogicUtil ListUtil SN ARelation RelUtil ACompat
  NatUtil.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (list rule).

(***********************************************************************)
(** projection function *)

Section proj.

  Variable pi : forall f : Sig, option {k | k < arity f}.

  Fixpoint proj t :=
    match t with
      | Var _ => t
      | Fun f ts =>
        match pi f with
          | None => Fun f (Vmap proj ts)
          | Some o => let (_, h) := o in proj (Vnth ts h)
        end
    end.

  Definition proj_rule a := mkRule (proj (lhs a)) (proj (rhs a)).

  Definition proj_rules := (map proj_rule).

(***********************************************************************)
(** properties wrt substitutions *)

  Definition psub s (x : variable) := proj (s x).

  Lemma proj_sub : forall s t,
    proj (sub s t) = sub (psub s) (proj t).

  Proof.
    intro. apply term_ind_forall; intros. refl. simpl. case (pi f).
    intros [k h]. rewrite Vnth_map. apply Vforall_nth. hyp.
    simpl. apply args_eq. repeat rewrite Vmap_map. apply Vmap_eq. hyp.
  Qed.

(***********************************************************************)
(** projection ordering *)

  Section proj_ordering.

    Variable succ : relation term.

    Definition proj_ord : relation term := fun t u => succ (proj t) (proj u).

    Notation psucc := proj_ord.

(***********************************************************************)
(** transitivity *)

    Lemma proj_trans : transitive succ -> transitive psucc.

    Proof.
      intro. unfold transitive, proj_ord. intros. eapply H. apply H0. hyp.
    Qed.

(***********************************************************************)
(** well-foundedness *)

    Lemma WF_proj : WF succ -> WF psucc.

    Proof.
      intro. unfold proj_ord. apply (WF_inverse proj H).
    Qed.

(***********************************************************************)
(** stability by substitution *)

    Lemma proj_subs_closed :
      substitution_closed succ -> substitution_closed psucc.

    Proof.
      unfold substitution_closed. intros. unfold proj_ord.
      repeat rewrite proj_sub. apply H. hyp.
    Qed.

(***********************************************************************)
(** compatibility *)

    Lemma proj_comp : forall R : rules,
      compat succ (proj_rules R) -> compat psucc R.

    Proof.
      unfold compat. intros. unfold proj_ord. apply H.
      change (In (proj_rule (mkRule l r)) (proj_rules R)).
      apply in_map. hyp.
    Qed.

(***********************************************************************)
(** stability wrt contexts *)

    Lemma proj_cont_closed :
      reflexive succ -> context_closed succ -> context_closed psucc.

    Proof.
      intros Hrefl H. unfold context_closed, proj_ord. induction c; intros.
      simpl. hyp. simpl. case_eq (pi f). destruct s as [k h].
      repeat rewrite Vnth_cast. repeat rewrite Vnth_app.
      case (le_gt_dec i k); intro. case (eq_nat_dec i k); intro.
      subst. repeat rewrite Vnth_cons_head; try omega. apply IHc. hyp.
      generalize (Vnth_app_aux (S j) (Vnth_cast_aux e h) l).
      assert (k-i=S(k-i-1)). omega. rewrite H2. intro.
      repeat rewrite Vnth_cons. apply Hrefl. apply Hrefl.
      repeat rewrite Vmap_cast. repeat rewrite Vmap_app. simpl.
      set (d := Cont f e (Vmap proj v) Hole (Vmap proj v0)).
      change (succ (fill d (proj (fill c t1))) (fill d (proj (fill c t2)))).
      apply H. apply IHc. hyp.
    Qed.

  End proj_ordering.

(***********************************************************************)
(** monotony wrt inclusion *)

  Lemma incl_proj : forall R S, R << S -> proj_ord R << proj_ord S.

  Proof.
    intros. unfold inclusion, proj_ord. intros. apply H. exact H0.
  Qed.

(***********************************************************************)
(** weak stability wrt contexts *)

  Section weak_cont_closed.

    Variable succ : relation term.
    Notation psucc := (proj_ord succ).

    Notation succ_eq := (clos_refl succ).
    Notation psucc_eq := (proj_ord succ_eq).

    Lemma proj_ord_rc : reflexive psucc_eq.

    Proof.
      unfold reflexive, proj_ord, clos_refl, union. auto.
    Qed.

    Lemma rc_proj_ord : inclusion (clos_refl psucc) psucc_eq.

    Proof.
      unfold inclusion, clos_refl, union, proj_ord.
      intros. decomp H. subst y. auto. auto.
    Qed.

    Lemma proj_weak_cont_closed :
      weak_context_closed succ succ_eq -> weak_context_closed psucc psucc_eq.

    Proof.
      intro. unfold weak_context_closed. intros.
      assert (clos_refl psucc t1 t2). unfold clos_refl, union. auto.
      ded (rc_proj_ord H1).
      assert (context_closed psucc_eq). apply proj_cont_closed. apply rc_refl.
      apply rc_context_closed. hyp. apply H3. hyp.
    Qed.

(***********************************************************************)
(** reduction ordering *)

    Lemma proj_weak_red_ord : weak_reduction_ordering succ succ_eq
      -> weak_reduction_ordering psucc psucc_eq.

    Proof.
      intro. destruct H as [Hwf (Hsubs,Hcont)]. split. apply WF_proj. hyp.
      split. apply proj_subs_closed. hyp.
      apply proj_weak_cont_closed. hyp.
    Qed.

  End weak_cont_closed.

(***********************************************************************)
(** rewriting *)

  Section red.

    Variable R : rules. Notation R' := (proj_rules R).

    Lemma red_incl_proj_red_rc : red R << proj_ord (red R' %).

    Proof.
      unfold inclusion, proj_ord. intros. redtac. subst. elim c.
      (* Hole *)
      simpl. right. repeat rewrite proj_sub. apply red_rule_top.
      change (In (proj_rule (mkRule l r)) R'). apply in_map. hyp.
      (* Cont *)
      intros. simpl. case (pi f).
      (* Some *)
      intros [k h]. repeat rewrite Vnth_cast.
      repeat rewrite Vnth_app. case (le_gt_dec i k); intro.
      case (eq_nat_dec i k); intro. subst.
      repeat (rewrite Vnth_cons_head; [idtac|omega]). hyp.
      generalize (Vnth_app_aux (S j) (Vnth_cast_aux e h) l0).
      assert (k-i=S(k-i-1)). omega. rewrite H0. intro. repeat rewrite Vnth_cons.
      left. refl. left. refl.
      (* None *)
      repeat rewrite Vmap_cast. repeat rewrite Vmap_app. simpl.
      destruct H. rewrite H. left. refl. right.
      set (d := Cont f e (Vmap proj v) Hole (Vmap proj v0)).
      set (t := proj (fill c0 (sub s l))). set (u := proj (fill c0 (sub s r))).
      change (red R' (fill d t) (fill d u)). apply red_fill. hyp.
    Qed.

    Lemma red_rtc_incl_proj_red_rtc : red R # << proj_ord (red R' #).

    Proof.
      unfold inclusion. induction 1.
      apply incl_proj with (red R' %). apply rc_incl_rtc.
      apply red_incl_proj_red_rc. exact H.
      unfold proj_ord. apply rt_refl.
      unfold proj_ord. apply rt_trans with (proj y).
      apply IHclos_refl_trans1. apply IHclos_refl_trans2.
    Qed.

    Lemma hd_red_incl_proj_hd_red : hd_red R << proj_ord (hd_red R').

    Proof.
      unfold inclusion, proj_ord. intros. redtac. subst x. subst y.
      repeat rewrite proj_sub. apply hd_red_rule.
      change (In (proj_rule (mkRule l r)) R'). apply in_map. hyp.
    Qed.

  End red.

(***********************************************************************)
(** rewriting modulo *)

  Section red_mod.

    Variable E R : rules.

    Notation E' := (proj_rules E).
    Notation R' := (proj_rules R).

    Lemma hd_red_mod_proj : hd_red_mod E R << proj_ord (hd_red_mod E' R').

    Proof.
      unfold inclusion, proj_ord. intros. redtac. exists (proj t). split.
      apply red_rtc_incl_proj_red_rtc. exact H.
      subst t. subst y. repeat rewrite proj_sub. apply hd_red_rule.
      change (In (proj_rule (mkRule l r)) R'). apply in_map. hyp.
    Qed.

    Lemma WF_hd_red_mod_proj : WF (hd_red_mod E' R') -> WF (hd_red_mod E R).

    Proof.
      intro. eapply WF_incl. apply hd_red_mod_proj. apply WF_proj. hyp.
    Qed.

  End red_mod.

End proj.

(***********************************************************************)
(** tactics *)

Ltac proj p := hd_red_mod; apply WF_hd_red_mod_proj with (pi:=p).

(***********************************************************************)
(** building a projection *)

Variable proj : Sig -> option nat.

Definition valid := forall f k, proj f = Some k -> k < arity f.

Section pi.

  Variable hyp : valid.

  Definition mk_proj (f : Sig) k := exist (fun k => k < arity f) k.

  Implicit Arguments mk_proj [f k].

  Definition build_pi : forall f : Sig, option {k | k < arity f}.

  Proof.
    intro f. case_eq (proj f). exact (Some (mk_proj (hyp H))). exact None.
  Defined.

End pi.

Variable Fs : list Sig.
Variable Fs_ok : forall f : Sig, In f Fs.

Definition bvalid_proj f :=
  match proj f with
    | Some k => bgt_nat (arity f) k
    | None => true
  end.

Lemma bvalid_proj_ok : forall f, bvalid_proj f = true
  <-> forall k, proj f = Some k -> k < arity f.

Proof.
intro f. unfold bvalid_proj. case_eq (proj f). rewrite bgt_nat_ok. intuition.
inversion H1. omega. intuition. discr.
Qed.

Definition bvalid_ok : forallb bvalid_proj Fs = true <-> valid.

Proof.
apply forallb_ok_fintype. apply bvalid_proj_ok. hyp.
Qed.

End S.

Implicit Arguments build_pi [proj].
Implicit Arguments valid [Sig].

(***********************************************************************)
(** tactics *)

Ltac proj p := hd_red_mod; apply WF_hd_red_mod_proj with (pi:=p).

Ltac valid Sig Fs_ok := rewrite <- (@bvalid_ok Sig _ _ Fs_ok);
  (check_eq || fail "bad projection").