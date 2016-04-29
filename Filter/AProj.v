(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-05-13

arguments filtering with projections only
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs VecUtil LogicUtil ListUtil SN ARelation RelUtil
     ACompat NatUtil.

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
    simpl. apply args_eq. rewrite !Vmap_map. apply Vmap_eq. hyp.
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
      rewrite !proj_sub. apply H. hyp.
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
      simpl. hyp. simpl. destruct (pi f) as [[k h]|].
      rewrite !Vnth_cast, !Vnth_app.
      case (le_gt_dec i k); intro. case (eq_nat_dec i k); intro.
      subst. rewrite !Vnth_cons_head; try omega. apply IHc. hyp.
      gen (Vnth_app_aux (S j) (Vnth_cast_aux e h) l).
      assert (k-i=S(k-i-1)). omega. rewrite H1. intro.
      rewrite !Vnth_cons. apply Hrefl. apply Hrefl.
      rewrite !Vmap_cast, !Vmap_app. simpl.
      set (d := Cont f e (Vmap proj t) Hole (Vmap proj t0)).
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
(** rewriting *)

  Section red.

    Variable R : rules. Notation R' := (proj_rules R).

    Lemma red_incl_proj_red_rc : red R << proj_ord (red R' %).

    Proof.
      unfold inclusion, proj_ord. intros. redtac. subst. elim c.
      (* Hole *)
      simpl. right. rewrite !proj_sub. apply red_rule_top.
      change (In (proj_rule (mkRule l r)) R'). apply in_map. hyp.
      (* Cont *)
      intros. simpl. case (pi f).
      (* Some *)
      intros [k h]. rewrite !Vnth_cast, !Vnth_app. case (le_gt_dec i k); intro.
      case (eq_nat_dec i k); intro. subst.
      repeat (rewrite Vnth_cons_head; [idtac|omega]). hyp.
      gen (Vnth_app_aux (S j) (Vnth_cast_aux e h) l0).
      assert (k-i=S(k-i-1)). omega. rewrite H0. intro. rewrite !Vnth_cons.
      left. refl. left. refl.
      (* None *)
      rewrite !Vmap_cast, !Vmap_app. simpl.
      destruct H. rewrite H. left. refl. right.
      set (d := Cont f e (Vmap proj t) Hole (Vmap proj t0)).
      set (t1 := proj (fill c0 (sub s l))). set (u := proj (fill c0 (sub s r))).
      change (red R' (fill d t1) (fill d u)). apply red_fill. hyp.
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
      rewrite !proj_sub. apply hd_red_rule.
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
      subst t. subst y. rewrite !proj_sub. apply hd_red_rule.
      change (In (proj_rule (mkRule l r)) R'). apply in_map. hyp.
    Qed.

    Lemma WF_hd_red_mod_proj : WF (hd_red_mod E' R') -> WF (hd_red_mod E R).

    Proof.
      intro. eapply WF_incl. apply hd_red_mod_proj. apply WF_proj. hyp.
    Qed.

  End red_mod.

End proj.

(***********************************************************************)
(** building a projection *)

Variable raw_pi : Sig -> option nat.

Definition valid := forall f k, raw_pi f = Some k -> k < arity f.

Section pi.

  Variable hyp : valid.

  Definition mk_proj (f : Sig) k := @exist _ (fun k => k < arity f) k.

  Arguments mk_proj [f k] _.

  Definition build_pi : forall f : Sig, option {k | k < arity f}.

  Proof.
    intro f. case_eq (raw_pi f).
    intros n H. exact (Some (mk_proj (hyp H))).
    intro H. exact None.
  Defined.

End pi.

Variable Fs : list Sig.
Variable Fs_ok : forall f : Sig, In f Fs.

Definition bvalid_symb f :=
  match raw_pi f with
    | Some k => bgt_nat (arity f) k
    | None => true
  end.

Definition bvalid := forallb bvalid_symb Fs.

Lemma bvalid_ok : bvalid = true <-> valid.

Proof.
unfold bvalid, valid. apply forallb_ok_fintype. 2: hyp.
intro f. unfold bvalid_symb. destruct (raw_pi f).
rewrite bgt_nat_ok. intuition. inversion H1. subst. auto.
intuition. discr.
Qed.

End S.

Arguments build_pi [Sig raw_pi] _ _.
Arguments valid [Sig] _.
Arguments bvalid [Sig] _ _.
Arguments bvalid_ok [Sig] _ [Fs] _.

(***********************************************************************)
(** tactics *)

Ltac proj p := hd_red_mod; apply WF_hd_red_mod_proj with (pi:=p).

Ltac valid Fs_ok :=
  match goal with
    | |- valid ?p => rewrite <- (@bvalid_ok _ p _ Fs_ok);
      (check_eq || fail 10 "invalid projection")
  end.
