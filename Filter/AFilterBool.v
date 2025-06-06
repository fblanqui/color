(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-05-13

arguments filtering with no projection
*)

Set Implicit Arguments.

From CoLoR Require Import ATrs VecFilter VecUtil LogicUtil RelUtil SN NatUtil
     ARelation ACompat.
From Stdlib Require Import List.

Section S.

  Variable Sig : Signature.

(***********************************************************************)
(** filtering function *)

  Variable pi : forall f, bools (@arity Sig f).

(***********************************************************************)
(** filtered signature *)

  Definition filter_arity f := Vtrue (pi f).

  Definition filter_sig := mkSignature filter_arity (@beq_symb_ok Sig).
  Notation Sig' := filter_sig.

  Notation term' := (ATerm.term Sig'). Notation Fun' := (@Fun Sig').
  Notation term := (term Sig). Notation terms := (vector term).

  Notation context' := (context Sig'). Definition Cont' := (@Cont Sig').
  Notation context := (context Sig).

(***********************************************************************)
(** term filtering *)

  Fixpoint filter (t : term) : term' :=
    match t with
      | Var x => Var x
      | Fun f ts => Fun' f (Vfilter (pi f) (Vmap filter ts))
    end.

(***********************************************************************)
(** rule filtering *)

  Notation rule' := (rule Sig'). Notation rules' := (list rule').
  Notation rule := (rule Sig). Notation rules := (list rule).

  Definition filter_rule a := mkRule (filter (lhs a)) (filter (rhs a)).

  Notation filter_rules := (List.map filter_rule).

(***********************************************************************)
(** properties wrt substitutions *)

  Definition filter_subs s (x : variable) := filter (s x).

  Lemma filter_sub : forall s t,
    filter (sub s t) = sub (filter_subs s) (filter t).

  Proof.
    intro. apply term_ind_forall with
    (P := fun t => filter (sub s t) = sub (filter_subs s) (filter t)); intros.
    refl. simpl.
    apply args_eq. rewrite <- !Vmap_filter, !Vmap_map.
    apply Vmap_eq. eapply Vforall_incl with (v2 := v). intros.
    eapply Vfilter_in. apply H0. hyp.
  Qed.

(***********************************************************************)
(** filter ordering *)

  Section filter_ordering.

    Variable succ : relation term'.

    Definition filter_ord : relation term :=
      fun t u => succ (filter t) (filter u).

    Notation fsucc := filter_ord.

(***********************************************************************)
(** transitivity *)

    Lemma filter_trans : transitive succ -> transitive fsucc.

    Proof.
      intro. unfold transitive, filter_ord. intros. eapply H. apply H0. hyp.
    Qed.

(***********************************************************************)
(** well-foundedness *)

    Lemma WF_filter : WF succ -> WF fsucc.

    Proof. intro. unfold filter_ord. apply (WF_inverse filter H). Qed.

(***********************************************************************)
(** stability by substitution *)

    Lemma filter_subs_closed :
      substitution_closed succ -> substitution_closed fsucc.

    Proof.
      unfold substitution_closed. intros. unfold filter_ord.
      rewrite !filter_sub. apply H. hyp.
    Qed.

(***********************************************************************)
(** compatibility *)

    Lemma filter_comp : forall R : rules,
      compat succ (filter_rules R) -> compat fsucc R.

    Proof.
      unfold compat. intros. unfold filter_ord. apply H.
      change (In (filter_rule (mkRule l r)) (filter_rules R)).
      apply in_map. hyp.
    Qed.

(***********************************************************************)
(** properties wrt contexts *)

    Section filter_cont.

      Variables (f : Sig) (i j : nat) (e : i + S j = arity f)
        (v1 : terms i) (c : context) (v2 : terms j) (t : term).

      Let bs := Vbreak (n1:=i) (n2:=S j) (Vcast (pi f) (sym_eq e)).
      Let v1' := Vfilter (fst bs) (Vmap filter v1).
      Let t' := filter (fill c t).
      Let v2' := Vfilter (Vtail (snd bs)) (Vmap filter v2).
      Let h := trans_eq (Vtrue_break (n1:=i) (n2:=S j)
        (Vcast (pi f) (sym_eq e))) (Vtrue_cast (pi f) (sym_eq e)).

      Section filter_cont_true.

        Variable H : Vhead (snd bs) = true.

        Definition e_true := trans_eq (plus_reg_l_inv (Vtrue (fst bs))
          (Vtrue_Sn_true (snd bs) H)) h.

        Lemma filter_cont_true : filter (fill (Cont f e v1 c v2) t)
          = fill (Cont' f e_true v1' Hole v2') t'.

        Proof.
          simpl. rewrite Vmap_cast, Vmap_app. simpl.
          rewrite Vfilter_cast, Vfilter_app, Vcast_cast. fold bs t' v1'.
          assert (Vfilter (snd bs) (Vcons t' (Vmap filter v2))
            = Vcast (Vcons t' v2') (Vtrue_Sn_true (snd bs) H)).
          rewrite (Vfilter_head_true t' (Vmap filter v2) H). refl.
          rewrite H0, Vapp_rcast, Vcast_cast. refl.
        Qed.

      End filter_cont_true.

      Section filter_cont_false.

        Variable H : Vhead (snd bs) = false.

        Definition e_false := trans_eq (plus_reg_l_inv (Vtrue (fst bs))
          (Vtrue_Sn_false (snd bs) H)) h.

        Lemma filter_cont_false : filter (fill (Cont f e v1 c v2) t)
          = Fun' f (Vcast (Vapp v1' v2') e_false).

        Proof.
          simpl. rewrite Vmap_cast, Vmap_app. simpl.
          rewrite Vfilter_cast, Vfilter_app, Vcast_cast. fold bs t' v1'.
          assert (Vfilter (snd bs) (Vcons t' (Vmap filter v2))
            = Vcast v2' (Vtrue_Sn_false (snd bs) H)).
          rewrite (Vfilter_head_false t' (Vmap filter v2) H). refl.
          rewrite H0, Vapp_rcast, Vcast_cast. refl.
        Qed.

      End filter_cont_false.

    End filter_cont.

    Arguments filter_cont_true [f i j] _ _ _ _ _ _.
    Arguments filter_cont_false [f i j] _ _ _ _ _ _.

(***********************************************************************)
(** stability wrt contexts *)

    Lemma filter_cont_closed :
      reflexive succ -> context_closed succ -> context_closed fsucc.

    Proof.
      intros Hrefl H. unfold context_closed, filter_ord. induction c; intros.
      simpl. hyp.
      set (bs := Vbreak (n1:=i) (n2:=S j) (Vcast (pi f) (sym_eq e))).
      case_eq (Vhead (snd bs)); intro H1.
      rewrite (filter_cont_true e t c t0 t1 H1).
      rewrite (filter_cont_true e t c t0 t2 H1). apply H. apply IHc. hyp.
      rewrite (filter_cont_false e t c t0 t1 H1).
      rewrite (filter_cont_false e t c t0 t2 H1). apply Hrefl.
    Qed.

  End filter_ordering.

(***********************************************************************)
(** monotony wrt inclusion *)

  Lemma incl_filter : forall R S, R << S -> filter_ord R << filter_ord S.

  Proof. intros. unfold inclusion, filter_ord. intros. apply H. exact H0. Qed.

(***********************************************************************)
(** weak stability wrt contexts *)

  Section weak_cont_closed.

    Variable succ : relation term'.

    Notation fsucc := (filter_ord succ).
    Notation succ_eq := (clos_refl succ).
    Notation fsucc_eq := (filter_ord succ_eq).

    Lemma filter_ord_rc : reflexive fsucc_eq.

    Proof. unfold reflexive, filter_ord, clos_refl, union. auto. Qed.

    Lemma rc_filter_ord : inclusion (clos_refl fsucc) fsucc_eq.

    Proof.
      unfold inclusion, clos_refl, union, filter_ord.
      intros. decomp H. subst y. auto. auto.
    Qed.

    Lemma filter_weak_cont_closed :
      weak_context_closed succ succ_eq -> weak_context_closed fsucc fsucc_eq.

    Proof.
      intro. unfold weak_context_closed. intros.
      assert (clos_refl fsucc t1 t2). unfold clos_refl, union. auto.
      ded (rc_filter_ord H1).
      assert (context_closed fsucc_eq). apply filter_cont_closed. apply rc_refl.
      apply rc_context_closed. hyp. apply H3. hyp.
    Qed.

(***********************************************************************)
(** reduction ordering *)

    Lemma filter_weak_red_ord : weak_reduction_ordering succ succ_eq
      -> weak_reduction_ordering fsucc fsucc_eq.

    Proof.
      intro. destruct H as [Hwf (Hsubs,Hcont)]. split. apply WF_filter. hyp.
      split. apply filter_subs_closed. hyp.
      apply filter_weak_cont_closed. hyp.
    Qed.

  End weak_cont_closed.

(***********************************************************************)
(** rewriting *)

  Section red.

    Variable R : rules.
    Notation R' := (filter_rules R).

    Lemma red_incl_filter_red_rc : red R << filter_ord (red R' %).

    Proof.
      unfold inclusion, filter_ord. intros. redtac. subst x. subst y.
      elim c. simpl. right. rewrite !filter_sub. apply red_rule_top.
      change (In (filter_rule (mkRule l r)) R'). apply in_map. hyp.
      intros. set (bs := Vbreak (n1:=i) (n2:=S j) (Vcast (pi f) (sym_eq e))).
      case_eq (Vhead (snd bs)); intro H0.
      rewrite (filter_cont_true f e t c0 t0 (sub s l) H0).
      rewrite (filter_cont_true f e t c0 t0 (sub s r) H0). fold bs. destruct H.
      left. simpl fill. rewrite H. refl. right. apply red_fill. hyp.
      left. rewrite (filter_cont_false f e t c0 t0 (sub s l) H0).
      rewrite (filter_cont_false f e t c0 t0 (sub s r) H0). refl.
    Qed.

    Lemma red_rtc_incl_filter_red_rtc : red R # << filter_ord (red R' #).

    Proof.
      unfold inclusion. induction 1.
      apply incl_filter with (red R' %). apply rc_incl_rtc.
      apply red_incl_filter_red_rc. exact H.
      unfold filter_ord. apply rt_refl.
      unfold filter_ord. apply rt_trans with (filter y).
      apply IHclos_refl_trans1. apply IHclos_refl_trans2.
    Qed.

    Lemma hd_red_incl_filter_hd_red : hd_red R << filter_ord (hd_red R').

    Proof.
      unfold inclusion, filter_ord. intros. redtac. subst x. subst y.
      rewrite !filter_sub. apply hd_red_rule.
      change (In (filter_rule (mkRule l r)) R'). apply in_map. hyp.
    Qed.

  End red.

(***********************************************************************)
(** rewriting modulo *)

  Section red_mod.

    Variable E R : rules.
    Notation E' := (filter_rules E).
    Notation R' := (filter_rules R).

    Lemma hd_red_mod_filter : hd_red_mod E R << filter_ord (hd_red_mod E' R').

    Proof.
      unfold inclusion, filter_ord. intros. redtac. exists (filter t). split.
      apply red_rtc_incl_filter_red_rtc. exact H.
      subst t. subst y. rewrite !filter_sub. apply hd_red_rule.
      change (In (filter_rule (mkRule l r)) R'). apply in_map. hyp.
    Qed.

    Lemma WF_hd_red_mod_filter : WF (hd_red_mod E' R') -> WF (hd_red_mod E R).

    Proof.
      intro. eapply WF_incl. apply hd_red_mod_filter. apply WF_filter. hyp.
    Qed.

  End red_mod.

End S.

Arguments filter_sig [Sig] _.

(***********************************************************************)
(** tactics *)

Ltac filter p := hd_red_mod; apply WF_hd_red_mod_filter with (pi:=p).

(***********************************************************************)
(** signature functor *)

Module Type Filter.
  Parameter Sig : Signature.
  Parameter pi : forall f : Sig, bools (arity f).
End Filter.

Module Make (S : FSIG) (F : Filter with Definition Sig := S.Sig) <: FSIG.
  Definition Sig := filter_sig F.pi.
  Definition Fs := S.Fs.
  Definition Fs_ok := S.Fs_ok.
End Make.
