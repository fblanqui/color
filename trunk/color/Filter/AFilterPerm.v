(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-09-09

non-collapsing arguments filtering with permutations
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil ATrs ListUtil NatUtil VecUtil SN BoolUtil
  RelUtil ListNodup VecFilterPerm ARelation ACompat NaryFunction BoundNat.

Section S.

  Variable Sig : Signature.

  Section pi.

    Variable pi : forall f : Sig, list (N (arity f)).

(***********************************************************************)
(** Assumption: pi does not duplicate arguments.

This hyp is not really necessary but it makes the proof of weak
monotony simpler. Otherwise, we also need to assume that the ordering
is transitive. *)

    Definition non_dup := forall f, nodup (map N_val (pi f)).

    Variable hyp : non_dup.

(***********************************************************************)
(** filtered signature *)

    Definition filter_arity f := length (pi f).

    Definition filter_sig := mkSignature filter_arity (@beq_symb_ok Sig).

    Notation Sig' := filter_sig. Notation term' := (term Sig').
    Notation term := (term Sig). Notation terms := (vector term).

(***********************************************************************)
(** term filtering *)

    Fixpoint filter (t : term) : term' :=
      match t with
        | Var x => Var x
        | Fun f ts => @Fun Sig' f (Vfilter (pi f) (Vmap filter ts))
      end.

(***********************************************************************)
(** rule filtering *)

    Notation rule := (ATrs.rule Sig). Notation rules := (list rule).
    Notation rule' := (ATrs.rule Sig'). Notation rules' := (list rule').

    Definition filter_rule a := mkRule (filter (lhs a)) (filter (rhs a)).

    Notation filter_rules := (map filter_rule).

(***********************************************************************)
(** properties of term filtering wrt substitutions *)

    Definition filter_subs s (x : variable) := filter (s x).

    Lemma filter_sub : forall s t,
      filter (sub s t) = sub (filter_subs s) (filter t).

    Proof.
      intro. apply term_ind_forall with (P := fun t =>
      filter (sub s t) = sub (filter_subs s) (filter t)); intros; simpl.
      refl. apply args_eq. rewrite !Vfilter_map, !Vmap_map.
      apply Vmap_eq. eapply Vforall_incl with (v2 := v). intros.
      eapply Vin_filter_elim_in. apply H0. hyp.
    Qed.

(***********************************************************************)
(** filter ordering *)

    Section filter_ordering.

      Variable succ : relation term'.

      Definition filter_ord : relation term :=
        fun t u => succ (filter t) (filter u).

      Notation fsucc := filter_ord.

(***********************************************************************)
(** preservation of transitivity *)

      (*FIXME: define a meta-theorem*)
      Lemma filter_trans : transitive succ -> transitive fsucc.

      Proof.
        intro. unfold transitive, filter_ord. intros. eapply H. apply H0. hyp.
      Qed.

(***********************************************************************)
(** preservation of well-foundedness *)

      (*FIXME: define a meta-theorem*)
      Lemma WF_filter : WF succ -> WF fsucc.

      Proof. intro. unfold filter_ord. apply (WF_inverse filter H). Qed.

(***********************************************************************)
(** stability by substitution *)

      (*FIXME: define a meta-theorem*)
      Lemma filter_subs_closed :
        substitution_closed succ -> substitution_closed fsucc.

      Proof.
        unfold substitution_closed. intros. unfold filter_ord.
        rewrite !filter_sub. apply H. hyp.
      Qed.

(***********************************************************************)
(** compatibility *)

       (*FIXME: define a meta-theorem*)
      Lemma filter_comp : forall R : rules,
        compat succ (filter_rules R) -> compat fsucc R.

      Proof.
        unfold compat. intros. unfold filter_ord. apply H.
        change (In (filter_rule (mkRule l r)) (filter_rules R)).
        apply in_map. hyp.
      Qed.

(***********************************************************************)
(** weak monotony wrt contexts *)

      Lemma filter_weak_cont_closed :
        reflexive succ -> context_closed succ -> context_closed fsucc.

      Proof.
        rewrite <- !Vmonotone_context_closed.
        unfold Vmonotone, Vmonotone_i, RelUtil.monotone.
        intros hrefl hcc f i j e vi vj. unfold fsucc. simpl. intros t u.
        set (t' := filter t). set (u' := filter u). intro h'.
        rewrite !Vmap_cast, !Vmap_app. simpl. fold t' u'.
        set (vi' := Vmap filter vi). set (vj' := Vmap filter vj).
        set (vt := Vcast (Vapp vi' (Vcons t' vj')) e).
        set (vu := Vcast (Vapp vi' (Vcons u' vj')) e).
        case (In_dec eq_nat_dec i (map N_val (pi f))); intro Hi.

        (*REMARK: sub-proof to be extracted since it is used both in
           filter_cont_closed and in red_incl_filter_red_rc *)

        (* i in (pi f) *)
        destruct (in_map_elim Hi) as [x [hx vx]].
        destruct (in_elim hx) as [l1 [l2 hf]].

        assert (a: length l1+length(x::l2)=@arity Sig' f).
        unfold arity, filter_sig, filter_arity. rewrite hf, length_app. refl.
        rewrite (Vfilter_app_eq (v:=vt) a hf), (Vfilter_app_eq (v:=vu) a hf).
        simpl.

        ded (hyp f). unfold non_dup in H. rewrite hf, map_app in H.
        simpl in H. destruct (nodup_app_cons H) as [h1 h2].
        rewrite <- vx in h1. rewrite <- vx in h2.

        assert (e1 : Vfilter l1 vt = Vfilter l1 vu). apply Vfilter_eq_notin.
        intros hi h. ded (in_map N_val h). contr. rewrite e1.
        assert (e2 : Vfilter l2 vt = Vfilter l2 vu). apply Vfilter_eq_notin.
        intros hi h. ded (in_map N_val h). contr. rewrite e2.

        apply hcc. unfold vt, vu. rewrite !Vnth_cast, !Vnth_app.
        destruct (le_gt_dec i x). 2: omega.
        repeat (rewrite Vnth_cons_head; [idtac|rewrite vx;omega]). hyp.

        (* i not in (pi f) *)
        apply eq_incl_refl_rel. hyp. apply args_eq. unfold vt, vu.
        apply Vfilter_eq_notin with (l:=pi f). intros hi h.
        ded (in_map N_val h). contr.
      Qed.

(***********************************************************************)
(** strong monotony wrt contexts *)

      Definition permut := forall f i,
        i < arity f -> In i (map N_val (pi f)).

      Lemma filter_strong_cont_closed :
        permut -> context_closed succ -> context_closed fsucc.

      Proof.
        rewrite <- !Vmonotone_context_closed.
        unfold Vmonotone, Vmonotone_i, RelUtil.monotone.
        intros hp hcc f i j e vi vj. unfold fsucc. simpl. intros t u.
        set (t' := filter t). set (u' := filter u). intro h'.
        rewrite !Vmap_cast, !Vmap_app. simpl. fold t' u'.
        set (vi' := Vmap filter vi). set (vj' := Vmap filter vj).
        set (vt := Vcast (Vapp vi' (Vcons t' vj')) e).
        set (vu := Vcast (Vapp vi' (Vcons u' vj')) e).
        case (In_dec eq_nat_dec i (map N_val (pi f))); intro Hi.

        (*REMARK: sub-proof to be extracted since it is used both in
           filter_cont_closed and in red_incl_filter_red_rc *)

        (* i in (pi f) *)
        destruct (in_map_elim Hi) as [x [hx vx]].
        destruct (in_elim hx) as [l1 [l2 hf]].

        assert (a: length l1+length(x::l2)=@arity Sig' f).
        unfold arity, filter_sig, filter_arity. rewrite hf, length_app. refl.
        rewrite (Vfilter_app_eq (v:=vt) a hf), (Vfilter_app_eq (v:=vu) a hf).
        simpl.

        ded (hyp f). unfold non_dup in H. rewrite hf, map_app in H.
        simpl in H. destruct (nodup_app_cons H) as [h1 h2].
        rewrite <- vx in h1. rewrite <- vx in h2.

        assert (e1 : Vfilter l1 vt = Vfilter l1 vu). apply Vfilter_eq_notin.
        intros hi h. ded (in_map N_val h). contr. rewrite e1.
        assert (e2 : Vfilter l2 vt = Vfilter l2 vu). apply Vfilter_eq_notin.
        intros hi h. ded (in_map N_val h). contr. rewrite e2.

        apply hcc. unfold vt, vu. rewrite !Vnth_cast, !Vnth_app.
        destruct (le_gt_dec i x). 2: omega.
        repeat (rewrite Vnth_cons_head; [idtac|rewrite vx;omega]). hyp.

        (* i not in (pi f) *)
        assert (hi : i<arity f). omega. ded (hp f i hi). contr.
      Qed.

    End filter_ordering.

(***********************************************************************)
(** monotony wrt inclusion *)

    (*FIXME: define a meta-theorem*)
    Lemma incl_filter : forall R S, R << S -> filter_ord R << filter_ord S.

    Proof. intros. unfold inclusion, filter_ord. intros. apply H. exact H0. Qed.

(***********************************************************************)
(** rewriting *)

    Section red.

      Variable R : rules. Notation R' := (filter_rules R).

      (*FIXME: define a meta-theorems?*)
      Lemma red_incl_filter_red_rc : red R << filter_ord (red R'%).

      Proof.
        unfold inclusion, filter_ord. intros. redtac. subst x. subst y.
        elim c; clear c.
        (* Hole *)
        simpl. right. rewrite !filter_sub. apply red_rule_top.
        change (In (filter_rule (mkRule l r)) R'). apply in_map. hyp.
        (* Cont *)
        intros f i j e vi c.
        set (t := filter (fill c (sub s l))).
        set (u := filter (fill c (sub s r))).
        intros htu vj. simpl. rewrite !Vmap_cast, !Vmap_app. simpl.
        fold t u. set (vi' := Vmap filter vi). set (vj' := Vmap filter vj).
        destruct htu as [htu|htu]. rewrite htu. left. refl.
        case (In_dec eq_nat_dec i (map N_val (pi f))); intro Hi.

        (*REMARK: sub-proof to be extracted since it is used both in
           filter_cont_closed and in red_incl_filter_red_rc *)

        (* i in (pi f) *)
        right. destruct (in_map_elim Hi) as [x [hx vx]].
        destruct (in_elim hx) as [l1 [l2 hf]].
        set (vt := Vcast (Vapp vi' (Vcons t vj')) e).
        set (vu := Vcast (Vapp vi' (Vcons u vj')) e).

        assert (a: length l1+length(x::l2)=@arity Sig' f).
        unfold arity, filter_sig, filter_arity. rewrite hf, length_app. refl.
        rewrite (Vfilter_app_eq a hf), (Vfilter_app_eq a hf). simpl.
        set (v1 := Vfilter l1 vu). set (v2 := Vfilter l2 vu).
        simpl in a. set (d := Cont (Sig:=Sig') f a v1 Hole v2).

        ded (hyp f). unfold non_dup in H. rewrite hf, map_app in H.
        simpl in H. destruct (nodup_app_cons H) as [h1 h2].
        rewrite <- vx in h1. rewrite <- vx in h2.

        assert (e1 : Vfilter l1 vt = Vfilter l1 vu). apply Vfilter_eq_notin.
        intros hi h. ded (in_map N_val h). contr. rewrite e1.
        assert (e2 : Vfilter l2 vt = Vfilter l2 vu). apply Vfilter_eq_notin.
        intros hi h. ded (in_map N_val h). contr. rewrite e2.

        unfold vt, vu. rewrite !Vnth_cast, !Vnth_app.
        destruct (le_gt_dec i x). 2: omega.
        repeat (rewrite Vnth_cons_head; [idtac|omega]).
        change (red R' (fill d t) (fill d u)). apply red_fill. hyp.

        (* i not in (pi f) *)
        left. apply args_eq. apply Vfilter_eq_notin with (l:=pi f). intros hi h.
        ded (in_map N_val h). contr.
      Qed.

      Lemma red_rtc_incl_filter_red_rtc : red R # << filter_ord (red R' #).

      Proof.
        unfold inclusion. induction 1.
        apply incl_filter with (red R'%). apply rc_incl_rtc.
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

    (*FIXME: define meta-theorems*)
    Section red_mod.

      Variable E R : rules.

      Notation E' := (filter_rules E). Notation R' := (filter_rules R).

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

  End pi.

(***********************************************************************)
(** building a filtering function *)

  Section build_pi.

    Variable raw_pi : Sig -> list nat.

    Definition valid := forall f x, In x (raw_pi f) -> arity f > x.

    Variable Fs : list Sig.
    Variable Fs_ok : forall f : Sig, In f Fs.

    Definition bvalid :=
      forallb (fun f => forallb (bgt_nat (arity f)) (raw_pi f)) Fs.

    Lemma bvalid_ok : bvalid = true <-> valid.

    Proof.
      apply forallb_ok_fintype. 2: hyp. intro f. rewrite forallb_forall.
      intuition. rewrite <- bgt_nat_ok. auto. rewrite bgt_nat_ok. auto.
    Qed.

    Variable raw_pi_ok : bvalid = true.

    Definition build_nat_lts : forall n l,
      forallb (bgt_nat n) l = true -> list (N n).

    Proof.
      induction l; simpl; intros. exact nil.
      eapply cons. eapply N_.
      rewrite andb_eq in H. destruct H. rewrite bgt_nat_ok in H. apply H.
      apply IHl.
      rewrite andb_eq in H. destruct H. hyp.
    Defined.

    Arguments build_nat_lts [n l] _.

    Lemma build_nat_lts_ok : forall n l (h : forallb (bgt_nat n) l = true),
      map N_val (build_nat_lts h) = l.

    Proof. induction l; simpl; intros. refl. rewrite IHl. refl. Qed.

    Definition build_pi : forall f : Sig, list (N (arity f)).

    Proof.
      intro f. eapply build_nat_lts. unfold bvalid in raw_pi_ok.
      rewrite forallb_forall in raw_pi_ok. apply raw_pi_ok. apply Fs_ok.
    Defined.

    Lemma build_pi_ok : forall f, map N_val (build_pi f) = raw_pi f.

    Proof. intro. apply build_nat_lts_ok. Qed.

(***********************************************************************)
(** verifying arguments non-duplication *)

    Definition bnon_dup :=
      forallb (fun f => bnodup beq_nat (raw_pi f)) Fs.

    Lemma bnon_dup_ok : bnon_dup = true <-> non_dup build_pi.

    Proof.
      unfold bnon_dup, non_dup. apply forallb_ok_fintype. 2: apply Fs_ok.
      intro f. rewrite build_pi_ok. apply bnodup_ok. apply beq_nat_ok.
    Qed.

(***********************************************************************)
(** verify if all filters are permutations *)

    From CoLoR Require Import ListDec.

    Definition bpermut :=
      forallb (fun f =>
        bforall_lt (fun i => mem beq_nat i (raw_pi f)) (arity f)) Fs.

    Lemma bpermut_ok : bpermut = true <-> permut build_pi.

    Proof.
      unfold bpermut, permut. apply forallb_ok_fintype. 2: hyp.
      intro f. apply bforall_lt_ok. intro x. rewrite build_pi_ok.
      apply mem_ok. apply beq_nat_ok.
    Qed.

  End build_pi.

End S.

Arguments filter_sig [Sig] _.
Arguments bvalid [Sig] _ _.
Arguments build_pi [Sig raw_pi Fs] _ _ _.
Arguments bnon_dup_ok [Sig raw_pi Fs] _ _.
Arguments non_dup [Sig] _.
Arguments bpermut_ok [Sig raw_pi Fs] _ _.
Arguments permut [Sig] _.

(***********************************************************************)
(** tactics *)

Ltac non_dup :=
  match goal with
    | |- non_dup (build_pi _ _) => rewrite <- bnon_dup_ok; check_eq
    | |- non_dup ?pi => unfold pi; non_dup
  end || fail 10 "duplicating arguments filter".

Ltac permut :=
  match goal with
    | |- permut (build_pi _ _) => rewrite <- bpermut_ok; check_eq
    | |- permut ?pi => unfold pi; permut
  end || fail 10 "non-permutative arguments filter".

(*COQ: does not work... the recursive call on filter fails...
Ltac filter p :=
  match goal with
    | |- WF (hd_red_Mod _ _) => hd_red_mod; filter p
    | |- WF (hd_red_mod _ _) =>
      apply WF_hd_red_mod_filter with (pi:=p); [non_dup | idtac]
  end.*)

Ltac filter p :=
  hd_red_mod; apply WF_hd_red_mod_filter with (pi:=p); [non_dup | idtac].

Ltac prove_cc_succ tac :=
  apply filter_strong_cont_closed; [non_dup | permut | tac].

(***********************************************************************)
(** signature functor *)

Module Type Filter.
  Parameter Sig : Signature.
  Parameter pi : forall f : Sig, list (N (arity f)).
End Filter.

Module Make (S : FSIG) (F : Filter with Definition Sig := S.Sig) <: FSIG.
  Definition Sig := filter_sig F.pi.
  Definition Fs := S.Fs.
  Definition Fs_ok := S.Fs_ok.
End Make.
