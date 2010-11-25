(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2009-09-09

non-collapsing arguments filtering with permutations
*)

Set Implicit Arguments.

Require Import LogicUtil ATrs ListUtil NatUtil VecUtil SN BoolUtil
  RelUtil ListRepeatFree VecFilterPerm ARelation ACompat NaryFunction.

Section S.

Variable Sig : Signature.

Section pi.

Variable pi : forall f : Sig, nat_lts (arity f).

(***********************************************************************)
(** Assumption: pi does not duplicate arguments.

This assumption is not really necessary but it makes the proof of weak
monotony simpler. Otherwise, we also need to assume that the ordering
is transitive. *)

Definition non_dup_val := forall f, repeat_free (map (@val (arity f)) (pi f)).

Variable hyp : non_dup_val.

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

Definition filters n (l : nat_lts n) (ts : terms n) :=
  Vfilter l (Vmap filter ts).

(***********************************************************************)
(** rule filtering *)

Notation rule := (ATrs.rule Sig). Notation rules := (list rule).
Notation rule' := (ATrs.rule Sig'). Notation rules' := (list rule').

Definition filter_rule a := mkRule (filter (lhs a)) (filter (rhs a)).

Notation filter_rules := (List.map filter_rule).

(***********************************************************************)
(** properties wrt substitutions *)

Definition filter_subs s (x : variable) := filter (s x).

Lemma filter_sub : forall s t,
  filter (sub s t) = sub (filter_subs s) (filter t).

Proof.
intro. apply term_ind_forall with (P := fun t =>
  filter (sub s t) = sub (filter_subs s) (filter t)); intros; simpl.
refl. apply args_eq. repeat rewrite Vfilter_map. repeat rewrite Vmap_map.
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
(** transitivity *)

Lemma filter_trans : transitive succ -> transitive fsucc.

Proof.
intro. unfold transitive, filter_ord. intros. eapply H. apply H0. hyp.
Qed.

(***********************************************************************)
(** well-foundedness *)

Lemma WF_filter : WF succ -> WF fsucc.

Proof.
intro. unfold filter_ord. apply (WF_inverse filter H).
Qed.

(***********************************************************************)
(** stability by substitution *)

Lemma filter_subs_closed :
  substitution_closed succ -> substitution_closed fsucc.

Proof.
unfold substitution_closed. intros. unfold filter_ord.
repeat rewrite filter_sub. apply H. hyp.
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
(** stability wrt contexts *)

Lemma filter_cont_closed :
  reflexive succ -> context_closed succ -> context_closed fsucc.

Proof.
repeat rewrite <- Vmonotone_context_closed.
unfold Vmonotone, Vmonotone_i, RelUtil.monotone.
intros hrefl hcc f i j e vi vj. unfold fsucc. simpl. intros t u.
set (t' := filter t). set (u' := filter u). intro h'.
repeat rewrite Vmap_cast. repeat rewrite Vmap_app. simpl. fold t' u'.
set (vi' := Vmap filter vi). set (vj' := Vmap filter vj).
set (vt := Vcast (Vapp vi' (Vcons t' vj')) e).
set (vu := Vcast (Vapp vi' (Vcons u' vj')) e).
case (In_dec eq_nat_dec i (map (@val (arity f)) (pi f))); intro Hi.

(*REMARK: sub-proof to be extracted since it is used both in
filter_cont_closed and in red_incl_filter_red_rc *)

(* i in (pi f) *)
destruct (in_map_elim Hi) as [x [hx vx]]. destruct (in_elim hx) as [l1 [l2 hf]].

assert (a: length l1+length(x::l2)=@arity Sig' f).
unfold arity, filter_sig, filter_arity. rewrite hf. rewrite length_app. refl.
rewrite (Vfilter_app_eq (v:=vt) a hf).
rewrite (Vfilter_app_eq (v:=vu) a hf). simpl.

(*REMOVE:assert (rf : repeat_free (map (@val (arity f)) (pi f))).
rewrite build_pi_ok. rewrite bpermut_ok in hyp. apply hyp.*)
ded (hyp f). unfold non_dup_val in H. rewrite hf in H. rewrite map_app in H.
simpl in H. destruct (repeat_free_app_cons H) as [h1 h2].
rewrite <- vx in h1. rewrite <- vx in h2.

assert (e1 : Vfilter l1 vt = Vfilter l1 vu). apply Vfilter_eq_notin.
intros hi h. ded (in_map (@val (arity f)) h). contradiction. rewrite e1.
assert (e2 : Vfilter l2 vt = Vfilter l2 vu). apply Vfilter_eq_notin.
intros hi h. ded (in_map (@val (arity f)) h). contradiction. rewrite e2.

apply hcc. unfold vt, vu. repeat rewrite Vnth_cast. repeat rewrite Vnth_app.
destruct (le_gt_dec i (val x)). 2: absurd_arith.
repeat (rewrite Vnth_cons_head; [idtac|rewrite vx;omega]). hyp.

(* i not in (pi f) *)
apply refl_intro. hyp. apply args_eq. unfold vt, vu.
apply Vfilter_eq_notin with (l:=pi f). intros hi h.
ded (in_map (@val (arity f)) h). contradiction.
Qed.

End filter_ordering.

(***********************************************************************)
(** monotony wrt inclusion *)

Lemma incl_filter : forall R S, R << S -> filter_ord R << filter_ord S.

Proof.
intros. unfold inclusion, filter_ord. intros. apply H. exact H0.
Qed.

(***********************************************************************)
(** weak stability wrt contexts *)

Section weak_cont_closed.

Variable succ : relation term'.
Notation fsucc := (filter_ord succ).

Notation succ_eq := (succ%).
Notation fsucc_eq := (filter_ord succ_eq).

Lemma filter_ord_rc : reflexive fsucc_eq.

Proof.
unfold reflexive, filter_ord, clos_refl, union. intuition.
Qed.

Lemma rc_filter_ord : fsucc% << fsucc_eq.

Proof.
unfold inclusion, clos_refl, filter_ord, union. intuition. subst. auto.
Qed.

Lemma filter_weak_cont_closed :
  weak_context_closed succ succ_eq -> weak_context_closed fsucc fsucc_eq.

Proof.
intro. unfold weak_context_closed. intros.
assert (clos_refl fsucc t1 t2). unfold clos_refl, union. auto.
ded (rc_filter_ord H1).
assert (context_closed fsucc_eq). apply filter_cont_closed.
apply rc_refl. apply rc_context_closed. hyp. apply H3. hyp.
Qed.

(***********************************************************************)
(** reduction ordering *)

Lemma filter_weak_red_ord : weak_reduction_ordering succ succ_eq ->
  weak_reduction_ordering fsucc fsucc_eq.

Proof.
intro. destruct H as [Hwf (Hsubs,Hcont)]. split. apply WF_filter. hyp.
split. apply filter_subs_closed. hyp.
apply filter_weak_cont_closed. hyp.
Qed.

End weak_cont_closed.

(***********************************************************************)
(** rewriting *)

Section red.

Variable R : rules. Notation R' := (filter_rules R).

Lemma red_incl_filter_red_rc : red R << filter_ord (red R'%).

Proof.
unfold inclusion, filter_ord. intros. redtac. subst x. subst y.
elim c; clear c.

(* Hole *)
simpl. right. repeat rewrite filter_sub. apply red_rule_top.
change (In (filter_rule (mkRule l r)) R'). apply in_map. hyp.

(* Cont *)
intros f i j e vi c.
set (t := filter (fill c (sub s l))). set (u := filter (fill c (sub s r))).
intros htu vj. simpl. repeat rewrite Vmap_cast. repeat rewrite Vmap_app. simpl.
fold t u. set (vi' := Vmap filter vi). set (vj' := Vmap filter vj).
destruct htu as [htu|htu]. rewrite htu. left. refl.
case (In_dec eq_nat_dec i (map (@val (arity f)) (pi f))); intro Hi.

(*REMARK: sub-proof to be extracted since it is used both in
filter_cont_closed and in red_incl_filter_red_rc *)

(* i in (pi f) *)
right. destruct (in_map_elim Hi) as [x [hx vx]].
destruct (in_elim hx) as [l1 [l2 hf]].
set (vt := Vcast (Vapp vi' (Vcons t vj')) e).
set (vu := Vcast (Vapp vi' (Vcons u vj')) e).

assert (a: length l1+length(x::l2)=@arity Sig' f).
unfold arity, filter_sig, filter_arity. rewrite hf. rewrite length_app. refl.
rewrite (Vfilter_app_eq a hf). rewrite (Vfilter_app_eq a hf). simpl.
set (v1 := Vfilter l1 vu). set (v2 := Vfilter l2 vu).
simpl in a. set (d := Cont (Sig:=Sig') f a v1 Hole v2).

(*REMOVE:assert (rf : repeat_free (map (@val (arity f)) (pi f))).
rewrite build_pi_ok. rewrite bpermut_ok in hyp. apply hyp.*)
ded (hyp f). unfold non_dup_val in H. rewrite hf in H. rewrite map_app in H.
simpl in H. destruct (repeat_free_app_cons H) as [h1 h2].
rewrite <- vx in h1. rewrite <- vx in h2.

assert (e1 : Vfilter l1 vt = Vfilter l1 vu). apply Vfilter_eq_notin.
intros hi h. ded (in_map (@val (arity f)) h). contradiction. rewrite e1.
assert (e2 : Vfilter l2 vt = Vfilter l2 vu). apply Vfilter_eq_notin.
intros hi h. ded (in_map (@val (arity f)) h). contradiction. rewrite e2.

unfold vt, vu. repeat rewrite Vnth_cast. repeat rewrite Vnth_app.
destruct (le_gt_dec i (val x)). 2: absurd_arith.
repeat (rewrite Vnth_cons_head; [idtac|omega]).
change (red R' (fill d t) (fill d u)). apply red_fill. hyp.

(* i not in (pi f) *)
left. apply args_eq. apply Vfilter_eq_notin with (l:=pi f). intros hi h.
ded (in_map (@val (arity f)) h). contradiction.
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
repeat rewrite filter_sub. apply hd_red_rule.
change (In (filter_rule (mkRule l r)) R'). apply in_map. hyp.
Qed.

End red.

(***********************************************************************)
(** rewriting modulo *)

Section red_mod.

Variable E R : rules.

Notation E' := (filter_rules E). Notation R' := (filter_rules R).

Lemma hd_red_mod_filter : hd_red_mod E R << filter_ord (hd_red_mod E' R').

Proof.
unfold inclusion, filter_ord. intros. redtac. exists (filter t). split.
apply red_rtc_incl_filter_red_rtc. exact H.
subst t. subst y. repeat rewrite filter_sub. apply hd_red_rule.
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
  forallb (bgt_nat n) l = true -> nat_lts n.

Proof.
induction l; simpl; intros. exact nil.
eapply cons. eapply mk_nat_lt.
rewrite andb_eq in H. destruct H. rewrite bgt_nat_ok in H. apply H.
apply IHl.
rewrite andb_eq in H. destruct H. hyp.
Defined.

Implicit Arguments build_nat_lts [n l].

Lemma build_nat_lts_ok : forall n l (h : forallb (bgt_nat n) l = true),
  map (@val n) (build_nat_lts h) = l.

Proof.
induction l; simpl; intros. refl. rewrite IHl. refl.
Qed.

Definition build_pi : forall f : Sig, nat_lts (arity f).

Proof.
intro f. eapply build_nat_lts. unfold bvalid in raw_pi_ok.
rewrite forallb_forall in raw_pi_ok. apply raw_pi_ok. apply Fs_ok.
Defined.

Lemma build_pi_ok : forall f, map (@val (arity f)) (build_pi f) = raw_pi f.

Proof.
intro. apply build_nat_lts_ok.
Qed.

Definition non_dup := forall f, repeat_free (raw_pi f).

Definition bnon_dup := forallb (fun f => brepeat_free beq_nat (raw_pi f)) Fs.

Lemma bnon_dup_ok : bnon_dup = true <-> non_dup.

Proof.
unfold bnon_dup, non_dup. apply forallb_ok_fintype. 2: apply Fs_ok.
intro. apply brepeat_free_ok. apply beq_nat_ok.
Qed.

Lemma non_dup_ok : non_dup <-> non_dup_val build_pi.

Proof.
unfold non_dup, non_dup_val. apply iff_forall.
intro f. rewrite build_pi_ok. refl.
Qed.

End build_pi.

End S.

Implicit Arguments filter_sig [Sig].
Implicit Arguments bvalid [Sig].
Implicit Arguments build_pi [Sig raw_pi Fs].
Implicit Arguments non_dup_ok [Sig raw_pi Fs].
Implicit Arguments bnon_dup_ok [Sig raw_pi Fs].
Implicit Arguments non_dup_val [Sig].

(***********************************************************************)
(** tactics *)

Implicit Arguments bnon_dup_ok [Sig raw_pi Fs].

Ltac non_dup Fs_ok := rewrite <- (bnon_dup_ok Fs_ok); check_eq.

Ltac non_dup_val Fs_ok := rewrite <- non_dup_ok; non_dup Fs_ok.

Ltac filter p p_ok :=
  hd_red_mod; apply WF_hd_red_mod_filter with (pi:=p);
    [apply p_ok | idtac].

(***********************************************************************)
(** signature functor *)

Module Type Filter.
  Parameter Sig : Signature.
  Parameter pi : forall f : Sig, nat_lts (arity f).
End Filter.

Module Make (S : SIG) (F : Filter with Definition Sig := S.Sig) <: SIG.
  Definition Sig := filter_sig F.pi.
  Definition Fs := S.Fs.
  Definition Fs_ok := S.Fs_ok.
End Make.
