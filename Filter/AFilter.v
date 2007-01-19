(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-05-13

arguments filtering
*)

(* $Id: AFilter.v,v 1.3 2007-01-19 17:22:39 blanqui Exp $ *)

Set Implicit Arguments.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).

(***********************************************************************)
(** filtering function *)

Require Export VecFilter.

Variable pi : forall f, bools (@arity Sig f).

(***********************************************************************)
(** associated signature *)

Definition arity' f := Vtrue (pi f).

Definition Sig' := mkSignature arity' (@eq_symb_dec Sig).

Notation term' := (ATerm.term Sig').
Notation terms' := (vector term').

Notation "'args' f" := (terms (arity f)) (at level 70).

Notation Fun' := (@Fun Sig').

(***********************************************************************)
(** term transformation *)

Fixpoint filter (t : term) : term' :=
  match t with
    | Var x => Var x
    | Fun f ts =>
      let fix filters n (ts : terms n) {struct ts} : terms' n :=
	match ts in vector _ n return terms' n with
	  | Vnil => Vnil
	  | Vcons t n2 ts2 => Vcons (filter t) (filters n2 ts2)
	end
	in Fun' f (Vfilter (pi f) (filters (arity f) ts))
  end.

Lemma filters_eq : forall n (ts : terms n),
  (fix filters n (ts : terms n) {struct ts} : terms' n :=
    match ts in vector _ n return terms' n with
      | Vnil => Vnil
      | Vcons t n2 ts2 => Vcons (filter t) (filters n2 ts2)
    end) n ts = Vmap filter ts.

Proof.
induction ts; intros; simpl. refl. apply (f_equal (@Vcons term' (filter a) n)).
apply IHts.
Qed.

Lemma filter_fun : forall f (ts : args f),
  filter (Fun f ts) = Fun' f (Vfilter (pi f) (Vmap filter ts)).

Proof.
intros. simpl. apply (f_equal (Fun' f)). rewrite filters_eq. refl.
Qed.

(*
Lemma filter_fun : forall f (ts : args f),
  filter (Fun f ts) = Fun' f (Vfilter_map filter (pi f) ts).

Proof.
intros. rewrite filter_fun_map. rewrite Vfilter_map_eq. refl.
Qed.
*)

(***********************************************************************)
(** context transformation *)

Require Export AContext.

Notation context := (context Sig).
Notation context' := (AContext.context Sig').

Definition Cont' := (@Cont Sig').

(***********************************************************************)
(** properties wrt substitutions *)

Require Export ASubstitution.

Definition filter_subs s (x : variable) := filter (s x).

Lemma filter_app : forall s t, filter (app s t) = app (filter_subs s) (filter t).

Proof.
intro. apply term_ind_forall with
(P := fun t => filter (app s t) = app (filter_subs s) (filter t)); intros. refl.
rewrite app_fun. repeat rewrite filter_fun. rewrite app_fun.
apply (f_equal (Fun' f)). repeat rewrite <- Vmap_filter. repeat rewrite Vmap_map.
apply Vmap_eq. eapply Vforall_incl with (v2 := v). intros.
eapply Vfilter_in. apply H0. assumption.
Qed.

(***********************************************************************)
(** extension to rules *)

Require Export ATrs.

Notation rule := (ATrs.rule Sig).
Notation rules := (list rule).

Notation rule' := (ATrs.rule Sig').
Notation rules' := (list rule').

Definition filter_rule rho := mkRule (filter (lhs rho)) (filter (rhs rho)).

Notation filter_rules := (List.map filter_rule).

(***********************************************************************)
(** filter ordering *)

Require Export ARelation.

Definition filter_ord (succ : relation term') t u := succ (filter t) (filter u).

Section filter_ordering.

Variable succ : relation term'.
Notation fsucc := (filter_ord succ).

(***********************************************************************)
(** transitivity *)

Lemma filter_trans : transitive succ -> transitive fsucc.

Proof.
intro. unfold transitive, filter_ord. intros. eapply H. apply H0. assumption.
Qed.

(***********************************************************************)
(** compatibility *)

Lemma filter_comp : forall R : rules,
  compatible succ (filter_rules R) -> compatible fsucc R.

Proof.
unfold compatible. intros. unfold filter_ord. apply H.
change (In (filter_rule (mkRule l r)) (filter_rules R)).
apply in_map. assumption.
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
unfold substitution_closed. intros. unfold filter_ord. repeat rewrite filter_app.
apply H. assumption.
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
Let h := trans_eq (Vtrue_break (n1:=i) (n2:=S j) (Vcast (pi f) (sym_eq e)))
  (Vtrue_cast (pi f) (sym_eq e)).

Section filter_cont_true.

Variable H : Vhead (snd bs) = true.

Let e' := trans_eq (plus_reg_l_inv (Vtrue (fst bs)) (Vtrue_Sn_true (snd bs) H)) h.

Lemma filter_cont_true :
  filter (fill (Cont f e v1 c v2) t) = fill (Cont' f e' v1' Hole v2') t'.

Proof.
simpl fill. rewrite filter_fun. rewrite Vmap_cast. rewrite Vmap_app. simpl.
rewrite Vfilter_cast. rewrite Vfilter_app. rewrite Vcast_cast. fold bs t' v1'.
assert (Vfilter (snd bs) (Vcons t' (Vmap filter v2))
  = Vcast (Vcons t' v2') (Vtrue_Sn_true (snd bs) H)).
rewrite (Vfilter_head_true t' (Vmap filter v2) H). refl. rewrite H0.
rewrite Vapp_rcast. rewrite Vcast_cast. refl.
Qed.

End filter_cont_true.

Section filter_cont_false.

Variable H : Vhead (snd bs) = false.

Let e' := trans_eq (plus_reg_l_inv (Vtrue (fst bs)) (Vtrue_Sn_false (snd bs) H)) h.

Lemma filter_cont_false :
  filter (fill (Cont f e v1 c v2) t) = Fun' f (Vcast (Vapp v1' v2') e').

Proof.
simpl fill. rewrite filter_fun. rewrite Vmap_cast. rewrite Vmap_app. simpl.
rewrite Vfilter_cast. rewrite Vfilter_app. rewrite Vcast_cast. fold bs t' v1'.
assert (Vfilter (snd bs) (Vcons t' (Vmap filter v2))
  = Vcast v2' (Vtrue_Sn_false (snd bs) H)).
rewrite (Vfilter_head_false t' (Vmap filter v2) H). refl. rewrite H0.
rewrite Vapp_rcast. rewrite Vcast_cast. refl.
Qed.

End filter_cont_false.

End filter_cont.

Implicit Arguments filter_cont_true [f i j].
Implicit Arguments filter_cont_false [f i j].

(***********************************************************************)
(** stability wrt contexts *)

Lemma filter_cont_closed :
  reflexive succ -> context_closed succ -> context_closed fsucc.

Proof.
intros Hrefl H. unfold context_closed, filter_ord. induction c; intros.
simpl. assumption. set (bs := Vbreak (n1:=i) (n2:=S j) (Vcast (pi f) (sym_eq e))).
booltac (Vhead (snd bs)). rewrite (filter_cont_true e v c v0 t1 H2).
rewrite (filter_cont_true e v c v0 t2 H2). apply H. apply IHc. assumption.
rewrite (filter_cont_false e v c v0 t1 H2).
rewrite (filter_cont_false e v c v0 t2 H2). apply Hrefl.
Qed.

End filter_ordering.

(***********************************************************************)
(** weak stability wrt contexts *)

Section weak_cont_closed.

Variable succ : relation term'.
Notation fsucc := (filter_ord succ).
Notation succ_eq := (clos_refl succ).
Notation fsucc_eq := (filter_ord succ_eq).

Lemma filter_ord_rc : reflexive fsucc_eq.

Proof.
unfold reflexive, filter_ord, clos_refl. auto.
Qed.

Lemma rc_filter_ord : inclusion (clos_refl fsucc) fsucc_eq.

Proof.
unfold inclusion, clos_refl, filter_ord. intros. decomp H. subst y. auto. auto.
Qed.

Lemma filter_weak_cont_closed :
  weak_context_closed succ succ_eq -> weak_context_closed fsucc fsucc_eq.

Proof.
intro. unfold weak_context_closed. intros.
assert (clos_refl fsucc t1 t2). unfold clos_refl. auto.
deduce (rc_filter_ord H1).
assert (context_closed fsucc_eq). apply filter_cont_closed. apply rc_refl.
apply rc_context_closed. assumption. apply H3. assumption.
Qed.

(***********************************************************************)
(** reduction ordering *)

Lemma filter_weak_red_ord : weak_reduction_ordering succ succ_eq
  -> weak_reduction_ordering fsucc fsucc_eq.

Proof.
intro. destruct H as [Hwf (Hsubs,Hcont)]. split. apply WF_filter. assumption.
split. apply filter_subs_closed. assumption.
apply filter_weak_cont_closed. assumption.
Qed.

End weak_cont_closed.

End S.
