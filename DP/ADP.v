(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2004-12-22

dependancy pairs
************************************************************************)

(* $Id: ADP.v,v 1.4 2006-12-04 12:53:51 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.

Section S.

Require Export ASignature.

Variable Sig : Signature.

Require Export ATerm.

Notation term := (term Sig).
Notation terms := (vector term).

Require Export ATrs.

Notation rule := (rule Sig).
Notation rules := (list rule).

Variable R : rules.

(***********************************************************************)
(* dependancy pairs *)

Require Export ACalls.

Fixpoint mkdp (l : rules) : rules :=
  match l with
    | nil => nil
    | r :: l' => map (mkRule (lhs r)) (calls R (rhs r)) ++ mkdp l'
  end.

Lemma mkdp_app : forall l1 l2, mkdp (l1 ++ l2) = mkdp l1 ++ mkdp l2.

Proof.
induction l1; simpl; intros. refl. rewrite app_ass. rewrite IHl1. refl.
Qed.

Definition dp := mkdp R.

Lemma in_calls_dp : forall l r t,
  In (mkRule l r) R -> In t (calls R r) -> In (mkRule l t) dp.

Proof.
intros. deduce (in_elim H). do 2 destruct H1. deduce (in_elim H0). do 2 destruct H2.
unfold dp. rewrite H1. simpl. rewrite mkdp_app. simpl. rewrite H2. rewrite map_app.
simpl. apply in_appr. apply in_appl. apply in_appr. apply in_eq.
Qed.

Lemma in_calls_dpr : forall l r t s,
  In (mkRule l r) R -> In t (calls R r) -> hd_red dp (app s l) (app s t).

Proof.
intros. unfold hd_red. exists l. exists t. exists s. split.
eapply in_calls_dp. apply H. assumption. auto.
Qed.

(***********************************************************************)
(* dependancy chains *)

Definition chain := compose (clos_refl_trans (int_red R)) (hd_red dp).

Lemma in_calls_chain : forall l r t s,
  In (mkRule l r) R -> In t (calls R r) -> chain (app s l) (app s t).

Proof.
intros. unfold chain, compose. exists (app s l). split. apply rt_refl.
eapply in_calls_dpr. apply H. assumption.
Qed.

Lemma gt_chain : forall f ts us v,
  terms_gt R ts us -> chain (Fun f us) v -> chain (Fun f ts) v.

Proof.
unfold chain, compose. intros. do 2 destruct H0. exists x. split.
apply rt_trans with (y := Fun f us). apply rt_step. apply Vgt_prod_fun.
exact H. exact H0. exact H1.
Qed.

(***********************************************************************)
(* usual assumptions on rules *)

Require Export ANotvar.

Variable hyp1 : forall l r, In (mkRule l r) R -> notvar l.

Variable hyp2 : forall l r x,
  In (mkRule l r) R -> In x (varlist r) -> In x (varlist l).

Implicit Arguments hyp2 [l r x].

(***********************************************************************)
(* fundamental dp theorem *)

Require Export ACap.

Notation capa := (capa R).
Notation cap := (cap R).
Notation alien_sub := (alien_sub R).

Notation SNR := (SN (red R)).

Require Export ASN.

Lemma chain_fun : forall f, defined f R = true
  -> forall ts, SN chain (Fun f ts) -> Vforall SNR ts -> SNR (Fun f ts).

Proof.
cut (forall t, SN chain t -> forall f, defined f R = true
  -> forall ts, t = Fun f ts -> Vforall SNR ts -> SNR t).
intros. apply H with (t := Fun f ts) (f := f) (ts := ts); (assumption || refl).
(* induction on t with chain as well-founded ordering *)
intros t H. pattern t. elim H. clear t H. intros t H IH f H0 ts H1 Hsnts.
assert (SN (@terms_gt Sig R (arity f)) ts). unfold terms_gt.
apply Vforall_SN_gt_prod. assumption.
(* induction on ts with red as well-founded ordering (ts is SN) *)
generalize IH. rewrite H1. elim H2. clear IH ts H1 Hsnts H2.
intros ts H1 IH1 IH2.
assert (Hsnts : Vforall SNR ts). apply SN_gt_prod_forall. apply SN_intro.
assumption. clear H1.
assert (H1 : forall y, terms_gt R ts y -> SNR (Fun f y)). intros. apply IH1.
assumption. intros. eapply IH2. unfold transp. eapply gt_chain. apply H1.
apply H2. apply H3. apply H4. assumption. clear IH1.
(* we prove that every reduct of (Fun f ts) is SN *)
apply SN_intro. intros u H2. redtac. destruct c; simpl in H3, H4.
(* c = Hole *)
deduce (fun_eq_app H3). destruct H5.
(* lhs = Fun f us *)
destruct e as [ls]. rewrite H5 in H3. rewrite app_fun in H3. Funeqtac.
(* begin assert: the substitution s is SN *)
assert (Hsnsx : forall x, In x (varlist l) -> SNR (s x)). intros.
eapply sub_fun_sn with (f := f). rewrite H5 in H3. apply H3.
rewrite <- H7. assumption.
(* end assert *)
(* we decompose r into its caps and its aliens *)
subst u. assert (r = app (alien_sub r) (cap r)). apply sym_eq.
apply (alien_sub_cap R). rewrite H3. rewrite app_app.
apply no_call_app_sn. apply hyp1. apply calls_cap.
(* we prove that the alien substitution is SN *)
intros. deduce (varlist_cap R H4).
case (le_lt_dec x (maxvar r)); intro; unfold comp, ACap.alien_sub.
(* x <= maxvar r *)
deduce (varlist_cap_inf R H4 l0). deduce (hyp2 H2 H8).
rewrite fsub_inf. simpl. apply Hsnsx. assumption. assumption.
(* x > maxvar r *)
rewrite (fsub_nth (aliens (capa r)) l0 H6).
set (a := Vnth (aliens (capa r)) (lt_pm (k:=projS1 (capa r)) l0 H6)).
assert (Fun f ts = app s l). rewrite H5. rewrite H7. refl.
assert (In a (calls R r)). apply aliens_incl_calls. unfold a. apply Vin_nth.
deduce (in_calls H9). destruct H10 as [g]. destruct H10 as [vs]. destruct H10.
(* every call is SN *)
eapply calls_sn. apply hyp1.
intros. apply Hsnsx. eapply hyp2. apply H2. apply H12.
intros h ws H13 H14.
apply IH2 with (y := Fun h (Vmap (app s) ws)) (f := h) (ts := Vmap (app s) ws).
unfold transp. rewrite H8. rewrite <- app_fun. eapply in_calls_chain.
apply H2. assumption. eapply in_calls_defined. apply H13. refl. assumption.
assumption.
(* lhs = Var x *)
destruct e. absurd (l = Var x). eapply lhs_notvar. apply hyp1. apply H2.
assumption.
(* c <> Hole *)
Funeqtac. subst u. apply H1. rewrite H6. unfold terms_gt. apply Vgt_prod_cast.
apply Vgt_prod_app. apply Vgt_prod_cons. left. split.
eapply red_rule. assumption. refl.
Qed.

Lemma wf_chain : WF chain -> WF (red R).

Proof.
intro Hwf. unfold WF. apply term_ind_forall.
(* var *)
apply sn_var. apply hyp1.
(* fun *)
intro f. pattern (defined f R). apply bool_eq_ind; intro.
(* f defined *)
intros ts Hsnts. apply chain_fun. assumption. apply Hwf. assumption.
(* f undefined *)
apply sn_args_sn_fun; auto.
Qed.

End S.
