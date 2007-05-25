(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2004-12-22

dependancy pairs
*)

(* $Id: ADP.v,v 1.12 2007-05-25 10:00:00 blanqui Exp $ *)

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
Notation lhs := (@lhs Sig).

Variable R : rules.

(***********************************************************************)
(** definition of dependancy pairs *)

Require Export ACalls.

Fixpoint mkdp (S : rules) : rules :=
  match S with
    | nil => nil
    | a :: S' => map (mkRule (lhs a)) (calls R (rhs a)) ++ mkdp S'
  end.

Lemma mkdp_app : forall l1 l2, mkdp (l1 ++ l2) = mkdp l1 ++ mkdp l2.

Proof.
induction l1; simpl; intros. refl. rewrite app_ass. rewrite IHl1. refl.
Qed.

Lemma mkdp_elim : forall l t S,
  In (mkRule l t) (mkdp S) -> exists r, In (mkRule l r) S /\ In t (calls R r).

Proof.
induction S; simpl; intros. contradiction. destruct a. simpl in H.
deduce (in_app_or H). destruct H0. deduce (in_map_elim H0). do 2 destruct H1.
injection H2. intros. subst x. subst lhs. exists rhs. intuition.
deduce (IHS H0). destruct H1. exists x. intuition.
Qed.

Implicit Arguments mkdp_elim [l t S].

Definition dp := mkdp R.

Lemma dp_intro : forall l r t,
  In (mkRule l r) R -> In t (calls R r) -> In (mkRule l t) dp.

Proof.
intros. deduce (in_elim H). do 2 destruct H1. deduce (in_elim H0).
do 2 destruct H2.
unfold dp. rewrite H1. simpl. rewrite mkdp_app. simpl. rewrite H2.
rewrite map_app.
simpl. apply in_appr. apply in_appl. apply in_appr. apply in_eq.
Qed.

Lemma dp_elim : forall l t,
  In (mkRule l t) dp -> exists r, In (mkRule l r) R /\ In t (calls R r).

Proof.
intros. deduce (mkdp_elim H). exact H0.
Qed.

Implicit Arguments dp_elim [l t].

Lemma in_calls_hd_red_dp : forall l r t s,
  In (mkRule l r) R -> In t (calls R r) -> hd_red dp (app s l) (app s t).

Proof.
intros. unfold hd_red. exists l. exists t. exists s. split.
eapply dp_intro. apply H. assumption. auto.
Qed.

Lemma lhs_dp : incl (map lhs dp) (map lhs R).

Proof.
unfold incl. intros. deduce (in_map_elim H). do 2 destruct H0. subst a.
destruct x as [l r]. deduce (dp_elim H0). do 2 destruct H1.
change (In (lhs (mkRule l x)) (map lhs R)). apply in_map. exact H1.
Qed.

(***********************************************************************)
(** dependancy chains *)

Definition chain := int_red R # @ hd_red dp.

Lemma in_calls_chain : forall l r t s,
  In (mkRule l r) R -> In t (calls R r) -> chain (app s l) (app s t).

Proof.
intros. unfold chain, compose. exists (app s l). split. apply rt_refl.
eapply in_calls_hd_red_dp. apply H. assumption.
Qed.

Lemma gt_chain : forall f ts us v,
  terms_gt R ts us -> chain (Fun f us) v -> chain (Fun f ts) v.

Proof.
unfold chain, compose. intros. do 2 destruct H0. exists x. split.
apply rt_trans with (y := Fun f us). apply rt_step. apply Vgt_prod_fun.
exact H. exact H0. exact H1.
Qed.

(***********************************************************************)
(** assumptions on rules *)

Require Export ANotvar.

Definition no_lhs_variable R := forall l r, In (mkRule l r) R -> @notvar Sig l.

Variable hyp1 : no_lhs_variable R.

Variable hyp2 : rules_preserv_vars R.

Implicit Arguments hyp2 [l r].

(***********************************************************************)
(** dp preserves variables *)

Lemma dp_elim_vars : forall l t, In (mkRule l t) dp ->
  exists r, In (mkRule l r) R /\ In t (calls R r) /\ incl (vars t) (vars l).

Proof.
intros. deduce (dp_elim H). do 2 destruct H0. exists x. intuition.
apply incl_tran with (m := vars x). unfold incl. intros.
eapply subterm_eq_vars. eapply in_calls_subterm. apply H1. exact H2.
apply hyp2. exact H0.
Qed.

Implicit Arguments dp_elim_vars [l t].

Lemma dp_preserv_vars : rules_preserv_vars dp.

Proof.
unfold rules_preserv_vars. intros. deduce (dp_elim_vars H). destruct H0.
intuition.
Qed.

Require Export ARename.

Lemma dp_preserv_pw_disjoint_vars :
  pw_disjoint_vars (map lhs R) -> pw_disjoint_vars (map lhs dp).

Proof.
unfold pw_disjoint_vars, disjoint_vars. intros. eapply H.
apply lhs_dp. exact H0. apply lhs_dp. exact H1. apply H2. exact H3.
Qed.

(***********************************************************************)
(** fundamental dp theorem *)

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
assert (Hsnsx : forall x, In x (vars l) -> SNR (s x)). intros.
eapply sub_fun_sn with (f := f). rewrite H5 in H3. apply H3.
rewrite <- H7. assumption.
(* end assert *)
(* we decompose r into its caps and its aliens *)
subst u. assert (r = app (alien_sub r) (cap r)). apply sym_eq.
apply (alien_sub_cap R). rewrite H3. rewrite app_app.
apply no_call_app_sn. apply hyp1. apply calls_cap.
(* we prove that the alien substitution is SN *)
intros. deduce (vars_cap R H4).
case (le_lt_dec x (maxvar r)); intro; unfold comp, ACap.alien_sub.
(* x <= maxvar r *)
deduce (vars_cap_inf R H4 l0). deduce (hyp2 H2 _ H8).
rewrite fsub_inf. simpl. apply Hsnsx. assumption. assumption.
(* x > maxvar r *)
rewrite (fsub_nth (aliens (capa r)) l0 H6).
set (a := Vnth (aliens (capa r)) (lt_pm (k:=projS1 (capa r)) l0 H6)).
assert (Fun f ts = app s l). rewrite H5. rewrite H7. refl.
assert (In a (calls R r)). apply aliens_incl_calls. unfold a. apply Vnth_in.
deduce (in_calls H9). destruct H10 as [g]. destruct H10 as [vs]. destruct H10.
(* every call is SN *)
eapply calls_sn with (r := r). apply hyp1.
intros. apply Hsnsx. apply (hyp2 H2 _ H12).
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

Lemma WF_chain : WF chain -> WF (red R).

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

Lemma chain_hd_red_mod : chain << hd_red_mod R dp.

Proof.
unfold chain, hd_red_mod. comp. apply incl_rtc. apply int_red_incl_red.
Qed.

End S.

(***********************************************************************)
(** declaration of implicit arguments *)

Implicit Arguments dp_elim [Sig l t].
Implicit Arguments dp_elim_vars [Sig l t].

(***********************************************************************)
(** tactics *)

Ltac no_lhs_variable :=
  match goal with
    | |- no_lhs_variable ?R =>
      unfold no_lhs_variable; let T := elt_type R in
      let P := fresh in set (P := fun a : T => notvar (lhs a));
        let H := fresh in assert (H : lforall P R);
          [unfold P; simpl; intuition
            | let H0 := fresh in
              do 2 intro; intro H0; apply (lforall_in H H0)]
  end.

Ltac rules_preserv_vars :=
  match goal with
    | |- rules_preserv_vars ?R =>
      unfold rules_preserv_vars; let T := elt_type R in
        let P := fresh in
          set (P := fun a : T => incl (vars (rhs a)) (vars (lhs a)));
            let H := fresh in assert (H : lforall P R);
              [unfold P, incl; simpl; intuition
                | let H0 := fresh in
                  do 2 intro; intro H0; apply (lforall_in H H0)]
  end.