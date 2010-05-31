(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2004-12-22, 2009-11-04 (Dershowitz' improvement)
- Joerg Endrullis, 2008-06-19 (extension to minimal chains)

dependancy pairs
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import ATrs.
Require Import ACalls.
Require Import AShift.
Require Import ACap.
Require Import ASN.
Require Import ListUtil.
Require Import RelUtil.
Require Import ListForall.
Require Import SN.
Require Import VecUtil.
Require Import VecOrd.
Require Import NatUtil.

Section S.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (list rule).
Notation lhs := (@lhs Sig).

Variable R : rules.

(***********************************************************************)
(** definition of dependancy pairs *)

Definition nbsubterm_of (t u : term) := negb (bsubterm u t).

Fixpoint mkdp (S : rules) : rules :=
  match S with
    | nil => nil
    | a :: S' => let (l,r) := a in
      map (mkRule l) (filter (nbsubterm_of l) (calls R r)) ++ mkdp S'
  end.

Lemma mkdp_app : forall l1 l2, mkdp (l1 ++ l2) = mkdp l1 ++ mkdp l2.

Proof.
induction l1; simpl; intros. refl. destruct a as [l r]. rewrite app_ass.
rewrite IHl1. refl.
Qed.

Lemma mkdp_elim : forall l t S, In (mkRule l t) (mkdp S) -> exists r,
  In (mkRule l r) S /\ In t (calls R r) /\ nbsubterm_of l t = true.

Proof.
induction S; simpl; intros. contradiction. destruct a.
rewrite in_app in H. destruct H. destruct (in_map_elim H). destruct H0.
injection H1. intros. subst x. subst lhs. clear H1.
rewrite filter_In in H0. destruct H0.
exists rhs. intuition. destruct (IHS H). destruct H0. destruct H1.
exists x. intuition.
Qed.

Implicit Arguments mkdp_elim [l t S].

Definition dp := mkdp R.

(***********************************************************************)
(** basic properties *)

Lemma dp_intro : forall l r t, In (mkRule l r) R -> In t (calls R r) ->
  nbsubterm_of l t = true -> In (mkRule l t) dp.

Proof.
intros. ded (in_elim H). do 2 destruct H2. ded (in_elim H0). do 2 destruct H3.
unfold dp. rewrite H2. rewrite mkdp_app. simpl. rewrite H3.
rewrite filter_app. rewrite map_app. simpl. rewrite H1.
apply in_appr. apply in_appl. apply in_appr. apply in_eq.
Qed.

Lemma dp_elim : forall l t, In (mkRule l t) dp -> exists r,
  In (mkRule l r) R /\ In t (calls R r) /\ nbsubterm_of l t = true.

Proof.
intros. apply mkdp_elim. hyp.
Qed.

Implicit Arguments dp_elim [l t].

Lemma in_calls_hd_red_dp : forall l r t s, In (mkRule l r) R ->
  In t (calls R r) -> nbsubterm_of l t = true -> hd_red dp (sub s l) (sub s t).

Proof.
intros. exists l. exists t. exists s. intuition.
eapply dp_intro. apply H. hyp. hyp.
Qed.

Lemma lhs_dp : incl (map lhs dp) (map lhs R).

Proof.
unfold incl. intros. ded (in_map_elim H). do 2 destruct H0. subst a.
destruct x as [l r]. ded (dp_elim H0). do 2 destruct H1.
change (In (lhs (mkRule l x)) (map lhs R)). apply in_map. exact H1.
Qed.

(*FIXME: to be finished

Lemma is_notvar_lhs_dp_aux :
  forall S, forallb (@is_notvar_lhs Sig) (mkdp S) = true.

Proof.
induction S; simpl; intros. refl. destruct a. simpl. rewrite forallb_app.
Qed.

Lemma is_notvar_lhs_dp : forallb (@is_notvar_lhs Sig) dp = true.

Proof.
unfold dp.
Qed.*)

(***********************************************************************)
(** dependancy chains *)

Definition chain := int_red R # @ hd_red dp.

Lemma in_calls_chain : forall l r t s, In (mkRule l r) R ->
  In t (calls R r) -> nbsubterm_of l t = true -> chain (sub s l) (sub s t).

Proof.
intros. unfold chain, compose. exists (sub s l). split. apply rt_refl.
eapply in_calls_hd_red_dp. apply H. hyp. hyp.
Qed.

Lemma gt_chain : forall f ts us v,
  terms_gt R ts us -> chain (Fun f us) v -> chain (Fun f ts) v.

Proof.
unfold chain, compose. intros. do 2 destruct H0. exists x. split.
apply rt_trans with (y := Fun f us). apply rt_step. apply Vgt_prod_fun.
exact H. exact H0. exact H1.
Qed.

(***********************************************************************)
(** minimal dependency chain (subterms are terminating) *)

Definition chain_min (s : ATerm.term Sig) (t : ATerm.term Sig) : Prop :=
  chain s t 
  /\ lforall (SN (red R)) (direct_subterms s)
  /\ lforall (SN (red R)) (direct_subterms t).

Lemma chain_min_incl_chain : chain_min << chain.

Proof.
red. intros x y cmin. elim cmin. auto.
Qed.

Lemma gt_chain_min : forall f ts us v, terms_gt R ts us ->
  Vforall (SN (red R)) ts -> chain_min (Fun f us) v -> chain_min (Fun f ts) v.

Proof.
intros f ts us v gt_ts_us sn_ts chain_min_fus_v.
unfold chain_min in chain_min_fus_v.
destruct chain_min_fus_v as [chain_fus_v sn].
destruct sn as [esn_us esn_ts].
unfold chain_min.
split. apply gt_chain with us; trivial.
split. simpl. apply Vforall_lforall in sn_ts. trivial. trivial.
Qed.

(***********************************************************************)
(** assumptions on rules *)

Variable hyp1 : forallb (@is_notvar_lhs Sig) R = true.

Variable hyp2 : rules_preserv_vars R.

Implicit Arguments hyp2 [l r].

(***********************************************************************)
(** dp preserves variables *)

Lemma dp_elim_vars : forall l t, In (mkRule l t) dp -> exists r,
  In (mkRule l r) R /\ In t (calls R r) /\ nbsubterm_of l t = true
  /\ incl (vars t) (vars l).

Proof.
intros. destruct (dp_elim H). decomp H0. exists x. intuition.
apply incl_tran with (m := vars x). unfold incl. intros.
eapply subterm_eq_vars. eapply in_calls_subterm. apply H3. hyp.
apply hyp2. hyp.
Qed.

Implicit Arguments dp_elim_vars [l t].

Lemma dp_preserv_vars : rules_preserv_vars dp.

Proof.
unfold rules_preserv_vars. intros. destruct (dp_elim_vars H). intuition.
Qed.

Lemma dp_preserv_pw_disjoint_vars :
  pw_disjoint_vars (map lhs R) -> pw_disjoint_vars (map lhs dp).

Proof.
unfold pw_disjoint_vars, disjoint_vars. intros. eapply H.
apply lhs_dp. hyp. apply lhs_dp. hyp. apply H2. hyp.
Qed.

(***********************************************************************)
(** fundamental dp theorem *)

Require Import BoolUtil.

Notation capa := (capa R).
Notation cap := (cap R).
Notation alien_sub := (alien_sub R).

Notation SNR := (SN (red R)).

Lemma chain_min_fun : forall f, defined f R = true
  -> forall ts, SN chain_min (Fun f ts) -> Vforall SNR ts -> SNR (Fun f ts).

Proof.
cut (forall t, SN chain_min t -> forall f, defined f R = true
  -> forall ts, t = Fun f ts -> Vforall SNR ts -> SNR t).
intros. apply H with (t := Fun f ts) (f := f) (ts := ts); (hyp || refl).
(* induction on t with chain_min as well-founded ordering *)
intros t H. elim H. clear t H. intros t H IH f H0 ts H1 Hsnts.
assert (SN (@terms_gt Sig R (arity f)) ts). unfold terms_gt.
apply Vforall_SN_gt_prod. hyp.
(* induction on ts with red as well-founded ordering (ts is SN) *)
generalize IH. rewrite H1. elim H2. clear IH ts H1 Hsnts H2.
intros ts H1 IH1 IH2.
assert (Hsnts : Vforall SNR ts). apply SN_gt_prod_forall. apply SN_intro.
hyp. clear H1.
assert (H1 : forall y, terms_gt R ts y -> SNR (Fun f y)). intros. apply IH1.
hyp. intros. eapply IH2. eapply gt_chain_min. apply H1.
trivial. apply H2. apply H3. apply H4. hyp. clear IH1.
(* we prove that every reduct of (Fun f ts) is SN *)
apply SN_intro. intros u H2. redtac. destruct c; simpl in xl, yr.
(* c = Hole *)
destruct (fun_eq_sub xl).
(* lhs = Fun f us *)
destruct e as [ls]. rewrite H2 in xl. rewrite sub_fun in xl. Funeqtac.
(* the substitution s is SN *)
assert (Hsnsx : forall x, In x (vars l) -> SNR (s x)). intros.
eapply sub_fun_sn with (f := f). subst l. apply H4.
rewrite H3 in Hsnts. exact Hsnts.
(* we decompose r into its caps and its aliens *)
subst u. assert (r = sub (alien_sub r) (cap r)). apply sym_eq.
apply (alien_sub_cap R). rewrite H4. rewrite sub_sub.
apply no_call_sub_sn. hyp. apply calls_cap.
(* we prove that the alien substitution is SN *)
intros. ded (vars_cap R H5).
case (le_lt_dec x (maxvar r)); intro; unfold sub_comp, ACap.alien_sub.
(* x <= maxvar r *)
ded (vars_cap_inf R H5 l0). ded (hyp2 lr _ H7).
rewrite fsub_inf. simpl. apply Hsnsx. hyp. hyp.
(* x > maxvar r *)
rewrite (fsub_nth (aliens (capa r)) l0 H6).
set (a := Vnth (aliens (capa r)) (lt_pm (k:=projS1 (capa r)) l0 H6)).
assert (Fun f ts = sub s l). rewrite H3. rewrite H2. refl.
assert (In a (calls R r)). apply aliens_incl_calls. unfold a. apply Vnth_in.
ded (in_calls H8). destruct H9 as [g]. destruct H9 as [vs]. destruct H9.
(* every call is SN *)
eapply calls_sn with (r := r). hyp.
intros. apply Hsnsx. apply (hyp2 lr _ H11).
intros h ws H13 H14.
case_eq (nbsubterm_of l (Fun h ws)). rename H11 into z.
apply IH2 with (y := Fun h (Vmap (sub s) ws)) (f := h) (ts := Vmap (sub s) ws).
unfold chain_min. split. 
rewrite H7. rewrite <- sub_fun. eapply in_calls_chain. 
apply lr. hyp. hyp.
split. simpl. apply Vforall_lforall. trivial. 
simpl. apply Vforall_lforall. trivial.
eapply in_calls_defined. apply H13. refl. hyp.
(* Dershowitz' improvement *)
revert H11. unfold nbsubterm_of. rewrite negb_lr. simpl negb.
rewrite bsubterm_ok. intro H11.
rewrite H2 in H11. destruct (subterm_fun_elim H11). destruct H12.
apply subterm_eq_sn with (t := sub s x0). eapply Vforall_in. apply Hsnts.
rewrite H3. apply Vin_map_intro. hyp. apply subterm_eq_sub. hyp.
hyp.
(* lhs = Var x *)
decomp e. subst l. is_var_lhs.
(* c <> Hole *)
Funeqtac. subst u. apply H1. rewrite H2. unfold terms_gt. apply Vgt_prod_cast.
apply Vgt_prod_app. apply Vgt_prod_cons. left. split.
eapply red_rule. hyp. refl.
Qed.

Lemma chain_fun : forall f, defined f R = true
  -> forall ts, SN chain (Fun f ts) -> Vforall SNR ts -> SNR (Fun f ts).

Proof.
intros f defined_f ts sn_chain_f_ts sn_ts.
apply chain_min_fun; auto.
apply SN_incl with chain. apply chain_min_incl_chain. hyp.
Qed.

Lemma WF_chain : WF chain -> WF (red R).

Proof.
intro Hwf. unfold WF. apply term_ind_forall.
(* var *)
apply sn_var. apply hyp1.
(* fun *)
intro f. case_eq (defined f R).
(* f defined *)
apply chain_fun. hyp. apply Hwf. hyp.
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

Require Import AVariables.

Ltac chain := no_relative_rules; apply WF_chain;
  [ check_eq || fail "a LHS is a variable"
  | rules_preserv_vars
  | idtac].