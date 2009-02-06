(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-02-09
- Frederic Blanqui, 2005-02-17

general results on the strong normalization of rewrite relations
*)

Set Implicit Arguments.

Section S.

Require Import ATrs.
Require Import SN.
Require Import List.
Require Import LogicUtil.
Require Import VecUtil.
Require Import VecOrd.
Require Import NatUtil.

Variable Sig : Signature.

Notation term := (term Sig). Notation terms := (vector term).
Notation rule := (rule Sig). Notation rules := (list rule).

Variable R : rules.

Notation Red := (@red Sig R). Notation SNR := (SN Red).

(***********************************************************************)
(** every subterm of an sn term is sn *)

Lemma subterm_sn : forall t, SNR t -> forall u, subterm_eq u t -> SNR u.

Proof.
intros t H. elim H. clear t H. intros t H IH u H0. apply SN_intro.
intros u' H1. ded (red_subterm H1 H0). destruct H2 as [t']. destruct H2.
eapply IH. apply H2. assumption.
Qed.

Lemma sub_sn : forall l x s, In x (vars l) -> SNR (sub s l) -> SNR (s x).

Proof.
intros. change (SNR (sub s (Var x))). eapply subterm_sn. apply H0.
apply subterm_sub. apply in_vars_subterm_eq. assumption.
Qed.

Lemma sub_fun_sn : forall f ts x s,
  In x (vars (Fun f ts)) -> Vforall SNR (Vmap (sub s) ts) -> SNR (s x).

Proof.
intros. change (SNR (sub s (Var x))). rewrite vars_fun in H.
ded (in_vars_vec_elim H). destruct H1 as [t]. destruct H1.
ded (in_vars_subterm_eq H2). apply subterm_sn with (t := sub s t).
eapply Vforall_in with (n := arity f). apply H0. apply Vin_map_intro. hyp.
apply subterm_sub. assumption.
Qed.

(***********************************************************************)
(** strongly normalizing terms when no lhs is a variable *)

Variable hyp1 : forallb (@is_notvar_lhs Sig) R = true.

(***********************************************************************)
(** variables are sn *)

Lemma sn_var : forall v, SNR (Var v).

Proof.
intro. apply SN_intro. intros t H. redtac. ded (is_notvar_lhs_elim hyp1 H).
decomp H2. subst l. rewrite sub_fun in H0. destruct c; discr.
Qed.

(***********************************************************************)
(** undefined symbol whose arguments are sn *)

Require Import ACalls.

Lemma sn_args_sn_fun : forall f, defined f R = false ->
  forall ts, Vforall SNR ts -> SNR (Fun f ts).

Proof.
intros. set (gt := (@Vgt_prod term Red (arity f))).
assert (SN gt ts). unfold gt. apply Vforall_SN_gt_prod. assumption.
elim H1. intros.
apply SN_intro. change (forall y, Red (Fun f x) y -> SNR y). intros.
redtac. subst y. destruct c; simpl in H5; simpl.
(* C = Hole *)
case (fun_eq_sub H5); intro H6; destruct H6.
(* lhs is Fun *)
cut (defined f R = true). rewrite H. discr.
eapply lhs_fun_defined. subst l. apply H4.
(* lhs is Var *)
subst l. is_var_lhs.
(* C <> Hole *)
Funeqtac. subst x. apply H3. unfold gt. eapply Vgt_prod_cast.
apply Vgt_prod_app.
apply Vgt_prod_cons. left. split. 2: reflexivity. apply red_rule. assumption.
Qed.

(***********************************************************************)
(** application of an sn substitution to a term without defined symbols *)

Lemma no_call_sub_sn : forall t, calls R t = nil -> forall s,
  (forall x, In x (vars t) -> SNR (s x)) -> SNR (sub s t).

Proof.
intro. pattern t. apply term_ind_forall; clear t; intros.
ded (H0 v). apply H1. simpl. auto.
rewrite sub_fun. pattern (defined f R). apply bool_eq_ind; intro.
simpl in H0. rewrite H2 in H0. discriminate.
apply sn_args_sn_fun. assumption. apply Vforall_map_intro. apply Vforall_intro.
intros. ded (Vforall_in H H3). apply H4.
simpl in H0. rewrite H2 in H0. change (vcalls R v = nil) in H0.
eapply in_vcalls_nil with (n := arity f). apply H3. assumption.
intros. apply H1. rewrite vars_fun. eapply vars_vec_in. apply H5. assumption.
Qed.

(***********************************************************************)
(** given a substitution [s] that is sn on [vars r],
if [sub s (Fun g vs)] is sn whenever [Fun g vs] is a call in [r]
such that [Vmap (sub s) vs] are sn,
then [sub s (Fun g vs)] is sn whenever [Gun g vs] is a call in [r] *)

Require Import ACap.

Lemma calls_sn_args : forall r s, (forall x, In x (vars r) -> SNR (s x))
  -> (forall g vs, In (Fun g vs) (calls R r)
                   -> Vforall SNR (Vmap (sub s) vs) -> SNR (sub s (Fun g vs)))
  -> forall g vs, In (Fun g vs) (calls R r) -> Vforall SNR (Vmap (sub s) vs).

Proof.
intros r s H H0. cut (forall a g vs, a = Fun g vs
  -> In a (calls R r) -> Vforall SNR (Vmap (sub s) vs)).
intros. apply H1 with (a := Fun g vs). refl. assumption.
intro a. pattern a. apply subterm_ind. clear a. intros. subst t.
apply Vforall_intro. intros w H2.
ded (Vin_map H2). destruct H4 as [v]. destruct H4. subst w.
assert (v = sub (alien_sub R v) (cap R v)). apply sym_eq.
apply (alien_sub_cap R).
rewrite H5. rewrite sub_sub. apply no_call_sub_sn. apply calls_cap. intros.
(* begin assert *)
assert (subterm v r). eapply subterm_trans_eq2 with (u := Fun g vs).
apply subterm_fun. assumption. eapply in_calls_subterm. apply H3.
(* end assert *)
unfold comp. unfold alien_sub. case (le_lt_dec x (maxvar v)); intro.
(* x <= maxvar v *)
rewrite fsub_inf. 2: assumption. simpl. apply H.
eapply subterm_eq_vars. apply subterm_strict. apply H7.
apply (vars_cap_inf R). assumption. assumption.
(* x > maxvar v *)
ded (vars_cap R H6). rewrite (fsub_nth (aliens (capa R v)) l H8).
set (a := Vnth (aliens (capa R v)) (lt_pm (k:=projS1 (capa R v)) l H8)).
assert (Vin a (aliens (capa R v))). unfold a. apply Vnth_in.
assert (subterm_eq a v). apply (in_aliens_subterm R). assumption.
assert (In a (calls R v)). apply aliens_incl_calls. assumption.
ded (in_calls H11). destruct H12 as [f]. destruct H12 as [us]. destruct H12.
rewrite H12. rewrite H12 in H10. rewrite H12 in H11.
assert (In (Fun f us) (calls R r)). apply subterm_in_calls. assumption.
apply subterm_strict. eapply subterm_trans_eq1. apply H10. assumption.
apply H0. assumption. apply H1 with (u := Fun f us).
eapply subterm_trans_eq1. eapply in_calls_subterm. apply H11.
apply subterm_fun. assumption. refl. assumption.
Qed.

Lemma calls_sn : forall r s, (forall x, In x (vars r) -> SNR (s x))
  -> (forall g vs, In (Fun g vs) (calls R r)
                   -> Vforall SNR (Vmap (sub s) vs) -> SNR (sub s (Fun g vs)))
  -> forall a, In a (calls R r) -> SNR (sub s a).

Proof.
intros. ded (in_calls H1). destruct H2 as [g]. destruct H2 as [vs].
destruct H2. subst a. apply H0. assumption. eapply calls_sn_args. apply H.
apply H0. assumption.
Qed.

End S.
