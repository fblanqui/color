(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-02-22, 2009-10-20 (rpo)

convert CoLoR terms into Coccinelle terms 
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Import ATerm.

(***********************************************************************)
(** convert a CoLoR signature into a Coccinelle signature *)

Module Type SIGNATURE.
  Parameter Sig : Signature.
End SIGNATURE.

Require Import term_spec.
Require Import EqUtil.

Module Make_Signature (Import S : SIGNATURE) <: Signature.
  Module Symb <: decidable_set.S.
    Definition A := symbol Sig.
    Definition eq_bool := @beq_symb Sig.
    Lemma eq_bool_ok : forall a1 a2,
      match eq_bool a1 a2 with true => a1 = a2 | false => ~ a1 = a2 end.
    Proof.
      intros a1 a2. unfold eq_bool. case_beq_symb Sig a1 a2. refl.
      rewrite <- (beq_ko (@beq_symb_ok Sig)). hyp.
    Qed.
  End Symb.
  Definition arity (f : Sig) := Free (arity f).
End Make_Signature.

(***********************************************************************)
(** convert CoLoR variables to Coccinelle variables *)

Require Import NatUtil.

Module Var <: decidable_set.S.
  Definition A := nat.
  Definition eq_bool := beq_nat.
  Lemma eq_bool_ok : forall a1 a2,
    match eq_bool a1 a2 with true => a1 = a2 | false => ~ a1 = a2 end.
  Proof.
    intros a1 a2. unfold eq_bool. case_beq_nat a1 a2. refl.
    rewrite <- (beq_ko beq_nat_ok). hyp.
  Qed.
End Var.

(***********************************************************************)
(** convert CoLoR terms into Coccinelle terms *)

Require Import term.
Require Import List.
Require Import Relations.
Require Import SN.
Require Import ASubstitution.

Module Make_Term (Import S : SIGNATURE) <: Term.

  Notation aterm := (term Sig). Notation aterms := (vector aterm).
  Notation AVar := ATerm.Var.

  Module Sig := Make_Signature S.

  Include (term.Make' Sig Var).

  Fixpoint term_of_aterm (t : aterm) :=
    match t with
      | AVar x => Var x
      | Fun f ts =>
        let fix terms_of_aterms n (ts : aterms n) :=
          match ts with
            | Vnil => nil
            | Vcons u k us => term_of_aterm u :: terms_of_aterms k us
          end in Term f (terms_of_aterms (arity f) ts)
    end.

  Fixpoint terms_of_aterms n (ts : aterms n) :=
    match ts with
      | Vnil => nil
      | Vcons u k us => term_of_aterm u :: terms_of_aterms us
    end.

  Lemma terms_of_aterms_eq : forall n (ts : aterms n),
    (fix terms_of_aterms n (ts : aterms n) :=
      match ts with
        | Vnil => nil
        | Vcons u k us => term_of_aterm u :: terms_of_aterms k us
      end) n ts = terms_of_aterms ts.

  Proof.
    induction ts; simpl; intros. refl. rewrite IHts. refl.
  Qed.

  Lemma term_of_aterm_fun : forall f ts,
    term_of_aterm (Fun f ts) = Term f (terms_of_aterms ts).

  Proof.
    intros. simpl. rewrite terms_of_aterms_eq. refl.
  Qed.

  Require Import VecUtil.

  Lemma terms_of_aterms_cast : forall n (ts : aterms n) p (e : n=p),
    terms_of_aterms (Vcast ts e) = terms_of_aterms ts.

  Proof.
    induction ts; destruct p; simpl; intros; try discr. refl.
    inversion e. subst p. rewrite IHts. refl.
  Qed.

  Lemma terms_of_aterms_app : forall n (ts : aterms n) p (us : aterms p),
    terms_of_aterms (Vapp ts us) = terms_of_aterms ts ++ terms_of_aterms us.

  Proof.
    induction ts; simpl; intros. refl. rewrite IHts. refl.
  Qed.

  Lemma length_terms_of_aterms : forall n (ts : aterms n),
    length (terms_of_aterms ts) = n.

  Proof.
    induction ts; simpl; intros. refl. rewrite IHts. refl.
  Qed.

  Fixpoint sub_of_asub (s : ASubstitution.substitution Sig) n :=
    match n with
      | 0 => nil
      | S n' => (n', term_of_aterm (s n')) :: sub_of_asub s n'
    end.

Require Import more_list.

Notation find := (@find _ eq_var_bool _).

  Lemma find_sub_of_asub : forall s n v, find v (sub_of_asub s n) =
    if bgt_nat n v then Some (term_of_aterm (s v)) else None.

  Proof.
    induction n; intros. refl. simpl sub_of_asub. simpl more_list.find.
    rewrite IHn. unfold eq_var_bool. case_beq_nat v n.
    assert (bgt_nat (S v) v = true). rewrite bgt_nat_ok. omega. rewrite H. refl.
    case_eq (bgt_nat n v); case_eq (bgt_nat (S n) v). refl.
    rewrite bgt_nat_ok in H0. rewrite bgt_nat_ko in H1. absurd_arith.
    rewrite bgt_nat_ok in H1. rewrite bgt_nat_ko in H0.
    rewrite (beq_ko beq_nat_ok) in H. absurd_arith. refl.
  Qed.

  Lemma term_of_aterm_sub : forall s k t, k > maxvar t ->
    term_of_aterm (sub s t) = apply_subst (sub_of_asub s k) (term_of_aterm t).

  Proof.
    intros s k t; pattern t; apply ATerm.term_ind
      with (Q := fun n (ts : aterms n) =>
        k > maxvars ts -> terms_of_aterms (Vmap (sub s) ts) =
        map (apply_subst (sub_of_asub s k)) (terms_of_aterms ts)); clear t.
    simpl. intros. rewrite find_sub_of_asub. case_eq (bgt_nat k x). refl.
    rewrite bgt_nat_ko in H0. absurd_arith.
    intros. simpl sub. repeat rewrite term_of_aterm_fun. simpl.
    apply (f_equal (Term f)). apply H. hyp.
    refl. intros t n ts. simpl. rewrite maxvars_cons. rewrite gt_max.
    intros. destruct H1. rewrite H. 2: hyp. rewrite H0. 2: hyp. refl.
  Qed.

  Require Import APosition.
  Require Import AContext.

  Lemma term_of_aterm_fill : forall u t c, term_of_aterm (fill c t) =
    replace_at_pos (term_of_aterm (fill c u)) (term_of_aterm t) (pos_context c).

  Proof.
    induction c; intros. refl. simpl fill. simpl pos_context.
    repeat rewrite term_of_aterm_fun. rewrite replace_at_pos_unfold.
    apply (f_equal (Term f)). repeat rewrite terms_of_aterms_cast.
    repeat rewrite terms_of_aterms_app. simpl.
    rewrite replace_at_pos_list_replace_at_pos_in_subterm. rewrite <- IHc. refl.
    rewrite length_terms_of_aterms. refl.
  Qed.

  Lemma is_a_pos_context : forall u c,
    is_a_pos (term_of_aterm (fill c u)) (pos_context c) = true.

  Proof.
    induction c; intros. refl. simpl fill. rewrite term_of_aterm_fun. simpl.
    rewrite terms_of_aterms_cast. rewrite terms_of_aterms_app. simpl.
    assert (nth_error (terms_of_aterms v ++ term_of_aterm (fill c u) ::
      terms_of_aterms v0) i = nth_error (terms_of_aterms v ++ term_of_aterm
        (fill c u) :: terms_of_aterms v0) (length (terms_of_aterms v))).
    apply (f_equal (nth_error (terms_of_aterms v ++ term_of_aterm (fill c u)
      :: terms_of_aterms v0))). rewrite length_terms_of_aterms. refl.
    rewrite H. rewrite nth_error_at_pos. hyp.
  Qed.

End Make_Term.

(***********************************************************************)
(** convert a CoLoR precedence into a Coccinelle precedence *)

Require Import rpo.

Module Type PRECEDENCE.
  Parameter Sig : Signature.
  Parameter status : Sig -> status_type.
  Parameter prec : Sig -> nat.
  Parameter bb : nat.
End PRECEDENCE.

Require Import RelUtil.
Require Import Wf_nat.

Module Make_Precedence (P : PRECEDENCE).

  Definition A := symbol P.Sig.
  Definition status := P.status.
  Definition prec := Rof lt P.prec.
  Definition prec_bool f g := bgt_nat (P.prec g) (P.prec f).

  Lemma prec_ok : forall f g, prec_bool f g = true <-> prec f g.

  Proof.
    intros f g. apply bgt_nat_ok.
  Qed.

  Lemma prec_bool_ok : forall a1 a2,
    match prec_bool a1 a2 with true => prec a1 a2 | false => ~prec a1 a2 end.

  Proof.
    intros a1 a2. case_eq (prec_bool a1 a2). rewrite <- prec_ok. hyp.
    intro h. rewrite <- prec_ok in h. rewrite H in h. discr.
  Qed.

  Lemma prec_antisym : forall s, prec s s -> False.

  Proof.
    intro s. unfold prec, Rof. intro. omega.
  Qed.

  Lemma prec_transitive : transitive prec.

  Proof.
    intros x y z. unfold prec, Rof. omega.
  Qed.

  Lemma prec_wf : well_founded prec.

  Proof.
    apply well_founded_ltof.
  Qed.

  Definition Prec := Build_Precedence
    status prec_bool prec_bool_ok prec_antisym prec_transitive.

End Make_Precedence.

(***********************************************************************)
(** convert Coccinelle RPO into a CoLoR WeakRedPair using rpo_dec *)

Require Import ARedPair.
Require Import ARelation.

Module Make_RPO_dec (Import P : PRECEDENCE) <: WeakRedPair.

  Module Q := Make_Precedence P.

  Module S. Definition Sig := Sig. End S.

  Module Import Term := Make_Term S.

  Module Import Rpo := rpo.Make Term.

  Notation rpo := (rpo Q.Prec P.bb).

  Definition Sig := Sig.
  Definition succ := transp (Rof rpo term_of_aterm).

  Require Import Inverse_Image.

  Lemma wf_succ : WF succ.

  Proof.
    apply wf_WF_transp. apply wf_inverse_image. apply wf_rpo. apply Q.prec_wf.
  Qed.

  Require Import Max.

  Lemma sc_succ : substitution_closed succ.

  Proof.
    intros t u s h. unfold succ, transp, Rof. set (k:=max(maxvar t)(maxvar u)).
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_r.
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_l.
    apply rpo_subst. hyp.
  Qed.

  Definition bsucc t u :=
    match rpo_dec Q.Prec P.bb (term_of_aterm u) (term_of_aterm t) with
      | left _ => true
      | right _ => false
    end.

  Lemma bsucc_ok : forall t u, bsucc t u = true <-> succ t u.

  Proof.
    intros t u. unfold bsucc.
    case (rpo_dec Q.Prec P.bb (term_of_aterm u) (term_of_aterm t)); intuition.
    discr.
  Qed.

  Lemma bsucc_sub : rel bsucc << succ.

  Proof.
    intros t u. unfold rel. rewrite bsucc_ok. auto.
  Qed.

  Definition equiv_aterm := Rof (equiv Q.Prec) term_of_aterm.

  Definition succeq := succ U equiv_aterm.

  Lemma sc_succeq : substitution_closed succeq.

  Proof.
    intros t u s [h|h]. left. apply sc_succ. hyp. right.
    unfold equiv_aterm, Rof. set (k := max (maxvar t) (maxvar u)).
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_l.
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_r.
    apply equiv_subst. hyp.
  Qed.

  Lemma cc_succ : context_closed succ.

  Proof.
    intros t u c h. unfold succ, transp, Rof.
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=t).
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=u).
    apply rpo_add_context. hyp. apply is_a_pos_context.
  Qed.

  Lemma cc_equiv_aterm : context_closed equiv_aterm.

  Proof.
    intros t u c h. unfold equiv_aterm, Rof.
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=t).
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=u).
    apply equiv_add_context. hyp. apply is_a_pos_context.
  Qed.

  Lemma cc_succeq : context_closed succeq.

  Proof.
    intros t u c [h|h]. left. apply cc_succ. hyp.
    right. apply cc_equiv_aterm. hyp.
  Qed.

  Lemma refl_succeq : reflexive succeq.

  Proof.
    intro t. right. apply Eq.
  Qed.

  Lemma succ_succeq_compat : absorb succ succeq.

  Proof.
    intros t v [u [[h1|h1] h2]]. apply rpo_trans with (term_of_aterm u); hyp.
    unfold succ, transp, Rof. rewrite equiv_rpo_equiv_1. apply h2. hyp.
  Qed.

  Definition bequiv t u :=
    match equiv_dec Q.Prec (term_of_aterm t) (term_of_aterm u) with
      | left _ => true
      | right _ => false
    end.

  Lemma bequiv_ok : forall t u, bequiv t u = true <-> equiv_aterm t u.

  Proof.
    intros t u. unfold bequiv, equiv_aterm, Rof.
    case (equiv_dec Q.Prec (term_of_aterm t) (term_of_aterm u)); intuition.
    discr.
  Qed.

  Definition bsucceq t u := bsucc t u || bequiv t u.

  Require Import BoolUtil.

  Lemma bsucceq_ok : forall t u, bsucceq t u = true <-> succeq t u.

  Proof.
    intros t u. unfold bsucceq, succeq. rewrite orb_eq. rewrite bsucc_ok.
    rewrite bequiv_ok. unfold Relation_Operators.union. tauto.
  Qed.

  Definition bsucceq_sub : rel bsucceq << succeq.

  Proof.
    intros t u. unfold rel. rewrite bsucceq_ok. auto.
  Qed.

End Make_RPO_dec.

(***********************************************************************)
(** convert Coccinelle RPO into a CoLoR WeakRedPair using rpo_eval *)

Module Make_RPO (Import P : PRECEDENCE) <: WeakRedPair.

  Module Q := Make_Precedence P.

  Module S. Definition Sig := Sig. End S.

  Module Import Term := Make_Term S.

  Module Import Rpo := rpo.Make Term.

  Notation rpo := (rpo Q.Prec P.bb).

  Definition Sig := Sig.
  Definition succ := transp (Rof rpo term_of_aterm).

  Require Import Inverse_Image.

  Lemma wf_succ : WF succ.

  Proof.
    apply wf_WF_transp. apply wf_inverse_image. apply wf_rpo. apply Q.prec_wf.
  Qed.

  Require Import Max.

  Lemma sc_succ : substitution_closed succ.

  Proof.
    intros t u s h. unfold succ, transp, Rof. set (k:=max(maxvar t)(maxvar u)).
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_r.
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_l.
    apply rpo_subst. hyp.
  Qed.

  Notation empty_rpo_infos := (empty_rpo_infos Q.Prec P.bb).
  Notation rpo_eval := (rpo_eval empty_rpo_infos P.bb).
  Notation rpo_eval_is_sound := (rpo_eval_is_sound_weak empty_rpo_infos P.bb).

  Require Import ordered_set.

  Definition bsucc t u :=
    match rpo_eval (term_of_aterm t) (term_of_aterm u) with
      | Some Greater_than => true
      | _ => false
    end.

  Lemma bsucc_ok : forall t u, bsucc t u = true -> succ t u.

  Proof.
    intros t u. unfold bsucc.
    generalize (rpo_eval_is_sound (term_of_aterm t) (term_of_aterm u)).
    case (rpo_eval (term_of_aterm t) (term_of_aterm u)); try discr.
    destruct c; try discr. unfold succ, transp, Rof. auto.
  Qed.

  Lemma bsucc_sub : rel bsucc << succ.

  Proof.
    intros t u. unfold rel. intro h. apply bsucc_ok. hyp.
  Qed.

  Definition equiv_aterm := Rof (equiv Q.Prec) term_of_aterm.

  Definition succeq := succ U equiv_aterm.

  Lemma sc_succeq : substitution_closed succeq.

  Proof.
    intros t u s [h|h]. left. apply sc_succ. hyp. right.
    unfold equiv_aterm, Rof. set (k := max (maxvar t) (maxvar u)).
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_l.
    rewrite term_of_aterm_sub with (k:=S k). 2: apply le_n_S; apply le_max_r.
    apply equiv_subst. hyp.
  Qed.

  Lemma cc_succ : context_closed succ.

  Proof.
    intros t u c h. unfold succ, transp, Rof.
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=t).
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=u).
    apply rpo_add_context. hyp. apply is_a_pos_context.
  Qed.

  Lemma cc_equiv_aterm : context_closed equiv_aterm.

  Proof.
    intros t u c h. unfold equiv_aterm, Rof.
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=t).
    rewrite term_of_aterm_fill with (u := AVar 0) (t:=u).
    apply equiv_add_context. hyp. apply is_a_pos_context.
  Qed.

  Lemma cc_succeq : context_closed succeq.

  Proof.
    intros t u c [h|h]. left. apply cc_succ. hyp.
    right. apply cc_equiv_aterm. hyp.
  Qed.

  Lemma refl_succeq : reflexive succeq.

  Proof.
    intro t. right. apply Eq.
  Qed.

  Lemma succ_succeq_compat : absorb succ succeq.

  Proof.
    intros t v [u [[h1|h1] h2]]. apply rpo_trans with (term_of_aterm u); hyp.
    unfold succ, transp, Rof. rewrite equiv_rpo_equiv_1. apply h2. hyp.
  Qed.

  Definition bsucceq t u :=
    match rpo_eval (term_of_aterm t) (term_of_aterm u) with
      | Some Greater_than | Some Equivalent => true
      | _ => false
    end.

  Lemma bsucceq_ok : forall t u, bsucceq t u = true -> succeq t u.

  Proof.
    intros t u. unfold bsucceq.
    generalize (rpo_eval_is_sound (term_of_aterm t) (term_of_aterm u)).
    case (rpo_eval (term_of_aterm t) (term_of_aterm u)); try discr.
    destruct c; try discr; unfold succeq, Relation_Operators.union,
      equiv_aterm, succ, transp, Rof; auto.
  Qed.

  Definition bsucceq_sub : rel bsucceq << succeq.

  Proof.
    intros t u. unfold rel. intro h. apply bsucceq_ok. hyp.
  Qed.

End Make_RPO.
