(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Joerg Endrullis, 2008-07
- Adam koprowski, 2009-09

Subterm Criterion from 
  Dependency Pairs Revisited (Nao Hirokawa and Aart Middeldorp).
*)

Set Implicit Arguments.

Require Import ATrs.
Require Import Union.
Require Import ACompat.
Require Import List.
Require Import VecUtil.
Require Import SN.
Require Import RelUtil.
Require Import LogicUtil.

(***********************************************************************)
(** Projections. *)

Record simple_proj (Sig : Signature) : Type := mk_simple_proj {
  pi : forall f : Sig, nat;
  pi_bound : forall f, pi f < (@arity Sig f)
}.

Section subterm_criterion.

Variable Sig : Signature.

Notation term := (term Sig).
Notation rule := (rule Sig).
Notation rules := (list rule).

Definition pi_term (p : simple_proj Sig) (t : term) : term :=
  match t with
  | Var _ => t
  | Fun f v => Vnth v (pi_bound p f)
  end.

Definition pi_trs (p : simple_proj Sig) (R : rules) : rules := 
  List.map (fun r => mkRule (pi_term p (lhs r)) (pi_term p (rhs r))) R.

(***********************************************************************)
(* Subterm Criterion from Dependency Pairs Revisited *)

Definition sub_lt : relation term := @subterm Sig.
Definition sub_eq : relation term := @subterm_eq Sig.

Lemma subterm_rel_wf : WF (transp sub_lt).

Proof.
  intros x. apply subterm_ind. clear x.
  intros x IH. apply SN_intro. intros y sy.
  assert (subterm y x); inversion sy as [c [hole subst]]; auto.
Qed.

Lemma comm_subterm_reduction : forall R : rules,
  (transp sub_lt) @ (red R) << (red R) @ (transp sub_lt).

Proof.
  intros R x z [y [xSuby yRz]].
  inversion xSuby as [C [notHoleC fillCy]].
  inversion yRz as [l [r [Cred [s [rule [yfillCredl zfillCredr]]]]]].
  exists (fill C z). split.
  exists l. exists r. exists (comp C Cred). exists s.
  split. assumption. split.
  rewrite <- fill_fill. rewrite <- yfillCredl. assumption.
  rewrite <- fill_fill. rewrite <- zfillCredr. refl.
  exists C. split. assumption. refl.
Qed.

Lemma subterm_and_reduction_sn : forall R : rules,
  forall x : term, 
    SN (red R) x -> SN (red R U (transp sub_lt)) x.

Proof.
  intros R x snx. apply sn_comm_sn; trivial.
  intros y _. apply subterm_rel_wf. clear. intros x y xy.
  assert ((red R @ transp sub_lt) x y) as [z [xz zy]].
  apply comm_subterm_reduction. assumption.
  exists z. split.
  apply t1_step. assumption.
  apply rt1_trans with y. assumption. apply rt1_refl.
Qed.

(** Subterm criterion *)

Lemma subterm_criterion : forall (p : simple_proj Sig) E R R',
  compat sub_eq (pi_trs p E) ->
  compat sub_eq (pi_trs p R) ->
  compat sub_lt (pi_trs p R') ->
  WF (hd_red_mod_min E  R       ) -> 
  WF (hd_red_mod_min E (R ++ R')).

Proof.
  intros p E R R' Eeq Req R'lt wfER.
Admitted.

(* Working on it
Lemma subterm_criterion :
  forall p : Projection Sig, forall R : list dprule, forall R' : list dprule, forall E : rules,
  lforall (fun rule => (transp subterm_eq_rel) 
                       (project p (lhs (r rule)) (proj1 (proof rule))) 
                       (project p (rhs (r rule)) (proj2 (proof rule)))) R
  -> lforall (fun rule => (transp subterm_rel) 
                       (project p (lhs (r rule)) (proj1 (proof rule))) 
                       (project p (rhs (r rule)) (proj2 (proof rule)))) R'
  -> WF (hd_red_mod_min E (map r R)) -> WF (hd_red_mod_min E (map r (R ++ R'))).

Proof.
  intros p R R' E subeqR subR' wfR.
  set (er := hd_red_mod_min E (map r R)). set (er' := hd_red_mod_min E (map r R')).
  apply WF_incl with (S := lex' er' (er!)).
  trans (er U er'). unfold er, er'. rewrite map_app. apply hd_red_mod_min_union.
  trans (er' U er). apply union_commut.
  trans (er' U er!). union. apply tc_incl.
  apply lex'_intro. apply WF_lex'.

  WFtac. apply WF_tc. exact H2. apply tc_trans.
  apply comp_tc_incl. trans (succ_eq! @ succ). comp. unfold er.
  trans (red_mod E R). apply incl_trans with (hd_red_mod E R).
  apply hd_red_mod_min_incl. apply hd_red_mod_incl_red_mod. incl_red.
  apply comp_tc_incl. rptac.
Qed.
*)

End subterm_criterion.
