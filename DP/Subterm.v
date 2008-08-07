(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Joerg Endrullis, 2008-07

Subterm Criterion from 
  Dependency Pairs Revisited (Nao Hirokawa and Aart Middeldorp).
*)

(* $Id: Subterm.v,v 1.2 2008-08-07 14:00:17 blanqui Exp $ *)

Set Implicit Arguments.

Require Export ATrs.
Require Export Union.

(***********************************************************************)
(** Projections. *)

Record Projection (Sig : Signature) : Type := mkProjection {
  pi : forall f : Sig, nat;
  pi_bound : forall f, pi f <= (@arity Sig f)
}.

Section subterm_criterion.

Variable Sig : Signature.

Notation term := (term Sig).
Notation rule := (rule Sig).
Notation rules := (list rule).

Variable R : rules.

(***********************************************************************)
(* Subterm Criterion from Dependency Pairs Revisited *)

Definition subterm_rel (x y : term) : Prop := subterm x y.

Lemma subterm_rel_wf : WF (transp subterm_rel).

Proof.
  intros x. apply subterm_ind. clear x.
  intros x IH. apply SN_intro. intros y sy.
  assert (subterm y x); inversion sy as [c [hole subst]]; auto.
Qed.

Lemma comm_subterm_reduction :
    (transp subterm_rel) @ (red R) << (red R) @ (transp subterm_rel).

Proof.
  intros x z [y [xSuby yRz]].
  inversion xSuby as [C [notHoleC fillCy]].
  inversion yRz as [l [r [Cred [s [rule [yfillCredl zfillCredr]]]]]].
  exists (fill C z). split.
  exists l. exists r. exists (AContext.comp C Cred). exists s.
  split. assumption. split.
  rewrite <- fill_comp. rewrite <- yfillCredl. assumption.
  rewrite <- fill_comp. rewrite <- zfillCredr. refl.
  exists C. split. assumption. refl.
Qed.

Lemma subterm_and_reduction_sn : 
  forall x : term, 
    SN (red R) x -> SN (red R U (transp subterm_rel)) x.

Proof.
  intros x snx. apply sn_comm_sn; trivial.
  intros y _. apply subterm_rel_wf. clear. intros x y xy.
  assert ((red R @ transp subterm_rel) x y) as [z [xz zy]].
  apply comm_subterm_reduction. assumption.
  exists z. split.
  apply t1_step. assumption.
  apply rt1_trans with y. assumption. apply rt1_refl.
Qed.

(** Subterm criterion *)

(** should be an easy consequence of subterm_and_reduction_sn *)

End subterm_criterion.
