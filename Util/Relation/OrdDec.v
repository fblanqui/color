(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2008-08-08

boolean function for total ordering
*)

Set Implicit Arguments.

Require Import RelUtil LogicUtil.

Section S.

Variable A : Type.

(***********************************************************************)
(** properties *)

Section properties.

Variable cmp : A -> A -> comparison.

Definition is_correct := forall x y, cmp x y = Eq -> x = y.

Definition greater x y := cmp x y = Gt.
Definition smaller x y := cmp x y = Lt.
Definition equal x y := cmp x y = Eq.

Definition is_symrefl := forall x y, cmp x y = CompOpp (cmp y x).

Variable hyp_symrefl : is_symrefl.

Lemma equal_refl : reflexive equal. (* forall x, cmp x x = Eq. *)

Proof.
unfold reflexive, equal. intro. case_eq (cmp x x). refl.
absurd (cmp x x = Gt). rewrite H. discr. rewrite hyp_symrefl. rewrite H. refl.
absurd (cmp x x = Lt). rewrite H. discr. rewrite hyp_symrefl. rewrite H. refl.
Qed.

Lemma equal_sym : symmetric equal.

Proof.
unfold symmetric, equal. intros. rewrite hyp_symrefl. rewrite H. refl.
Qed.

Lemma greater_antisym : antisymmetric greater.

Proof.
unfold antisymmetric, greater. intros x y h. rewrite hyp_symrefl. rewrite h.
discr.
Qed.

(***********************************************************************)
(** transitivity *)

Definition is_trans :=
  forall x y z c, cmp x y = c -> cmp y z = c -> cmp x z = c.

Variable hyp_trans : is_trans.

Lemma equal_trans : transitive equal.

Proof.
unfold transitive, equal. intros. apply hyp_trans with y; hyp.
Qed.

Lemma greater_trans : transitive greater.

Proof.
unfold transitive, greater. intros. apply hyp_trans with y; hyp.
Qed.

Lemma smaller_trans : transitive smaller.

Proof.
unfold transitive, smaller. intros. apply hyp_trans with y; hyp.
Qed.

End properties.

End S.

(***********************************************************************)
(** type equipped with a boolean total ordering *)

Record Bool_ord_type : Type := mkBool_ord_type {
  bot_type :> Type;
  bot_cmp : bot_type -> bot_type -> comparison;
  bot_symrefl : is_symrefl bot_cmp;
  bot_trans : is_trans bot_cmp;
  bot_correct : is_correct bot_cmp
}.

(***********************************************************************)
(** natural numbers *)

Fixpoint nat_cmp (x y : nat) : comparison :=
  match x, y with
    | 0, 0 => Eq
    | 0, S _ => Lt
    | S _, 0 => Gt
    | S a, S b => nat_cmp a b
  end.

Lemma nat_cmp_symrefl : is_symrefl nat_cmp.

Proof.
unfold is_symrefl. induction x; intros; destruct y; simpl; auto.
Qed.

Lemma nat_cmp_trans : is_trans nat_cmp.

Proof.
unfold is_trans. induction x; induction y; simpl; intros; destruct z; simpl;
  subst; auto; try discr. transitivity (nat_cmp y z). 2: hyp.
apply (IHx y z (nat_cmp y z)); auto.
Qed.

Lemma nat_cmp_correct : is_correct nat_cmp.

Proof.
unfold is_correct. induction x; destruct y; simpl; intros; auto; discr.
Qed.
