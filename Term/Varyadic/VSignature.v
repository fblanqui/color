(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2005-06-10

signature for algebraic terms with no arity
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil.

(***********************************************************************)
(** Variables are represented by natural numbers. *)

Notation variable := nat (only parsing).

(***********************************************************************)
(** Signature with a decidable set of symbols of fixed arity. *)

Record Signature : Type := mkSignature {
  symbol :> Type;
  beq_symb : symbol -> symbol -> bool;
  beq_symb_ok : forall x y, beq_symb x y = true <-> x = y
}.

Arguments mkSignature [symbol beq_symb] _.
Arguments beq_symb [s] _ _.
Arguments beq_symb_ok {s x y}.

From CoLoR Require Import EqUtil.

Ltac case_beq_symb Sig := EqUtil.case_beq (@beq_symb Sig) (@beq_symb_ok Sig).

Definition eq_symb_dec Sig := dec_beq (@beq_symb_ok Sig).

Arguments eq_symb_dec [Sig] _ _.

(***********************************************************************)
(** Tactic for proving beq_symb_ok *)

Ltac beq_symb_ok := intros f g; split;
  [destruct f; destruct g; simpl; intro; (discr || refl)
    | intro; subst g; destruct f; refl].

(***********************************************************************)
(** Modules and module types for signatures *)

Module Type SIG.
  Parameter Sig : Signature.
End SIG.

(* DecidableType *)
From Stdlib Require Import DecidableType.
Module DecType (Import S : SIG) <: DecidableType.
  Definition t := @symbol Sig.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Definition eq_dec := EqUtil.dec_beq (@beq_symb_ok Sig).
End DecType.

(* finite signature *)
From CoLoR Require Import ListUtil.
Module Type FSIG.
  Parameter Sig : Signature.
  Parameter Fs : list Sig.
  Parameter Fs_ok : forall f, In f Fs.
End FSIG.

(***********************************************************************)
(** Weighted signatures *)

Module Type WSIG.
  Parameter Sig : Signature.
  Parameter weight : Sig -> nat.
  Parameter weight_inj : forall f g, weight f = weight g -> f = g.
End WSIG.

From CoLoR Require Import NatUtil BoolUtil.

Section weight_inj.

  Variable Sig : Signature.
  Variable Fs : list Sig.
  Variable Fs_ok : forall f, In f Fs.
  Variable weight : Sig -> nat.

  Definition bweight_inj :=
    forallb (fun f => forallb (fun g =>
      implb (beq_nat (weight f) (weight g)) (beq_symb f g)) Fs) Fs.

  Lemma bweight_inj_ok : bweight_inj = true <->
    (forall f g, weight f = weight g -> f = g).

  Proof.
    unfold bweight_inj. apply forallb_ok_fintype. 2: hyp. intro f.
    apply forallb_ok_fintype. 2: hyp. intro g. unfold implb.
    case_eq (beq_nat (weight f) (weight g)).
    rewrite beq_nat_ok, beq_symb_ok. tauto.
    rewrite (beq_ko beq_nat_ok). tauto.
  Qed.

End weight_inj.

(*Arguments bweight_inj_ok _ [Fs] _ [weight].*)

Ltac weight_inj Fs_ok := rewrite <- (bweight_inj_ok _ Fs_ok);
  (check_eq || fail 10 "non-injective weight function").

(***********************************************************************)
(** Ordered signatures *)

From Stdlib Require Import OrderedType.

Module OrdType (Import S : WSIG) <: OrderedType.

  Include (DecType S).

  Definition lt f g := weight f < weight g.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.

  Proof. unfold lt. intros. lia. Qed.

  Lemma lt_not_eq : forall x y, lt x y -> x <> y.

  Proof. unfold lt. intros x y l e. subst. lia. Qed.

  Definition blt f g := bgt_nat (weight g) (weight f).

  Lemma blt_ok : forall f g, blt f g = true <-> lt f g.

  Proof. intros f g. unfold blt, lt. apply bgt_nat_ok. Qed.

  Lemma lt_total : forall f g,
    beq_symb f g = false -> blt f g = false -> blt g f = true.

  Proof.
    intros f g. unfold blt.
    rewrite bgt_nat_ok, bgt_nat_ko, (beq_ko (@beq_symb_ok Sig)). intros.
    destruct (eq_nat_dec (weight f) (weight g)).
    ded (weight_inj e). subst g. cong.
    lia.
  Qed.

  Definition compare : forall x y, Compare lt (@Logic.eq t) x y.

  Proof.
    intros x y. case_eq (beq_symb x y); intro H.
    rewrite beq_symb_ok in H. apply (EQ H).
    case_eq (blt x y); intro H0.
    rewrite blt_ok in H0. apply (LT H0).
    eapply GT. rewrite <- blt_ok. apply lt_total; hyp.
  Defined.

End OrdType.
