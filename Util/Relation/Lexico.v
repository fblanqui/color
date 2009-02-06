(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-25

lexicographic ordering
*)

Set Implicit Arguments.

Require Import SN.
Require Import RelUtil.

(****************************************************************************)
(** lexicographic quasi-ordering on pairs *)

Section lexp.

Variable (A : Type) (gtA eqA : relation A) (Hcomp : eqA @ gtA << gtA).

Lemma SN_compat : forall a, SN gtA a -> forall a', eqA a a' -> SN gtA a'.

Proof.
intros a SN_a a' eqaa'. apply SN_intro. intros a'' gta'a''.
inversion SN_a. apply H. apply (incl_elim Hcomp). exists a'. auto.
Qed.

Variable (B : Type) (gtB : relation B).

Inductive lexp : relation (prod A B) :=
| lexp1 : forall a a' b b', gtA a a' -> lexp (a,b) (a',b')
| lexp2 : forall a a' b b', eqA a a' -> gtB b b' -> lexp (a,b) (a',b').

Lemma lexp_intro : forall a a' b b',
  gtA a a' \/ (eqA a a' /\ gtB b b') -> lexp (a,b) (a',b').

Proof.
intros. destruct H. apply lexp1. exact H. destruct H. apply lexp2.
exact H. exact H0.
Qed.

Variable (WF_gtB : WF gtB) (eqA_trans : transitive eqA).

Lemma lexp_SN_eq : forall a b,
  SN lexp (a,b) -> forall a', eqA a a' -> SN lexp (a',b).

Proof.
intros a b SN_ab a' eqaa'. inversion SN_ab. apply SN_intro.
destruct y as (a'',b'). intro H'. inversion H'; subst a'0 b'0 a0 b0; apply H.
apply lexp1. apply (incl_elim Hcomp). exists a'. auto.
apply lexp2. apply (eqA_trans eqaa' H4). exact H6.
Qed.

Lemma lexp_SN :
  forall a, SN gtA a -> forall b, SN gtB b -> SN lexp (a, b).

Proof.
induction 1 as [a Ha1 Ha2]. induction 1 as [b Hb1 Hb2]. apply SN_intro.
destruct y as (a'',b'). intro H. inversion H; subst a'' b'0 a0 b0.
(* gtA a a' *)
apply Ha2. exact H1. apply WF_gtB.
(* eqA a a' /\ gtB b b' *)
apply (@lexp_SN_eq a). 2: exact H3. apply Hb2. exact H5.
Qed.

Variable WF_gtA : WF gtA.

Lemma WF_lexp : WF lexp.

Proof.
unfold WF. destruct x as (a,b). apply lexp_SN. apply WF_gtA. apply WF_gtB.
Qed.

End lexp.

(****************************************************************************)
(** lexicographic ordering on the same argument *)

Section lex.

Variable (A : Type) (gtA eqA gtA' : relation A)
  (eqA_trans : transitive eqA) (Hcomp : eqA @ gtA << gtA)
  (WF_gtA : WF gtA) (WF_gtA' : WF gtA').

Definition lex x y := lexp gtA eqA gtA' (x,x) (y,y).

Lemma WF_lex : WF lex.

Proof.
exact (WF_inverse (fun x:A => (x,x)) (WF_lexp Hcomp WF_gtA' eqA_trans WF_gtA)).
Qed.

End lex.

Section lex'.

Variable (A : Type) (gt1 gt2 : relation A)
  (WF_gt1 : WF gt1) (WF_gt2 : WF gt2)
  (trans_gt2 : transitive gt2) (Hcomp : gt2 @ gt1 << gt1).

Definition lex' := lex gt1 gt2 gt2.

Lemma WF_lex' : WF lex'.

Proof.
unfold lex'. apply WF_lex; assumption.
Qed.

Lemma lex'_intro : gt1 U gt2 << lex'.

Proof.
unfold lex', lex, inclusion. intros. apply lexp_intro. destruct H; auto.

Qed.

End lex'.