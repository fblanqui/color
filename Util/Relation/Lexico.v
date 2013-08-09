(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-25

lexicographic ordering
*)

Set Implicit Arguments.

Require Import SN RelUtil LogicUtil Morphisms.

(****************************************************************************)
(** lexicographic quasi-ordering on pairs *)

Section lex.

  Variable (A : Type) (gtA eqA : relation A) (Hcomp : eqA @ gtA << gtA).

  Lemma SN_compat : forall a, SN gtA a -> forall a', eqA a a' -> SN gtA a'.

  Proof.
    intros a SN_a a' eqaa'. apply SN_intro. intros a'' gta'a''.
    inversion SN_a. apply H. apply (inclusion_elim Hcomp). exists a'. auto.
  Qed.

  Variable (B : Type) (gtB : relation B).

  Inductive lex : relation (prod A B) :=
  | lex1 : forall a a' b b', gtA a a' -> lex (a,b) (a',b')
  | lex2 : forall a a' b b', eqA a a' -> gtB b b' -> lex (a,b) (a',b').

  Lemma lex_intro : forall a a' b b',
    gtA a a' \/ (eqA a a' /\ gtB b b') -> lex (a,b) (a',b').

  Proof.
    intros. destruct H. apply lex1. exact H. destruct H. apply lex2.
    exact H. exact H0.
  Qed.

  Variable (WF_gtB : WF gtB) (eqA_trans : Transitive eqA).

  Lemma lex_SN_eq : forall a b,
    SN lex (a,b) -> forall a', eqA a a' -> SN lex (a',b).

  Proof.
    intros a b SN_ab a' eqaa'. inversion SN_ab. apply SN_intro.
    destruct y as (a'',b'). intro H'.
    inversion H'; subst a'0 b'0 a0 b0; apply H.
    apply lex1. apply (inclusion_elim Hcomp). exists a'. auto.
    apply lex2. apply (eqA_trans eqaa' H3). exact H5.
  Qed.

  Lemma lex_SN :
    forall a, SN gtA a -> forall b, SN gtB b -> SN lex (a, b).

  Proof.
    induction 1 as [a Ha1 Ha2]. induction 1 as [b Hb1 Hb2]. apply SN_intro.
    destruct y as (a'',b'). intro H. inversion H; subst a'' b'0 a0 b0.
    (* gtA a a' *)
    apply Ha2. exact H1. apply WF_gtB.
    (* eqA a a' /\ gtB b b' *)
    apply (@lex_SN_eq a). 2: exact H3. apply Hb2. exact H5.
  Qed.

  Variable WF_gtA : WF gtA.

  Lemma WF_lex : WF lex.

  Proof.
    unfold WF. destruct x as (a,b). apply lex_SN. apply WF_gtA. apply WF_gtB.
  Qed.

End lex.

(****************************************************************************)
(** * Lexicographic order on tuples and vectors. *)

Section lexn.

  Variables (A : Type) (gtA eqA : relation A) (Hcomp : eqA @ gtA << gtA)
    (eqA_trans : Transitive eqA) (gtA_wf : WF gtA).

  Fixpoint prodn n : Type :=
    match n with
      | 0 => unit
      | S n' => prod A (prodn n')
    end.

  Fixpoint lexn n :=
    match n as n return relation (prodn n) with
      | 0 => empty_rel
      | S n' => lex gtA eqA (lexn n')
    end.

  Lemma lexn_wf n : WF (lexn n).

  Proof. induction n; simpl. apply WF_empty_rel. apply WF_lex; hyp. Qed.

  Require Import VecUtil.

  Fixpoint prod_of_vec n (v : vector A n) :=
    match v in vector _ n return prodn n with
      | Vnil => tt
      | Vcons x _ v' => (x, prod_of_vec v')
    end.

  Definition lexv n (v w : vector A n) :=
    lexn n (prod_of_vec v) (prod_of_vec w).

  Lemma lexv_wf n : WF (@lexv n).

  Proof. apply WF_inverse. apply lexn_wf. Qed.

End lexn.
