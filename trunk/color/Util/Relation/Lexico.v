(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-25

lexicographic ordering
*)

Set Implicit Arguments.

Require Import SN RelUtil LogicUtil Morphisms.

(****************************************************************************)
(** ** Lexicographic quasi-ordering on pairs. *)

Section lex.

  (** We assume given a set [A] equipped with two relations [gtA] and
  [eqA] satisfying the following compatibility condition: *)

  Variable (A : Type) (gtA eqA : relation A) (Hcomp : eqA @ gtA << gtA).

  Lemma SN_compat : forall a, SN gtA a -> forall a', eqA a a' -> SN gtA a'.

  Proof.
    intros a SN_a a' eqaa'. apply SN_intro. intros a'' gta'a''.
    inversion SN_a. apply H. apply (inclusion_elim Hcomp). exists a'. auto.
  Qed.

  (** We assime given a set [B] equipped with a relation [gtB]. *)

  Variable (B : Type) (gtB : relation B).

  (** Definition of the lexicographic relation. *)

  Inductive lex : relation (prod A B) :=
  | lex1 : forall a a' b b', gtA a a' -> lex (a,b) (a',b')
  | lex2 : forall a a' b b', eqA a a' -> gtB b b' -> lex (a,b) (a',b').

  Lemma lex_intro : forall a a' b b',
    gtA a a' \/ (eqA a a' /\ gtB b b') -> lex (a,b) (a',b').

  Proof.
    intros. destruct H. apply lex1. exact H. destruct H. apply lex2.
    exact H. exact H0.
  Qed.

  (** We now prove that [lex] is wellfounded if both [gtA] and [gtB]
  are wellfounded, and if [eqA] is transitive. *)

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
(** ** Lexicographic order on tuples and vectors. *)

Section lexn.

  Variables (A : Type) (gtA eqA : relation A) (Hcomp : eqA @ gtA << gtA)
    (eqA_trans : Transitive eqA) (gtA_wf : WF gtA).

  (** Type of n-tuples of elements of [A]. *)

  Fixpoint prodn n : Type :=
    match n with
      | 0 => unit
      | S n' => prod A (prodn n')
    end.

  (** Lexicographic relation on n-tuples. *)

  Fixpoint lexn n :=
    match n as n return relation (prodn n) with
      | 0 => empty_rel
      | S n' => lex gtA eqA (lexn n')
    end.

  Lemma lexn_wf n : WF (lexn n).

  Proof. induction n; simpl. apply WF_empty_rel. apply WF_lex; hyp. Qed.

  Require Import VecUtil.

  (** Convert of vector of size [n] into an [n]-tuple. *)

  Fixpoint prod_of_vec n (v : vector A n) :=
    match v in vector _ n return prodn n with
      | Vnil => tt
      | Vcons x _ v' => (x, prod_of_vec v')
    end.

  (** Lexicographic relation on vectors. *)

  Definition lexv n (v w : vector A n) :=
    lexn n (prod_of_vec v) (prod_of_vec w).

  Lemma lexv_wf n : WF (@lexv n).

  Proof. apply WF_inverse. apply lexn_wf. Qed.

  Require Import NatUtil.

  (** Nth projection for n-tuples. *)

  Fixpoint projn n :=
    match n as n return prodn n -> forall i, i<n -> A with
      | 0 => fun xs i (hi : i<0) => False_rect _ (lt_n_0 hi)
      | S n' => fun xs i =>
        match i as i return i<S n' -> A with
          | 0 => fun _ => fst xs
          | S i' => fun hi => projn _ (snd xs) _ (lt_S_n hi)
        end
    end.

  Lemma projn_prod_of_vec : forall n (xs : vector A n) i (hi : i<n),
    projn (prod_of_vec xs) hi = Vnth xs hi.

  Proof. induction xs; intros i hi. omega. simpl. destruct i as [|i]; fo. Qed.

  Require Import Syntax.

  (** Equivalence definition of [lexn]. *)
 
  Lemma lexn_eq : forall n (xs ys : prodn n),
    lexn _ xs ys <-> (exists i (hi : i<n), gtA (projn xs hi) (projn ys hi)
      /\ forall j, j<i -> forall hj : j<n, eqA (projn xs hj) (projn ys hj)).

  Proof.
    induction n; simpl prodn.
    (* 0 *)
    intuition. destruct H as [i [hi _]]. omega.
    (* S *)
    intros [x xs] [y ys]. simpl lexn. split; intro h.
    (* -> *)
    inversion h; subst.
    exists 0 (lt_0_Sn n). split. simpl projn. hyp. intros. omega.
    rewrite IHn in H4. destruct H4 as [i [hi [h1 h2]]].
    exists (S i) (lt_n_S hi). split.
    simpl. rewrite lt_unique with (h1 := lt_S_n (lt_n_S hi)) (h2:=hi). hyp.
    intros [|j] k hj; simpl. hyp. apply h2. omega.
    (* <- *)
    destruct h as [i [hi [h1 h2]]]. destruct i as [|i].
    apply lex1. hyp. 
    apply lex2. gen (h2 _ (lt_0_Sn i) (lt_0_Sn n)). simpl. auto.
    rewrite IHn. exists i (lt_S_n hi). split. fo.
    intros j ji jn. gen (h2 _ (lt_n_S ji) (lt_n_S jn)). simpl.
    rewrite lt_unique with (h1 := lt_S_n (lt_n_S jn)) (h2:=jn). auto.
  Qed.

  (** Equivalence definition of [lexv]. *)

  Lemma lexv_eq : forall n (xs ys : vector A n),
    lexv xs ys <-> (exists i (hi : i<n), gtA (Vnth xs hi) (Vnth ys hi)
      /\ forall j, j<i -> forall hj : j<n, eqA (Vnth xs hj) (Vnth ys hj)).

  Proof.
    intros n xs ys. unfold lexv. rewrite lexn_eq.
    split; intros [i [hi [h1 h2]]]; exists i hi; split.
    rewrite !projn_prod_of_vec in h1. hyp.
    intros j ji hj. gen (h2 _ ji hj). rewrite !projn_prod_of_vec. auto.
    rewrite !projn_prod_of_vec. hyp.
    intros j ji hj. rewrite !projn_prod_of_vec. fo.
  Qed.

End lexn.
