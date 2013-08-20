(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2006-10-25

lexicographic ordering
*)

Set Implicit Arguments.

Require Import SN RelUtil LogicUtil Morphisms NatUtil VecUtil VecOrd Basics.

(****************************************************************************)
(** ** Lexicographic quasi-ordering on pairs. *)

Section lex.

  (** We assume given a set [A] equipped with two relations [gtA] and
  [eqA] satisfying some compatibility condition, and a set [B]
  equipped with a relation [gtB]. *)

  Variables (A B : Type) (gtA eqA : relation A) (gtB : relation B).

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
  are wellfounded, [eqA] is transitive and [gtA] absorbs [eqA]. *)

  Variables (WF_gtA : WF gtA) (WF_gtB : WF gtB)
    (eqA_trans : Transitive eqA) (Hcomp : eqA @ gtA << gtA).

  Lemma SN_compat : forall a, SN gtA a -> forall a', eqA a a' -> SN gtA a'.

  Proof.
    intros a SN_a a' eqaa'. apply SN_intro. intros a'' gta'a''.
    inversion SN_a. apply H. apply (inclusion_elim Hcomp). exists a'. auto.
  Qed.

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

  Lemma WF_lex : WF lex.

  Proof.
    unfold WF. destruct x as (a,b). apply lex_SN. apply WF_gtA. apply WF_gtB.
  Qed.

End lex.

(** [symprod] is included in [lex]. *)

Lemma symprod_lex A (gtA : relation A) :
  symprod gtA gtA << lex gtA Logic.eq gtA.

Proof.
  intros t u tu. inversion tu; clear tu; subst.
  apply lex1. hyp. apply lex2. refl. hyp.
Qed.

(** [lex] is monotone wrt inclusion. *)

Instance lex_incl A B :
  Proper (inclusion ==> inclusion ==> inclusion ==> inclusion) (@lex A B).

Proof.
  intros gtA gtA' gtAgtA' eqA eqA' eqAeqA' gtB gtB' gtBgtB' t u tu.
  inversion tu; clear tu; subst. apply lex1. fo. apply lex2; fo.
Qed.

Instance lex_same_rel A B :
  Proper (same_relation ==> same_relation ==> same_relation ==> same_relation)
  (@lex A B).

Proof.
  intros gtA1 gtA' [gtAgtA' gtA'gtA] eqA eqA' [eqAeqA' eqA'eqA]
    gtB gtB' [gtBgtB' gtB'gtB]. split; apply lex_incl; fo.
Qed.

(****************************************************************************)
(** ** Type of n-tuples of elements of [A]. *)

Fixpoint prodn n A : Type :=
  match n with
    | 0 => unit
    | S n' => prod A (prodn n' A)
  end.

Fixpoint projn n {A} :=
  match n as n return prodn n A -> forall i, i<n -> A with
    | 0 => fun xs i (hi : i<0) => False_rect _ (lt_n_0 hi)
    | S n' => fun xs i =>
      match i as i return i<S n' -> A with
        | 0 => fun _ => fst xs
        | S i' => fun hi => projn _ (snd xs) _ (lt_S_n hi)
      end
  end.

(****************************************************************************)
(** ** Lexicographic order on tuples. *)

Fixpoint lexn {n A} (eqA gtA : relation A) :=
  match n as n return relation (prodn n A) with
    | 0 => empty_rel
    | S n' => lex gtA eqA (lexn eqA gtA)
  end.

Section lexn.

  Variables (A : Type) (eqA gtA : relation A).

  (** Equivalent definition. *)
 
  Lemma lexn_eq : forall n (xs ys : prodn n A), lexn eqA gtA xs ys <->
    (exists i (hi : i<n), gtA (projn xs hi) (projn ys hi)
      /\ forall j, j<i -> forall hj : j<n, eqA (projn xs hj) (projn ys hj)).

  Proof.
    induction n; simpl prodn.
    (* 0 *)
    intuition. destruct H as [i [hi _]]. omega.
    (* S *)
    intros [x xs] [y ys]. simpl lexn. split; intro h.
    (* -> *)
    inversion h; clear h; subst.
    ex 0 (lt_0_Sn n). split. simpl projn. hyp. intros. omega.
    rewrite IHn in H4. destruct H4 as [i [hi [h1 h2]]].
    ex (S i) (lt_n_S hi). split.
    simpl. rewrite lt_unique with (h1 := lt_S_n (lt_n_S hi)) (h2:=hi). hyp.
    intros [|j] k hj; simpl. hyp. apply h2. omega.
    (* <- *)
    destruct h as [i [hi [h1 h2]]]. destruct i as [|i].
    apply lex1. hyp. 
    apply lex2. gen (h2 _ (lt_0_Sn i) (lt_0_Sn n)). simpl. auto.
    rewrite IHn. ex i (lt_S_n hi). split. fo.
    intros j ji jn. gen (h2 _ (lt_n_S ji) (lt_n_S jn)). simpl.
    rewrite lt_unique with (h1 := lt_S_n (lt_n_S jn)) (h2:=jn). auto.
  Qed.

  (** Wellfoundedness. *)

  Variables (gtA_wf : WF gtA) (eqA_trans : Transitive eqA)
    (Hcomp : eqA @ gtA << gtA).

  Lemma lexn_wf n : WF (lexn (n:=n) eqA gtA).

  Proof. induction n; simpl. apply WF_empty_rel. apply WF_lex; hyp. Qed.

End lexn.

(** Monotony wrt inclusion. *)

Instance lexn_incl : forall A n,
  Proper (inclusion ==> inclusion ==> inclusion) (@lexn n A). 

Proof.
  intro A. induction n; simpl. fo.
  intros eqA eqA' eqAeqA' gtA gtA' gtAgtA'. apply lex_incl; auto.
  apply IHn; hyp.
Qed.

(****************************************************************************)
(** ** Convert of vector of size [n] into an [n]-tuple. *)

Fixpoint prod_of_vec n A (v : vector A n) :=
  match v in vector _ n return prodn n A with
    | Vnil => tt
    | Vcons x _ v' => (x, prod_of_vec v')
  end.

Lemma projn_prod_of_vec : forall A n (xs : vector A n) i (hi : i<n),
  projn (prod_of_vec xs) hi = Vnth xs hi.

Proof.
  intro A. induction xs; intros i hi. omega. simpl. destruct i as [|i]; fo.
Qed.

(****************************************************************************)
(** ** Lexicographic order on vectors. *)

Definition lexv {n A} (eqA gtA : relation A) : relation (vector A n) :=
  fun v w => lexn eqA gtA (prod_of_vec v) (prod_of_vec w).

Section lexv.

  Variables (A : Type) (eqA gtA : relation A).

  (** Equivalent definition. *)

  Lemma lexv_eq : forall n (xs ys : vector A n), lexv eqA gtA xs ys <->
    (exists i (hi : i<n), gtA (Vnth xs hi) (Vnth ys hi)
      /\ forall j, j<i -> forall hj : j<n, eqA (Vnth xs hj) (Vnth ys hj)).

  Proof.
    intros n xs ys. unfold lexv. rewrite lexn_eq.
    split; intros [i [hi [h1 h2]]]; ex i hi; split.
    rewrite !projn_prod_of_vec in h1. hyp.
    intros j ji hj. gen (h2 _ ji hj). rewrite !projn_prod_of_vec. auto.
    rewrite !projn_prod_of_vec. hyp.
    intros j ji hj. rewrite !projn_prod_of_vec. fo.
  Qed.

  (** Wellfoundedness. *)

  Section wf.

    Variables (gtA_wf : WF gtA) (eqA_trans : Transitive eqA)
      (Hcomp : eqA @ gtA << gtA).

    Lemma lexv_wf n : WF (lexv (n:=n) eqA gtA).

    Proof. apply WF_inverse. apply lexn_wf; hyp. Qed.

  End wf.

  (** [lexv eqA gtA] absorbs [Vreln eqA]. *)

  Lemma lexv_reln_l : eqA @ gtA << gtA -> Transitive eqA ->
    forall n, Vreln (n:=n) eqA @ lexv eqA gtA << lexv eqA gtA.

  Proof.
    intros gtA_eqA eqA_trans n ts vs [us [tsus usvs]].
    revert usvs. rewrite !lexv_eq. intros [i [hi [h1 h2]]]. ex i hi. split.
    apply gtA_eqA. exists (Vnth us hi). split. apply Vforall2n_nth. hyp. hyp.
    intros j ji jn. trans (Vnth us jn). apply Vforall2n_nth. hyp. fo.
  Qed.

  Lemma lexv_reln_r : gtA @ eqA << gtA -> Transitive eqA ->
    forall n, lexv eqA gtA @ Vreln (n:=n) eqA << lexv eqA gtA.

  Proof.
    intros gtA_eqA eqA_trans n ts vs [us [tsus usvs]].
    revert tsus. rewrite !lexv_eq. intros [i [hi [h1 h2]]]. ex i hi. split.
    apply gtA_eqA. exists (Vnth us hi). split. hyp. apply Vforall2n_nth. hyp.
    intros j ji jn. trans (Vnth us jn). fo. apply Vforall2n_nth. hyp.
  Qed.

  (** [lexv eqA gtA] is invariant by [Vreln eqA]. *)

  Global Instance lexv_reln n : Transitive eqA -> Symmetric eqA ->
    Proper (eqA ==> eqA ==> impl) gtA ->
    Proper (Vreln eqA ==> Vreln eqA ==> impl) (lexv (n:=n) eqA gtA).

  Proof.
    intros eqA_trans eqA_sym gtA_eqA ts ts' tsts' us us' usus'; unfold impl.
    rewrite !lexv_eq. intros [i [i1 [i2 i3]]]. ex i i1. split.
    eapply gtA_eqA. apply Vreln_nth_intro. apply tsts'.
    apply Vreln_nth_intro. apply usus'. hyp.
    intros j ji jn.
    rewrite <- (Vreln_nth_intro tsts'), <- (Vreln_nth_intro usus'). fo.
  Qed.

  (** Transitivity. *)

  Lemma lexv_trans n : Transitive eqA -> Transitive gtA ->
    gtA @ eqA << gtA -> eqA @ gtA << gtA ->
    Transitive (lexv (n:=n) eqA gtA).

  Proof.
    intros eqA_trans gtA_trans gtA_eqA_r gtA_eqA_l ts us vs. rewrite !lexv_eq.
    intros [i [i1 [i2 i3]]] [j [j1 [j2 j3]]]. destruct (lt_dec i j).
    (* i < j *)
    ex i i1. split. apply gtA_eqA_r. exists (Vnth us i1). fo.
    intros k ki kn. trans (Vnth us kn). fo. apply j3. omega.
    destruct (eq_nat_dec i j).
    (* i = j *)
    subst j. ex i i1. split.
    trans (Vnth us i1). hyp. rewrite !(Vnth_eq _ i1 j1); auto.
    intros k ki kn. trans (Vnth us kn); fo.
    (* i > j *)
    ex j j1. split. apply gtA_eqA_l. exists (Vnth us j1). split. fo. hyp.
    intros k kj kn. trans (Vnth us kn). apply i3. omega. fo.
  Qed.

End lexv.

(** Monotony wrt inclusion. *)

Instance lexv_incl n A :
  Proper (inclusion ==> inclusion ==> inclusion) (@lexv n A). 

Proof. intros eqA eqA' eqAeqA' gtA gtA' gtAgtA' t u. apply lexn_incl; hyp. Qed.

(** [Vrel1] is included in [lexv]. *)

Lemma Vrel1_lexv n A (gtA : relation A) :
  Vrel1 (n:=n) gtA << lexv Logic.eq gtA.

Proof.
  intros t u. rewrite Vrel1_nth_iff, lexv_eq. intros [i [hi [h1 h2]]].
  ex i hi. fo.
Qed.
