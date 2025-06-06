(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-28

Some results concerning permutations of lists.
*)

Set Implicit Arguments.

From Stdlib Require Import Setoid Morphisms Basics.
From CoLoR Require Import ListExtras NatUtil LogicUtil.
From Stdlib Require Export Permutation PermutSetoid Multiset.

Arguments list_contents [A eqA] _ _.
Arguments permutation [A eqA] _ _ _.

Section Multiplicity.

  Variables
    (A : Type) (eqA : relation A)
    (eqA_dec : forall x y, {eqA x y} + {~eqA x y})
    (eqA_Equivalence : Equivalence eqA).

  Lemma multiplicity_in: forall l x,
    multiplicity (list_contents eqA_dec l) x > 0 ->
    exists x', eqA x' x /\ In x' l.

  Proof.
    induction l; simpl; intros.
    lia.
    destruct (eqA_dec a x).
    exists a; auto.
    destruct (IHl x) as [x' [x'x x'l]]; trivial.
    exists x'; split; auto.
  Qed.

  Lemma in_multiplicity: forall l a,
    In a l ->
    multiplicity (list_contents eqA_dec l) a > 0.

  Proof.
    induction l; simpl; intros.
    lia.
    destruct H.
    destruct (eqA_dec a a0).
    lia.
    absurd (eqA a a0); trivial.
    rewrite H; intuition auto with *.
    set (w := IHl a0 H); lia.
  Qed.

  Lemma multiplicity_countIn: forall l el,
    multiplicity (list_contents eqA_dec l) el = countIn eqA eqA_dec el l.

  Proof.
    induction l; simpl; intros; trivial.
    destruct (eqA_dec a el); destruct (eqA_dec el a).
    rewrite IHl; lia.
    absurd (eqA el a); intuition auto with *.
    absurd (eqA a el); intuition auto with *.
    rewrite IHl; lia.
  Qed.

  Lemma multiplicity_dropNth_eq: forall l p el el',
    nth_error l p = Some el' ->
    eqA el el' ->
    multiplicity (list_contents eqA_dec (drop_nth l p)) el = 
    multiplicity (list_contents eqA_dec l) el - 1. 

  Proof.
    intros.
    rewrite !multiplicity_countIn.
    apply countIn_dropNth_eq with el'; trivial.
  Qed.

  Lemma multiplicity_dropNth_neq: forall l p el el',
    nth_error l p = Some el' ->
    ~eqA el el' ->
    multiplicity (list_contents eqA_dec (drop_nth l p)) el = 
    multiplicity (list_contents eqA_dec l) el. 

  Proof.
    intros.
    rewrite !multiplicity_countIn.
    apply countIn_dropNth_neq with el'; trivial.
  Qed.

End Multiplicity.

Section Permutation.

  Variables
    (A : Type) (eqA : relation A)
    (eqA_dec : forall x y, {eqA x y} + {~eqA x y})
    (eqA_Equivalence : Equivalence eqA).

  Lemma permutation_sym: forall l l',
    permutation eqA_dec l l' -> permutation eqA_dec l' l.

  Proof. intros; intro; auto. Qed.

  Lemma permutation_in: forall l l' a, permutation eqA_dec l l' ->
    In a l -> exists a', eqA a' a /\ In a' l'.

  Proof.
    intros.
    destruct (multiplicity_in eqA eqA_dec l' a) as [a' [aa' a'l']].
    rewrite <- (H a); trivial.
    apply in_multiplicity; trivial.
    exists a'; split; trivial.
  Qed.

  Lemma permutation_drop: forall (l l': list A) a b p,
    eqA a b -> nth_error l' p = Some b ->
    permutation eqA_dec (a :: l) l' -> permutation eqA_dec l (drop_nth l' p).

  Proof.
    intros; intro el.
    destruct (eqA_dec a el).
    assert (eqA el b).
    apply (Seq_trans A eqA eqA_Equivalence) with a; intuition auto with *.
    rewrite (multiplicity_dropNth_eq eqA_dec eqA_Equivalence l' p el H0 H2).
    set (w := H1 el); simpl in w.
    replace (if eqA_dec a el then 1 else 0) with 1 in w.
    lia.
    clear w; destruct (eqA_dec a el); [trivial | contr].
    assert (~eqA el b).
    intro elb.
    absurd (eqA a el); trivial.
    apply (Seq_trans A eqA eqA_Equivalence) with b; intuition auto with *.
    rewrite (multiplicity_dropNth_neq eqA_dec eqA_Equivalence l' p el H0 H2).
    set (w := H1 el); simpl in w.
    replace (if eqA_dec a el then 1 else 0) with 0 in w.
    lia.
    clear w; destruct (eqA_dec a el); [contr | trivial].
  Qed.

  Lemma permutation_cons: forall l l' a,
    permutation eqA_dec (a :: l) l' ->
    exists p a',
      nth_error l' p = Some a' /\
      eqA a a' /\
      permutation eqA_dec l (drop_nth l' p).

  Proof.
    intros.
    destruct (permutation_in a H) as [a' [aa' a'l']].
    auto with datatypes.
    destruct (list_In_nth l' a' a'l') as [p l'p].
    exists p; exists a'; split; [idtac | split]; trivial.
    intuition auto with *.
    apply permutation_drop with a a'; trivial.
    intuition auto with *.
  Qed.

  Lemma permutation_length: forall (l l': list A),
    permutation eqA_dec l l' ->
    length l = length l'.

  Proof.
    induction l; intros.
     (* base *)
    simpl.
    destruct l'; trivial.
    unfold permutation in H.
    exfalso.
    assert (w := H a); simpl in w; clear H.
    destruct (eqA_dec a a).
    lia.
    intuition auto with *.
     (* step *)
    destruct (permutation_cons H) as [p [a' [l'p [aa' ll'p]]]].
    simpl.
    rewrite (IHl (drop_nth l' p)); trivial.
    set (w := nth_some l' p l'p).
    rewrite drop_nth_in_length; trivial.
    lia.
  Qed.

  Lemma insert_nth_permut: forall (l: list A) el n,
    permutation eqA_dec (insert_nth l n el) (el::l). 

  Proof.
    induction l; intros.
    unfold insert_nth, finalSeg; destruct n; simpl; apply permut_refl.
    destruct n; unfold insert_nth; simpl.
    rewrite finalSeg_full; apply permut_refl.
    unfold finalSeg; simpl.
    fold (finalSeg l n); fold (insert_nth l n el).
    apply permut_tran with (a :: el :: l).
    apply permut_cons.
    apply IHl.
    change (el :: a :: l) with ((el :: nil) ++ a :: l).
    change (a :: el :: l) with (a :: (el :: nil) ++ l).
    apply permut_middle.
  Qed.

  Lemma insert_nth_permut': forall (l l': list A) el n,
    permutation eqA_dec l l' ->
    permutation eqA_dec (insert_nth l n el) (el::l'). 

  Proof.
    intros; intro w.
    unfold insert_nth.
    change (el :: finalSeg l n) with ((el :: nil) ++ finalSeg l n).
    change (el :: l') with ((el :: nil) ++ l').
    rewrite !list_contents_app.
    simpl.
    rewrite Nat.add_0_r.
    match goal with
    | |- ?a + (?b + ?c) = ?d => replace (a + (b + c)) with (a + c + b)
    end.
    replace (multiplicity (list_contents eqA_dec (initialSeg l n)) w + 
      multiplicity (list_contents eqA_dec (finalSeg l n)) w) 
    with (multiplicity
      (list_contents eqA_dec (initialSeg l n ++ finalSeg l n)) w).
    rewrite initialSeg_finalSeg_full; trivial.
    rewrite (H w); auto with arith.
    rewrite list_contents_app; trivial.
    lia.
  Qed.

End Permutation.

Section ListSim.

  Variable A : Type.
  Variable B : Type.
  Variable R : A -> B -> Prop.

  Inductive list_sim: list A -> list B -> Prop :=
  | conv_empty: 
      list_sim nil nil
  | conv_cons: forall x y xs ys,
      R x y ->
      list_sim xs ys ->
      list_sim (x::xs) (y::ys).

  Lemma list_sim_nth : forall p l l' a, list_sim l l' ->
    nth_error l p = Some a ->
    exists b, nth_error l' p = Some b /\ R a b.

  Proof.
    induction p.
    intros.
    inversion H.
    rewrite <- H1 in H0; discr.
    exists y; split; auto.
    replace a with x; trivial.
    rewrite <- H3 in H0; inversion H0; trivial.
    intros.
    destruct l; destruct l'; try discr.
    inversion H.
    inversion H.
    destruct (IHp l l' a); trivial.
    destruct H7.
    exists x0; split; trivial.
  Qed.

  Lemma list_sim_nth_rev : forall p l l' b, list_sim l l' ->
    nth_error l' p = Some b ->
    exists a, nth_error l p = Some a /\ R a b.

  Proof.
    induction p.
    intros.
    inversion H.
    rewrite <- H2 in H0; discr.
    exists x; split; auto.
    replace b with y; trivial.
    rewrite <- H4 in H0; inversion H0; trivial.
    intros.
    destruct l; destruct l'; try discr.
    inversion H.
    inversion H.
    destruct (IHp l l' b); trivial.
    destruct H7.
    exists x0; split; trivial.
  Qed.

  Lemma list_sim_app : forall l1 l1' l2 l2',
    list_sim l1 l1' -> list_sim l2 l2' -> list_sim (l1 ++ l2) (l1' ++ l2').

  Proof.
    induction l1; intros.
    inversion H; trivial.
    inversion H.
    simpl; constructor; trivial.
    apply IHl1; trivial.
  Qed.

  Lemma list_sim_unique : forall l m m',
    (forall x y y', In x l -> In y m -> In y' m' ->
      R x y -> R x y' -> y = y') ->
    list_sim l m -> list_sim l m' -> m = m'.

  Proof.
    induction l; intros; inversion H0; inversion H1; trivial.
    rewrite (H x y y0).
    rewrite (IHl ys ys0); trivial.
    intros.
    destruct (list_In_nth l x1 H12) as [p lp].    
    apply H with x1; trivial.
    right; trivial.
    rewrite <- H5; right; trivial.
    rewrite <- H10; right; trivial.
    rewrite H2; auto with datatypes.
    rewrite <- H5; left; trivial.
    rewrite <- H10; left; trivial.
    rewrite H2; trivial.
    rewrite H2; trivial.
  Qed.

  Lemma list_sim_insert_nth : forall p l l' a a', nth_error l p = Some a ->
    nth_error l' p = Some a' -> R a a' ->
    list_sim (drop_nth l p) (drop_nth l' p) -> list_sim l l'.

  Proof.
    induction p; intros.
     (* induction base *)
    destruct l; destruct l'.
    constructor.
    inversion H2; discr.
    inversion H2; discr.
    constructor.
    inversion H; inversion H0; trivial.
    rewrite !drop_nth_cons in H2; trivial.
     (* induction step *)
    destruct l; destruct l'.
    constructor.
    inversion H2; discr.
    inversion H2; discr.
    rewrite !drop_nth_succ in H2.
    inversion H2.
    constructor; trivial.
    apply IHp with a a'; trivial.
  Qed.

  Lemma list_sim_length : forall l l', list_sim l l' -> length l = length l'.

  Proof.
    induction l; intros.
    inversion H; trivial.
    destruct l'.
    inversion H.
    simpl.
    rewrite (IHl l'); trivial.
    inversion H; trivial.
  Qed.

  Lemma list_sim_tail : forall l l',
    list_sim l l' -> list_sim (tail l) (tail l').

  Proof.
    intros.
    destruct H; trivial.
    simpl; constructor.
  Qed.

End ListSim.

Section ListSim_iso.

  Variables
    (A : Type) (P eqA : relation A)
    (eqA_dec : forall x y, {eqA x y} + {~eqA x y})
    (eqA_Equivalence : Equivalence eqA)
    (P_eqA_comp : Proper (eqA ==> eqA ==> impl) P).

  Definition list_simA := @list_sim A A P.

  Lemma list_sim_permutation : forall l l' m,
    list_simA l l' -> permutation eqA_dec l m ->
    exists m', list_simA m m' /\ permutation eqA_dec l' m'.

  Proof.
    unfold Setoid_Theory in eqA_Equivalence.
    induction l; intros.
     (* induction base *)
    exists (nil (A:=A)); split.
    destruct m.
    constructor.
    set (w := H0 a); inversion w.
    destruct (eqA_dec a a).
    lia.
    absurd (eqA a a); intuition auto with *.
    inversion H.
    apply permut_refl.
     (* induction step *)
    destruct l'.
    inversion H.
    destruct (permutation_cons eqA_Equivalence H0) as [p [a' [mp [aa' lm]]]].
    destruct (IHl l' (drop_nth m p)) as [m' [mm' l'm']]; trivial.
    inversion H; trivial.
    assert (length m' >= p).
    rewrite <- (list_sim_length mm').
    set (h := nth_some m p mp).
    set (w := drop_nth_length m p).
    lia.
    exists (insert_nth m' p a0); split.
    unfold list_simA; apply list_sim_insert_nth with p a' a0; trivial.
    apply nth_insert_nth; trivial.
    apply P_eqA_comp with a a0; intuition auto with *.
    inversion H; intuition.
    rewrite drop_nth_insert_nth; trivial.
    apply permutation_sym.
    apply insert_nth_permut'.
    apply permutation_sym; trivial.
  Qed.

End ListSim_iso.
