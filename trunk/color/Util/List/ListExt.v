(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-28

Extensions of the Coq library on lists
*)

(* $Id: ListExt.v,v 1.5 2007-08-07 09:23:36 blanqui Exp $ *)

Set Implicit Arguments.

Require Export List.
Require Import NatUtil.
Require Omega.

Section ListsGeneral.

  Variable A: Type.

  Lemma list_empty_dec : forall l : list A, {l = nil} + {l <> nil}.

  Proof.
    destruct l; auto.
    right; congruence.
  Qed.

  Lemma list_app_first_last : forall l m (a : A),
    (l ++ a::nil) ++ m = l ++ a::m.

  Proof.
    induction l.
    auto.
    intros m a'.
    repeat rewrite <- app_comm_cons.
    destruct (IHl m a'); trivial.
  Qed.

  Lemma list_app_last : forall l m n (a : A),
    l ++ m = n ++ a::nil -> m <> nil -> In a m.

  Proof.
    intros l m n; generalize n l m; clear l m n.
    induction n; simpl; intros.
     (* induction base *)
    destruct l.
    simpl in H; rewrite H; auto with datatypes.
    inversion H.
    absurd (m = nil); trivial.
    apply (proj2 (app_eq_nil l m H3)).
     (* induction case *)
    destruct l.
    simpl in H; rewrite H; auto with datatypes.
    inversion H.
    apply IHn with l; trivial.
  Qed.

  Lemma list_drop_last : forall l m n (a : A),
    l ++ m = n ++ a::nil -> m <> nil -> exists2 w, incl w m & l ++ w = n.

  Proof.
    induction l; intros.
     (* induction base *)
    simpl in H.
    exists n.
    rewrite H; auto with datatypes.
   auto.
     (* induction case *)
    destruct n.
     (*   n = nil -> contradiction *)
    simpl in H.
    destruct (app_eq_unit (a::l) m H) as 
      [[l_nil r_unit] | [l_unit r_nil]]; try contradiction.
    discriminate.
     (*   n <> nil *)    
    inversion H.
    destruct (IHl m n a0); trivial.
    exists x; trivial.
    rewrite <- H4.
    auto with datatypes.
  Qed.

  Lemma tail_in : forall (x: A) l, In x (tail l) -> In x l.

  Proof.
    intros.
    destruct l; auto with datatypes.
  Qed.

  Lemma tail_cons_tail : forall (l1 l2: list A),
    l1 <> nil -> tail l1 ++ l2 = tail (l1 ++ l2).

  Proof.
    destruct l1.
    tauto.
    auto.
  Qed.

  Lemma length_tail : forall (l : list A), length (tail l) = length l - 1.

  Proof.
    destruct l; simpl; omega.
  Qed.

  Definition head_notNil : forall (l : list A) (lne : l <> nil),
    {a : A | head l = Some a}.

  Proof.
    destruct l.
    tauto.
    exists a; auto.
  Defined.

  Lemma head_of_notNil : forall (l : list A) a (lne: l <> nil),
    head l = Some a -> proj1_sig (head_notNil lne) = a.

  Proof.
    intros.
    destruct l; try discriminate.
    simpl; inversion H; trivial.
  Qed.

  Lemma head_app : forall (l l': list A)(lne: l <> nil), head (l ++ l') = head l.

  Proof.
    destruct l.
    tauto.
    auto.
  Qed.

  Lemma list_decompose_head : forall (l : list A) el (lne: l <> nil),
    head l = Some el -> l = el :: tail l.

  Proof.
    intros.
    destruct l.
    discriminate.
    inversion H.
    rewrite <- H1; trivial.
  Qed.

  Lemma length_app : forall (l m: list A), length (l ++ m) = length l + length m.

  Proof.
    induction l.
    trivial.
    intro m.
    simpl.
    rewrite (IHl m); trivial.
  Qed.

  Lemma in_head_tail : forall a (l : list A),
    In a l -> Some a = head l \/ In a (tail l).

  Proof.
    induction l; intros; inversion H.
    left; simpl; rewrite H0; trivial.
    right; trivial.
  Qed.

End ListsGeneral.

Hint Resolve tail_in tail_cons_tail head_app : datatypes.
Hint Rewrite head_app length_app : datatypes.

Section ListsNth.

  Variable A: Type.

  Lemma nth_error_In : forall (l : list A) i, 
    {a : A | nth_error l i = Some a} + {nth_error l i = None}.

  Proof.
    induction l.
    right; compute; case i; trivial.
    intro i.
    case i.
    left; exists a; trivial.
    intro n.
    destruct (IHl n) as [[a' a'nth] | nth_none].
    left; exists a'; trivial.
    right; trivial.
  Qed.

  Lemma nth_some_in : forall (l : list A) i a, nth_error l i = Some a -> In a l.

  Proof.
    induction l; intros.
    destruct i; simpl in *; discriminate.
    destruct i; simpl in *.
    left; compute in *; congruence.
    right; eapply IHl; eauto.
  Qed.

  Lemma list_In_nth : forall (l : list A) a,
    In a l -> exists p: nat, nth_error l p = Some a.

  Proof.
    induction l.
    contradiction.
    intros; destruct H.
    exists 0.
    rewrite H; trivial.
    destruct (IHl a0 H).
    exists (S x); trivial.
  Qed.

  Lemma nth_app_left : forall (l m: list A) i,
    i < length l -> nth_error (l ++ m) i = nth_error l i.

  Proof.
    induction l; simpl; intros m i i_l.
    absurd_arith.
    destruct i; simpl.
    trivial.
    apply (IHl m i).
    auto with arith.
  Qed.

  Lemma nth_app_right : forall (l m: list A) i, i >= length l ->
     nth_error (l ++ m) i = nth_error m (i - length l).

  Proof.
    induction l; simpl; intros m i i_l.
    auto with arith.
    destruct i; simpl.
    absurd_arith.
    apply IHl.
    auto with arith.
  Qed.

  Lemma nth_app : forall (l m: list A) a i, nth_error (l ++ m) i = Some a ->
    (nth_error l i = Some a /\ i < length l) \/ 
    (nth_error m (i - length l) = Some a /\ i >= length l).

  Proof.
    intros.
    destruct (le_lt_dec (length l) i).
    right; split; trivial.
    rewrite (nth_app_right l m l0) in H; trivial.
    left; split; trivial.
    rewrite (nth_app_left l m l0) in H; trivial.
  Qed.

  Lemma nth_beyond : forall (l : list A) i,
    i >= length l -> nth_error l i = None.

  Proof.
    induction l; simpl; intro i.
    destruct i; trivial.
    destruct i; simpl.
    intros.
    absurd_arith.
    intro.
    rewrite (IHl i); trivial.
    auto with arith.
  Qed.

  Lemma nth_beyond_idx : forall (l : list A) i,
    nth_error l i = None -> i >= length l.

  Proof.
    induction l; simpl; intro i.
    auto with arith.
    destruct i; simpl.
    intros.
    discriminate.
    intro.
    assert (i >= length l).
    apply (IHl i); trivial.
    auto with arith.
  Qed.

  Lemma nth_in : forall (l : list A) i,
    nth_error l i <> None <-> i < length l.

  Proof.
    induction l; simpl; intro i.
    split.
    destruct i; intro; elimtype False; auto.
    intro; absurd_arith.
    destruct i; simpl.
    split; intro.
    auto with arith.
    discriminate.
    split; intro.
    assert (i < length l).
    apply (proj1 (IHl i)); trivial.
    auto with arith.
    apply (proj2 (IHl i)); auto with arith.
  Qed.

  Lemma nth_some : forall (l : list A) n a,
    nth_error l n = Some a -> n < length l.

  Proof.
    intros.
    apply (proj1 (nth_in l n)).
    rewrite H; discriminate.
  Qed.

  Lemma nth_map_none : forall (l : list A) i (f: A -> A),
    nth_error l i = None -> nth_error (map f l) i = None.

  Proof. 
    induction l.
    trivial.
    intros i f; destruct i; simpl.
    intro; discriminate.
    apply IHl.
  Qed.

  Lemma nth_map_none_rev : forall (l : list A) i (f: A -> A),
    nth_error (map f l) i = None -> nth_error l i = None.

  Proof.
    induction l.
    trivial.
    intros i f; destruct i; simpl.
    intro; discriminate.
    apply IHl.
  Qed.

  Lemma nth_map_some : forall (l : list A) i (f: A -> A) a,
    nth_error l i = Some a -> nth_error (map f l) i = Some (f a).

  Proof.
    induction l.
    destruct i; intros; discriminate.
    intros i f a'.
    destruct i; simpl.
    intro aa'; inversion aa'; trivial.
    apply IHl.
  Qed.

  Lemma nth_map_some_rev : forall (l : list A) i (f: A -> A) a,
    nth_error (map f l) i = Some a ->
    exists a', nth_error l i = Some a' /\ f a' = a.

  Proof.
    induction l.
    destruct i; intros; discriminate.
    intros i f a'.
    destruct i; simpl.
    intros aa'; inversion aa'; exists a; auto.
    apply IHl.
  Qed.

  Lemma nth_error_singleton_in : forall (a b: A) i,
    nth_error (a :: nil) i = Some b -> a = b /\ i = 0.

  Proof.
    intros.
    destruct i.
    inversion H; auto.
    inversion H; destruct i; discriminate.
  Qed.

End ListsNth.
