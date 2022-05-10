(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Adam Koprowski, 2006-04-28

Some additional functions on lists.
*)

Set Implicit Arguments.

From CoLoR Require Export ListUtil.
From Coq Require Import Min Permutation Setoid.
From CoLoR Require Import NatUtil LogicUtil.

(***********************************************************************)
(** initial segment of a list *)

Section InitialSeg.

  Variable A : Type.

  Fixpoint initialSeg (l: list A) (size: nat) {struct size} : list A :=
  match size, l with
  | O, _ => nil
  | _, nil => nil
  | S n, hd::tl => hd :: initialSeg tl n
  end.

  Lemma initialSeg_full : forall l n, n >= length l -> initialSeg l n = l.

  Proof.
    induction l.
    destruct n; trivial.
    simpl.
    intros n n_l.
    destruct n.
    lia.
    simpl.
    rewrite IHl; trivial.
    auto with arith.
  Qed.

  Lemma initialSeg_length : forall (l: list A) size, 
    length (initialSeg l size) = min size (length l).

  Proof.
    induction l; intro size.
    destruct size; trivial.
    destruct size; simpl.
    trivial.
    rewrite IHl; trivial.
  Qed.

  Lemma initialSeg_nth : forall (l: list A) size x, x < size ->
    nth_error (initialSeg l size) x = nth_error l x.

  Proof.
    induction l; intros size x x_size.
    destruct size; trivial.
    destruct size; simpl.
    lia.
    destruct x; simpl.
    trivial.
    apply IHl.
    auto with arith.
  Qed.

  Lemma initialSeg_prefix : forall (l: list A) x p el,
    nth_error (initialSeg l x) p = Some el -> nth_error l p = Some el.

  Proof.
    induction l; intros.
    destruct x; trivial.
    destruct x.
    destruct p; discr.
    inversion H.
    destruct p; trivial.
    rewrite H1.
    simpl; apply IHl with x; trivial.
  Qed.

  Lemma initialSeg_app : forall l l' n,
    n <= length l -> initialSeg (l ++ l') n = initialSeg l n.

  Proof.
    induction l; intros.
    destruct n; simpl; trivial.
    simpl in H; lia.
    destruct n; simpl; trivial.
    rewrite (IHl l' n); trivial.
    simpl in H; lia.
  Qed.

End InitialSeg.

(***********************************************************************)
(** sublist *)

Section Seg.

  Variable A : Type.

  Fixpoint seg (l: list A) (from size : nat) {struct from} : list A := 
  match from, l with
  | 0, _ => initialSeg l size
  | _, nil => nil
  | S n, hd::tl => seg tl n size
  end.

  Lemma seg_tillEnd : forall l m n,
    n >= length l - m -> seg l m n = seg l m (length l - m).

  Proof.
    induction l.
    destruct m; destruct n; trivial.
    destruct m; destruct n; simpl; try solve
      [intro x; lia].
    intro n_l; do 2 (rewrite initialSeg_full; [idtac | lia]); trivial.
    apply IHl.
    intro n_m; rewrite (IHl m (S n)); trivial.
  Qed.

  Lemma seg_nth : forall (l: list A) i j x,
    x < j -> nth_error (seg l i j) x = nth_error l (i + x).

  Proof.
    induction l.
    destruct i; destruct j; destruct x; trivial.
    intros i j x x_j.
    destruct i; simpl.
    destruct j; destruct x; simpl; try solve [lia | trivial].
    change x at 2 with (0 + x).
    assert (xj: x < j).
    auto with arith.
    rewrite <- (IHl 0 j x xj); trivial.
    apply IHl; trivial.
  Qed.

  Lemma seg_exceeded l k n : n >= length l -> seg l k n = seg l k (length l).

  Proof.
    intro. rewrite seg_tillEnd, (@seg_tillEnd l k (length l)); trivial; lia.
  Qed.

End Seg.

(***********************************************************************)
(** final segment of a list *)

Section FinalSeg.

  Variable A: Type.

  Definition finalSeg (l: list A) fromPos
    := seg l fromPos (length l - fromPos).

  Lemma finalSeg_full l : finalSeg l 0 = l.

  Proof. unfold finalSeg; simpl. rewrite initialSeg_full; trivial. lia. Qed.

  Lemma finalSeg1_tail : forall l, finalSeg l 1 = tail l.

  Proof.
    destruct l; unfold finalSeg; simpl; trivial.
    rewrite initialSeg_full; trivial.
    lia.
  Qed.

  Lemma finalSeg_empty : forall l k, k >= length l -> finalSeg l k = nil.

  Proof.
    induction l.
    destruct k; trivial.
    intros k k_al.
    destruct k.
    simpl in k_al.
    lia.
    unfold finalSeg; simpl.
    fold (finalSeg l k).
    apply IHl.
    simpl in k_al.
    lia.
  Qed.

  Lemma finalSeg_cons : forall a l, finalSeg (a::l) 1 = l.

  Proof.
    intros.
    unfold finalSeg; simpl.
    rewrite initialSeg_full; trivial.
    lia.
  Qed.

  Lemma nth_finalSeg_nth: forall l k p,
    nth_error (finalSeg l k) p = nth_error l (k + p).
  Proof.
    intros l k; revert l.
    induction k; intros; simpl.
    rewrite finalSeg_full; trivial.
    destruct l.
    destruct p; trivial.
    rewrite <- IHk; trivial.
  Qed.

  Lemma finalSeg_nth_nth : forall l k p, p >= k ->
    nth_error l p = nth_error (finalSeg l k) (p - k).

  Proof.
    intros.
    rewrite nth_finalSeg_nth.
    replace (k + (p - k)) with p; trivial.
    lia.
  Qed.

  Lemma finalSeg_length : forall l k, length (finalSeg l k) = length l - k.

  Proof.
    induction l.
    destruct k; trivial.
    destruct k; trivial.
    simpl.
    rewrite initialSeg_full; trivial.
    lia.
    unfold finalSeg; simpl.
    fold (finalSeg l k).
    apply IHl.
  Qed.

  Lemma finalSeg_app_right : forall (l: list A) k n, n > length l ->
    finalSeg (l ++ k) n = finalSeg k (n - length l).

  Proof.
    induction l; intros.    
    simpl; replace (n - 0) with n; [trivial | lia].
    destruct n.
    lia.
    unfold finalSeg; simpl.
    fold (finalSeg (l ++ k) n).
    rewrite (IHl k n).
    unfold finalSeg; trivial.
    simpl in H; lia.
  Qed.

  Lemma finalSeg_nth_idx : forall l i j a,
    nth_error (finalSeg l i) j = Some a -> length l > i + j.

  Proof.
    induction l; unfold finalSeg; intros.
    destruct i; destruct j; inversion H.
    destruct i.
    destruct j.
    simpl; lia.
    simpl in *; rewrite initialSeg_full in H; auto with arith.
    set (w := nth_some l j H); lia.
    simpl in * .
    assert (length l > i + j).
    apply IHl with a0; trivial.
    lia.
  Qed.

  Lemma initialFinalSeg_length : forall l k,
    length (initialSeg l k) + length (finalSeg l k) = length l.

  Proof.
    intros.
    rewrite initialSeg_length, finalSeg_length.
    destruct (Compare_dec.le_gt_dec k (length l)); 
      solve [rewrite min_l; lia | rewrite min_r; lia].
  Qed.

  Lemma initialSeg_finalSeg_full : forall l k,
    initialSeg l k ++ finalSeg l k = l.

  Proof.
    intros l k; revert l; induction k.
    simpl; apply finalSeg_full.
    destruct l; trivial.
    unfold finalSeg; simpl.
    fold (finalSeg l k).
    rewrite IHk; trivial.
  Qed.

End FinalSeg.

(***********************************************************************)
(** create copies of an element *)

Section Copy.

  Variable A : Type.

  Fixpoint copy (n : nat) (el : A) : list A := 
  match n with
  | 0 => nil
  | S n => el :: copy n el
  end.

  Lemma copy_split : forall a m n, copy (m + n) a = copy m a ++ copy n a.

  Proof.
    induction m.
    trivial.
    intro n; simpl.
    rewrite (IHm n); trivial.
  Qed.

  Lemma copy_length : forall n el, length (copy n el) = n.

  Proof.
    induction n.
    trivial.
    intro el; simpl.
    rewrite IHn; trivial.
  Qed.

  Lemma copy_in : forall n el x, In x (copy n el) -> x = el.

  Proof.
    induction n.
    contr.
    destruct 1.
    auto.
    apply IHn; trivial.
  Qed.

  Lemma nth_copy_in : forall n el x,
    x < n -> nth_error (copy n el) x = Some el.

  Proof.
    intros sn el x x_n.
    destruct (nth_error_In (copy sn el) x) as [[es es_nth] | en].
    rewrite es_nth, (copy_in sn el es); trivial.
    eapply nth_some_in; eauto.
    assert (x >= length (copy sn el)).
    apply nth_beyond_idx; trivial.
    rewrite copy_length in H.
    absurd (x < sn); auto with arith.
  Qed.

  Lemma nth_after_copy : forall n el el',
    nth_error (copy n el' ++ el::nil) n = Some el.

  Proof.
    intros.
    rewrite nth_app_right, copy_length.
    replace (n - n) with 0; [trivial | lia].
    rewrite copy_length.
    auto with arith.
  Qed.

  Lemma copy_cons : forall n el, el :: copy n el = copy (S n) el.

  Proof.
    trivial.
  Qed.

  Lemma copy_add : forall n el l, el :: copy n el ++ l = copy n el ++ el :: l.

  Proof.
    induction n; trivial.
    simpl.
    intros el l.
    rewrite IHn; trivial.
  Qed.

  Lemma initialSeg_copy : forall el n k,
    initialSeg (copy n el) k = copy (min n k) el.

  Proof.
    induction n; destruct k; intros; simpl; trivial.
    rewrite IHn; trivial.
  Qed.

  Lemma finalSeg_copy : forall l el k n, k <= n ->
     finalSeg (copy n el ++ l) k = copy (n - k) el ++ l.

  Proof.
    induction k; intros.
    rewrite finalSeg_full.
    replace (n - 0) with n; [trivial | lia].
    destruct n.
    lia.
    unfold finalSeg; simpl.
    fold (finalSeg (copy n el ++ l) k).
    rewrite IHk; trivial.
    lia.
  Qed.

End Copy.

(***********************************************************************)
(** insert an element *)

Section InsertNth.

  Variable A : Type.

  Definition insert_nth (l: list A) (n: nat) (el: A) : list A :=
    initialSeg l n ++ el :: finalSeg l n.

  Lemma insert_nth_step : forall a l n el,
    insert_nth (a :: l) (S n) el = a :: insert_nth l n el.

  Proof.
    trivial.
  Qed.

  Lemma nth_insert_nth : forall l p el,
    length l >= p -> nth_error (insert_nth l p el) p = Some el.

  Proof.
    induction l; simpl; intros.
    destruct p; trivial.
    lia.
    destruct p; trivial.
    simpl.
    unfold finalSeg; simpl.
    fold (finalSeg l p); fold (insert_nth l p el).
    apply IHl.
    lia.
  Qed.

End InsertNth.

(***********************************************************************)
(** erase an element *)

Section DropNth.

  Variable A : Type.

  Definition drop_nth (l: list A) n := initialSeg l n ++ finalSeg l (S n).

  Lemma drop_nth_in_length : forall p l,
    length l > p -> length (drop_nth l p) = pred (length l).

  Proof.
    induction p; destruct l; auto; intros.
    unfold drop_nth; simpl.
    rewrite finalSeg_cons; trivial.
    change (drop_nth (a :: l) (S p)) with (a :: drop_nth l p).
    simpl in *; rewrite IHp.
    destruct l; trivial.
    simpl in H; lia.
    lia.
  Qed.

  Lemma drop_nth_beyond : forall l p, length l <= p -> drop_nth l p = l.

  Proof.
    induction l; intros.
    destruct p; trivial.
    destruct p.
    simpl in H; lia.
    change (drop_nth (a::l) (S p)) with (a :: drop_nth l p).
    rewrite IHl; trivial.
    simpl in H; lia.
  Qed.

  Lemma drop_nth_length : forall l p,
    length (drop_nth l p) >= pred (length l).

  Proof. 
    intros.
    destruct (le_gt_dec (length l) p).
    rewrite drop_nth_beyond; trivial.
    lia.
    rewrite drop_nth_in_length; auto.
  Qed.

  Lemma drop_nth_cons : forall a l, drop_nth (a::l) 0 = l.

  Proof.
    intros.
    unfold drop_nth; simpl.
    rewrite finalSeg_cons; trivial.
  Qed.

  Lemma drop_nth_succ : forall a l p,
    drop_nth (a::l) (S p) = a :: drop_nth l p.

  Proof.
    unfold drop_nth, finalSeg; trivial.
  Qed.

  Lemma drop_nth_insert_nth : forall l p el,
    length l >= p -> drop_nth (insert_nth l p el) p = l.

  Proof.
    induction l; simpl; intros.
    destruct p; trivial.
    lia.
    destruct p.
    unfold insert_nth; simpl.
    rewrite finalSeg_full.
    unfold drop_nth; simpl.
    rewrite finalSeg_cons; trivial.    
    change (drop_nth (insert_nth (a::l) (S p) el) (S p)) with
      (a :: drop_nth (insert_nth l p el) p).
    rewrite IHl; trivial.
    lia.
  Qed.

  Lemma insert_nth_drop_nth : forall p l el, nth_error l p = Some el ->
    insert_nth (drop_nth l p) p el = l.

  Proof.
    induction p; intros.
    destruct l.
    inversion H.
    unfold drop_nth, insert_nth; simpl.
    rewrite finalSeg_cons, finalSeg_full.
    inversion H; trivial.
    destruct l.
    inversion H.
    unfold drop_nth, insert_nth; simpl.
    change (finalSeg (a::l) (S (S p))) with (finalSeg l (S p)).
    fold (drop_nth l p).
    change (finalSeg (a::drop_nth l p) (S p)) with (finalSeg (drop_nth l p) p).
    fold (insert_nth (drop_nth l p) p el).
    rewrite IHp; trivial.
  Qed.

End DropNth.

(***********************************************************************)
(** number of occurrences of an element *)

Section CountIn.

  Variables
    (A : Type) (eqA : relation A)
    (eqA_dec : forall x y, {eqA x y} + {~eqA x y})
    (eqA_Equivalence : Equivalence eqA).

  Fixpoint countIn (a: A) (l: list A) : nat :=
    match l with
      | nil => 0
      | x::xs => 
	match eqA_dec a x with
	| left _ => S(countIn a xs)
	| right _ => countIn a xs
	end
    end.

  Lemma in_countIn : forall a a' l, In a l -> eqA a a' -> countIn a' l > 0.

  Proof.
    induction l; inversion 1; intro; simpl.
    rewrite H0; destruct (eqA_dec a' a).
    lia.
    absurd (eqA a' a); intuition.
    destruct (eqA_dec a' a0).
    lia.
    apply IHl; trivial.
  Qed.

  Lemma count_pos_in : forall a (l: list A),
    countIn a l > 0 -> exists a', eqA a a' /\ In a' l.

  Proof.
    induction l; simpl.
    intro w; lia.
    destruct (eqA_dec a a0).
    intros _.
    exists a0; auto.
    intro w.
    destruct (IHl w) as [a' [aa' a'l]].
    exists a'; auto.
  Qed.

  Lemma countIn_nth : forall a (l: list A), countIn a l > 0 ->
    exists p, exists a', eqA a a' /\ nth_error l p = Some a'.

  Proof.
    induction l.
    simpl; intros; lia.
    simpl; intros.
    destruct (eqA_dec a a0).
    exists 0; exists a0.
    split; trivial.
    destruct IHl as [p [a' [aa' lpa']]]; trivial.
    exists (S p); exists a'; split; trivial.
  Qed.

  Lemma countIn_dropNth_eq : forall l p el el',
    nth_error l p = Some el' -> eqA el el' -> 
    countIn el (drop_nth l p) = countIn el l - 1.

  Proof.
    induction l; intros.
    destruct p; trivial.
    destruct p.
    simpl; rewrite drop_nth_cons; destruct (eqA_dec el a).
    lia.
    absurd (eqA el el'); trivial.
    inversion H; rewrite <- H2; trivial.
    rewrite drop_nth_succ.
    simpl; rewrite IHl with p el el'; trivial.
    destruct (eqA_dec el a); trivial.
    set (el'l := nth_some_in l p H).
    assert (el'el: eqA el' el).
    intuition.
    set (w := in_countIn l el'l el'el).
    lia.
  Qed.

  Lemma countIn_dropNth_neq : forall l p el el',
    nth_error l p = Some el' -> ~eqA el el' ->
    countIn el (drop_nth l p) = countIn el l.

  Proof.
    induction l; intros.
    destruct p; trivial.
    destruct p.
    simpl; rewrite drop_nth_cons; destruct (eqA_dec el a); trivial.
    absurd (eqA el el'); trivial.
    inversion H; rewrite <- H2; trivial.
    rewrite drop_nth_succ.
    simpl; rewrite IHl with p el el'; trivial.
  Qed.

End CountIn.

(***********************************************************************)
(** erase the last element of a list *)

Section DropLast.

  Variable A : Type.

  Fixpoint dropLast (l: list A) : list A :=
    match l with
    | nil => nil
    | x::nil => nil
    | x::xs  => x :: dropLast xs
    end.

  Lemma dropLast_last : forall a (l: list A),
    l <> nil -> dropLast (l ++ a::nil) = l.

  Proof.
    induction l; trivial.
    intros; simpl.
    destruct l; trivial.
    destruct ((a1 :: l) ++ a::nil).
    absurd (dropLast nil = a1 :: l).
    simpl; discr.
    apply IHl; discr.
    rewrite IHl; trivial.
    discr.
  Qed.

  Lemma dropLast_eq : forall l1 l2, l1 = l2 -> dropLast l1 = dropLast l2.

  Proof. intros; rewrite H; trivial. Qed.

  Lemma dropLast_app : forall a (l1 l2: list A),
    dropLast (l1 ++ a :: l2) = l1 ++ dropLast (a :: l2).

  Proof.
    induction l1; trivial.
    intro.
    replace (dropLast ((a0 :: l1) ++ a :: l2))
      with (a0 :: dropLast (l1 ++ a::l2)).
    rewrite (IHl1 l2); trivial.
    simpl.
    cut (l1 ++ a :: l2 <> nil).
    destruct (l1 ++ a :: l2); fo.
    auto with datatypes.
  Qed.

End DropLast.

(***********************************************************************)
(** last element of a list *)

Section Last.

  Variable A : Type.

  Fixpoint last (l: list A) : option A :=
    match l with
    | nil => error
    | x::nil => value x
    | x::xs  => last xs
    end.

  Lemma last_eq : forall (l1 l2: list A), l1 = l2 -> last l1 = last l2.

  Proof. intros; rewrite H; trivial. Qed.

  Lemma last_app : forall a (l1 l2: list A),
    last (l1 ++ a :: l2) = last (a :: l2).

  Proof.
    induction l1; trivial.
    intro.
    replace (last ((a0 :: l1) ++ a::l2)) with (last (l1 ++ a::l2)).
    rewrite (IHl1 l2); trivial.
    cut (l1 ++ a::l2 <> nil).
    simpl; destruct (l1 ++ a::l2); fo.
    auto with datatypes.
  Qed.

  Lemma dropLast_plus_last : forall (l1: list A) a b,
    last (a :: l1) = Some b -> dropLast (a :: l1) ++ b :: nil = a :: l1.

  Proof.
    induction l1.
    simpl; intros.
    inversion H; trivial.
    intros.
    simpl.
    rewrite <- (IHl1 a b); trivial.
  Qed.

End Last.

(***********************************************************************)
(** remove the first occurrence of an element *)

Section Remove.

  Variable A : Type.
  Variable eqA : relation A.
  Variable eqA_dec : forall x y, {eqA x y} + {~eqA x y}.

  Fixpoint removeElem (el: A) (l: list A) : list A :=
    match l with
    | nil => nil
    | hd::tl =>
      match eqA_dec el hd with
      | left _ => tl
      | right _ => hd::removeElem el tl
      end
    end.

  Fixpoint removeAll (l m: list A) : list A :=
    match m with
    | nil => l
    | hd::tl => removeAll (removeElem hd l) tl
    end.

  Lemma removeElem_length_in : forall a l, (exists a', eqA a a' /\ In a' l) ->
    length (removeElem a l) = pred (length l).

  Proof.
    induction l; intros; destruct H as [b [ab bl]]; inversion bl.
    simpl; destruct (eqA_dec a a0); trivial.
    absurd (eqA a a0); trivial.
    rewrite H; trivial.
    simpl; destruct (eqA_dec a a0); trivial.
    simpl; rewrite IHl; trivial.
    destruct l; auto.
    contr.
    exists b; split; trivial.
  Qed.

End Remove.

(***********************************************************************)
(** find the first/last occurrence of an element *)

Section Find.

  Variable A : Type.
  Variable P : A -> Prop.
  Variable P_dec : forall a : A, {P a} + {~P a}.

Lemma exists_in_list_dec : forall l,
  {exists r, P r /\ In r l} + {~exists r, P r /\ In r l}.

Proof.
induction l.
right. intuition. do 2 destruct H; simpl in H; auto.
destruct (P_dec a).
left; exists a; simpl; auto.
destruct IHl.
left. destruct e. exists x. simpl; tauto.
right; intuition. do 2 destruct H. simpl in H0. destruct H0.
subst; tauto. apply n0. exists x; auto.
Defined.

  Fixpoint find_first (l: list A) : option nat := 
    match l with
    | nil => None
    | hd::tl => 
      match P_dec hd with
      | left _ => Some 0
      | right _ => 
	match find_first tl with
        | None => None
	| Some i => Some (S i)
	end
      end
    end.

  Fixpoint find_last (l: list A) : option nat := 
    match l with
    | nil => None
    | hd::tl => 
      match find_last tl with
      | Some i => Some (S i)
      | None => 
	match P_dec hd with
	| left _ => Some 0
	| right _ => None
	end
      end
    end.

  Lemma find_first_ok : forall l p, find_first l = Some p ->
    exists el, nth_error l p = Some el /\ P el.

  Proof.
    induction l.
    inversion 1.
    simpl.
    destruct (P_dec a).
    intros q q0.
    inversion q0.
    exists a; split; trivial.
    destruct p.
    destruct (find_first l); inversion 1.
    intros pl.
    destruct (IHl p) as [el [lp Pl]].
    destruct (find_first l); inversion pl; trivial.
    exists el; split; trivial.
  Qed.

  Lemma find_last_ok : forall l p, find_last l = Some p ->
    exists el, nth_error l p = Some el /\ P el.

  Proof.
    induction l.
    inversion 1.
    simpl.
    destruct (P_dec a).
    intros q q0.
    destruct q.
    exists a; split; trivial.
    destruct (IHl q) as [el [lq Pel]].
    destruct (find_last l); inversion q0; trivial.
    exists el; split; trivial.
    intros q q0.
    destruct q.
    destruct (find_last l); discr.
    destruct (IHl q) as [el [lq Pel]].
    destruct (find_last l); inversion q0; trivial.
    exists el; split; trivial.
  Qed.

  Lemma find_last_last: forall l p el, nth_error l p = Some el -> P el ->
    exists q, find_last l = Some q /\ q >= p.

  Proof.
    induction l; intros.
    destruct p; inversion H.
    destruct p.
    inversion H.
    simpl; destruct (P_dec el).
    destruct (find_last l).
    exists (S n); split; [trivial | lia].
    exists 0; split; [trivial | lia].
    absurd (P el); trivial.
    destruct (IHl p el) as [w [lw wp]]; trivial.
    exists (S w); split.
    simpl; rewrite lw; trivial.
    lia.
  Qed.

Lemma find_first_exist : forall x l, In x l -> P x -> find_first l <> None.

Proof.
intros. induction l. simpl in H;tauto.
simpl in H. destruct H. subst; simpl.
destruct (P_dec x); auto; discr.
simpl. destruct (P_dec a). discr.
ded (IHl H). destruct (find_first l). discr. tauto.
Qed.


Lemma find_first_Some : forall l,
  find_first l <> None -> exists z, In z l /\ P z.

Proof.
intros.
induction l.
simpl in H; tauto.
simpl in H. destruct (P_dec a).
exists a; split; simpl; tauto.
destruct (find_first l); try discr.
assert (exists z : A, In z l /\ P z).
apply IHl; discr.
destruct H0. exists x.
simpl; tauto.
tauto.
Qed.

Lemma find_first_Some_bound : forall l x,
  find_first l = Some x -> x < length l.

Proof.
induction l; intros.
simpl in H; discr.
simpl in H. destruct (P_dec a).
inversion H; subst.
simpl; lia.
destruct (find_first l).
inversion H; subst.
simpl; apply lt_n_S; apply IHl; auto.
discr.
Qed.

Lemma In_find_first2 : forall l z,
  find_first l = Some z -> exists y, l[z] = Some y /\ P y.

Proof.
induction l; intros; simpl in H. discr; tauto.
destruct (P_dec a).
inversion H; subst. exists a; simpl; split; auto.
destruct (find_first l); try discr; try tauto.
inversion H. ded (IHl n0 (eq_refl (Some n0))).
destruct H0. exists x. simpl; auto.
Qed.

Lemma find_first_exact : forall l i,
  find_first l = Some i -> exists z, l[i] = Some z /\ P z.

Proof.
induction l; intros. simpl in H. discr.
simpl in H. destruct (P_dec a).
inversion H. exists a; subst; simpl; tauto.
destruct (find_first l); try discr.
inversion H; subst. simpl. apply IHl; auto.
Qed.

End Find.

Arguments In_find_first2 [A P P_dec l z] _.

Section Find_more.

Variable A : Type.
Variables P Q : A -> Prop.
Variable P_dec : forall a : A, {P a} + {~P a}.
Variable Q_dec : forall a : A, {Q a} + {~Q a}.

Lemma find_first_indep : (forall x, P x <-> Q x) ->
  forall l, find_first P P_dec l = find_first Q Q_dec l.

Proof.
induction l; simpl. refl.
destruct (P_dec a); destruct (Q_dec a); try rewrite H in *; try tauto.
rewrite IHl. refl.
Qed.

Variable eq_dec : forall x y : A, {x=y} +{~x=y}.

Lemma eq_In_find_first : forall x l, In x l ->
  exists z, find_first (eq x) (eq_dec x) l = Some z /\ l[z] = Some x.

Proof.
intros; induction l.
unfold In in H; tauto.
simpl in H.
destruct (eq_dec x a); subst.
exists 0; split; simpl; auto with *.
destruct (eq_dec a a); auto with *; tauto.
destruct H; subst; try tauto.
ded (IHl H); destruct H0 as [z]; destruct H0.
exists (S z); split; simpl; auto with *.
destruct (eq_dec x a); subst; try tauto.
destruct (find_first (eq x) (eq_dec x) l); subst; try tauto;
inversion H0; subst; auto.
Qed.

Lemma eq_find_first_exact : forall l x z,
  find_first (eq x) (eq_dec x) l = Some z -> l[z] = Some x.

Proof.
intro; intro.
induction l; intros; simpl in *. discr.
destruct (eq_dec x a); subst.
inversion H; subst; auto with *.
assert (exists i, find_first (eq x) (eq_dec x) l = Some i).
destruct (find_first (eq x) (eq_dec x) l); try discr.
exists n0; auto with *.
destruct H0.
ded (IHl _ H0).
rewrite H0 in H.
destruct z; inversion H; subst; hyp.
Qed.

Lemma element_at_find_first_eq : forall l x i,
  l[i] = Some x -> exists j, j <= i /\ find_first (eq x) (eq_dec x) l = Some j.

Proof.
induction l; simpl; intros. discr. destruct i.
inversion H. subst x. case (eq_dec a a); intro. exists 0. auto. cong.
case (eq_dec x a); intro. exists 0. intuition.
destruct (IHl _ _ H). destruct H0. rewrite H1. exists (S x0). intuition.
Qed.

End Find_more.

Arguments eq_In_find_first [A] _ [x l] _.
Arguments eq_find_first_exact [A eq_dec l x z] _.
Arguments element_at_find_first_eq [A] _ [l x i] _.

(***********************************************************************)
(** decidability of finding an element satisfying some relation *)

Section List_Rel_Dec.

  Variable A : Type.
  Variable B : Type.
  Variable P : A -> Prop.
  Variable R : A -> B -> Prop.

  Lemma many_one_dec : forall (l : list A) r,
    (forall x, In x l -> {R x r} + {~R x r})
    -> {x : A | In x l /\ R x r} + {forall x, In x l -> ~R x r}.

  Proof.
    induction l; intros.
    right; intros.
    inversion H.
    destruct (X a); auto with datatypes.
    left; exists a; auto with datatypes.
    case (IHl r); intro.
    intros; apply X; auto with datatypes.
    left.
    destruct s as [x [x_l x_r]].
    exists x; auto with datatypes.
    right.
    intros.
    destruct H.
    rewrite <- H; trivial.
    apply n0; trivial.
  Defined.

  Lemma list_dec_all : forall (l : list A),
    (forall x, In x l -> {P x} + {~P x}) ->
    {forall x, In x l -> P x} + {exists x, In x l /\ ~P x}.

  Proof.
    induction l; intros.
    left; intros; inversion H.
    destruct (IHl).
    intros; apply X.
    auto with datatypes.
    destruct (X a).
    auto with datatypes.
    left; intros; inversion H.
    rewrite <- H0; trivial.
    apply p; trivial.
    right; exists a; split; auto with datatypes.
    right.
    destruct e as [x [x_l nPx]].
    exists x; split; auto with datatypes.
  Defined.

End List_Rel_Dec.

(***********************************************************************)
(** hints *)

Global Hint Rewrite initialSeg_full initialSeg_nth seg_nth seg_tillEnd seg_exceeded
  finalSeg_empty nth_finalSeg_nth nth_copy_in nth_app_left nth_app_right
  using solve [lia | auto] : datatypes.

Global Hint Rewrite initialSeg_length finalSeg_full finalSeg_cons finalSeg_length
  initialFinalSeg_length copy_split copy_length : datatypes.
