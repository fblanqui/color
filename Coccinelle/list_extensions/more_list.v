(**************************************************************************)
(*           *                                                            *)
(*     _     *   The Coccinelle Library / Evelyne Contejean               *)
(*    <o>    *          CNRS-LRI-Universite Paris Sud                     *)
(*  -/@|@\-  *                   A3PAT Project                            *)
(*  -@ | @-  *                                                            *)
(*  -\@|@/-  *      This file is distributed under the terms of the       *)
(*    -v-    *      CeCILL-C licence                                      *)
(*           *                                                            *)
(**************************************************************************)

(** * Some additional properties for the Coq lists. *)

Set Implicit Arguments.

From Stdlib Require Import Bool List Arith Setoid Relations FunInd.
From CoLoR Require Import closure.

Lemma tail_prop : forall A :  Type, forall (P : A -> Prop), forall a, forall l, 
  (forall b, In b (a::l) -> P b) -> (forall b, In b l -> P b).
Proof.
intros Ar P a l H b In_b; apply H; right; trivial.
Qed.

Lemma tail_set : forall A : Type, forall (P : A -> Type), forall a, forall l, 
  (forall b, In b (a::l) -> P b) -> (forall b, In b l -> P b).
Proof.
intros Ar P a l H b In_b; apply H; right; trivial.
Qed.

(** ** How to add or remove an element, how to split a list *)
Lemma split_list : 
  forall (A : Type) (l1 l2 l3 l4 : list A), l1 ++ l2 = l3 ++ l4 ->
  {l | l1 = l3 ++ l /\ l4 = l ++ l2} + {l | l3 = l1 ++ l /\ l2 = l ++ l4}.
Proof.
intros A l1; induction l1 as [ | a1 l1].
right; exists l3; split; trivial.
intros l2 [ | a3 l3] l4 H.
left; exists (a1 :: l1); split; trivial.
rewrite H; trivial.
injection H; clear H; intros H a1_eq_a3; subst a3.
destruct (IHl1 _ _ _ H) as [H' | H'].
destruct H' as [l [H1 H2]]; subst l1 l4.
left; exists l; split; trivial.
destruct H' as [l [H1 H2]]; subst l2 l3.
right; exists l; split; trivial.
Qed.

Lemma in_insert :
forall (A : Type) (l1 l2 : list A) e a, In a (l1 ++ l2) -> In a (l1 ++ e :: l2).
Proof.
intros A l1 l2 e a a_in_l1_l2; 
destruct (in_app_or _ _ _ a_in_l1_l2) as [a_in_l1 | a_in_l2]; 
apply in_or_app; [left | right; right]; trivial.
Qed.

Lemma diff_in_remove :
forall (A : Type) (l1 l2 : list A) e a, a <> e -> In a (l1 ++ e :: l2) -> In a (l1 ++ l2).
Proof.
intros A l1 l2 e a a_diff_e a_in_l1_e_l2; 
destruct (in_app_or _ _ _ a_in_l1_e_l2) as [a_in_l1 | [a_eq_e | a_in_l2]]; 
apply in_or_app; 
[left
| absurd (a=e); subst
| right]; trivial.
Qed.

Lemma in_split :
  forall (A : Type)  (a : A) (l : list A), In a l -> exists l1, exists l2, l = l1 ++ a :: l2.
Proof.
intros A a l; induction l as [ | e l].
contradiction.
intros [a_eq_e | a_in_l].
subst e.
exists (@nil A); exists l; trivial.
destruct (IHl a_in_l) as [l' [l'' H]].
exists (e :: l'); exists l''; subst l; simpl; trivial.
Qed.

Lemma in_split_set :
  forall (A : Type) 
    (eq_bool : A -> A -> bool) 
	(eq_bool_ok : forall a1 a2 : A, match eq_bool a1 a2 with true => a1 = a2 | false => a1 <> a2 end)
   (a : A) (l : list A), In a l -> {l1 : list A & { l2 : list A | l = l1 ++ a :: l2}}.
Proof.
intros A eq_bool eq_bool_ok a l; induction l as [ | e l].
contradiction.
generalize (eq_bool_ok e a); case (eq_bool e a); [intro e_eq_a | intro e_diff_a].
intros _; exists (@nil A); exists l; simpl; subst; trivial.
intro a_in_el; destruct IHl as [l' [l'' H]].
destruct a_in_el as [e_eq_a | a_in_l]; trivial.
absurd (e = a); trivial.
exists (e :: l'); exists l''; subst l; simpl; trivial.
Qed.

Lemma in_in_split_set :
  forall (A : Type) 
   (a b : A) (l1 l2 k1 k2 : list A), l1 ++ a :: l2 = k1 ++ b :: k2 ->
   {l | l1 = k1 ++ b :: l /\ k2 = l ++ a :: l2} +
   {l | k1 = l1 ++ a :: l /\ l2 = l ++ b :: k2} +
   {a = b /\ l1 = k1 /\ l2 = k2}.
Proof.
intros A a b l1; revert a b; induction l1 as [ | a1 l1];
intros a b l2 k1 k2 H; destruct k1 as [ | b1 k1].
simpl in H; injection H; intros l2_eq_k2 a_eq_b; right; repeat split; trivial.
simpl in H; injection H; intros l2_eq_k a_eq_b1; subst; clear H.
left; right; exists k1; repeat split; trivial.
simpl in H; injection H; intros l_eq_k2 a1_eq_b; subst; clear H.
left; left; exists l1; repeat split; trivial.
simpl in H; injection H; intros l_eq_k a1_eq_b1; subst; clear H.
destruct (IHl1 _ _ _ _ _ l_eq_k) as [[H | H] | H].
destruct H as [l [H1 H2]]; subst.
left; left; exists l; repeat split; trivial.
destruct H as [l [H1 H2]]; subst.
left; right; exists l; repeat split; trivial.
destruct H as [a_eq_b [H1 H2]]; subst.
right; repeat split; trivial.
Qed.

Lemma insert_1 :
forall (A : Type) (l1 l2 r1 r2 : list A) (a b : A), l1 ++ l2 = r1 ++ b :: r2 ->
 exists r1', exists r2', l1 ++ a :: l2 = r1' ++ b :: r2'.
Proof.
intros A l1; induction l1 as [ | a1 l1].
simpl; intros l2 r1 r2 a b H; rewrite H; exists (a :: r1); exists r2; simpl; trivial.
intros l2 [ | b1 r1] r2 a b H; simpl in H;
injection H; clear H; intros H a1_eq; subst a1.
exists (@nil A); exists (l1 ++ a :: l2); simpl; trivial.
destruct (IHl1 _ _ _ a _ H) as [r1' [r2' H']]; simpl; rewrite H'.
exists (b1 :: r1'); exists r2'; simpl; trivial.
Qed.

Lemma insert_2 :
forall (A : Type) (l1 l2 r1 r2 r3 : list A) (a b b' : A), 
  l1 ++ l2 = r1 ++ b :: r2 ++ b' :: r3 ->
 exists r1', exists r2', exists r3', l1 ++ a :: l2 = r1' ++ b :: r2' ++ b' :: r3'.
Proof.
intros A l1; induction l1 as [ | a1 l1].
simpl; intros l2 r1 r2 r3 a b b' H; rewrite H; 
exists (a :: r1); exists r2; exists r3; simpl; trivial.
intros l2 [ | b1 r1] r2 r3 a b b' H; simpl in H;
injection H; clear H; intros H a1_eq; subst a1.
destruct (insert_1 l1 l2  r2 r3 a b' H) as [r2' [r3' H']]; simpl; rewrite H'.
exists (@nil A); exists r2'; exists r3'; simpl; trivial.
destruct (IHl1 l2 r1  r2 r3 a b b' H) as [r1' [r2' [r3' H']]]; simpl; rewrite H'.
exists (b1 :: r1'); exists r2'; exists r3'; simpl; trivial.
Qed.

(** ** Properties of map. *)
Lemma map_id : forall (A : Type) l, map (fun t : A => t) l = l.
Proof.
intros A l; induction l as [ | t l]; simpl; trivial.
rewrite IHl; trivial.
Qed.

Lemma map_eq : forall (A B : Type) (f g : A -> B) l, (forall a, In a l -> f a = g a) -> map f l = map g l. 
Proof.
intros A B f g l; induction l as [ | a l]; intros H; trivial.
simpl; rewrite (H a).
rewrite IHl; trivial.
intros; apply H; right; trivial.
left; trivial.
Qed.

Lemma split_map_set : forall (A B : Type) (f : A -> B) l l1 l2, map f l = l1 ++ l2 -> 
   {k1 : list A & {k2 : list A | l = k1 ++ k2 /\ map f k1 = l1 /\ map f k2 = l2}}.
Proof.
fix split_map_set 4.
intros A B f l; case l; clear l.
intros l1 l2 H; exists nil; exists nil.
revert H; case l1; clear l1.
case l2; clear l2.
intros _; repeat split; apply eq_refl.
intros b2 l2 H; discriminate.
intros b1 l1 H; discriminate.
intros a l l1; case l1; clear l1.
intros l2 H; exists nil; exists (a :: l); repeat split; trivial.
intros b1 l1 l2 H; injection H; clear H; intros H H'.
destruct (split_map_set A B f l l1 l2 H) as [k1 [k2 [H1 [H2 H3]]]].
exists (a :: k1); exists k2; repeat split; trivial.
simpl; apply f_equal; assumption.
simpl; rewrite H'; rewrite H2; apply eq_refl.
Qed.

Lemma in_map_set :
forall (A B : Type) (eqB_dec : forall b1 b2 : B, {b1 = b2}+{b1 <> b2}) (f : A -> B) b l, 
In b (map f l) -> {a : A | f a = b /\ In a l}.
Proof.
intros A B eqB_dec f b; induction l as [ | a1 l].
contradiction.
destruct (eqB_dec b (f a1)) as [b_eq_fa1 | b_diff_fa1].
intros _; exists a1; split; [apply sym_eq; assumption | left; apply eq_refl].
simpl; intro b_in_fa1_fl.
destruct IHl as [a [fa_eq_b a_in_l]].
destruct b_in_fa1_fl as [fa1_eq_b | b_in_fl]; [apply False_rect; apply b_diff_fa1; apply sym_eq | idtac]; assumption.
exists a; split; [assumption | right; assumption].
Qed.

Lemma flat_map_app : 
	forall A B (f : A -> list B) (l1 l2 : list A), flat_map f (l1 ++ l2) = (flat_map f l1) ++ (flat_map f l2).
intros A B f; fix flat_map_app 1.
intros l1; case l1; clear l1.
intros l2; apply eq_refl.
intros a1 l1 l2; simpl; rewrite (flat_map_app l1 l2); rewrite app_assoc; apply eq_refl.
Qed.

(** ** Iterators. *) 
Lemma fold_left_in_acc : 
  forall (A B : Type) (f : list B -> A -> list B) x l,
  (forall acc x y, In y acc -> In x l -> In y (f acc x)) ->
  forall acc, In x acc -> In x (fold_left f l acc).
Proof.
  intros A B f x l; induction l as [ | a l]; intros Hf acc x_in_acc; simpl; trivial.
  apply IHl.
  intros; apply Hf; [idtac | right]; trivial.
  apply Hf; [idtac | left]; trivial.
Qed.

Lemma fold_left_in_acc_split : 
  forall (A B : Type) (f : A -> list B), 
    let g := fun acc x => (f x) ++ acc in 
      forall  acc1 acc2 x l,
        In x (fold_left g l (acc1 ++ acc2)) <-> In x (fold_left g l acc1) \/ In x acc2.
Proof.
  intros A B f g acc1 acc2 x l.
  revert acc1 acc2;induction l as [ | y l]; simpl.
  split; auto with *.
  intros acc1 acc2; rewrite <- IHl.
  unfold g.
  rewrite app_assoc. 
  reflexivity.
Qed.

Fixpoint fold_left2 (A B C : Type) (f : A -> B -> C -> A) (a : A) (l1 : list B) (l2 : list C)  
  {struct l1} : option A :=
  match l1, l2 with
  | nil, nil => Some a
  | b :: t1, c :: t2 => fold_left2 f (f a b c) t1 t2
  | _, _ => None
  end.

(** ** length and size *)
Lemma length_add : 
  forall (A : Type) (l1 l2 : list A) a, length (l1 ++ a :: l2) = S (length (l1 ++ l2)).
Proof.
intros A l1 l2 a; rewrite length_app; simpl;
rewrite Nat.add_comm; simpl; rewrite Nat.add_comm;
rewrite length_app; trivial.
Qed.

(** ** A measure on lists based on a measure on elements. *)

Fixpoint list_size (A : Type) (size : A -> nat) (l : list A) {struct l} : nat :=
  match l with
  | nil => 0
  | h :: tl => size h + list_size size tl
  end.

Lemma list_size_tl_compat :
  forall (A : Type) (size : A -> nat) a b l, size a < size b -> 
    list_size size (a :: l) < list_size size (b :: l).
Proof.
intros A size a b l H; simpl. apply Nat.add_lt_mono_r; trivial.
Qed.

Lemma list_size_app:
 forall (A : Type) (size : A -> nat) l1 l2,
 list_size size (l1 ++ l2) = list_size size l1 + list_size size l2.  
Proof. 
induction l1 as [ | a1 l1 ]; trivial.
intros; simpl; rewrite IHl1; auto with arith.
Qed.

Lemma list_size_fold :
  forall (A : Type) (size : A -> nat) l,
  (fix size_list (l0 : list A) : nat :=
   match l0 with
   | nil => 0
   | t :: lt => size t + size_list lt
   end) l = list_size size l.
Proof.
intros A size l; induction l; trivial.
simpl; rewrite IHl; trivial.
Qed.

Lemma list_size_size_eq :
  forall (A : Type) (size1 : A -> nat) (size2 : A -> nat) l,
 (forall a, In a l -> size1 a = size2 a) -> list_size size1 l = list_size size2 l.
Proof.
intros A size1 size2 l; induction l as [ | a l]; simpl; trivial.
intros size1_eq_size2.
rewrite (size1_eq_size2 a (or_introl _ (eq_refl _))).
apply (f_equal (fun n => size2 a + n)); apply IHl;
intros; apply size1_eq_size2; right; trivial.
Qed.

(** ** Induction principles for list. 
 Induction on the length. *)
Definition list_rec2 :
  forall A, forall P : list A -> Type,
    (forall (n:nat) (l : list A), length l <= n -> P l) -> 
    forall l : list A, P l.
Proof.
intros A P H l; apply (H (length l) l); apply le_n.
Defined.

(** Induction on the the size. *)
Definition list_rec3 : forall (A : Type) (size : A -> nat),
  forall P : list A -> Type,
    (forall (n:nat) (l : list A), list_size size l <= n -> P l) -> 
    forall l : list A, P l.
Proof.
intros A size P H l; apply (H (list_size size l) l); apply le_n.
Defined.

(** ** Properties on the nth element. *)
Lemma nth_error_nil : forall (A : Type) n, @nth_error A nil n = None.
Proof.
intros A [ | n]; simpl; trivial.
Qed.

Lemma nth_error_ok_in :
  forall (A : Type) n (l : list A) (a : A),
  nth_error l n = Some a -> {l1 : list A & {l2 : list A | length l1 = n /\ l = l1 ++ a :: l2}}.
Proof.
intros A n l; generalize n; clear n; induction l as [ | a' l].
intros n a; rewrite nth_error_nil; intros; discriminate.
intros [ | n] a; simpl; intros H.
injection H; intro; subst a'.
exists (@nil A); exists l; split; trivial.
destruct (IHl n a H) as [l1 [l2 [L H']]].
exists (a' :: l1); exists l2; simpl; split; subst; trivial.
Qed.

Lemma nth_error_at_pos :
  forall (A : Type) l1 a l2, nth_error (l1 ++ a :: l2) (length l1) = @Some A a.
Proof.
intros A l1; induction l1 as [ | a1 l1]; intros a l2; simpl; trivial.
Qed.

Lemma nth_error_remove :
  forall (A : Type) (a : A) k k' n,
    nth_error (k ++ a :: k') (if le_lt_dec (length k) n then S n else n) = 
	nth_error (k ++ k') n.
Proof.
intros A b k; induction k as [ | a k]; intros k' m.
simpl; trivial.
simpl length; simpl app.
destruct m as [ | m].
simpl; trivial.
generalize (IHk k' m);
destruct (le_lt_dec (length k) m) as [k_le_m | k_gt_m];
destruct (le_lt_dec (S (length k)) (S m)) as [k_le_m' | k_gt_m'].
simpl; trivial.
absurd (S m <= m); auto with arith; apply Nat.lt_le_trans with (length k); auto with arith.
absurd (S m <= m); auto with arith; apply Nat.lt_le_trans with (length k); auto with arith.
simpl; trivial.
Qed.

Lemma nth_error_none :
   forall A n (l : list A) , nth_error l n = None -> length l <= n.
Proof.
fix nth_error_none 3.
intros A n [ | a l]; case n; clear n; simpl.
intros _; apply le_n.
intros; apply Nat.le_0_l.
intros; discriminate.
intros; apply le_n_S.
apply nth_error_none.
assumption.
Qed.

Lemma nth_error_almost_id :
  forall A n l l' (a1 a2 : A), 
	nth_error (l ++ a1 :: l') n = nth_error (l ++ a2 :: l') n \/
	(nth_error (l ++ a1 :: l') n = Some a1 /\ nth_error (l ++ a2 :: l') n = Some a2).
Proof.
fix nth_error_almost_id 2.
intros A [ | n] l l' a1 a2; case l; clear l; simpl.
right; split; reflexivity.
intro a; left; reflexivity.
left; reflexivity.
intros _ l; apply (nth_error_almost_id A n).
Qed.

Lemma nth_error_map :
  forall (A B : Type) (f : A -> B) (l : list A) i,
  match nth_error (map f l) i with
  | Some f_li => 
           match nth_error l i with
            | Some li => f_li = f li
            | None => False
            end
  | None =>
            match nth_error l i with
            | Some li => False
            | None => True
            end
end.
Proof.
induction l as [ | a l ]; 
intro i; destruct i as [ | i ]; simpl; trivial.
apply IHl; trivial.
Qed.

Fixpoint list_eq_bool A (eq_bool : A -> A -> bool) (l1 l2 : list A) {struct l1} : bool :=
   match l1 with
  | nil => match l2 with nil => true | _ :: _ => false end
  | t1 :: l1 => match l2 with nil => false | t2 :: l2 => andb (eq_bool t1 t2) (list_eq_bool eq_bool l1 l2) end
  end.

Lemma list_eq_bool_ok : 
  forall A eq_bool 
  (eq_bool_ok : forall a1 a2, match eq_bool a1 a2 with true => a1 = a2 | false => a1 <> a2 end) 
  (l1 l2 : list A), 
  match list_eq_bool eq_bool l1 l2 with true => l1 = l2 | false => l1 <> l2 end.
Proof.
intros A eq_bool eq_bool_ok.
fix list_eq_bool_ok 1; intro l1; case l1; clear l1; [idtac | intros a1 l1]; (intro l2; case l2; clear l2; [idtac | intros a2 l2]).
simpl; reflexivity.
simpl; discriminate.
simpl; discriminate.
simpl; generalize (eq_bool_ok a1 a2); case (eq_bool a1 a2); [intro a1_eq_a2 | intro a1_diff_a2]; simpl.
generalize (list_eq_bool_ok l1 l2); case (list_eq_bool eq_bool l1 l2); [intro l1_eq_l2 | intro l1_diff_l2].
apply f_equal2; assumption.
intro a1l1_eq_a2l2; apply l1_diff_l2; injection a1l1_eq_a2l2; intros; assumption.
intro a1l1_eq_a2l2; apply a1_diff_a2; injection a1l1_eq_a2l2; intros; assumption.
Qed.

Section Eq_bool.
Variable A : Type.
Variable eqA : relation A.
Variable eq_bool : A -> A -> bool.
Variable eq_bool_ok : forall a1 a2, match eq_bool a1 a2 with true => eqA a1 a2 | false => ~ eqA a1 a2 end.

Fixpoint mem (e : A) (l : list A) {struct l} : Prop :=
   match l with
   | nil => False
   | e' :: l => (eqA e e') \/ mem e l
   end.

Lemma mem_eq_mem :
  equivalence _ eqA -> forall a a' l, eqA a a' -> mem a l -> mem a' l.
Proof.
intros E a a'; fix mem_eq_mem 1.
intro l; case l; clear l.
intros _ a_mem_nil; contradiction.
intros b l a_eq_a' H; simpl in H; case H; clear H; [intro a_eq_b | intro a_mem_l].
left; apply (equiv_trans _ _ E) with a.
apply (equiv_sym _ _ E); assumption.
assumption.
right; apply mem_eq_mem; assumption.
Qed.

Lemma mem_in_eq :
  forall a l, mem a l <-> (exists a', eqA a a' /\ In a' l).
Proof.
fix mem_in_eq 2.
intros a l; case l; clear l; simpl.
split.
intro; contradiction.
intro H; case H; clear H; intros a' H; case H; clear H; intros _ F; assumption.
intros a' l; split.
intro H; case H; clear H.
intro a_eq_a'; exists a'; split; [assumption | left; reflexivity].
intro a_in_l; rewrite mem_in_eq in a_in_l; case a_in_l; clear a_in_l; intros a'' H; case H; clear H.
intros a_eq_a'' a''_in_l; exists a''; split; [assumption | right; assumption].
intro H; case H; clear H; intros a'' H; case H; clear H; intros a_eq_a'' H; case H; clear H.
intro; subst a''; left; assumption.
intro a''_in_l; right; rewrite mem_in_eq; exists a''; split; assumption.
Qed.

Lemma in_impl_mem : (forall a, eqA a a) -> forall e l, In e l -> mem e l.
Proof.
intros refl_eq e l e_in_l; rewrite (mem_in_eq e l); exists e; split; [apply (refl_eq e) | assumption].
Qed.

Lemma mem_impl_in : (forall a b, eqA a b -> a = b) -> forall e l, mem e l -> In e l.
Proof.
fix mem_impl_in 3.
intros eq_is_eq e l; case l; clear l.
intro e_mem_nil; contradiction.
simpl; intros a l [e_eq_a | e_mem_l].
left; symmetry; apply eq_is_eq; assumption.
right; apply mem_impl_in; assumption.
Qed.

Function mem_bool (a : A) (l : list A) {struct l} : bool :=
match l with
| nil => false
| b :: k => orb (eq_bool a b) (mem_bool a k)
end.

Lemma mem_bool_ok  : forall a l, match mem_bool a l with true => mem a l | false => ~mem a l end.
Proof.
fix mem_bool_ok 2.
intros a l; case l; simpl.
intro F; assumption.
intros b k; generalize (eq_bool_ok a b); case (eq_bool a b).
intro a_eq_b; left; assumption.
intro a_diff_b; simpl; generalize (mem_bool_ok a k); case (mem_bool a k).
intro a_in_k; right; assumption.
intros a_not_in_k a_in_bk; case a_in_bk; clear a_in_bk.
exact a_diff_b.
exact a_not_in_k.
Defined.

Lemma mem_bool_app : forall a l1 l2, mem_bool a (l1 ++ l2) = orb (mem_bool a l1) (mem_bool a l2).
Proof.
fix mem_bool_app 2.
intros a l1; case l1; clear l1.
intros l2; reflexivity.
simpl; intros a1 l1 l2; rewrite mem_bool_app; rewrite orb_assoc; reflexivity.
Qed.

Lemma mem_or_app :
  forall l m a, mem a l \/ mem a m <-> mem a (l ++ m).
Proof.
intros l m a; split.
induction l as [ | e l]; intros [a_mem_l | a_mem_m].
contradiction.
simpl; trivial.
destruct a_mem_l as [a_eq_e | a_mem_l].
simpl; left; trivial.
simpl; right; apply IHl; left; trivial.
simpl; right; apply IHl; right; trivial.
induction l as [ | e l]; intro a_mem_lm.
right; trivial.
simpl in a_mem_lm; destruct a_mem_lm as [a_eq_e | a_mem_lm].
left; left; trivial.
destruct (IHl a_mem_lm) as [a_mem_l | a_mem_m].
left; right; trivial.
right; trivial.
Qed.

Lemma mem_insert :
  forall l1 l2 e a, mem a (l1 ++ l2) -> mem a (l1 ++ e :: l2).
Proof.
intro l1; induction l1 as [ | e1 l1]; intros l2 e a a_mem_l1l2.
simpl; right; trivial.
simpl in a_mem_l1l2; destruct a_mem_l1l2 as [a_eq_e1 | a_mem_l1l2].
simpl; left; trivial.
simpl; right; apply IHl1; trivial.
Qed.

Lemma diff_mem_remove :
  forall l1 l2 e a, ~eqA  a e -> mem a (l1 ++ e :: l2) -> mem a (l1 ++ l2).
Proof.
intros l1; induction l1 as [ | e1 l1]; simpl; intros l2 e a a_diff_e a_in_l1el2.
destruct a_in_l1el2 as [e_eq_a | a_mem_l2]; trivial.
absurd (eqA a e); trivial; symmetry; trivial.
destruct a_in_l1el2 as [e1_eq_a | a_mem_l1el2].
left; trivial.
right; apply (IHl1 l2 e); trivial.
Qed.

Function remove (a : A) (l : list A) {struct l} : option (list A) :=
match l with
| nil => None
| h :: tl =>
   match eq_bool a h with
   | true => Some tl
   | false => 
        match remove a tl with
        | Some rmv => Some (h :: rmv)
        | None => None
        end
    end
end.


Lemma in_remove :  forall a l,
 match remove a l with
  | None => ~mem a l
  | Some l' => {a' : A & {l' : list A & {l'' : list A | eqA a a' /\ l = l' ++ a' :: l'' /\ remove a l = Some (l' ++ l'')}}}
  end.
Proof.
intros a l; 
functional induction (remove a l) 
     as [ l l_eq_nil
          | l a' l' l_eq_a'_l' a_eq_a' 
          | l a' l' l_eq_a'_l' a_diff_a' IH rmv H
          | l a' l' l_eq_a'_l' a_diff_a' IH H].
intros a_in_nil; contradiction.
exists a'; exists (@nil A); exists l'; simpl; repeat split; trivial.
generalize (eq_bool_ok a a'); rewrite a_eq_a'; trivial.
rewrite H in IH; revert IH; intros [a'' [l'' [l''' [H' [H'' H''']]]]]. 
exists a''; exists (a' :: l''); exists l'''; subst l'; rewrite app_comm_cons; injection H'''; intros; subst. 
simpl; intuition.
rewrite H in IH.
simpl; intros [a_eq_a' | a_in_l'].
generalize (eq_bool_ok a a'); rewrite a_diff_a'; intro Abs; apply Abs; assumption.
apply (IH a_in_l'); trivial.
Qed.

Lemma mem_split_set :
forall a l, mem a l ->
{a' : A & {l' : list A & {l'' : list A | eqA a a' /\ l = l' ++ a' :: l'' /\ remove a l = Some (l' ++ l'')}}}.
Proof.
intros a l a_mem_l; generalize (in_remove a l); case (remove a l).
intros l' H; exact H.
intro a_not_mem_l; absurd (mem a l); assumption.
Qed.

(* Definition remove_equiv *)
Function remove_equiv  (l1 l2 : list A) {struct l1} : (list A) * (list A) := 
  match l1 with 
    | nil => (l1,  l2)
    | x1 :: l1' =>
        match remove x1 l2 with
        | Some l2' => remove_equiv l1' l2'
        | None =>
              match remove_equiv l1' l2 with
              | (l1'', l2'') => ((x1 :: l1'') , l2'')
              end
          end
     end.

Fixpoint included_list (l1 l2:list A) {struct l1} : bool :=
  match l1 with 
    | nil => true
    | x::l1 => andb (mem_bool x l2) (included_list l1 l2)
  end.

Lemma included_list_sound : 
  (forall a1 a2 a3, eqA a1 a2 -> eqA a2 a3 -> eqA a1 a3) ->
  forall l1 l2, (included_list l1 l2 = true) -> forall x, mem x l1 -> mem x l2.
Proof.
  intro eq_trans.
  fix included_list_sound 1.
  intros l1 l2;case l1.

  intros _ x abs;elim abs.
  simpl.
  intros a l H x H0.
  case H0.
  revert H; generalize (mem_bool_ok a l2); case (mem_bool a l2).
  intros a_mem_l2 Heq; rewrite mem_in_eq in a_mem_l2; case a_mem_l2; clear a_mem_l2.
intros a' [a_eq_a' a'_in_l2] x_eq_a.
rewrite mem_in_eq; exists a'; split; [apply eq_trans with a | idtac]; assumption.
 intros; discriminate.
  apply included_list_sound.
  case (andb_prop _ _ H );auto.
Qed.

(** ** Association lists. 
*** find. *)
Function find (B : Type) (a : A) (l : list (A * B)) {struct l} : option B :=
 match l with
 | nil => None
 | (a1,b1) :: l =>
     if (eq_bool a a1)
     then Some b1
     else find a l
  end.

Lemma eq_find_eq : equivalence _ eqA -> forall B a a' l, eq_bool a a'  = true -> find (B := B) a l = find a' l.
Proof.
intro eq_proof.
fix eq_find_eq 4.
intros B a a' l; case l; clear l; simpl.
intros _; reflexivity.
intros p l; case p; clear p; simpl.
intros a'' b a_eq_a'; case_eq (eq_bool a a''); case_eq (eq_bool a' a''). 
intros _ _; reflexivity.
intros a'_diff_a'' a_eq_a''; absurd (eqA a' a'').
generalize (eq_bool_ok a' a''); rewrite a'_diff_a''; intro H; exact H.
case eq_proof; intros Req Teq Seq.
apply (Teq a' a a'').
apply Seq; generalize (eq_bool_ok a a'); rewrite a_eq_a'; intro H; exact H.
generalize (eq_bool_ok a a''); rewrite a_eq_a''; intro H; exact H.
intros a'_eq_a'' a_diff_a''; absurd (eqA a a'').
generalize (eq_bool_ok a a''); rewrite a_diff_a''; intro H; exact H.
case eq_proof; intros Req Teq Seq.
apply (Teq a a' a'').
generalize (eq_bool_ok a a'); rewrite a_eq_a'; intro H; exact H.
generalize (eq_bool_ok a' a''); rewrite a'_eq_a''; intro H; exact H.
intros _ _; apply eq_find_eq; assumption.
Qed.

Lemma find_diff :
     forall (B : Type) a1 a2, eq_bool a2 a1 = false -> 
     forall l1 l2 b, find a2 (l1 ++ (a1,b) :: l2) = find (B:= B) a2 (l1 ++ l2).
Proof.
fix find_diff 5.
intros B a1 a2 a2_diff_a1 l1; case l1; clear l1; simpl.
revert a2_diff_a1; generalize (eq_bool_ok a2 a1); case (eq_bool a2 a1).
intros _ Abs; discriminate.
intros _ _ l2; reflexivity.
intros p l1 l2; case p; clear p; intros a b.
intros b1; case (eq_bool a2 a).
reflexivity.
apply find_diff; assumption.
Qed.

Lemma find_mem :
   forall (B : Type)  (a : A)  (l : list (A * B)) (b : B),
  find a l = Some b -> {a' : A & {l1 : list (A * B) & {l2 : list (A * B) | eqA a a' /\ l = l1 ++ (a',b) :: l2 } } }.
Proof.
fix find_mem 3.
intros B a l b; case l; clear l; simpl. 
intro Abs; discriminate.
intros p l; case p; clear p; intros a1 b1.
generalize (eq_bool_ok a a1); case (eq_bool a a1).
intros a_eq_a1 H.
injection H; clear H; intro b1_eq_b.
exists a1; exists (@nil (A*B)) ; exists l; subst; split.
assumption.
reflexivity.
intros _ F; case (find_mem _ _ _ _ F).
intros a' M; case M; clear M.
intros l1 M; case M; clear M.
intros l2 M; case M; clear M.
intros a_eq_a' M.
exists a'; exists ((a1,b1) :: l1); exists l2; repeat split.
assumption.
subst l; reflexivity.
Qed.

Lemma find_not_mem :
  equivalence _ eqA ->
  forall (B : Type)  (a : A) (b : B) (l : list (A * B)) (dom : list A),
  ~mem a dom -> (forall a', mem a' dom -> find a' ((a,b) :: l) = find a' l).
Proof.
intros eq_proof B a b l dom a_not_in_dom a' a'_in_dom; simpl.
generalize (eq_bool_ok a' a); case (eq_bool a' a).
intro a'_eq_a; apply False_rect; apply a_not_in_dom.
apply (mem_eq_mem eq_proof dom a'_eq_a); assumption.
intros _; reflexivity.
Qed.

Lemma find_not_found : 
  forall (B : Type) (a a' : A) (b : B) (l : list (A * B)), find a l = None -> eq_bool a a' = true -> ~In (a',b) l.
Proof.
fix find_not_found 5.
intros B a a' b l; case l; clear l.
intros _ _ Abs; contradiction.
intros p l; case p; clear p; intros a1 b1; simpl.
case_eq (eq_bool a a1).
intros _ Abs; discriminate.
intros a_diff_a1 F a_eq_a' H; case H; clear H; intro H.
injection H; clear H; intros; subst a1 b1.
rewrite a_eq_a' in a_diff_a1; discriminate.
apply (find_not_found _ _ _ _ _ F a_eq_a' H).
Qed.

Lemma find_app :
  forall (B : Type)  a (l1 l2 : list (A * B)),
  find a (l1 ++ l2) =
     if mem_bool a (map (fun st => fst st) l1) then find a l1 else find a l2.  
Proof.
fix find_app 3.
intros B a l1; case l1; clear l1; simpl.
intros l2; reflexivity.
intros p l1 l2; case p; clear p; intros a1 b1; simpl.
case (eq_bool a a1); simpl.
reflexivity.
apply find_app.
Qed.

Lemma find_map : 
  forall (B C : Type) (f : B -> C),
  forall a l, 
   match find a l with
   | Some b => find a (map (fun xval : A * B => (fst xval, f (snd xval))) l) = Some (f b)
   | None => find a (map (fun xval : A * B => (fst xval, f (snd xval))) l) = None
   end.
Proof.
fix find_map 5.
intros B C  f a l; case l; clear l; simpl.
reflexivity.
intros p l; case p; clear p; intros a1 b1; simpl.
case (eq_bool a a1).
reflexivity.
apply find_map.
Qed.

Lemma find_map2 : 
  forall (B C : Type) (f : (A * B) -> C),
  forall a l, 
   match find a l with
   | Some b => exists a', eqA a a' /\ find a (map (fun xval : A * B => (fst xval, f xval)) l) = Some (f (a',b))
   | None => find a (map (fun xval : A * B => (fst xval, f xval)) l) = None
   end.
Proof.
intros B C f a l; induction l as [ | [a1 b1] l]; simpl; trivial.
generalize (eq_bool_ok a a1); destruct (eq_bool a a1).
intro a_eq_a1; exists a1; split; trivial.
trivial.
Qed.

Section Merge.
Variable B : Type.
Variable eqB : relation B.
Variable eqB_bool : B -> B -> bool.
Variable eqB_bool_ok : forall a1 a2, match eqB_bool a1 a2 with true => eqB a1 a2 | false => ~ eqB a1 a2 end.

Fixpoint merge (partial_res l : list (A*B)) {struct l} : option (list (A*B)) :=
  match l with
  | nil => Some partial_res
  | ((a,b) as p) :: l => 
       match find a partial_res with
       | Some b' => if eqB_bool b b' then merge partial_res l else None
       | None => merge (p :: partial_res) l
       end
   end.

Lemma merge_correct :
   equivalence _ eqA -> (reflexive _ eqB) ->
   forall (l1 l2 : list (A * B)), 
       (* (forall a a' b c, In (a,b) l2 -> In (a,c) l2 -> eq_bool a a' = true -> eqB_bool b c = true) -> *)
       match merge l1 l2 with
       | Some l => (forall a b, find a l1 = Some b -> find a l = Some b) /\
                            (forall a b, find a l2 = Some b -> (exists b', find a l = Some b' /\ eqB_bool b b' = true)) /\
                            (forall a b, find a l = Some b -> (find a l1 = Some b \/ (find a l1 = None /\ find a l2 = Some b)))
        | None => exists a, exists a', exists b1, exists b2, 
                                                  (find a l1 = Some b1 \/ In (a,b1) l2) /\ In (a',b2) l2 /\
                                                  eq_bool a a' = true /\ eqB_bool b2 b1 = false
        end.
Proof.
intros eq_proof RB; fix merge_correct 2.
intros l1 l2; case l2; clear l2; simpl.
(* 1/2 l2 = [] *)
repeat split.
intros a b H; exact H.
intros a b H; discriminate.
intros a b H; left; exact H.
(* 1/1 l2 = _ :: _ *)
intros p l2; case p; clear p; intros a2 b2; simpl.
case_eq (find a2 l1).
(* 1/2 find a2 l1 = Some _ *)
intros b F; case_eq (eqB_bool b2 b).
(* 1/3 b2 = b *)
intro b2_eq_b.
generalize (merge_correct l1 l2).
case (merge l1 l2).
(* 1/4 merge l1 l2 = Some l *)
intros l H; case H; clear H.
intros H1 H; case H; clear H.
intros H2 H3.
repeat split.
(* 1/6 *)
assumption.
(* 1/5 *)
intros a b'; case_eq (eq_bool a a2).
intros a_eq_a2 H; injection H; clear H; intro H; subst b'.
exists b; split.
apply H1; rewrite <- F; apply eq_find_eq; assumption.
assumption.
intros a_diff_a2 F'; apply H2; assumption.
(* 1/4 *)
intros a b' F'; case_eq (eq_bool a a2).
intros a_eq_a2.
generalize (H3 _ _ F'); rewrite (eq_find_eq eq_proof l1 a_eq_a2).
intro FF; case FF; clear FF; intro F''.
left; assumption.
case F''; clear F''; intros F'' _; rewrite F in F''; discriminate.
intro a_diff_a2; apply H3; assumption.
(* 1/3 merge l1 l2 = None *)
intros [a [a' [b1 [b1' [[F' | F'] [F'' [a_eq_a' b1_diff_b1']]]]]]];
exists a; exists a'; exists b1; exists b1'; repeat split.
left; assumption.
right; assumption.
assumption.
assumption.
do 2 right; assumption.
right; assumption.
assumption.
assumption.
(* 1/2 b2 <> b *)
intro b2_diff_b.
exists a2; exists a2; exists b; exists b2; repeat split.
left; assumption.
left; reflexivity.
generalize (eq_bool_ok a2 a2); case (eq_bool a2 a2).
intros _; reflexivity.
intro a2_diff_a2; apply False_rect; apply a2_diff_a2; destruct eq_proof as [R _ _]; apply R.
assumption.
(* 1/1 find a2 l1 = None *)
intro F.
generalize (merge_correct ((a2,b2) :: l1) l2).
case (merge ((a2,b2) :: l1) l2); simpl.
(* 1/2 merge ((a2,b2) :: l1) l2 = Some l *)
intros l H; case H; clear H.
intros H1 H; case H; clear H.
intros H2 H3.
repeat split.
(* 1/4 *)
intros a b F'; generalize (H1 a b); case_eq (eq_bool a a2).
intro a_eq_a2; rewrite (eq_find_eq eq_proof l1 a_eq_a2) in F'; rewrite F in F'; discriminate.
intros _ H1a; apply H1a; assumption.
(* 1/3 *)
intros a b'; case_eq (eq_bool a a2).
intros a_eq_a2 H; injection H; clear H; intro H; subst b'.
exists b2; split.
generalize (H1 a b2); rewrite a_eq_a2; intro H1a; apply H1a; reflexivity.
generalize (eqB_bool_ok b2 b2); case (eqB_bool b2 b2).
intros _; reflexivity.
intro b2_diff_b2; apply False_rect; apply b2_diff_b2; apply RB.
intros a_diff_a2 F'; exact (H2 a b' F').
(* 1/2 *)
intros a b F'; generalize (H3 a b F'); case_eq (eq_bool a a2).
intros a_eq_a2 [F'' | FF].
right; split.
rewrite (eq_find_eq eq_proof l1 a_eq_a2); assumption.
assumption.
case FF; intros F'' _; discriminate.
intros _ H; exact H.
(* 1/1 *)
intros [a [a' [b1 [b1' [[F' | F'] [F'' [a_eq_a' b1_diff_b1']]]]]]].
revert F'; case_eq (eq_bool a a2).
intros a_eq_a2 F'; injection F'; clear F'; intro; subst b1.
exists a2; exists a'; exists b2; exists b1'; repeat split.
right; left; reflexivity.
right; assumption.
generalize (eq_bool_ok a2 a'); case (eq_bool a2 a').
intros _; reflexivity.
intro a2_diff_a'; apply False_rect; apply a2_diff_a'.
destruct eq_proof as [Re Te Se].
apply Te with a.
apply Se; generalize (eq_bool_ok a a2); rewrite a_eq_a2; intro H; exact H.
generalize (eq_bool_ok a a'); rewrite a_eq_a'; intro H; exact H.
assumption.
intros a_diff_a2 F'; exists a; exists a'; exists b1; exists b1'; repeat split.
left; assumption.
right; assumption.
assumption.
assumption.
exists a; exists a'; exists b1; exists b1'; repeat split.
do 2 right; assumption.
right; assumption.
assumption.
assumption.
Qed.

Lemma merge_inv :
  equivalence _ eqA -> (reflexive _ eqB) ->
  forall (l1 l2 : list (A*B)), 
       (forall a1 a1' b1 c1, In (a1,b1) l1 -> In (a1',c1) l1 -> eq_bool a1 a1' = true -> eqB_bool b1 c1 =true) ->
       (forall a2 a2' b2 c2, In (a2,b2) l2 -> In (a2',c2) l2 -> eq_bool a2 a2' = true -> eqB_bool b2 c2 = true) ->
       match merge l1 l2 with
       | Some l => (forall a a' b c, In (a,b) l -> In (a',c) l -> eq_bool a a' = true -> eqB_bool b c = true) 
       | None => True
       end.
Proof.
intros eq_proof RB; fix merge_inv 2.
intros l1 l2; case l2; clear l2.
(* 1/2 l2 = [] *)
intros Inv1 _; exact Inv1.
(* 1/1 l2 = _ :: _ *)
intros p l2; case p; clear p; simpl.
intros a2 b2 Inv1 Inv2.
case_eq (find a2 l1).
(* 1/2 find eqA a2 l1 = Some b *)
intros b H; case_eq (eqB_bool b2 b); [intro b2_eq_b | intro b2_diff_b].
(* 1/3 b = b2 *)
apply merge_inv.
exact Inv1.
intros a a' b' c ab_in_l2 ac_in_l2; apply (Inv2 a a' b' c).
right; assumption.
right; assumption.
(* b <> b2 *)
exact I.
(* 1/1 find eqA a2 l1 = None *)
intro H; apply merge_inv; simpl.
intros a a' b' c [H1 | ab_in_l1] [H2 | ac_in_l1].
injection H1; injection H2; intros; subst a a' b' c.
generalize (eqB_bool_ok b2 b2); case (eqB_bool b2 b2).
intros _; reflexivity.
intro b2_diff_b2; apply False_rect; apply b2_diff_b2; apply RB.
injection H1; intros; subst a b'.
apply False_rect; apply (find_not_found c l1 H H3 ac_in_l1).
injection H2; intros; subst a' c.
apply False_rect; refine (find_not_found (a' := a) b' l1 H _ ab_in_l1).
generalize (eq_bool_ok a2 a) (eq_bool_ok a a2); rewrite H3; case (eq_bool a2 a).
intros _ _; reflexivity.
intros a2_diff_a a_eq_a2; apply False_rect; apply a2_diff_a; destruct eq_proof as [_ _ Se]; apply Se; assumption.
apply Inv1; assumption.
intros a a' b' c ab_in_l2 ac_in_l2; apply (Inv2 a a' b' c).
right; assumption.
right; assumption.
Qed.

End Merge.

(** *** number of occurences of the first element of a pair. *)
Function nb_occ (B : Type)  (a : A) (l : list (A * B)) {struct l} : nat :=
  match l with
  | nil => 0
  | (a',_) :: tl =>
     if (eq_bool a a') then S (nb_occ a tl) else nb_occ a tl
  end.

Lemma nb_occ_app :
  forall (B : Type) a (l1 l2 : list (A * B)), 
  nb_occ a (l1++l2) = nb_occ a l1 + nb_occ a l2.
Proof.
fix nb_occ_app 3.
intros B a l1; case l1; clear l1; simpl.
intros l2; reflexivity.
intros p l1 l2; case p; clear p; intros a1 _; simpl.
case (eq_bool a a1).
simpl; rewrite nb_occ_app; reflexivity.
rewrite nb_occ_app; reflexivity.
Qed.

Lemma none_nb_occ_O :
  forall (B : Type) (a : A) (l : list (A * B)), find a l = None -> nb_occ a l = 0.
Proof.
fix none_nb_occ_O 3.
intros B a l; case l; clear l; simpl.
intros _; reflexivity.
intros p l; case p; clear p; intros a1 b1; simpl.
case (eq_bool a a1).
intro Abs; discriminate.
apply none_nb_occ_O.
Qed.

Lemma some_nb_occ_Sn :
  forall (B : Type) (a : A) (l : list (A * B)) b, find a l = Some b -> 1 <= nb_occ a l.
Proof.
fix some_nb_occ_Sn 3.
intros B a l; case l; clear l; simpl.
intros b Abs; discriminate.
intros p l b; case p; clear p; simpl.
intros a1 b1; case (eq_bool a a1).
intros _; apply le_n_S; apply Nat.le_0_l.
apply some_nb_occ_Sn.
Qed.

Lemma reduce_assoc_list :
  equivalence _ eqA ->
  forall (B : Type) (l : list (A * B)),  {l' : list (A * B) | (forall a, nb_occ a l' <= 1) /\ (forall a, find a l = find a l')}.
Proof.
intro eq_proof.
fix reduce_assoc_list 2.
intros B l; case l; clear l; simpl.
exists (nil : list (A * B)); simpl; split.
intros _; apply Nat.le_0_l.
intros _; reflexivity.
intros p l; case p; clear p; simpl.
case (reduce_assoc_list _ l).
intros k' H; case H; clear H; intros H1 H2.
intros a b; case_eq (find a l).
intros b' F; rewrite H2 in F.
case (find_mem _ _ F).
intros a' H; case H; clear H.
intros k1 H; case H; clear H.
intros k2 H; case H; clear H.
intros a_eq_a' H; subst k'.
exists (k1 ++ (a',b) :: k2); split.
intro a''; generalize (H1 a''); do 2 rewrite nb_occ_app; simpl; intro H; exact H.
intro a''; rewrite H2; generalize (H1 a''); rewrite nb_occ_app; simpl.
case_eq (eq_bool a'' a').
intro a''_eq_a'; rewrite Nat.add_comm; simpl; rewrite Nat.add_comm; intro L.
assert (L' := le_S_n _ _ L).
inversion L' as [L'' | ]; clear L L'.
assert (L1 : nb_occ a'' k1 = 0).
revert L''; case (nb_occ a'' k1).
intros _; reflexivity.
simpl; intros n Abs; discriminate.
case_eq (eq_bool a'' a).
intro a''_eq_a.
revert L1; generalize k1; fix IHk 1.
intro k; case k; clear k; simpl.
intros _; rewrite a''_eq_a'; reflexivity.
intros p k; case p; clear p.
intros a1 b1; case (eq_bool a'' a1).
intro; discriminate.
apply IHk.
intro a''_diff_a.
absurd (eqA a'' a).
generalize (eq_bool_ok a'' a); rewrite a''_diff_a; intro H; exact H.
case eq_proof; intros Req Teq Seq.
apply (Teq a'' a' a).
generalize (eq_bool_ok a'' a'); rewrite a''_eq_a'; intro H; exact H.
apply Seq; assumption.
intro a''_diff_a'; case_eq (eq_bool a'' a).
intro a''_eq_a; absurd (eqA a'' a').
generalize (eq_bool_ok a'' a'); rewrite a''_diff_a'; intro H; exact H.
case eq_proof; intros Req Teq Seq.
apply (Teq a'' a a').
generalize (eq_bool_ok a'' a); rewrite a''_eq_a; intro H; exact H.
assumption.
intros _ _; generalize k1; fix IHk 1.
intro k; case k; clear k; simpl.
rewrite a''_diff_a'; reflexivity.
intros p k; case p; clear p; simpl; intros a1 b1; rewrite IHk; reflexivity.

intro F; rewrite H2 in F; exists ((a,b) :: k'); repeat split.
simpl; intro a'; case_eq (eq_bool a' a).
intro a'_eq_a; rewrite <- (eq_find_eq eq_proof k' a'_eq_a) in F.
rewrite (none_nb_occ_O _ _ F); apply le_n.
intros _; apply H1.
simpl; intro a''; rewrite H2; reflexivity.
Qed.

End Eq_bool.

Lemma mem_map_set :
forall (A B : Type) eqB eqB_bool 
(eqB_bool_ok : forall a1 a2, match eqB_bool a1 a2 with true => eqB a1 a2 | false => ~ eqB a1 a2 end)
(f : A -> B) b l, 
mem eqB b (map f l) -> {a : A | eqB b (f a) /\ In a l}.
Proof.
intros A B eqB eqB_bool eqB_bool_ok f b; induction l as [ | a1 l].
contradiction.
generalize (eqB_bool_ok b (f a1)); case (eqB_bool b (f a1)); [intro b_eq_fa1 | intro b_diff_fa1].
intros _; exists a1; split; [assumption | left; apply eq_refl].
simpl; intro b_in_fa1_fl.
destruct IHl as [a [fa_eq_b a_in_l]].
destruct b_in_fa1_fl as [fa1_eq_b | b_in_fl]; [apply False_rect; apply b_diff_fa1 | idtac]; assumption.
exists a; split; [assumption | right; assumption].
Qed.

Function list_forall (A : Type) (f : A -> bool) (l : list A) {struct l} : bool :=
  match l with 
  | nil => true
  | a :: l => ifb (f a) (list_forall f l) false
  end.

Lemma list_forall_app :
   forall (A : Type) (f : A -> bool) (l1 l2 : list A),
   list_forall f (l1 ++ l2) = andb (list_forall f l1) (list_forall f l2).
Proof.
intros A f l1; induction l1 as [ | a1 l1]; simpl; trivial.
intro l2; rewrite (IHl1 l2); destruct (f a1); simpl; trivial.
Qed.

Lemma list_forall_is_sound :
  forall (A : Type) P_bool (l : list A),
  list_forall P_bool l = true <-> 
  (forall a, In a l -> P_bool a = true).
Proof.
fix list_forall_is_sound 3.
intros A P_bool l; case l; clear l; simpl.
split.
intros _ a Abs; contradiction.
intros _; reflexivity.
intros a l; split.
case_eq (P_bool a); intro Pa; simpl.
intros Pl b b_in_al; case b_in_al; clear b_in_al.
intro a_eq_b; subst b; exact Pa.
revert b; rewrite <- (list_forall_is_sound A P_bool l); exact Pl.
intro Abs; discriminate.
intros Pal; rewrite (Pal a (or_introl _ (eq_refl _))); simpl.
rewrite (list_forall_is_sound A P_bool l).
intros b b_in_l; apply Pal; right; assumption.
Qed.

Lemma list_forall_impl :
  forall (A : Type) (f f' : A -> bool) (l : list A), 
  (forall a, In a l -> f a = true -> f' a = true) ->
  (list_forall f l) = true -> (list_forall f' l) = true.
Proof.
intros A f f' l; induction l as [ | a l]; simpl; trivial.
intros Hl; assert (Ha := Hl a (or_introl _ (eq_refl _))).
destruct (f a); simpl.
intro H; rewrite IHl; simpl; trivial.
rewrite (Ha (eq_refl _)); trivial.
intros; apply Hl; trivial; right; trivial.
intro; absurd (false = true); trivial; discriminate.
Qed.

Function list_forall2 (A B : Type) (f : A -> B -> bool) (l : list A) (l' : list B){struct l} : bool :=
  match l, l' with 
  | nil, nil => true
  | (a :: l), (b :: l') => ifb (f a b) (list_forall2 f l l') false
  | _, _ => false
  end.

Lemma list_forall2_is_sound :
  forall (A B : Type) (f : A -> B -> bool) (l : list A) (l' : list B),
  list_forall2 f l l' = true <-> 
  (length l = length l' /\ forall a b, In (a,b) (combine l l') -> f a b = true).
Proof.
intros A B f l; induction l as [ | a l]; destruct l' as [ | b l'].
simpl; intuition.
simpl; intuition; discriminate.
simpl; intuition; discriminate.
simpl; intuition.
destruct (f a b); try discriminate; simpl in H;
destruct (proj1 (IHl l') H) as [H' _]; rewrite H'; trivial.
injection H1; intros; subst a0 b0; 
destruct (f a b); try discriminate; trivial.
destruct (f a b); try discriminate; simpl in H;
destruct (proj1 (IHl l') H) as [_ H']; apply H'; trivial.
rewrite (H1 a b (or_introl _ (eq_refl _))); simpl.
apply (proj2 (IHl l')); split.
injection H0; trivial.
intros; apply H1; right; trivial.
Qed.

Function list_forall_option (A : Type) (f : A -> option bool) (l : list A) 
  {struct l} : option bool :=
  match l with 
  | nil => Some true
  | a :: l => match f a with
	          | None => None
	          | Some true => list_forall_option f l
                  | Some false =>
                         match list_forall_option f l with
                         | None => None
	                 | Some _ => Some false
	                 end
                  end
 end.

Lemma list_forall_option_is_sound :
  forall (A : Type) f l,
  match @list_forall_option A f l with
  | Some true => forall a, In a l -> f a = Some true
  | Some false => (exists a, In a l /\ f a = Some false) /\ 
                            (forall a, In a l -> f a = None -> False)
  | None => exists a, In a l /\ f a = None
  end.
Proof.
intros A f l; induction l as [ | a l].
simpl; intros; contradiction.
simpl; assert (Fa : forall b, b = a -> f b = f a).
intros; subst; trivial.
destruct (f a) as [ [ | ] | ]; generalize (Fa _ (eq_refl _)); clear Fa; intro Fa.
destruct (list_forall_option f l) as [ [ | ] | ].
intros b [b_eq_a | b_in_l]; [subst; rewrite Fa | rewrite IHl]; trivial.
destruct IHl as [[b [b_in_l fb_eq_false]] IHl].
split.
exists b; split; trivial; right; trivial.
intros c [c_eq_a | c_in_l]; 
[ subst; rewrite Fa; discriminate
| apply IHl; trivial].
destruct IHl as [b [b_in_l fb_eq_none]]; exists b; split; trivial; right; trivial.
destruct (list_forall_option f l) as [ [ | ] | ].
split.
exists a; split; trivial; left; trivial.
intros b [b_eq_a | b_in_l]; 
[ subst; rewrite Fa | rewrite IHl; trivial]; discriminate.
destruct IHl as [[b [b_in_l fb_eq_false]] IHl].
split.
exists a; split; trivial; left; trivial.
intros c [c_eq_a | c_in_l]; 
[ subst; rewrite Fa; discriminate | apply IHl; trivial].
destruct IHl as [b [b_in_l fb_eq_none]]; exists b; split; trivial; right; trivial.
exists a; split; trivial; left; trivial.
Qed.

Lemma list_forall_option_is_complete_true :
  forall (A : Type) f l, (forall a, In a l -> f a = Some true) ->
    @list_forall_option A f l = Some true.
Proof.
intros A f l; induction l as [ | a l].
simpl; intros; trivial.
intro H; simpl; rewrite (H _ (or_introl _ (eq_refl _)));
apply IHl; intros; apply H; right; trivial.
Qed.

Lemma list_forall_option_is_complete_false :
  forall (A : Type) f l, (exists a, In a l /\ f a = Some false) ->
                            (forall a, In a l -> f a = None -> False) ->
    @list_forall_option A f l = Some false.
Proof.
intros A f l; induction l as [ | a l].
intros [a [a_in_nil _]] _; contradiction.
intros [b [[b_eq_a | b_in_l] fb_eq_false]] H; simpl.
subst b; rewrite fb_eq_false.
generalize (list_forall_option_is_sound f l);
destruct (list_forall_option f l) as [ [ | ] | ]; trivial.
intros [c [c_in_l fc_eq_none]].
assert (H' := H c (or_intror _ c_in_l) fc_eq_none); contradiction.
generalize (H a (or_introl _ (eq_refl _))); destruct (f a) as [ [ | ] | ].
intros _; apply IHl.
exists b; split; trivial.
intros c c_in_l; apply H; right; trivial.
intros;
generalize (list_forall_option_is_sound f l);
destruct (list_forall_option f l) as [ [ | ] | ]; trivial.
intros [c [c_in_l fc_eq_none]].
assert (H' := H c (or_intror _ c_in_l) fc_eq_none); contradiction.
intro H'; generalize (H' (eq_refl _)); contradiction.
Qed.

Function list_exists (A : Type) (f : A -> bool) (l : list A) {struct l} : bool :=
  match l with
  | nil => false
  | a :: l => ifb (f a) true (list_exists f l)
  end.

Lemma list_exists_app :
   forall (A : Type) (f : A -> bool) (l1 l2 : list A),
   list_exists f (l1 ++ l2) = orb (list_exists f l1) (list_exists f l2).
Proof.
intros A f l1; induction l1 as [ | a1 l1]; simpl; trivial.
intro l2; rewrite (IHl1 l2); destruct (f a1); simpl; trivial.
Qed.
 
Lemma list_exists_is_sound :
  forall (A : Type) (f : A -> bool) (l : list A),
  list_exists f l = true <-> 
  (exists a, In a l /\ f a = true).
Proof.
intros A f l; induction l as [ | a l]; simpl.
split; [intros; discriminate | intros [a [Abs _]]; contradiction].
assert (H: forall a', a' = a -> f a' = f a).
intros; subst; trivial.
destruct (f a); simpl;
  generalize (H _ (eq_refl _)); clear H; intro H; split; intro H'.
exists a; split; trivial; left; trivial.
trivial.
destruct ((proj1 IHl) H') as [a' [a'_in_l fa']]; exists a'; split; trivial;
  right; trivial.
destruct H' as [a' [[a_eq_a' | a'_in_l] fa']]. 
subst a'; rewrite H in fa'; absurd (false = true); trivial; discriminate.
apply (proj2 IHl); exists a'; split; trivial.
Qed.

Lemma list_exists_is_complete_false :
  forall (A : Type) (f : A -> bool) (l : list A), list_exists f l = false ->
  forall a, In a l -> f a = false.
Proof.
intros A f l; induction l as [ | a l]; simpl.
intros; contradiction.
intros H b [a_eq_b | b_in_l].
subst b; destruct (f a); [simpl in H; discriminate | reflexivity].
destruct (f a); [simpl in H; discriminate | apply IHl; trivial].
Qed.

Lemma list_exists_impl :
  forall (A : Type) (f f' : A -> bool) (l : list A), 
  (forall a, In a l -> f a = true -> f' a = true) ->
  (list_exists f l) = true -> (list_exists f' l) = true.
Proof.
intros A f f' l; induction l as [ | a l]; simpl; trivial.
intros Hl; assert (Ha := Hl a (or_introl _ (eq_refl _))).
destruct (f a); simpl.
rewrite (Ha (eq_refl _)); trivial.
intro H; rewrite IHl; simpl; trivial.
destruct (f' a); trivial.
intros; apply Hl; trivial; right; trivial.
Qed.

Function list_exists_option (A : Type) (f : A -> option bool) (l : list A) 
 {struct l} : option bool :=
  match l with
  | nil => Some false
  | a :: l => match f a with
                  | Some true => Some true
                  | Some false => (list_exists_option f l)
                  | None => 
                         match list_exists_option f l with
                         | Some true => Some true
                         | _ => None
                         end
                 end
 end.

Lemma list_exists_option_is_sound :
  forall (A : Type) f l,
  match @list_exists_option A f l with
  | Some true => exists a, In a l /\ f a = Some true
  | Some false => forall a, In a l -> f a = Some false
  | None => (exists a, In a l /\ f a = None) /\ 
                   (forall a, In a l -> f a = Some true -> False)
  end.
Proof.
intros A f l; induction l as [ | a l].
simpl; intros; contradiction.
simpl; assert (Fa : forall b, b = a -> f b = f a).
intros; subst; trivial.
destruct (f a) as [ [ | ] | ]; generalize (Fa _ (eq_refl _)); clear Fa; intro Fa.
destruct (list_exists_option f l) as [ [ | ] | ];
exists a; split; trivial; left; trivial.
destruct (list_exists_option f l) as [ [ | ] | ].
destruct IHl as [b [b_in_l fb_eq_true]]; exists b; split; trivial; right; trivial.
intros b [b_eq_a | b_in_l]; [subst; rewrite Fa | rewrite IHl]; trivial.
destruct IHl as [ [b [b_in_l fb_eq_none]] IHl]; split.
exists b; split; trivial; right; trivial.
intros c [c_eq_a | c_in_l]; 
[ subst; rewrite Fa; discriminate | apply IHl; trivial].
destruct (list_exists_option f l) as [ [ | ] | ].
destruct IHl as [b [b_in_l fb_eq_true]]; exists b; split; trivial; right; trivial.
split.
exists a; split; trivial; left; trivial.
intros b [b_eq_a | b_in_l]; 
[ subst; rewrite Fa | rewrite IHl; trivial]; discriminate.
split.
exists a; split; trivial; left; trivial.
destruct IHl as [ _ IHl]; intros b [b_eq_a | b_in_l]; 
[ subst; rewrite Fa; discriminate | apply IHl; trivial].
Qed.

Lemma list_exists_option_is_complete_true :
  forall (A : Type) f l, (exists a, In a l /\ f a = Some true) ->
                       @list_exists_option A f l = Some true.
Proof.
intros A f l; induction l as [ | a l].
simpl; intros [a [a_in_nil fa_eq_true]]; contradiction.
intros [b [[b_eq_a | b_in_l] fb_eq_true]]; simpl.
subst b; rewrite fb_eq_true; trivial.
destruct (f a) as [ [ | ] | ]; trivial.
rewrite IHl; trivial; exists b; split; trivial.
rewrite IHl; trivial; exists b; split; trivial.
Qed.

Lemma list_exists_option_is_complete_false :
  forall (A : Type) f l, (forall a, In a l -> f a = Some false) ->
                       @list_exists_option A f l = Some false.
Proof.
intros A f l; induction l as [ | a l].
intros; simpl; trivial.
intros H; simpl.
rewrite (H _ (or_introl _ (eq_refl _)));
apply IHl; intros; apply H; right; trivial.
Qed.

Lemma list_exists_option_is_complete_none :
 forall A f l, (exists a, In a l /\ f a = None) ->
                   (forall a, In a l -> f a = Some true -> False) ->
	               @list_exists_option A f l = None.
Proof.
intros A f l; induction l as [ | t l].
intros [a [a_in_nil _]]; contradiction.
simpl; intros [a [[a_eq_t | a_in_l] fa_eq_none]] H.
subst a; rewrite fa_eq_none.
generalize (list_exists_option_is_sound f l);
destruct (list_exists_option f l) as [ [ | ] | ]; trivial.
intros [a [a_in_l fa_eq_true]]; 
assert False; [idtac | contradiction].
apply (H a); trivial; right; trivial.
generalize (H t (or_introl _ (eq_refl _))); destruct (f t) as [ [ | ] | ].
intro H'; assert (H'' := H' (eq_refl _)); contradiction.
intros _; apply IHl.
exists a; split; trivial.
intros b b_in_l; apply H; right; trivial.
intros _; generalize (list_exists_option_is_sound f l);
destruct (list_exists_option f l) as [ [ | ] | ].
intros [b [b_in_l fb_eq_true]]; 
assert False; [idtac | contradiction].
apply (H b); trivial; right; trivial.
trivial.
trivial.
Qed.

Definition list_exists_rest : forall (A : Type) (P : A -> Prop) l 
(P_dec : forall a, In a l -> {P a}+{~P a}), bool.
Proof.
intros A P l; induction l as [ | a l]; intro P_dec.
exact false.
case (P_dec a (or_introl _ (eq_refl _))).
intros; exact true.
intros; assert (P_dec' : forall a : A, In a l -> {P a} + {~ P a}).
intros; apply P_dec; right; trivial.
exact (IHl P_dec').
Defined.

Lemma list_exists_rest_is_sound :
  forall (A : Type) (P : A -> Prop) l P_dec,
  list_exists_rest P l P_dec= true <->  (exists a, In a l /\ P a).
Proof.
intros A P l; induction l as [ | a l]; intros P_dec; simpl.
split; [intros; discriminate | intros [a [Abs _]]; contradiction].
destruct (P_dec a) as [Pa | not_Pa].
split; trivial.
intros _; exists a; split; trivial; left; trivial.
split.
intro H; rewrite IHl in H.
destruct H as [b [b_in_l Pb]]; exists b; split; trivial; right; trivial.
intro H; destruct H as [b [[b_eq_a | b_in_l] Pb]].
subst b; absurd (P a); trivial.
rewrite IHl; exists b; split; trivial.
Qed.

Fixpoint mapi (A : Type) (f : A -> A) (l : list A) {struct l} : list (list A) :=
  match l  with
  | nil => nil
  | a :: l => ((f a) :: l) :: (map (fun k => a :: k) (mapi f l))
  end.

Lemma mapi_spec :
  forall (A : Type) (f : A -> A) l l',
  (In l' (mapi f l) <-> exists l1, exists a, exists l2, l = l1 ++ a :: l2 /\ l' = l1 ++ (f a) :: l2).
Proof.
intros A f l; induction l as [ | a l]; intros l'; split; intro H.
contradiction.
destruct H as [[ | a1 l1] [a [l2 [H _]]]]; discriminate.
simpl in H; destruct H as [H | H].
exists (@nil A); exists a; exists l; split; subst; trivial.
rewrite in_map_iff in H; destruct H as [l'' [H1 H2]].
rewrite (IHl l'') in H2.
destruct H2 as [l1 [b [l2 [K K']]]].
exists (a :: l1); exists b; exists l2; subst; split; trivial.
destruct H as [l1 [b [l2 [K K']]]]; subst.
destruct l1 as [ | a1 l1]; simpl in K; injection K; clear K; intros; subst.
simpl; left; trivial.
right; simpl; rewrite in_map_iff.
exists (l1 ++ f b :: l2); split; trivial.
rewrite IHl.
exists l1; exists b; exists l2; split; trivial.
Qed.

Fixpoint mapii (A : Type) (f : A -> list A) (l : list A) {struct l} : list (list A) :=
  match l  with
  | nil => nil
  | a :: l => (map (fun b => b :: l) (f a)) ++ (map (fun k => a :: k) (mapii f l))
  end.

Lemma mapii_spec :
  forall (A : Type) (f : A -> list A) l l',
  (In l' (mapii f l) <-> exists l1, exists a, exists b, exists l2, 
                                  In b (f a) /\ l = l1 ++ a :: l2 /\ l' = l1 ++ b :: l2).
Proof.
intros A f l; induction l as [ | a l]; intros l'; split; intro H.
contradiction.
destruct H as [[ | a1 l1] [a [b [l2 [_ [H _]]]]]]; discriminate.
simpl in H; destruct (in_app_or _ _ _ H) as [H' | H']; clear H; rename H' into H.
rewrite in_map_iff in H; destruct H as [b [H1 H2]].
exists (@nil A); exists a; exists b; exists l; subst; repeat split; trivial.
rewrite in_map_iff in H; destruct H as [l'' [H1 H2]].
rewrite (IHl l'') in H2.
destruct H2 as [l1 [a' [b [l2 [K [K' K'']]]]]].
exists (a :: l1); exists a'; exists b; exists l2; subst; repeat split; trivial.
destruct H as [l1 [a' [b [l2 [K [K' K'']]]]]]; subst.
destruct l1 as [ | a1 l1]; simpl in K'; injection K'; clear K'; intros; subst.
simpl; apply in_or_app; left; rewrite in_map_iff; exists b; split; trivial.
simpl; apply in_or_app; right; simpl; rewrite in_map_iff.
exists (l1 ++ b :: l2); split; trivial.
rewrite IHl.
exists l1; exists a'; exists b; exists l2; repeat split; trivial.
Qed.

Section DepFun.
Variable A : Type.

Inductive dep_fun : Type :=
  | Dep_fun : forall (l : list A) (f : forall t, In t l -> list A), dep_fun. 

Definition o_length (lf1 lf2: dep_fun) := 
  match lf1, lf2 with
  | Dep_fun l1 _, Dep_fun l2 _ => length l1 < length l2
  end.

Lemma wf_length : well_founded o_length.
Proof.
unfold well_founded, o_length.
intros [l f]; apply Acc_intro.
generalize (length l); clear f l. 
intro n; induction n as [ | n].
intros [y f] Abs; absurd (length y < 0); auto with arith.
intros [y f] Sy; inversion Sy; subst.
apply Acc_intro; intros x Sx; apply IHn; trivial.
apply IHn; trivial.
Defined.

Definition dep_fun_tail : forall (a : A) (l : list A) (f : forall t, In t (a :: l) -> list A), dep_fun. 
intros a l f.
assert (f' : forall t, In t l -> list A).
intros t t_in_l; exact (f t (or_intror _ t_in_l)).
exact (Dep_fun l f').
Defined.

Lemma map_dep_call :
  forall a l f, o_length (dep_fun_tail f) (Dep_fun (a :: l) f).
Proof.
intros a f l; simpl; auto with arith.
Qed.

Definition F_mapii: 
    forall (lf : dep_fun) (mrec : forall lf', o_length lf' lf -> list (list A)), list (list A).
Proof.
intros [l f] mrec; destruct l as [ | a l].
exact nil.
exact (map (fun b => b :: l) (f a (or_introl _ (eq_refl _))) ++
          (map (fun k => a :: k) (mrec (dep_fun_tail f) (map_dep_call f)))).
Defined.

Definition mapii_dep : dep_fun -> list (list A) :=
Fix wf_length (fun lf => list (list A)) F_mapii.

Lemma mapii_dep_unfold : 
  forall lf : dep_fun, mapii_dep lf = @F_mapii lf (fun y _ => mapii_dep y).
Proof.
intros lf; unfold mapii_dep.
refine (Fix_eq _ _ _ _ lf).
clear lf; intros [l f] F G H.
unfold F_mapii; destruct l as [ | a l]; simpl; auto.
rewrite H; trivial.
Qed.

Lemma mapii_dep_spec :
  (forall a1 a2 : A, {a1 = a2}+{a1 <> a2}) -> forall l f l',
  (forall a a_in_l a_in_l', f a a_in_l = f a a_in_l') ->
  (In l' (mapii_dep (Dep_fun l f)) <-> exists l1, exists a, exists a_in_l, exists b, exists l2,  
                                  In b (f a a_in_l) /\ l = l1 ++ a :: l2 /\ l' = l1 ++ b :: l2).
Proof.
intros eqA l; induction l as [ | a l]; intros f l' proof_ir; split; intro H.
contradiction.
destruct H as [[ | a1 l1] [a [a_in_l [b [l2 [_ [H _]]]]]]]; discriminate.
rewrite mapii_dep_unfold in H; simpl in H.
destruct (in_app_or _ _ _ H) as [H' | H']; clear H; rename H' into H.
rewrite in_map_iff in H; destruct H as [b [H1 H2]].
exists (@nil A); exists a; 
exists (or_introl
             ((fix In (a : A) (l : list A) {struct l} : Prop :=
                 match l with
                 | nil => False
                 | b :: m => b = a \/ In a m
                 end) a l) (eq_refl a));
exists b; exists l; subst; repeat split; trivial.
rewrite in_map_iff in H; destruct H as [l'' [H1 H2]].
unfold dep_fun_tail in H2.
rewrite IHl in H2.
destruct H2 as [l1 [a' [a'_in_l [b [l2 [K [K' K'']]]]]]].
exists (a :: l1); exists a'; exists (or_intror (a = a') a'_in_l);
exists b; exists l2; subst; repeat split; trivial.
intros; apply proof_ir; right; trivial.
destruct H as [l1 [a' [a'_in_l [b [l2 [K [K' K'']]]]]]]; subst.
destruct l1 as [ | a1 l1]; simpl in K'; injection K'; clear K'; intros.
subst l2 a'.
simpl; rewrite mapii_dep_unfold; simpl.
apply in_or_app; left; rewrite in_map_iff; exists b; split; trivial.
simpl; rewrite <- (proof_ir a a'_in_l); trivial.
rewrite mapii_dep_unfold; simpl.
apply in_or_app; right; simpl; rewrite in_map_iff.
exists (l1 ++ b :: l2); split; subst a1; trivial.
unfold dep_fun_tail.
rewrite IHl.
destruct (eqA a a') as [a_eq_a' | a_diff_a'].
subst a'.
assert (a_in_l : In a l).
clear K; subst l; apply in_or_app; right; left; trivial.
exists l1; exists a; exists a_in_l; exists b; exists l2; repeat split; trivial.
rewrite <- (proof_ir a a'_in_l); trivial.
assert (a'_in_l' : In a' l).
clear K; destruct a'_in_l as [a'_eq_a | a'_in_l]; trivial.
absurd (a = a'); trivial.
exists l1; exists a'; exists a'_in_l'; exists b; exists l2; repeat split; trivial.
rewrite <- (proof_ir a' a'_in_l); trivial.
intros a'' a''_in_l1 a''_in_l2; refine (proof_ir a'' _ _).
Qed.

Lemma mapii_dep_eq :
  forall l f g, (forall t (t_in_l : In t l), f t t_in_l = g t t_in_l) -> 
  mapii_dep (Dep_fun l f) = mapii_dep (Dep_fun l g).
Proof.
intro l; induction l as [ | a l]; intros f g H; do 2 rewrite mapii_dep_unfold; simpl; trivial.
rewrite (H a).
apply (f_equal (fun ll =>
 map (fun b : A => b :: l)
  (g a
     (or_introl
        ((fix In (a0 : A) (l0 : list A) {struct l0} : Prop :=
            match l0 with
            | nil => False
            | b :: m => b = a0 \/ In a0 m
            end) a l) (eq_refl a))) ++
   map (fun k : list A => a :: k) ll)).
unfold dep_fun_tail.
apply IHl.
intros; apply H; right; trivial.
Qed.
End DepFun.

(* 
Lemma list_exists_is_sound :
  forall (A : Type) P (P_dec : forall a, {P a}+{~P a}) (l : list A),
  list_exists (fun a => if P_dec a then true else false) l = true <-> 
  (exists a, In a l /\ P a).
Proof.
intros A P P_dec l; induction l as [ | a l]; simpl.
split; [intros; discriminate | intros [a [Abs _]]; contradiction].
destruct (P_dec a) as [Pa | not_Pa]; simpl; split; intro H.
exists a; split; trivial; left; trivial.
trivial.
destruct ((proj1 IHl) H) as [a' [a'_in_l Pa']]; exists a'; split; trivial; right; trivial.
destruct H as [a' [[a_eq_a' | a'_in_l] Pa']]. 
absurd (P a); subst; trivial.
apply (proj2 IHl); exists a'; split; trivial.
Qed.
*)

(** map_without_repetition applies a function to the elements of a list,
but only a single time when there are several consecutive occurences of the
same element. Moreover, the function is supposed to return an option as a result,
in order to simulate exceptions, and the abnormal results are discarted.
*)

Function map_without_repetition (A B : Type) 
  (eq_bool : A -> A -> bool) 
  (f : A -> option B) (l : list A) {struct l} : list B :=
    match l with
    | nil => (nil : list B)
    | a1 :: l1 =>
           match l1 with
           | nil =>
              match f a1 with
              | None => nil
              | Some b1 => b1 :: nil
              end
           | a2 :: _ =>
              if eq_bool a1 a2 
              then map_without_repetition eq_bool f l1
              else 
                 match f a1 with
                 | None => map_without_repetition eq_bool f l1
                 | Some b1 => b1 :: (map_without_repetition eq_bool f l1)
                 end
           end
      end.

Lemma prop_map_without_repetition :
 forall (A B : Type) (eq_bool : A -> A -> bool) 
 (eq_bool_ok :forall a1 a2 : A, match eq_bool a1 a2 with true => a1 = a2 | false => a1 <> a2 end)
  (P : B -> Prop) f l,
  (forall a, In a l -> 
   match f a with 
   | None => True 
   | Some f_a => P f_a
   end) ->
   (forall b, In b (map_without_repetition eq_bool f l) -> P b).
Proof.
intros A B eq_bool eq_bool_ok P f; fix prop_map_without_repetition 1; intro l; case l; clear l; simpl.
(* 1/2 l = nil *)
intros _ b b_in_nil; contradiction.
(* 1/1 l = _ :: _ *)
intros a l IH; generalize (prop_map_without_repetition l (tail_prop _ IH)); revert IH.
case l; clear l.
(* 1/2 l = _ :: nil *)
intros IH H b; generalize (IH a (or_introl _ (eq_refl _))); case (f a).
simpl; intros b' Pb' [b_eq_b' | b_in_nil].
subst b'; assumption.
contradiction.
intros _ b_in_nil; contradiction.
(* 1/1 l = _ :: _ :: _ *)
intros a2 l IH H b; generalize (eq_bool_ok a a2); case (eq_bool a a2); [intro a_eq_a2 | intro a_diff_a2].
apply H.
generalize (IH a (or_introl _ (eq_refl _))); case (f a).
simpl In; intros b' Pb' [b_eq_b' | b_in_mapl].
subst b'; assumption.
apply H; assumption.
intros _; apply H.
Qed.

Lemma exists_map_without_repetition :
  forall (A B : Type) (eq_bool : A -> A -> bool) 
 (eq_bool_ok :forall a1 a2 : A, match eq_bool a1 a2 with true => a1 = a2 | false => a1 <> a2 end)
  (P : B -> Prop) f l,
  (exists a,  In a l /\ match f a with 
                        | None => False
                        | Some b => P b
                        end) ->
  (exists b, In b (map_without_repetition eq_bool f l) /\ P b).
Proof.
intros A B eq_bool eq_bool_ok P f; fix exists_map_without_repetition 1; intro l; case l; clear l; simpl.
(* 1/2 l = nil *)
intros [a [F _]]; contradiction.
(* 1/1 l = _ :: _ *)
intros a l; generalize (exists_map_without_repetition l).
case l; clear l.
(* 1/2 l = _ :: nil *)
intros _ [a' [[a_eq_a' | a'_in_nil] H2]].
subst a'; revert H2; case (f a).
intros b Pb; exists b; split; [left; reflexivity | assumption].
contradiction.
contradiction.
(* 1/1 l = _ :: _ :: _ *)
intros a2 l IH H; generalize (eq_bool_ok a a2); case (eq_bool a a2); [intro a_eq_a2 | intro a_diff_a2].
apply IH.
destruct H as [a' [[a_eq_a' | a'_in_a2l] H]].
subst a' a2; exists a; split; [left; reflexivity | assumption].
exists a'; split; assumption.
destruct H as [a' [[a_eq_a' | a'_in_a2l] H]].
subst a'; revert H; case (f a).
intros b Pb; exists b; split; [left; reflexivity | assumption].
contradiction.
destruct IH as [b [b_in_map Pb]].
exists a'; split; assumption.
exists b; split; [case (f a) | assumption].
intros b'; right; assumption.
assumption.
Qed.

(** map12_without_repetition is similar to map_without_repetition, but the 
applied function returns two optional results instead of one.
*)

Function map12_without_repetition (A B : Type) 
  (eq_bool : A -> A -> bool) 
  (f : A -> option B * option B) (l : list A) {struct l} : list B :=
   match l with
    | nil => (nil : list B)
    | a1 :: l1 =>
           match l1 with
           | nil =>
              match f a1 with
              | (None, None) => nil
              | (Some b1, None) => b1 :: nil
              | (None, Some c1) => c1 :: nil
              | (Some b1, Some c1) => b1 :: c1 :: nil
              end
           | a2 :: _ =>
              if eq_bool a1 a2
              then map12_without_repetition eq_bool f l1
              else 
                 match f a1 with
                 | (None, None) => map12_without_repetition eq_bool f l1
                 | (Some b1, None) => b1 :: map12_without_repetition eq_bool f l1
                 | (None, Some c1) => c1 :: map12_without_repetition eq_bool f l1
                 | (Some b1, Some c1) => b1 :: c1 :: map12_without_repetition eq_bool f l1
                  end
           end
      end.

Lemma prop_map12_without_repetition :
  forall A B  (eq_bool : A -> A -> bool) 
 (eq_bool_ok :forall a1 a2 : A, match eq_bool a1 a2 with true => a1 = a2 | false => a1 <> a2 end)
   (P : B -> Prop) f l,
  (forall a, In a l -> 
   match f a with 
   | (None, None) => True 
   | (Some b, None) => P b
   | (None, Some c) => P c
   | (Some b, Some c) => P b /\ P c
   end) ->
 (forall d, In d (map12_without_repetition eq_bool f l) -> P d).
Proof.
intros A B eq_bool eq_bool_ok P f; fix prop_map12_without_repetition 1; intro l; case l; clear l.
(* 1/2 l = nil *)
intros _ b b_in_nil; contradiction.
(* 1/1 l = _ :: _ *)
intros a l IH; generalize (prop_map12_without_repetition l (tail_prop _ IH)); revert IH.
case l; clear l; simpl.
(* 1/2 l = _ :: nil *)
intros IH H b; generalize (IH a (or_introl _ (eq_refl _))); destruct (f a) as [[b' | ] [b'' | ]].
intros [Pb' Pb''] [b_eq_b' | [b_eq_b'' | b_in_nil]].
subst b'; assumption.
subst b''; assumption.
contradiction.
intros Pb' [b_eq_b' | b_in_nil].
subst b'; assumption.
contradiction.
intros Pb'' [b_eq_b'' | b_in_nil].
subst b''; assumption.
contradiction.
contradiction.
(* 1/1 l = _ :: _ :: _ *)
intros a2 l IH; simpl; generalize (eq_bool_ok a a2); case (eq_bool a a2); [intro a_eq_a2 | intro a_diff_a2].
intros Hl b b_in_map; apply Hl; assumption.
generalize (IH a (or_introl _ (eq_refl _))); destruct (f a) as [[b' | ] [b'' | ]].
intros [Pb' Pb''] Hl b [b_eq_b' | [b_eq_b'' | b_in_map]].
subst b; assumption.
subst b; assumption.
apply Hl; assumption.
intros Pb' Hl b [b_eq_b' | b_in_map].
subst b; assumption.
apply Hl; assumption.
intros Pb'' Hl b [b_eq_b'' | b_in_map].
subst b; assumption.
apply Hl; assumption.
intros _ Hl b b_in_map; apply Hl; assumption.
Qed.

Lemma exists_map12_without_repetition :
  forall A B (eq_bool : A -> A -> bool) 
 (eq_bool_ok :forall a1 a2 : A, match eq_bool a1 a2 with true => a1 = a2 | false => a1 <> a2 end)
 (P : B -> Prop) f l,
  ((exists a, In a l /\ match f a with 
                        | (None, None) => False
                        | (Some b, None) => P b
                        | (None, Some c) => P c
                        | (Some b, Some c) => P b \/ P c
                        end) ->
  (exists d, In d (map12_without_repetition eq_bool f l) /\ P d)).
Proof.
intros A B eq_bool eq_bool_ok P f; fix exists_map12_without_repetition 1; intro l; case l; clear l.
(* 1/2 l = nil *)
intros [a [a_in_nil _]]; contradiction.
(* 1/1 l = _ :: _ *)
intros a l; assert (IH := exists_map12_without_repetition l).
intros [a0 [[a0_eq_a | a0_in_l] H]].
(* 1/2 a is the witness *)
subst a0; simpl; revert IH; case l; clear l. 
(* 1/3 l = _ :: nil *)
intros _; revert H; destruct (f a) as [[b' | ] [b'' | ]].
intros [Pb' | Pb''].
exists b'; split; [left; reflexivity | assumption].
exists b''; split; [right; left; reflexivity | assumption].
intros Pb'; exists b'; split; [left; reflexivity | assumption].
intros Pb''; exists b''; split; [left; reflexivity | assumption].
contradiction.
(* 1/2 l = _ :: _ :: _ *)
intros a2 l IH.
generalize (eq_bool_ok a a2); case (eq_bool a a2); [intro a_eq_a2 | intro a_diff_a2].
apply IH; exists a; split; [left; symmetry | idtac]; assumption.
revert H; destruct (f a) as [[b' | ] [b'' | ]].
intros [Pb' | Pb''].
exists b'; split; [left; reflexivity | assumption].
exists b''; split; [right; left; reflexivity | assumption].
intros Pb'; exists b'; split; [left; reflexivity | assumption].
intros Pb''; exists b''; split; [left; reflexivity | assumption].
contradiction.
(* 1/1 the witness is in l *)
destruct IH as [d [d_in_map Pd]].
exists a0; split; assumption.
exists d; split; [idtac | assumption].
revert d_in_map; simpl; case l; clear a0_in_l l.
contradiction.
intros a2 l; case (eq_bool a a2).
intro; assumption.
destruct (f a) as [[b' | ] [b'' | ]].
intro; do 2 right; assumption.
intro; right; assumption.
intro; right; assumption.
intro; assumption.
Qed.



