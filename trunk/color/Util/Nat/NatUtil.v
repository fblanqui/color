(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02
- Adam Koprowski, 2007-03-29
- Frederic Blanqui, 2009-05-11

useful definitions and lemmas on natural numbers
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Export Arith Omega.

(***********************************************************************)
(** implicit arguments *)

Implicit Arguments lt_S_n [n m].
Implicit Arguments lt_n_S [n m].
Implicit Arguments le_S [n m].
Implicit Arguments gt_le_S [n m].
Implicit Arguments le_lt_n_Sm [n m].
Implicit Arguments lt_le_weak [n m].
Implicit Arguments le_plus_minus [n m].
Implicit Arguments le_plus_minus_r [n m].

(***********************************************************************)
(** tactics *)

Ltac Omega := intros; omega.

Ltac absurd_arith := elimtype False; Omega.

(***********************************************************************)
(** natural numbers strictly smaller than some n *)

Record nat_lt (n : nat) : Type := mk_nat_lt { val :> nat; prf : val < n }.

(***********************************************************************)
(** relations and morphisms *)

Add Relation nat le
  reflexivity proved by le_refl
  transitivity proved by le_trans
    as le_rel.

Add Relation nat lt
  transitivity proved by lt_trans
    as lt_rel.

Lemma ge_refl : forall x, x >= x.

Proof. Omega. Qed.

Lemma ge_trans : forall x y z, x >= y -> y >= z -> x >= z.

Proof. Omega. Qed.

Add Relation nat ge
  reflexivity proved by ge_refl
  transitivity proved by ge_trans
    as ge_rel.

Add Relation nat gt
  transitivity proved by gt_trans
    as gt_rel.

(***********************************************************************)
(** boolean function for equality *)

Fixpoint beq_nat (x y : nat) :=
  match x, y with
    | 0, 0 => true
    | S x', S y' => beq_nat x' y'
    | _, _ => false
  end.

Lemma beq_nat_ok : forall x y, beq_nat x y = true <-> x = y.

Proof.
induction x; destruct y; simpl; split; intro; try (refl || discriminate).
apply (f_equal S). exact (proj1 (IHx _) H).
apply (proj2 (IHx y)). inversion H. refl.
Defined.

Require Import EqUtil.

Ltac case_beq_nat := case_beq beq_nat beq_nat_ok.

Lemma eq_nat_dec_refl : forall n, eq_nat_dec n n = left (n<>n) (refl_equal n).

Proof.
intro. generalize (eq_nat_dec n n). destruct s.
rewrite (UIP_refl eq_nat_dec e). refl. irrefl.
Qed.

(***********************************************************************)
(** boolean functions for ordering *)

Fixpoint bgt_nat (x y : nat) :=
  match x, y with
    | 0, _ => false
    | S _, 0 => true
    | S x', S y' => bgt_nat x' y'
  end.

Lemma bgt_nat_ok : forall x y, bgt_nat x y = true <-> x > y.

Proof.
induction x; destruct y; simpl; split; intro;
  try (refl || discr || absurd_arith || omega).
rewrite IHx in H. omega. apply lt_S_n in H. rewrite IHx. hyp.
Qed.

Ltac check_gt := rewrite <- bgt_nat_ok; check_eq.

Lemma bgt_nat_ko : forall x y, bgt_nat x y = false <-> x <= y.

Proof.
induction x; destruct y; simpl; split; intro;
  try (refl || discr || absurd_arith || omega).
rewrite IHx in H. omega. apply le_S_n in H. rewrite IHx. hyp.
Qed.

Fixpoint bge_nat (x y : nat) :=
  match x, y with
    | 0, 0 => true
    | 0, _ => false
    | S _, 0 => true
    | S x', S y' => bge_nat x' y'
  end.

Lemma bge_nat_ok : forall x y, bge_nat x y = true <-> x >= y.

Proof.
induction x; destruct y; simpl; split; intro;
  try (refl || discr || absurd_arith || omega).
rewrite IHx in H. omega. apply le_S_n in H. rewrite IHx. hyp.
Qed.

Ltac check_ge := rewrite <- bge_nat_ok; check_eq.

Definition blt_nat x y := bgt_nat y x.

Lemma blt_nat_ok : forall x y, blt_nat x y = true <-> x < y.

Proof. intros. unfold blt_nat. rewrite bgt_nat_ok. omega. Qed.

Definition bne_nat x y := negb (beq_nat x y).

Require Import BoolUtil.

Lemma bne_nat_ok : forall x y, bne_nat x y = true <-> x <> y.

Proof.
  intros x y. unfold bne_nat. rewrite negb_lr. simpl.
  rewrite (beq_ko beq_nat_ok). refl.
Qed.

(***********************************************************************)
(** unicity of eq, le and lt proofs *)

Lemma eq_unique : forall (n m : nat) (h1 h2 : n = m), h1 = h2.

Proof.
intros. apply UIP. apply eq_nat_dec.
Qed.

Scheme le_ind_dep := Induction for le Sort Prop.

Lemma le_unique : forall n m (h1 h2 : n <= m), h1 = h2.

Proof.
intro n.
assert (forall m : nat, forall h1 : le n m, forall p : nat, forall h2 : le n p,
  m=p -> eq_dep nat (le n) m h1 p h2).
 intros m h1; elim h1 using le_ind_dep.
  intros p h2; case h2; intros.
   auto.
   subst n. absurd (S m0 <= m0); auto with arith.
 intros m0 l Hrec p h2. 
  case h2; intros.
   subst n; absurd (S m0 <= m0); auto with arith.
   assert (m0=m1); auto ; subst m0.
   replace l0 with l; auto.
   apply (@eq_dep_eq _ eq_nat_dec (le n) m1); auto.
 intros; apply (@eq_dep_eq _ eq_nat_dec (le n) m); auto.
Qed.

Lemma lt_unique : forall n m (h1 h2 : n < m), h1 = h2.

Proof.
intros n m. unfold lt. intros. apply le_unique.
Qed.

Lemma lt_Sn_nS : forall m n (H : m < n), lt_S_n (lt_n_S H) = H.

Proof.
  intros. apply lt_unique.
Qed.

Lemma lt_nS_Sn : forall m n (H : S m < S n), lt_n_S (lt_S_n H) = H.

Proof.
  intros. apply lt_unique.
Qed.

(***********************************************************************)
(** max *)

Require Import Max.

Implicit Arguments max_r [x y].
Implicit Arguments max_l [x y].
Implicit Arguments le_trans [n m p].

Require Import Compare.

Lemma max_assoc : forall a b c, max a (max b c) = max (max a b) c.

Proof.
intros.
case (le_dec b c); intro H.
 rewrite (max_r H).
 case (le_dec a b); intro H'.
  rewrite (max_r (le_trans H' H)).
  rewrite (max_r H'). rewrite (max_r H). reflexivity.
  case (le_dec a c); intro H''; rewrite (max_l H'); reflexivity.
  rewrite (max_l H).
  case (le_dec a b); intro H'.
   rewrite (max_r H').
   apply (sym_equal (max_l H)).
   assert (H'' : c <= max a b). eapply le_trans. apply H. apply le_max_r.
   apply (sym_equal (max_l H'')).
Qed.

Lemma le_max_intro_l : forall x y z, x <= y -> x <= max y z.

Proof.
intros. eapply le_trans. apply H. apply le_max_l.
Qed.

Lemma lt_max_intro_l : forall x y z, x < y -> x < max y z.

Proof.
intros. eapply lt_le_trans. eexact H. apply le_max_l.
Qed.

Lemma le_max_intro_r : forall x y z, x <= z -> x <= max y z.

Proof.
intros. eapply le_trans. apply H. apply le_max_r.
Qed.

Lemma lt_max_intro_r : forall x y z, x < z -> x < max y z.

Proof.
intros. rewrite max_comm. apply lt_max_intro_l. hyp.
Qed.

Lemma le_max_elim_l : forall x y z, max x y <= z -> x <= z.

Proof.
intros. eapply le_trans. 2: apply H. apply le_max_l.
Qed.

Lemma le_max_elim_r : forall x y z, max x y <= z -> y <= z.

Proof.
intros. eapply le_trans. 2: apply H. apply le_max_r.
Qed.

Lemma max_ge_compat : forall x y x' y',
  x >= x' -> y >= y' -> max x y >= max x' y'.

Proof.
intros. destruct (max_dec x' y'); rewrite e; unfold ge.
rewrite max_comm. apply le_max_intro_r. hyp.
apply le_max_intro_r. hyp.
Qed.

Lemma max_gt_compat : forall x y x' y',
  x > x' -> y > y' -> max x y > max x' y'.

Proof.
intros. destruct (le_ge_dec x y); destruct (le_ge_dec x' y');
  do 2 first
    [ rewrite max_r; [idtac | hyp] 
    | rewrite max_l; [idtac | hyp]
    ]; omega.
Qed.

Lemma min_gt_compat : forall x y x' y',
  x > x' -> y > y' -> min x y > min x' y'.

Proof.
intros. destruct (le_ge_dec x y); destruct (le_ge_dec x' y');
  do 2 first
    [ rewrite min_r; [idtac | hyp] 
    | rewrite min_l; [idtac | hyp]
    ]; omega.
Qed.
 
Lemma max_lt : forall x y z, max y z < x <-> y < x /\ z < x.

Proof.
intuition. eapply le_lt_trans. apply le_max_l. apply H.
eapply le_lt_trans. apply le_max_r. apply H. apply max_case; hyp.
Qed.

Lemma gt_max : forall x y z, x > max y z <-> x > y /\ x > z.

Proof. exact max_lt. Qed.

Lemma max_0_r : forall x, max x 0 = x.

Proof.
destruct x; refl.
Qed.

(***********************************************************************)
(** min *)

Require Import Min.

Lemma elim_min_l : forall x y z, x <= z -> min x y <= z.

Proof.
intros. eapply le_trans. apply le_min_l. exact H.
Qed.

Lemma elim_min_r : forall x y z, y <= z -> min x y <= z.

Proof.
intros. eapply le_trans. apply le_min_r. exact H.
Qed.

(* setting up some hints for the following lemmas *)
Hint Resolve le_lt_trans le_min_l le_min_r le_trans.

Lemma lt_min_intro_l : forall x y z, x < z -> min x y < z.

Proof. eauto. Qed.

Lemma lt_min_intro_r : forall x y z, y < z -> min x y < z.

Proof. eauto. Qed.

Lemma le_min_intro_l : forall x y z, x <= z -> min x y <= z.

Proof. eauto. Qed.

Lemma le_min_intro_r : forall x y z, y <= z -> min x y <= z.

Proof. eauto. Qed.

Ltac min_simpl :=
  match goal with
  | H : ?x <= ?y |- context [min ?x ?y] => 
      rewrite (min_l x y H)
  | H : ?y < ?x |- context [min ?x ?y] =>
      rewrite (min_r x y (lt_le_weak H))
  end.

Lemma min_ge_compat : forall x y x' y',
  x >= x' -> y >= y' -> min x y >= min x' y'.

Proof.
  intros. destruct (le_lt_dec x y); destruct (le_lt_dec x' y');
    repeat min_simpl; omega.
Qed.

(***********************************************************************)
(** decidability results on orderings *)

Require Import RelMidex.

Lemma ge_dec : rel_dec ge.

Proof.
intros i j. destruct (le_lt_dec j i); intuition.
Defined. 

Lemma gt_dec : rel_dec gt.

Proof.
intros i j. destruct (le_gt_dec i j); auto with arith.
Defined.

Lemma lt_ge_dec : forall x y, {x < y} + {x >= y}.

Proof.
intros. destruct (lt_eq_lt_dec x y); auto; try destruct s; auto with *.
Defined.

(***********************************************************************)
(** Euclidian division *)

Require Import Euclid.

Lemma mult_is_not_O : forall m n, m * n <> 0 <-> m <> 0 /\ n <> 0.

Proof.
intuition. subst. apply H. refl. subst. apply H. apply mult_0_r.
destruct (mult_is_O _ _ H0); auto.
Qed.

Lemma mult_lt_r_elim : forall x x' y, x * y < x' * y -> x < x'.

Proof.
induction x; induction y; simpl; intros. rewrite mult_0_r in H. omega.
rewrite mult_succ_r in H. omega. repeat rewrite mult_0_r in H. omega.
simpl in *. repeat rewrite mult_succ_r in H. omega.
Qed.

Implicit Arguments mult_lt_r_elim [x x' y].

Lemma eucl_div_unique : forall b q1 r1 q2 r2,
  b > r1 -> b > r2 -> q1 * b + r1 = q2 * b + r2 -> q1 = q2 /\ r1 = r2.

Proof.
intros.
assert ((q1-q2)*b=r2-r1). rewrite mult_minus_distr_r. omega.
assert ((q2-q1)*b=r1-r2). rewrite mult_minus_distr_r. omega.
destruct (le_gt_dec r1 r2).
(* r1 <= r2 *)
destruct (eq_nat_dec r1 r2).
(* r1 = r2 *)
subst. rewrite minus_diag in H2. rewrite minus_diag in H3.
destruct (mult_is_O _ _ H2); destruct (mult_is_O _ _ H3); intuition; omega.
(* r1 < r2 *)
assert (r2 - r1 < b). omega. rewrite <- H2 in H4.
rewrite <- (mult_1_l b) in H4 at -1. ded (mult_lt_r_elim H4).
assert (q1=q2). omega. intuition. subst q2. omega.
(* r1 > r2 *)
assert (r1 - r2 < b). omega. rewrite <- H3 in H4.
rewrite <- (mult_1_l b) in H4 at -1. ded (mult_lt_r_elim H4).
assert (q1=q2). omega. intuition. subst q2. omega.
Qed.

Implicit Arguments eucl_div_unique [b q1 r1 q2 r2].

(***********************************************************************)
(** iteration of a function *)

Section iter.

  Variables (A : Type) (f : A -> A).

  Fixpoint iter n x :=
    match n with
      | 0 => x
      | S n' => iter n' (f x)
    end.

  Lemma iter_com : forall n x, iter n (f x) = f (iter n x).

  Proof.
    induction n; simpl; intros. refl. rewrite IHn. refl.
  Qed.

End iter.

(***********************************************************************)
(** arithmetical lemmas *)

Lemma le_lt_S : forall i k, i <= k -> i < S k.

Proof. auto with arith. Qed.

Lemma i_lt_n : forall n i j : nat, n = i + S j -> i < n.

Proof. Omega. Qed.

Implicit Arguments i_lt_n [n i j].

Lemma S_neq_O : forall n, S n = O -> False.

Proof. discr. Qed.

Lemma plus_reg_l_inv : forall n1 n2 p2, n2=p2 -> n1+n2=n1+p2.

Proof. Omega. Qed.

Lemma plus_reg_r_inv : forall n1 p1 n2, n1=p1 -> n1+n2=p1+n2.

Proof. Omega. Qed.

Lemma plus_minus_eq : forall v p, v+p-p=v.

Proof. Omega. Qed.

Lemma le_minus_plus : forall v p, p<=v -> v-p+p=v.

Proof. Omega. Qed.

Implicit Arguments le_minus_plus [v p].

Lemma plus_1_S : forall n, n+1 = S n.

Proof. Omega. Qed.

Lemma lt_from_le : forall x y, 0 < y -> x <= y-1 -> x < y.

Proof. Omega. Qed.

Lemma le_from_lt : forall x y, x < y+1 -> x <= y.

Proof. Omega. Qed.

Lemma lt_pm : forall n k x, n < x -> x <= n+k -> x-n-1 < k.

Proof. Omega. Qed.

Implicit Arguments lt_pm [n k x].

Lemma le_plus : forall k l, k <= k+l.

Proof. Omega. Qed.

Lemma misc1 : forall x k, S k = x+2+k-x-1.

Proof. Omega. Qed.

Lemma misc2 : forall x k, k = x+2+k-(x+1)-1.

Proof. Omega. Qed.

Lemma mult_gt_0 : forall i j, i > 0 -> j > 0 -> i * j > 0.

Proof.
destruct i; destruct j; intros; solve [absurd_arith | simpl; auto with arith].
Qed.

Lemma mult_lt_compat_lr : forall i j k l,
  i <= j -> j > 0 -> k < l -> i * k < j * l.

Proof.
  destruct i; intros.
  rewrite mult_0_l. apply mult_gt_0. hyp.
  destruct l. absurd_arith. auto with arith.
  simpl. destruct j. absurd_arith.
  simpl. apply plus_lt_le_compat. hyp.
  apply mult_le_compat; omega. 
Qed.

Lemma S_add_S : forall n1 n2 n, n1 + S n2 = n -> S n1 + S n2 = S n.

Proof.
intros. subst n. reflexivity.
Qed.

Implicit Arguments S_add_S [n1 n2 n].

Lemma gt_plus : forall l k, l > k -> exists m, l = (m + 1) + k.

Proof.
induction 1. exists 0. omega. destruct IHle. exists (S x). omega.
Qed.

Implicit Arguments gt_plus [l k].

(***********************************************************************)
(** given a non-null function [F], [Interval_list F i] is the pair
[(S(i),S(i+1)] where S(0)=0 and S(i+1)=S(i)+F(i) *)

Section Interval_list.

  Variables (F : nat -> nat) (HFi : forall i, exists y, F i = S y).

  Fixpoint Interval_list i : nat * nat := 
    match i with
      | 0 => (0, F 0)
      | S i' => let x := snd (Interval_list i') in (x, x + F i)
    end.

  Notation Local F' := Interval_list.

  Lemma int_exPi : forall i, exists j, fst (F' j) <= i /\ i < snd (F' j).

  Proof.
    intros i. induction i. exists 0. simpl. destruct (HFi 0); rewrite H. omega.
    destruct IHi as [k Hk]. assert (HSi : S i <= snd (F' k)). omega.
    destruct (le_lt_or_eq _ _ HSi). exists k. intuition.
    exists (S k). simpl. rewrite H. split. omega.
    destruct (HFi (S k)). rewrite H0. omega.
  Qed.

End Interval_list.

(***********************************************************************)
(** monotonic functions on nat *)

Require Import RelUtil.

Section mon.

  Variables (A : Type) (ltA : relation A) (ht : transitive ltA) (f : nat->A).

  Lemma monS : (forall x, ltA (f x) (f (S x)))
    -> (forall x y, x < y -> ltA (f x) (f y)).

  Proof.
    intros hf x. cut (forall k, ltA (f x) (f (k+S x))).
    intros hx y xy. assert (y = (y-S x)+S x). omega. rewrite H. apply hx.
    induction k; simpl. apply hf. apply ht with (f (k+S x)). hyp. apply hf.
  Qed.

End mon.

Implicit Arguments monS [A ltA f x y].
