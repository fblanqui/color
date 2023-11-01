(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-04-02
- Adam Koprowski, 2007-03-29
- Frederic Blanqui, 2009-05-11

useful definitions and lemmas on natural numbers
*)

Set Implicit Arguments.

From Coq Require Import Morphisms Euclid Peano Lia.
From Coq Require Export Arith.
From Coq Require Import Compare.

From CoLoR Require Import LogicUtil EqUtil BoolUtil NatCompat RelUtil.

(***********************************************************************)
(** Declare implicit arguments. *)

Arguments Nat.lt_lt_succ_r [n m] _.
Arguments lt_S_n [n m] _.
Arguments lt_n_S [n m] _.
Arguments le_S [n m] _.
Arguments gt_le_S [n m] _.
Arguments le_lt_n_Sm [n m] _.
Arguments Nat.lt_le_incl [n m] _.
Arguments le_plus_minus [n m] _.
Arguments le_plus_minus_r [n m] _.
Arguments Nat.nlt_0_r [n] _.
Arguments Nat.le_lt_trans [n m p] _ _.
Arguments Nat.lt_le_trans [n m p] _ _.
Arguments le_lt_or_eq [n m] _.
Arguments lt_n_Sm_le [n m] _.
Arguments Nat.lt_trans [n m p] _ _.
Arguments Nat.le_trans [n m p] _ _.
Arguments Nat.lt_le_incl [n m] _.
Arguments lt_le_S [n m] _.
Arguments lt_not_le [n m] _ _.
Arguments le_lt_eq_dec [n m] _.
Arguments le_S_n [n m] _.
Arguments le_not_lt [n m] _ _.
Arguments eq_add_S [n m] _.
Arguments le_n_S [n m] _.

(***********************************************************************)
(** Tactics. *)

Tactic Notation "lia" := intros; lia.

Ltac max :=
  match goal with
    | |- context [max ?x ?y] => gen (Nat.le_max_l x y); gen (Nat.le_max_r x y)
  end; lia.

(***********************************************************************)
(** Properties of ordering relations on nat. *)

Global Instance le_preorder : PreOrder le.

Proof. split; intro; lia. Qed.

Global Instance lt_trans : Transitive lt. 

Proof. intro; lia. Qed.

Global Instance ge_preorder : PreOrder ge.

Proof. split; intro; lia. Qed.

Global Instance gt_trans : Transitive gt.

Proof. intro; lia. Qed.

(***********************************************************************)
(** Boolean function for equality. *)

Fixpoint beq_nat (x y : nat) :=
  match x, y with
    | 0, 0 => true
    | S x', S y' => beq_nat x' y'
    | _, _ => false
  end.

Lemma beq_nat_ok : forall x y, beq_nat x y = true <-> x = y.

Proof.
  induction x; destruct y; simpl; split; intro; try (refl || discr).
  f_equal. fo. fo.
Qed.

Ltac case_beq_nat := case_beq beq_nat beq_nat_ok.

Lemma eq_nat_dec_refl : forall n, eq_nat_dec n n = left (n<>n) (eq_refl n).

Proof.
  intro. gen (eq_nat_dec n n). destruct s.
  rewrite (UIP_refl eq_nat_dec e). refl. cong.
Qed.

(***********************************************************************)
(** Boolean functions for orderings. *)

Fixpoint bgt_nat (x y : nat) :=
  match x, y with
    | 0, _ => false
    | S _, 0 => true
    | S x', S y' => bgt_nat x' y'
  end.

Lemma bgt_nat_ok : forall x y, bgt_nat x y = true <-> x > y.

Proof.
  induction x; destruct y; simpl; split; intro; try (lia||discr||refl).
  rewrite IHx in H. lia. rewrite IHx. lia.
Qed.

Ltac check_gt := rewrite <- bgt_nat_ok; check_eq.

Lemma bgt_nat_ko : forall x y, bgt_nat x y = false <-> x <= y.

Proof.
  induction x; destruct y; simpl; split; intro; try (lia||discr||refl).
  rewrite IHx in H. lia. apply le_S_n in H. rewrite IHx. hyp.
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
  induction x; destruct y; simpl; split; intro; try (refl || discr || lia).
  rewrite IHx in H. lia. apply le_S_n in H. rewrite IHx. hyp.
Qed.

Ltac check_ge := rewrite <- bge_nat_ok; check_eq.

Definition blt_nat x y := bgt_nat y x.

Lemma blt_nat_ok : forall x y, blt_nat x y = true <-> x < y.

Proof. intros. unfold blt_nat. rewrite bgt_nat_ok. lia. Qed.

Definition bne_nat x y := negb (beq_nat x y).

Lemma bne_nat_ok : forall x y, bne_nat x y = true <-> x <> y.

Proof.
  intros x y. unfold bne_nat. rewrite negb_lr. simpl.
  rewrite (beq_ko beq_nat_ok). refl.
Qed.

(***********************************************************************)
(** Unicity of equality and ordering proofs on nat. *)

Lemma eq_unique : forall (n m : nat) (h1 h2 : n = m), h1 = h2.

Proof. intros. apply UIP. apply eq_nat_dec. Qed.

Scheme le_ind_dep := Induction for le Sort Prop.

Lemma le_unique : forall n m (h1 h2 : n <= m), h1 = h2.

Proof.
intro n.
assert (forall m (h1 : n <= m) p (h2 : n <= p),
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

Proof. intros n m. unfold lt. intros. apply le_unique. Qed.

Lemma lt_Sn_nS : forall m n (H : m < n), lt_S_n (lt_n_S H) = H.

Proof. intros. apply lt_unique. Qed.

Lemma lt_nS_Sn : forall m n (H : S m < S n), lt_n_S (lt_S_n H) = H.

Proof. intros. apply lt_unique. Qed.

(***********************************************************************)
(** Lemmas on the maximum of two numbers. *)

Arguments max_r [n m] _.
Arguments max_l [n m] _.

Lemma max_assoc : forall a b c, max a (max b c) = max (max a b) c.

Proof.
intros.
case (le_dec b c); intro H.
 rewrite (max_r H).
 case (le_dec a b); intro H'.
  rewrite (max_r (Nat.le_trans H' H)), (max_r H'), (max_r H). refl.
  case (le_dec a c); intro H''; rewrite (max_l H'); refl.
  rewrite (max_l H).
  case (le_dec a b); intro H'.
   rewrite (max_r H').
   apply (sym_equal (max_l H)).
   assert (H'' : c <= max a b). eapply Nat.le_trans. apply H. apply Nat.le_max_r.
   apply (sym_equal (max_l H'')).
Qed.

Lemma le_max_intro_l x y z : x <= y -> x <= max y z.

Proof. lia. Qed.

Lemma lt_max_intro_l x y z : x < y -> x < max y z.

Proof. lia. Qed.

Lemma le_max_intro_r x y z : x <= z -> x <= max y z.

Proof. lia. Qed.

Lemma lt_max_intro_r x y z : x < z -> x < max y z.

Proof. lia. Qed.

Lemma le_max_elim_l x y z : max x y <= z -> x <= z.

Proof. lia. Qed.

Lemma le_max_elim_r x y z : max x y <= z -> y <= z.

Proof. lia. Qed.

Lemma max_ge_compat x y x' y' : x >= x' -> y >= y' -> max x y >= max x' y'.

Proof. lia. Qed.

Lemma max_gt_compat x y x' y' : x > x' -> y > y' -> max x y > max x' y'.

Proof. lia. Qed.

Lemma min_gt_compat x y x' y' : x > x' -> y > y' -> min x y > min x' y'.

Proof. lia. Qed.
 
Lemma max_lt x y z : max y z < x <-> y < x /\ z < x.

Proof. lia. Qed.

Lemma gt_max x y z : x > max y z <-> x > y /\ x > z.

Proof. apply max_lt. Qed.

Lemma max_0_r x : max x 0 = x.

Proof. destruct x; refl. Qed.

(***********************************************************************)
(** Lemmas on the minimum of two numbers. *)

Lemma elim_min_l x y z : x <= z -> min x y <= z.

Proof. lia. Qed.

Lemma elim_min_r : forall x y z, y <= z -> min x y <= z.

Proof. lia. Qed.

Lemma lt_min_intro_l x y z : x < z -> min x y < z.

Proof. lia. Qed.

Lemma lt_min_intro_r x y z : y < z -> min x y < z.

Proof. lia. Qed.

Lemma le_min_intro_l x y z : x <= z -> min x y <= z.

Proof. lia. Qed.

Lemma le_min_intro_r x y z : y <= z -> min x y <= z.

Proof. lia. Qed.

Lemma min_ge_compat x y x' y' : x >= x' -> y >= y' -> min x y >= min x' y'.

Proof. lia. Qed.

(***********************************************************************)
(** Decidability of ordering relations on nat. *)

Lemma ge_dec : rel_dec ge.

Proof. intros i j. destruct (le_lt_dec j i); intuition. Defined. 

Lemma gt_dec : rel_dec gt.

Proof. intros i j. destruct (le_gt_dec i j); auto with arith. Defined.

Lemma lt_ge_dec x y : {x < y} + {x >= y}.

Proof.
  destruct (lt_eq_lt_dec x y); auto; try destruct s; auto with *.
Defined.

(***********************************************************************)
(** Euclidian division. *)

Lemma mult_is_not_O m n : m * n <> 0 <-> m <> 0 /\ n <> 0.

Proof. nia. Qed.

Lemma mult_lt_r_elim : forall x x' y, x * y < x' * y -> x < x'.

Proof. induction x; induction y; simpl; nia. Qed.

Arguments mult_lt_r_elim [x x' y] _.

Lemma eucl_div_unique b q1 r1 q2 r2 :
  b > r1 -> b > r2 -> q1 * b + r1 = q2 * b + r2 -> q1 = q2 /\ r1 = r2.

Proof.
intros.
assert ((q1-q2)*b=r2-r1). nia.
assert ((q2-q1)*b=r1-r2). (*nia works but is slow*)
rewrite Nat.mul_sub_distr_r. clear H2; lia.
(*nia works but is slow*)
destruct (le_gt_dec r1 r2).
(* r1 <= r2 *)
destruct (eq_nat_dec r1 r2).
(* r1 = r2 *)
subst. rewrite Nat.sub_diag in *. nia.
(* r1 < r2 *)
assert (r2 - r1 < b). clear -H H0; lia.
rewrite <- H2 in H4. rewrite <- (Nat.mul_1_l b) in H4 at -1.
ded (mult_lt_r_elim H4).
assert (q1=q2). clear H H0 H1 H3 H4; lia.
subst q2; clear H2 H3 H4 H5. lia.
(* r1 > r2 *)
assert (r1 - r2 < b). clear -H H0; lia.
rewrite <- H3 in H4. rewrite <- (Nat.mul_1_l b) in H4 at -1.
ded (mult_lt_r_elim H4).
assert (q1=q2). clear H H0 H1 H2 H4; lia.
subst q2; clear H2 H3 H4 H5. lia.
Qed.

Arguments eucl_div_unique [b q1 r1 q2 r2] _ _ _.

(***********************************************************************)
(** Iteration of a function. *)

Section iter.

  Variables (A : Type) (a : A) (f : A -> A).

  Fixpoint iter i :=
    match i with
      | 0 => a
      | S i' => f (iter i')
    end.

End iter.

Section iter_prop.

  Variables (A : Type) (f : A -> A).

  Lemma iter_com : forall a i, iter (f a) f i = f (iter a f i).

  Proof. induction i; simpl; intros. refl. rewrite IHi. refl. Qed.

  Lemma red_iter : forall R : relation A,
    (forall x y, R x y -> R (f x) (f y)) ->
    forall i x y, R x y -> R (iter x f i) (iter y f i).

  Proof. induction i; simpl; intros. hyp. apply H. apply IHi. hyp. Qed.

End iter_prop.

(***********************************************************************)
(** Arithmetical lemmas. *)

Lemma le_plus : forall x y, x <= y -> exists k, y = k + x.

Proof.
  induction 1; simpl. ex 0. refl. destruct IHle as [k e]. ex (S k). lia.
Qed.

Lemma le_lt_S : forall i k, i <= k -> i < S k.

Proof. auto with arith. Qed.

Lemma i_lt_n : forall n i j : nat, n = i + S j -> i < n.

Proof. lia. Qed.

Arguments i_lt_n [n i j] _.

Lemma S_neq_O : forall n, S n = O -> False.

Proof. discr. Qed.

Lemma plus_reg_l_inv : forall n1 n2 p2, n2=p2 -> n1+n2=n1+p2.

Proof. lia. Qed.

Lemma plus_reg_r_inv : forall n1 p1 n2, n1=p1 -> n1+n2=p1+n2.

Proof. lia. Qed.

Lemma plus_minus_eq : forall v p, v+p-p=v.

Proof. lia. Qed.

Lemma le_minus_plus : forall v p, p<=v -> v-p+p=v.

Proof. lia. Qed.

Arguments le_minus_plus [v p] _.

Lemma plus_1_S : forall n, n+1 = S n.

Proof. lia. Qed.

Lemma lt_from_le : forall x y, 0 < y -> x <= y-1 -> x < y.

Proof. lia. Qed.

Lemma le_from_lt : forall x y, x < y+1 -> x <= y.

Proof. lia. Qed.

Lemma lt_pm : forall n k x, n < x -> x <= n+k -> x-n-1 < k.

Proof. lia. Qed.

Arguments lt_pm [n k x] _ _.

Lemma le_plus_r : forall k l, k <= k+l.

Proof. lia. Qed.

Lemma misc1 : forall x k, S k = x+2+k-x-1.

Proof. lia. Qed.

Lemma misc2 : forall x k, k = x+2+k-(x+1)-1.

Proof. lia. Qed.

Lemma mult_gt_0 : forall i j, i > 0 -> j > 0 -> i * j > 0.

Proof. nia. Qed.

Lemma mult_lt_compat_lr : forall i j k l,
  i <= j -> j > 0 -> k < l -> i * k < j * l.

Proof. nia. Qed.

Lemma S_add_S : forall n1 n2 n, n1 + S n2 = n -> S n1 + S n2 = S n.

Proof. intros. subst. refl. Qed.

Arguments S_add_S [n1 n2 n] _.

Lemma gt_plus : forall l k, l > k -> exists m, l = (m + 1) + k.

Proof. induction 1. exists 0. lia. destruct IHle. exists (S x). lia. Qed.

Arguments gt_plus [l k] _.

(***********************************************************************)
(** Given a non-null function [F], [Interval_list F i] is the pair
[(S(i),S(i+1)] where S(0)=0 and S(i+1)=S(i)+F(i). *)

Section Interval_list.

  Variables (F : nat -> nat) (HFi : forall i, exists y, F i = S y).

  Fixpoint Interval_list i : nat * nat := 
    match i with
      | 0 => (0, F 0)
      | S i' => let x := snd (Interval_list i') in (x, x + F i)
    end.

  Local Notation F' := Interval_list.

  Lemma int_exPi : forall i, exists j, fst (F' j) <= i /\ i < snd (F' j).

  Proof.
    intros i. induction i. exists 0. simpl. destruct (HFi 0); rewrite H. lia.
    destruct IHi as [k Hk]. assert (HSi : S i <= snd (F' k)). lia.
    destruct (le_lt_or_eq HSi). exists k. intuition.
    exists (S k). simpl. rewrite H. split. lia.
    destruct (HFi (S k)). rewrite H0. lia.
  Qed.

End Interval_list.

(***********************************************************************)
(** Monotone functions on nat. *)

Section mon.

  Variables (A : Type) (ltA : relation A) (ht : transitive ltA) (f : nat->A).

  Lemma monS : (forall x, ltA (f x) (f (S x)))
    -> (forall x y, x < y -> ltA (f x) (f y)).

  Proof.
    intros hf x. cut (forall k, ltA (f x) (f (k+S x))).
    intros hx y xy. assert (y = (y-S x)+S x). lia. rewrite H. apply hx.
    induction k; simpl. apply hf. apply ht with (f (k+S x)). hyp. apply hf.
  Qed.

End mon.

Arguments monS [A ltA] _ [f] _ [x y] _.

(****************************************************************************)
(** Smallest natural number satisfying some satisfiable property. *)

Section smallest.

  Variables (P : nat -> Prop) (P_dec : forall x, {P x}+{~P x}).

  Section smallest_aux.

    Variables (n : nat) (h : P n).

    Fixpoint smallest_aux acc k :=
      match k with
        | 0 => if P_dec k then 0 else acc
        | S k' => smallest_aux (if P_dec k then k else acc) k'
      end.

    Definition smallest := smallest_aux n n.

    Lemma smallest_aux_ok : forall k acc, P acc -> P (smallest_aux acc k).

    Proof.
      induction k; intros acc Pacc; simpl.
      destruct (P_dec 0); hyp.
      destruct (P_dec (S k)); fo.
    Qed.

    Lemma smallest_ok : P smallest.

    Proof. unfold smallest. apply smallest_aux_ok. hyp. Qed.

    Lemma smallest_aux_le_max_args l :
      forall k acc, acc <= l -> k <= l -> smallest_aux acc k <= l.

    Proof.
      induction k; intros acc accl kl; simpl.
      destruct (P_dec 0); lia.
      destruct (P_dec (S k)); apply IHk; lia.
    Qed.

    Lemma smallest_le_arg : smallest <= n.

    Proof. apply smallest_aux_le_max_args; refl. Qed.

    Lemma smallest_aux_plus_exists m :
      forall k acc, exists acc', smallest_aux acc (k + m) = smallest_aux acc' m.

    Proof.
      induction k; intro acc; simpl.
      ex acc. refl.
      set (a := if P_dec (S (k + m)) then S (k + m) else acc).
      destruct (IHk a) as [acc' hacc']. ex acc'. hyp.
    Qed.

    Lemma smallest_aux_plus m : P (S m) ->
      forall k acc acc', smallest_aux acc (k + S m) = smallest_aux acc' (S m).

    Proof.
      intro PSm. induction k; intros acc acc'; simpl.
      destruct (P_dec (S m)). refl. contr. erewrite IHk. refl.
    Qed.

    Lemma smallest_aux_le_exists k l acc :
      k <= l -> exists acc', smallest_aux acc l = smallest_aux acc' k.

    Proof.
      intro kl. destruct (le_plus kl) as [m e]; subst.
      apply smallest_aux_plus_exists.
    Qed.

    Lemma smallest_aux_le k l acc acc' :
      k <= l -> P (S k) -> smallest_aux acc (S l) = smallest_aux acc' (S k).

    Proof.
      intros kl Pk. destruct (le_plus kl) as [m e]; subst.
      assert (e : S (m + k) = m + S k). lia. rewrite e.
      apply smallest_aux_plus. hyp.
    Qed.

  End smallest_aux.

  Lemma smallest_inv_le k l : k <= l -> P k -> smallest l = smallest k.

  Proof.
    unfold smallest. destruct k; simpl.
    (* k=0 *)
    intros _ P0. destruct (P_dec 0). 2: contr. clear p. revert l.
    cut (forall l acc, smallest_aux acc l = 0). fo.
    induction l; intro acc; simpl. destruct (P_dec 0). refl. contr. fo.
    (* k > 0 *)
    destruct l; simpl. lia. intro kl. apply smallest_aux_le. lia.
  Qed.

  Lemma smallest_inv m n : P m -> P n -> smallest m = smallest n.

  Proof.
    intros Pm Pn. destruct (le_dec n m). apply smallest_inv_le; hyp.
    sym. apply smallest_inv_le. lia. hyp.
  Qed.

  Lemma smallest_comp m n : P m -> P n -> smallest m <= n.

  Proof.
    intros Pm Pn. destruct (le_dec m n). rewrite smallest_le_arg. hyp.
    rewrite smallest_inv with (n:=n); auto. apply smallest_le_arg.
  Qed.

End smallest.

Arguments smallest [P] _ _.
Arguments smallest_ok [P] _ [n] _.
Arguments smallest_comp [P] _ [m n] _ _.
