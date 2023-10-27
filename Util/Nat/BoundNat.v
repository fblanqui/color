(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2014-12-11
- Adam Koprowski, 2009-04-24
- Leo Ducas, 2007-08-06

Type of natural numbers strictly smaller that some bound.
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil NatUtil ListUtil ListNodup FunUtil VecUtil.

Definition N n := sig (gt n).
 
Definition N_ n := @exist nat (gt n).
 
Definition N_val {n} (x : N n) : nat := proj1_sig x.

Coercion N_val : N >-> nat.
 
Definition N_prf {n} (x : N n) : x < n := proj2_sig x.

Coercion N_prf : N >-> lt.

Definition zero {n} : N (S n). Proof. apply (@N_ _ 0). lia. Defined.

(* One can define anything from [N 0] since [N 0] is empty. *)
Definition any_of_N0 {B : Type} : N 0 -> B.

Proof. intros [k_val k]. lia. Qed.

Lemma inj_N_val n : injective (@N_val n).

Proof.
  intros [x xn] [y yn]; simpl. intro e. subst y. f_equal. apply lt_unique.
Qed.

Lemma N_eq {n} : forall x y : N n, N_val x = N_val y <-> x = y.

Proof.
  intros [x xn] [y yn]; simpl. split; intro e.
  subst y. rewrite (lt_unique xn yn). refl.
  gen (f_equal N_val e). tauto.
Qed.

Lemma N_eq_dec {n} : forall x y : N n, {x=y}+{~x=y}.

Proof.
  intros [x xn] [y yn]. destruct (eq_nat_dec x y).
  left. apply N_eq. hyp.
  right. intro e. apply n0. apply N_eq in e. hyp.
Defined.

(****************************************************************************)
(** List [n-1; ..; 0] of the n first natural numbers starting from 0
in reverse order. *)

Fixpoint nats_decr_lt n :=
  match n with
    | 0 => nil
    | S n' => n' :: nats_decr_lt n'
  end.

Definition nats_incr_lt n := rev' (nats_decr_lt n).

Lemma In_nats_decr_lt : forall n x, x < n <-> In x (nats_decr_lt n).

Proof. induction n; simpl; intros. lia. rewrite <- IHn. lia. Qed.

Lemma length_nats_decr_lt n : length (nats_decr_lt n) = n.

Proof. induction n; simpl. refl. rewrite IHn. refl. Qed.

(****************************************************************************)
(** List [@N_ n (n-1) _; ..; @N_ n 0 _] of all the elements of [N n] in
reverse order. *)

Section list_N.

  Variable n : nat.

  Lemma L_ k : S k < n -> k < n. Proof. lia. Qed.

  (* Given k<n, returns the list [@N_ n k _; ..; @N_ n 0 _]. *)
  Fixpoint L_aux k :=
    match k as k return k<n -> list (N n) with
      | 0 => fun h => N_ h :: nil
      | S k' => fun h => N_ h :: L_aux k' (L_ h)
    end.

  Lemma length_L_aux : forall k (hk : k<n), length (L_aux hk) = S k.

  Proof. induction k; intro hk; simpl. lia. rewrite IHk. lia. Qed.

  Lemma nth_L_aux x :
    forall k (h : k<n) i, i <= k -> N_val (nth i (L_aux h) x) = k - i.

  Proof.
    induction k; simpl; intros; destruct i; simpl. refl. lia. refl.
    rewrite IHk. refl. lia.
  Qed.

  Lemma In_L_aux_elim x k (h : k<n) :
    In x (L_aux h) -> exists i, N_val x = k - i.

  Proof.
    intro xL. destruct (In_nth x xL) as [i [i1 i2]].
    apply N_eq in i2. rewrite nth_L_aux in i2. ex i. hyp.
    rewrite length_L_aux in i1. lia.
  Qed.

  Arguments In_L_aux_elim [x k h] _.

  Lemma In_L_aux :
    forall k (h : k<n) i (p : i<n), i <= k -> In (N_ p) (L_aux h).

  Proof.
    induction k; simpl; intros.
    left. apply N_eq; simpl. lia.
    destruct (eq_nat_dec (S k) i).
    left. apply N_eq; simpl. hyp.
    right. apply IHk. lia.
  Qed.

End list_N.

Arguments In_L_aux_elim [n x k h] _.

(* Returns the list [@N_ n (n-1) _; ..; @N_ n 0 _]. *)
Definition L n :=
  match n return list (N n) with
    | 0 => nil
    | S n' => L_aux (le_n (S n'))
  end.

Arguments L : clear implicits.

Lemma nth_L n x i : i < n -> N_val (nth i (L n) x) = pred n - i.

Proof. intros. unfold L. destruct n. lia. apply nth_L_aux. lia. Qed.

Lemma In_L n i (p : i<n) : In (N_ p) (L n).

Proof. unfold L. destruct n. lia. apply In_L_aux. lia. Qed.

Lemma In_L_elim n x : In x (L n) -> exists i, N_val x = n - i.

Proof.
  destruct n; simpl. fo.
  intro xl. destruct (In_L_aux_elim xl) as [i e]. ex (S i). hyp.
Qed.

Arguments In_L_elim [n x] _.

Lemma length_L n : length (L n) = n.

Proof. destruct n; simpl. refl. unfold N. rewrite length_L_aux. refl. Qed.

Lemma nodup_L_aux {n} : forall k (hk : k < n), nodup (L_aux hk).

Proof.
  induction k; intro hk; simpl. tauto. split. 2: apply IHk.
  intro h. destruct (In_L_aux_elim h) as [i e]. simpl in e. lia.
Qed.

Lemma nodup_L n : nodup (L n).

Proof. destruct n; simpl. auto. apply nodup_L_aux. Qed.

(****************************************************************************)
(** Functions between [N m] and [N n]. *)

Lemma N_inj_le m n (f : N m -> N n) : injective f -> m <= n.

Proof.
  intro f_inj.
  assert (e : length (map f (L m)) = m). rewrite map_length, length_L. refl.
  rewrite <- e, <- (@length_L n). apply nodup_incl_length_le.
  apply nodup_map_inj. hyp. apply nodup_L.
  intros y hy. destruct y as [y_val y]. apply In_L.
Qed.

Lemma N_bij_eq m n (f : N m -> N n) : bijective f -> m = n.

Proof.
  intros [f_inj f_surj]. apply Nat.le_antisymm.
  apply N_inj_le with (f := f). hyp.
  apply N_inj_le with (f := inverse f_surj). inj. 
Qed.

(****************************************************************************)
(** Vector [@N_ n (n-1) _; ..; @N_ n 0 _] of all the elements of [N n] in
reverse order. *)

Section vec_N.

  Variable n : nat.

  (* Given k<n, returns the list [@N_ n k _; ..; @N_ n 0 _]. *)
  Fixpoint V_aux k :=
    match k as k return k<n -> vector (N n) (S k) with
      | 0 => fun h => Vcons (N_ h) Vnil
      | S k' => fun h => Vcons (N_ h) (V_aux k' (L_ h))
    end.

  Lemma Vnth_V_aux :
    forall k (h : k<n) i (hi : i < S k), N_val (Vnth (V_aux h) hi) = k - i.

  Proof.
    induction k; simpl; intros; destruct i; simpl. refl. lia. refl.
    rewrite IHk. refl.
  Qed.

  Lemma Vin_V_aux_elim x k (h : k<n) :
    Vin x (V_aux h) -> exists i, N_val x = k - i.

  Proof.
    intro xL. destruct (Vin_nth xL) as [i [i1 i2]].
    apply N_eq in i2. rewrite Vnth_V_aux in i2. ex i. hyp.
  Qed.

  Arguments Vin_V_aux_elim [x k h] _.

  Lemma Vin_V_aux :
    forall k (h : k<n) i (p : i<n), i <= k -> Vin (N_ p) (V_aux h).

  Proof.
    induction k; simpl; intros.
    left. apply N_eq; simpl. lia.
    destruct (eq_nat_dec (S k) i).
    left. apply N_eq; simpl. hyp.
    right. apply IHk. lia.
  Qed.

End vec_N.

Arguments Vin_V_aux_elim [n x k h] _.

(* Returns the list [@N_ n (n-1) _; ..; @N_ n 0 _]. *)
Definition V n :=
  match n return vector (N n) n with
    | 0 => Vnil
    | S n' => V_aux (le_n (S n'))
  end.

Arguments V : clear implicits.

Lemma Vnth_V n i (hi : i < n) : N_val (Vnth (V n) hi) = pred n - i.

Proof. intros. unfold L. destruct n. lia. apply Vnth_V_aux. Qed.

Lemma Vin_V n i (p : i<n) : Vin (N_ p) (V n).

Proof. unfold L. destruct n. lia. apply Vin_V_aux. lia. Qed.

Lemma Vin_V_elim n x : Vin x (V n) -> exists i, N_val x = n - i.

Proof.
  destruct n; simpl. fo.
  intro xl. destruct (Vin_V_aux_elim xl) as [i e]. ex (S i). hyp.
Qed.

Arguments Vin_V_elim [n x] _.

(****************************************************************************)
(** Multiplicity and sorting properties. *)

Lemma map_N_val_L_aux n :
  forall k (hk : k<n), map N_val (L_aux hk) = nats_decr_lt (S k).

Proof. induction k; intro hk; simpl. refl. rewrite IHk. refl. Qed.

Lemma map_N_val_L n : map N_val (L n) = nats_decr_lt n.

Proof. destruct n; simpl. refl. apply map_N_val_L_aux. Qed.

From CoLoR Require Import SortUtil RelUtil.

Lemma lelistA_map_N_val n R (a : N n) :
  forall l, lelistA (Rof R N_val) a l -> lelistA R a (map N_val l).

Proof.
  induction l; intro h; simpl.
  apply nil_leA.
  inversion h; subst. apply cons_leA; auto.
Qed.

Lemma sort_map_N_val n R :
  forall l : list (N n), sort (Rof R N_val) l -> sort R (map N_val l).

Proof.
  induction l; intro h; simpl.
  apply nil_sort.
  inversion h; subst. apply cons_sort. tauto. apply lelistA_map_N_val. hyp.
Qed.

From CoLoR Require Import ListPermutation.

Lemma multiplicity_nats_decr_lt i :
  forall n, multiplicity (list_contents eq_nat_dec (nats_decr_lt n)) i
            = if lt_ge_dec i n then 1 else 0.

Proof.
  induction n; simpl.
  destruct (lt_ge_dec i 0); lia.
  rewrite IHn. destruct (lt_ge_dec i n); destruct (eq_nat_dec n i);
    destruct (lt_ge_dec i (S n)); lia.
Qed.

Lemma multiplicity_L_aux n (i : N n) : forall k (kn : k < n),
    multiplicity (list_contents N_eq_dec (L_aux kn)) i
    = if le_dec i k then 1 else 0.

Proof.
  destruct i as [i hi]; simpl.
  induction k; intro hk.
  simpl. destruct i.
  destruct (le_dec 0 0); lia.
  destruct (le_dec (S i) 0); lia.
  simpl. destruct i; rewrite IHk.
  destruct (le_dec 0 k); destruct (le_dec 0 (S k)); lia.
  destruct (eq_nat_dec k i); simpl;
    destruct (le_dec (S i) k); destruct (le_dec (S i) (S k)); lia.
Qed.

Lemma multiplicity_L n (i : N n) :
  multiplicity (list_contents N_eq_dec (L n)) i = 1.

Proof.
  destruct n as [|n]. apply any_of_N0. hyp.
  unfold L. rewrite multiplicity_L_aux. destruct (le_dec i n). refl.
  destruct i as [i hi]. simpl in n0. lia.
Qed.

Lemma multiplicity_map_N_val n i (hi : i<n) :
  forall l, multiplicity (list_contents eq_nat_dec (map N_val l)) i
            = multiplicity (list_contents N_eq_dec l) (N_ hi).

Proof.
  induction l; simpl. refl. rewrite IHl. destruct a as [j hj]; simpl.
  destruct (eq_nat_dec j i); refl.
Qed.

Lemma multiplicity_map_N_val_notin n i (hi : i>=n) : forall l : list (N n),
    multiplicity (list_contents eq_nat_dec (map N_val l)) i = 0.

Proof.
  induction l; simpl. refl. rewrite IHl. destruct (eq_nat_dec a i).
  subst. destruct a as [a ha]. simpl in hi. lia. refl.
Qed.

(****************************************************************************)
(** Given [n:nat], a predicate [Pr : N n -> Prop] and a function
[P] that can check whether [Pr i] is true, [check_seq Pr P] checks
whether [Pr i] is true for all [i] strictly smaller than [n]. *)

Section Check_seq_aux.

  Variables (n : nat) (Pr : N n -> Prop) (P : forall i : N n, option (Pr i)).

  Program Fixpoint check_seq_aux p (H : forall i : N n, N_val i < p -> Pr i)
    {measure (n - p)} : option (forall i : N n, Pr i) :=
    match le_lt_dec n p with
      | left _ => Some _
      | right cmp =>
        match P (N_ cmp) with
          | None => None
          | Some _ => @check_seq_aux (S p) _ _
        end
    end.

  Next Obligation. apply H. destruct i. simpl. lia. Qed.
  Next Obligation.
    destruct i as [x l]. simpl in *.
    destruct (eq_nat_dec x p).
    subst. rewrite (lt_unique l cmp). hyp.
    apply H. simpl. lia.
  Qed.
  Next Obligation. lia. Qed.

End Check_seq_aux.

Program Definition check_seq (n : nat) (Pr : N n -> Prop)
  (P : forall (i : N n), option (Pr i)) : option (forall (i : N n), Pr i)
  := check_seq_aux _ P (p:=0) _.

Next Obligation. lia. Qed.

Arguments check_seq [n Pr] _.
