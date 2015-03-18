(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2014-12-11
- Adam Koprowski, 2009-04-24

Type of natural numbers strictly smaller that some bound.
*)

Set Implicit Arguments.

Require Import LogicUtil NatUtil ListUtil ListNodup FunUtil.

Definition N n := sig (gt n).

Definition N_ n := @exist _ (gt n).

Definition N_val {n} (x : N n) : nat := proj1_sig x.

Coercion N_val : N >-> nat.

Definition N_prf {n} (x : N n) : x < n := proj2_sig x.

Coercion N_prf : N >-> lt.

Definition zero {n} : N (S n).

Proof. apply (@N_ _ 0). omega. Defined.

(* One can define anything from [N 0] since [N 0] is empty. *)
Definition any_of_N0 {B : Type} : N 0 -> B.

Proof. intros [k_val k]. omega. Qed.

Lemma N_eq {n} : forall x y : N n, N_val x = N_val y <-> x = y.

Proof.
  intros [x xn] [y yn]; simpl. split; intro e.
  subst y. rewrite (lt_unique xn yn). refl.
  gen (f_equal (@N_val _) e). tauto.
Qed.

Lemma N_eq_dec {n} : forall x y : N n, {x=y}+{~x=y}.

Proof.
  intros [x xn] [y yn]. destruct (eq_nat_dec x y).
  left. apply N_eq. hyp.
  right. intro e. apply n0. apply N_eq in e. hyp.
Defined.

Lemma inj_N_val n : injective (@N_val n).

Proof.
  intros [x xn] [y yn]; simpl. intro e. subst y.
  apply (f_equal (@exist _ _ x)). apply lt_unique.
Qed.

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

Proof. induction n; simpl; intros. omega. rewrite <- IHn. omega. Qed.

Lemma length_nats_decr_lt n : length (nats_decr_lt n) = n.

Proof. induction n; simpl. refl. rewrite IHn. refl. Qed.

(****************************************************************************)
(** List [@N_ n (n-1) _; ..; @N_ n 0 _] of all the elements of [N n] in
reverse order. *)

Section list_N.

  Variable n : nat.

  Lemma L_ k' : S k' < n -> k' < n. Proof. omega. Qed.

  (* Given k<n, returns the list [@N_ n k _; ..; @N_ n 0 _]. *)
  Fixpoint L_aux k :=
    match k as k return k<n -> list (N n) with
      | 0 => fun h => N_ h :: nil
      | S k' => fun h => N_ h :: L_aux k' (L_ h)
    end.

  Lemma length_L_aux : forall k (hk : k<n), length (L_aux hk) = S k.

  Proof. induction k; intro hk; simpl. omega. rewrite IHk. omega. Qed.

  Lemma nth_L_aux x :
    forall k (h : k<n) i, i <= k -> N_val (nth i (L_aux h) x) = k - i.

  Proof.
    induction k; simpl; intros; destruct i; simpl. refl. omega. refl.
    rewrite IHk. refl. omega.
  Qed.

  Lemma In_L_aux_elim x k (h : k<n) :
    In x (L_aux h) -> exists i, N_val x = k - i.

  Proof.
    intro xL. destruct (In_nth x xL) as [i [i1 i2]].
    apply N_eq in i2. rewrite nth_L_aux in i2. ex i. sym. hyp.
    rewrite length_L_aux in i1. omega.
  Qed.

  Arguments In_L_aux_elim [x k h] _.

  Lemma In_L_aux :
    forall k (h : k<n) i (p : i<n), i <= k -> In (N_ p) (L_aux h).

  Proof.
    induction k; simpl; intros.
    left. apply N_eq; simpl. omega.
    destruct (eq_nat_dec (S k) i).
    left. apply N_eq; simpl. hyp.
    right. apply IHk. omega.
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

Proof. intros. unfold L. destruct n. omega. apply nth_L_aux. omega. Qed.

Lemma In_L n i (p : i<n) : In (N_ p) (L n).

Proof. unfold L. destruct n. omega. apply In_L_aux. omega. Qed.

Lemma In_L_elim n x : In x (L n) -> exists i, N_val x = n - i.

Proof.
  destruct n; simpl. fo.
  intro xl. destruct (In_L_aux_elim xl) as [i e]. ex (S i). hyp.
Qed.

Arguments In_L_elim [n x] _.

Lemma length_L n : length (L n) = n.

Proof. destruct n; simpl. refl. rewrite length_L_aux. refl. Qed.

Lemma nodup_L_aux {n} : forall k (hk : k < n), nodup (L_aux hk).

Proof.
  induction k; intro hk; simpl. tauto. split. 2: apply IHk.
  intro h. destruct (In_L_aux_elim h) as [i e]. simpl in e. omega.
Qed.

Lemma nodup_L n : nodup (L n).

Proof. destruct n; simpl. auto. apply nodup_L_aux. Qed.

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
  intros [f_inj f_surj]. apply le_antisym.
  apply N_inj_le with (f := f). hyp.
  apply N_inj_le with (f := inverse f_surj). inj. 
Qed.

(****************************************************************************)
(** Given [n:nat], a predicate [Pr : N n -> Prop] and a function
[P] that can check whether [Pr i] is true, [check_seq Pr P] checks
whether [Pr i] is true for all [i] strictly smaller than [n]. *)

Section Check_seq_aux.

  Variables (n : nat) (Pr : N n -> Prop)
    (P : forall i : N n, Exc (Pr i)).

  Program Fixpoint check_seq_aux p (H : forall i : N n, N_val i < p -> Pr i)
    {measure (n - p)} : Exc (forall i : N n, Pr i) :=
    match le_lt_dec n p with
      | left _ => value _
      | right cmp =>
        match @P (N_ cmp) with
          | error => error
          | value _ => @check_seq_aux (S p) _ _
        end
    end.

  Next Obligation.
  Proof.
    apply H. destruct i. simpl. omega.
  Qed.
  Next Obligation.
  Proof.
    destruct i as [x l]. simpl in *.
    destruct (eq_nat_dec x p).
    subst. rewrite (lt_unique l cmp). hyp.
    apply H. simpl. omega.
  Qed.
  Next Obligation.
  Proof.
    omega.
  Qed.

End Check_seq_aux.

Program Definition check_seq (n : nat) (Pr : N n -> Prop)
  (P : forall (i : N n), Exc (Pr i)) :
  Exc (forall (i : N n), Pr i) :=
  check_seq_aux _ P (p:=0) _.

Next Obligation.
Proof.
  elimtype False. omega.
Qed.

Arguments check_seq [n Pr] _.
