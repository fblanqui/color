(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Leo Ducas, 2007-08-06

type of natural numbers smaller than some constant
*)

Set Implicit Arguments.

Require Import NatUtil LogicUtil ListPermutation NatLt List.

Section S.

  Variable dim : nat.

  (*FIXME: replace by NatLt.L ?*)
  Fixpoint bnats_of_nats l :=
    match l with
      | nil => nil
      | x::q =>
        match lt_ge_dec x dim with 
          | left h => N_ h :: bnats_of_nats q
          | right _ => bnats_of_nats q
        end
    end.

  Definition nfirst_bnats := bnats_of_nats (nats_decr_lt dim).

  Require Import SortUtil RelUtil.

  Lemma map_lelistA_bnat_to_nat : forall R (a : N dim) l,
    lelistA (Rof R N_val) a l -> lelistA R a (map N_val l).

  Proof.
    induction l; intros. simpl; apply nil_leA.
    simpl. inversion H; subst. apply cons_leA; auto.
  Qed.

  Lemma map_sort_bnat_to_nat : forall R (l : list (N dim)),
    sort (Rof R N_val) l -> sort R (map N_val l).

  Proof.
    induction l; intros. simpl; apply nil_sort.
    simpl. inversion H; apply cons_sort; try tauto.
    apply map_lelistA_bnat_to_nat. intuition.
  Qed.

  Lemma nfirst_multiplicity : forall n i,
    multiplicity (list_contents eq_nat_dec (nats_decr_lt n)) i
    = if lt_ge_dec i n then 1 else 0.

  Proof. 
    induction n; intros. simpl. destruct (lt_ge_dec i 0); omega.
    simpl. rewrite IHn. destruct (lt_ge_dec i n); destruct (eq_nat_dec n i);
    destruct (lt_ge_dec i (S n)); try omega.
  Qed.

  Lemma bnfirst_multiplicity n (i : N dim) :
    multiplicity (list_contents N_eq_dec (bnats_of_nats (nats_decr_lt n))) i
    = if lt_ge_dec (N_val i) n then 1 else 0.

  Proof.
    destruct i as [i hi]. fold (N_ hi). simpl. induction n.
    simpl. destruct (lt_ge_dec i 0); omega.
    simpl. destruct (lt_ge_dec n dim); simpl; rewrite IHn;
    destruct(eq_nat_dec n i); destruct(lt_ge_dec i n);
      destruct(lt_ge_dec i (S n)); subst; simpl; try omega;
        try congruence.
  Qed.

  Lemma map_multiplicity : forall a (h : a<dim) mb,
    multiplicity (list_contents N_eq_dec mb) (N_ h)
    = multiplicity (list_contents eq_nat_dec (map N_val mb)) a.

  Proof.
    induction mb. simpl; auto.
    simpl. rewrite IHmb. destruct (eq_nat_dec a0 a);
    destruct (N_eq_dec a0 (N_ h)); try omega; try congruence.
    destruct a0. simpl in *. subst. ded (lt_unique g h).
    unfold N_ in n. congruence.
    destruct a0. simpl in *. unfold N_ in e. congruence.
  Qed.

  Lemma lemme_foo : forall a (H:a>=dim) (mb : list (N dim)), 
    multiplicity (list_contents eq_nat_dec (map N_val mb)) a = 0.

  Proof.
    induction mb. simpl; auto.
    simpl. destruct (eq_nat_dec a0 a).
    destruct a0; simpl in *; subst; omega. simpl. apply IHmb.
  Qed.

End S.
