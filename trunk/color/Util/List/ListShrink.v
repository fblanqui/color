(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17

prefix, suffix, cut, elimination of doubles, etc.
*)

Set Implicit Arguments.

Require Import ListUtil.
Require Import ListRepeatFree.
Require Import Le.

(***********************************************************************)
(** prefix *)

Section prefix.

Variable A : Type.

Fixpoint prefix (l l' : list A) {struct l} : Prop :=
  match l with
    | nil => True
    | x::l => match l' with
                | nil => False
                | y::l' => x=y /\ prefix l l'
              end
  end.

Lemma prefix_nil : forall l : list A, prefix l nil -> l = nil.

Proof.
destruct l; intros. trivial. simpl. contradiction.
Qed.

Lemma reflexive_prefix : forall l : list A, prefix l l.

Proof.
induction l; simpl; intros; tauto.
Qed.

Lemma prefix_incl : forall l l' : list A, prefix l l' -> incl l l'.

Proof.
induction l; intros. apply incl_nil.
destruct l'. pose (prefix_nil (a::l) H). inversion e. simpl in H. 
rewrite (proj1 H). unfold incl. simpl. intros. 
destruct H0. tauto. constructor 2. apply IHl; tauto. 
Qed.

Lemma prefix_app_right_right : forall l l' l'',
  prefix l l' -> prefix l (l' ++ l'').

Proof.
induction l; simpl; intros. trivial. destruct l'; simpl in *|-* . contradiction.
split. tauto. apply IHl. tauto.
Qed.

Lemma prefix_smaller : forall (x : A) l l',
  l <> l'++x::nil -> prefix l (l'++x::nil) -> prefix l l'.

Proof.
induction l; intros. trivial. destruct l'. simpl in H0. destruct H0.
pose (prefix_nil l H1). rewrite H0 in H. rewrite e in H. tauto. simpl in H0.
simpl. 
split. tauto. apply IHl. intro. rewrite (proj1 H0) in H. rewrite H1 in H.
tauto. tauto.
Qed.

End prefix.

(***********************************************************************)
(** suffix *)

Section suffix.

Variable A : Type.

Definition suffix (l l' : list A) : Prop := prefix (rev l)(rev l').

Lemma suffix_incl : forall l l' : list A, suffix l l' -> incl l l'.

Proof.
intros. apply incl_rev_intro. unfold suffix in H. apply prefix_incl. assumption. 
Qed.

Lemma suffix_smaller : forall l (x : A) l',
  l <> x::l' -> suffix l (x::l') -> suffix l l'.

Proof.
unfold suffix. intros. assert (rev l<>rev (x::l')). intro.
assert (rev (rev l)=rev(rev (x::l'))).
rewrite H1. trivial. pose (rev_involutive l). pose (rev_involutive (x::l')).
rewrite e in H2.
rewrite e0 in H2. tauto. apply prefix_smaller with x; assumption.
Qed.

End suffix.

(***********************************************************************)
(** cut *)

Section cut.

Variable A : Type.
Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Fixpoint cut (x : A) (l : list A) {struct l} : list A :=
  match l with
    | nil => nil
    | y::l' => if eq_dec x y then l else cut x l'
  end.

Lemma suffix_cut : forall (x : A) l, suffix (cut x l) l.

Proof.
unfold suffix. induction l; simpl; intros. trivial. destruct (eq_dec x a).
rewrite <- e. apply reflexive_prefix. apply prefix_app_right_right. assumption.
Qed.

Lemma cut_head : forall (x : A) l, In x l -> cut x l = x::(tail (cut x l)).

Proof.
induction l; simpl; intros. contradiction. destruct (eq_dec x a). simpl.
rewrite e. trivial.
destruct H. rewrite H in n. tauto. tauto.
Qed.

Lemma length_cut : forall (x : A) l, length (cut x l) <= length l.

Proof.
induction l; simpl. apply le_O_n. destruct (eq_dec x a).
apply le_refl. apply le_trans with (length l). assumption. apply le_n_Sn.
Qed.

Lemma length_tail_cut_cons : forall (x y : A) l,
  length (tail (cut x (y::l))) <= length l.

Proof.
intros. simpl. destruct (eq_dec x y); simpl. trivial.
apply le_trans with (length (cut x l)). apply length_tail. apply length_cut. 
Qed.

Lemma repeat_free_cut : forall (x : A) l, repeat_free l -> repeat_free (cut x l).

Proof.
induction l; simpl; intros. trivial. destruct (eq_dec x a). simpl. tauto. tauto.
Qed.

Lemma incl_cut :  forall (x : A) l, incl (cut x l) l.

Proof.
intros. apply suffix_incl. apply suffix_cut. 
Qed.

End cut.

(***********************************************************************)
(** shrink *)

Section shrink.

Variable A : Type.
Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Fixpoint shrink (l :list A) : list A :=
  match l with
    | nil => nil
    | x::l => if In_dec eq_dec x (shrink l) then cut eq_dec x (shrink l)
      else x::(shrink l)
  end.

Lemma repeat_free_shrink : forall l : list A, repeat_free (shrink l).

Proof.
induction l; simpl; intros. trivial. destruct (In_dec eq_dec a (shrink l)).
apply repeat_free_cut. assumption. simpl. tauto.
Qed.

Lemma incl_shrink : forall l : list A, incl (shrink l) l.

Proof.
induction l; simpl; intros. apply incl_nil.
destruct (In_dec eq_dec a (shrink l)).
apply incl_tran with (shrink l). apply incl_cut. apply incl_tl. assumption.
unfold incl. intros. simpl in H. simpl. case (eq_dec a a0); intro.
subst a0. auto. right. apply IHl. destruct H. contradiction. exact H.
Qed.

Require Import RelMidex.

Lemma length_shrink : forall l l' : list A,
  incl l l' -> length (shrink l) <= length l'.

Proof.
intros. apply repeat_free_incl_length. exact (eq_dec_midex eq_dec). apply repeat_free_shrink.
apply incl_tran with l. apply incl_shrink. assumption.
Qed.

End shrink.
