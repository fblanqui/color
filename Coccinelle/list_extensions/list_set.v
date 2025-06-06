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

(** * Sets built with lists *)

Set Implicit Arguments. 

From Stdlib Require Import Relations List Setoid Arith FunInd.
From CoLoR Require Import decidable_set more_list list_permut.

Module Type S.

Declare Module Import EDS : decidable_set.ES.
Declare Module Import LP : list_permut.S with Module EDS := EDS.

Fixpoint without_red_bool (l : list A) {struct l} : bool :=
  match l with
  | nil => true
  | e :: le => if (mem_bool eq_bool e le) then false else without_red_bool le
  end.

Definition without_red l := without_red_bool l = true.

Record t : Type :=
  mk_set 
  {
     support : list A;
     is_a_set : without_red support
  }.

Definition mem e s := mem eq_A e s.(support).

Definition cardinal s := List.length s.(support).

(*** Equality of sets. *)
Definition eq_set s1 s2 := forall e, mem e s1 <-> mem e s2.

Parameter eq_set_refl : forall s, eq_set s s.

Parameter eq_set_list_permut_support :
  forall s1 s2,  eq_set s1 s2 -> permut s1.(support) s2.(support).

Definition subset s1 s2 : Prop :=
  forall e, mem e s1 -> mem e s2.

Parameter cardinal_subset :
  forall s1 s2, subset s1 s2 -> cardinal s1 <= cardinal s2.

End S.

(** ** Definition of sets using lists. *)
Module Make (EDS1 : decidable_set.ES) <: S with Module EDS:= EDS1.

Module Import EDS := EDS1.

Module Import LP := list_permut.Make (EDS).

(*** Property of being without redundancy for lists of elements, intended as sets. *)
Function without_red_bool (l : list A) {struct l} : bool :=
  match l with
  | nil => true
  | e :: le => if (mem_bool eq_bool e le) then false else without_red_bool le
  end.

Definition without_red l := without_red_bool l = true.

Lemma without_red_remove :
  forall e l1 l2, without_red (l1 ++ e :: l2) -> without_red (l1 ++ l2).
Proof.
unfold without_red; fix without_red_remove 2.
intros e l1 l2; case l1; clear l1; simpl.
case (mem_bool eq_bool e l2); [intro H; discriminate | trivial].
intros e1 l1;
generalize (mem_bool_ok _ _ eq_bool_ok e1 (l1 ++ e :: l2)).
case (mem_bool eq_bool e1 (l1 ++ e :: l2)).
intros; discriminate.
intros e1_not_mem_l Wl.
generalize (mem_bool_ok _ _ eq_bool_ok e1 (l1 ++ l2)).
case (mem_bool eq_bool e1 (l1 ++ l2)).
intro e1_mem_l'; apply False_rect; apply e1_not_mem_l; apply mem_insert; trivial.
intro; apply (without_red_remove e l1 l2); trivial.
Qed.

Lemma without_red_not_in :
  forall e l1 l2, without_red (l1 ++ e :: l2) -> ~mem eq_A e (l1 ++ l2).
Proof.
unfold without_red; fix without_red_not_in 2.
intros e l1 l2; case l1; clear l1; simpl.
generalize (mem_bool_ok _ _ eq_bool_ok e l2); case (mem_bool eq_bool e l2).
intros _ H _; discriminate.
intros H _; exact H.
intros e1 l1; generalize (mem_bool_ok _ _ eq_bool_ok e1 (l1 ++ e :: l2)); 
case (mem_bool eq_bool e1 (l1 ++ e :: l2)).
intros _ H _; discriminate.
intros e1_not_in_l1_e_l2 wr [e_eq_e1 | e_mem_l1l2]; apply e1_not_in_l1_e_l2.
rewrite <- mem_or_app; right; left; symmetry; assumption.
apply False_rect; apply (without_red_not_in e l1 l2 wr e_mem_l1l2).
Qed.

Lemma add_prf :
  forall e l1 l2, without_red (l1 ++ l2) -> ~mem eq_A e (l1 ++ l2) ->
  without_red (l1 ++ e :: l2).
Proof.
unfold without_red; fix add_prf 2.
intros e l1 l2; case l1; clear l1; simpl.
intros wr12 e_not_in_l1_l2; 
generalize (mem_bool_ok _ _ eq_bool_ok e l2); case (mem_bool eq_bool e l2).
intro e_in_l2; absurd (mem eq_A e l2); assumption.
intros _; exact wr12.
intros e1 l1 wr12 e_not_in_l1_l2; generalize (mem_bool_ok _ _ eq_bool_ok e1 (l1 ++ e :: l2)).
case (mem_bool eq_bool e1 (l1 ++ e :: l2)).
intro e1_in_l1_l2; 
absurd (mem eq_A e1 (l1 ++ l2)).
apply (without_red_not_in e1 nil (l1 ++ l2)); trivial.
apply diff_mem_remove with e; trivial;
intro; apply e_not_in_l1_l2; subst; left; symmetry; trivial.
intros _; apply add_prf.
apply (without_red_remove e1 nil (l1 ++ l2)); trivial.
intro; apply e_not_in_l1_l2; right; trivial.
Qed.

Lemma without_red_permut :
 forall l1 l2, without_red l1 -> LP.permut l1 l2 -> without_red l2.
Proof.
unfold without_red; fix without_red_permut 1.
intros l1; case l1; clear l1.
intros l2 _ P; rewrite (permut_nil (permut_sym P)); reflexivity.
intros a1 l1 l2; simpl.
generalize (mem_bool_ok _ _ eq_bool_ok a1 l1); case (mem_bool eq_bool a1 l1).
intros; discriminate.
intros a1_not_in_l1 wr1 P;assert (a1_in_l2 := cons_permut_mem (Relation_Definitions.equiv_refl _ _ eq_proof a1) P).
case (mem_split_set _ _ eq_bool_ok _ _ a1_in_l2);
intros a1' M; case M; clear M.
intros l2' M; case M; clear M.
intros l2'' M; case M; clear M.
intros a1_eq_a1' M; case M; clear M.
intros H _; subst l2.
rewrite <- permut_cons_inside in P; [idtac | exact a1_eq_a1'].
apply add_prf.
apply (without_red_permut l1); trivial.
rewrite <- (mem_permut_mem a1' P).
intro a1_in_l1; apply a1_not_in_l1.
apply (mem_eq_mem eq_proof a1' a1 l1 (equiv_sym _ _ eq_proof _ _ a1_eq_a1') a1_in_l1).
Qed.

(*** How to remove redundancies from a list with remove_red. *)
Function remove_red (l : list A) : list A :=
  match l with
  | nil => nil
  | e :: le => 
           if (mem_bool eq_bool e le) 
           then remove_red le 
           else e :: (remove_red le)
   end.

Lemma included_remove_red : 
forall e l, mem eq_A e (remove_red l) -> mem eq_A e l.
Proof.
fix included_remove_red 2.
intros x l; case l; clear l.
intro H; exact H.
intros a l; simpl; case (mem_bool eq_bool a l).
intros x_in_rl; right; exact (included_remove_red x l x_in_rl).
intro x_in_arl; simpl in x_in_arl; case x_in_arl; clear x_in_arl.
intro x_eq_a; left; exact x_eq_a.
intro x_in_rl; right; exact (included_remove_red x l x_in_rl).
Qed.

Lemma remove_red_included : forall e l, mem eq_A e l -> mem eq_A e (remove_red l).
Proof.
fix remove_red_included 2.
intros x l; case l; clear l.
intro H; exact H.
intros a l; simpl; generalize (mem_bool_ok _ _ eq_bool_ok a l); case (mem_bool eq_bool a l).
intros a_in_l x_in_al; case x_in_al; clear x_in_al.
intro x_eq_a; apply remove_red_included.
apply (mem_eq_mem eq_proof a x l (equiv_sym _ _ eq_proof _ _ x_eq_a) a_in_l).
intro x_in_l; exact (remove_red_included x l x_in_l).
intros _ x_in_al; case x_in_al; clear x_in_al.
intro x_eq_a; left; exact x_eq_a.
intro x_in_l; right; exact (remove_red_included x l x_in_l).
Qed.

Lemma without_red_remove_red :  forall l, without_red (remove_red l).
Proof.
unfold without_red; fix without_red_remove_red 1.
intro l; case l; clear l.
reflexivity.
intros a l; simpl.
generalize (mem_bool_ok _ _ eq_bool_ok a l); case (mem_bool eq_bool a l).
intro a_in_l; apply without_red_remove_red.
intro a_not_in_l; simpl; generalize (mem_bool_ok _ _ eq_bool_ok a (remove_red l)).
case (mem_bool eq_bool a (remove_red l)).
intro a_in_rl; absurd (mem eq_A a l).
assumption.
apply included_remove_red; trivial.
intro a_not_in_rl; apply without_red_remove_red.
Qed.

(*** Definition of sets as lists without redundancy and a proof of this fact. *)
Record t : Type :=
  mk_set 
  {
     support : list A;
     is_a_set : without_red support
  }.

Definition mem e s := mem eq_A e s.(support).

Lemma eq_mem_mem :
  forall s e e', eq_A e e' -> mem e s -> mem e' s.
Proof.
intros s e e' e_eq_e' e_mem_s;
destruct (mem_split_set _ _ eq_bool_ok _ _ e_mem_s) as [a [l' [l'' [e_eq_a [H _]]]]].
unfold mem; rewrite H.
rewrite <- mem_or_app; right; left.
transitivity e; trivial.
symmetry; trivial.
Qed.

Definition add : A -> t -> t.
intros e s.
generalize (mem_bool_ok _ _ eq_bool_ok e s.(support)).
case (mem_bool eq_bool e s.(support)).
intros _; exact s.
intros e_not_in_s.
exact (mk_set (add_prf e nil s.(support) s.(is_a_set) e_not_in_s)).
Defined.

Lemma already_mem_add : forall e s, mem e s -> add e s = s.
intros a [l prf]; unfold mem, add; simpl; generalize (mem_bool_ok _ _ EDS1.eq_bool_ok a l).
case (mem_bool EDS1.eq_bool a l).
intros; reflexivity.
intros a_not_in_l a_in_l; apply False_rect; apply a_not_in_l; assumption.
Qed.

Lemma not_already_mem_add :
  forall e s, ~ mem e s -> e :: support s = support (add e s).
intros a [l prf]; unfold mem, add; simpl; generalize (mem_bool_ok _ _ EDS1.eq_bool_ok a l).
case (mem_bool EDS1.eq_bool a l).
intros a_in_l a_not_in_l; apply False_rect; apply a_not_in_l; assumption.
intros; reflexivity.
Qed.

Lemma add_1 : forall e s, mem e (add e s).
Proof.
intros e s; unfold mem, add; simpl.
generalize (mem_bool_ok _ _ eq_bool_ok e s.(support)).
case (mem_bool eq_bool e s.(support)).
intro H; exact H.
simpl; intros _; left; reflexivity.
Qed.

Lemma add_2 : forall e e' s, mem e s -> mem e (add e' s).
Proof.
intros e e' s; unfold mem, add; simpl; 
generalize (mem_bool_ok _ _ eq_bool_ok e' s.(support)).
case (mem_bool eq_bool e' s.(support)).
intros _ H; exact H.
simpl; intros _; right; assumption.
Qed.

Lemma add_12 : forall e e' s, mem e (add e' s) -> eq_A e e' \/ mem e s.
Proof.
intros e e' s; unfold mem, add; simpl;
generalize (mem_bool_ok _ _ eq_bool_ok e' s.(support)).
case (mem_bool eq_bool e' s.(support)).
intros _ H; right; assumption.
simpl; intros _ H; assumption.
Qed.

Function filter_aux (P_bool : A -> bool)  (l : list A) {struct l} : list A :=
  match l with
  | nil => nil
  | e :: le => 
           if (P_bool e)
           then e :: (filter_aux P_bool le) 
           else filter_aux P_bool le
   end.

(*** Properties of filter. *)
Lemma included_filter_aux : 
  forall P_bool e l, 
  more_list.mem eq_A e (filter_aux P_bool l) -> more_list.mem eq_A e l.
Proof.
intros P_bool x l; 
functional induction (filter_aux P_bool l) 
    as [ | H1 e l H2 P_e IH | H1 e l H2 not_P_e IH ].
trivial.
intros [x_eq_e | x_in_fl]; [left | right; apply IH]; trivial.
intros  x_in_fl; right; apply IH; trivial.
Qed.

Lemma without_red_filter_aux :  
  forall P_bool l, without_red l -> without_red (filter_aux P_bool l).
Proof.
unfold without_red; fix without_red_filter_aux 2.
intros P_bool l; case l; clear l.
intros _; reflexivity.
simpl; intros a l.
generalize (mem_bool_ok _ _ eq_bool_ok a l); case (mem_bool eq_bool a l).
intros; discriminate.
intros a_not_in_l Wl; case (P_bool a); simpl; rewrite (without_red_filter_aux P_bool l Wl).
generalize (mem_bool_ok _ _ eq_bool_ok a (filter_aux P_bool l));
case (mem_bool eq_bool a (filter_aux P_bool l)).
intro a_in_l; absurd (more_list.mem eq_A a l).
assumption.
apply included_filter_aux with P_bool; assumption.
intros _; reflexivity.
reflexivity.
Defined.

Definition filter (P_bool : A -> bool) s 
  (P_compat : forall e e', eq_A e e' -> (P_bool e = P_bool e')) := 
   mk_set (without_red_filter_aux P_bool s.(is_a_set)).

Lemma filter_1_list :
  forall (P_bool : A -> bool) l e 
  (P_compat : forall e e', eq_A e e' -> (P_bool e = P_bool e')),
  more_list.mem eq_A e l -> P_bool e = true -> more_list.mem eq_A e (filter_aux P_bool l).
Proof.
intros P_bool l e P_compat e_in_l P_e;
functional induction (filter_aux P_bool l) 
    as [ | H1 e' l H2 P_e' IH | H1 e' l H2 not_P_e IH ].
contradiction.
destruct e_in_l as [e_eq_e' | e_in_l]; [left | right; apply IH]; trivial.
simpl in e_in_l; destruct e_in_l as [e_eq_e' | e_in_l].
rewrite (P_compat e e') in P_e; trivial; rewrite P_e in not_P_e; discriminate.
apply IH; trivial.
Qed.

Lemma filter_1 :
  forall (P_bool : A -> bool) s P_compat e, 
  mem e s -> P_bool e = true -> mem e (filter P_bool s P_compat).
Proof.
unfold mem, support; 
intros P_bool [l wr] P_compat e e_in_s P_e; simpl;  apply filter_1_list; trivial.
Qed.

Lemma filter_2_list :
 forall (P_bool : A -> bool) l e  
  (P_compat : forall e e', eq_A e e' -> (P_bool e = P_bool e')),
  more_list.mem eq_A e (filter_aux P_bool l) -> more_list.mem eq_A e l /\ P_bool e = true.
Proof.
intros P_bool l e P_compat H; 
functional induction (filter_aux P_bool l) 
    as [ | H1 e' l H2 P_e' IH | H1 e' l H2 not_P_e IH ].
contradiction.
destruct H as [e_eq_e' | e_in_fl]; split.
left; trivial.
rewrite (P_compat e e'); trivial.
right; apply (proj1 (IH e_in_fl)).
apply (proj2 (IH e_in_fl)).
split; [right | idtac]; destruct (IH H); trivial.
Qed.

Lemma filter_2 :
 forall (P_bool : A -> bool) s P_compat e, 
  mem e (filter P_bool s P_compat) -> mem e s /\ P_bool e = true.
Proof.
unfold mem, support; 
intros P_bool [l wr] e E e_in_l_and_P_e.
apply filter_2_list; trivial.
Qed.

(*** Empty set. *)
Lemma without_red_nil : without_red nil.
Proof.
unfold without_red; simpl; trivial.
Qed.

Definition empty : t := mk_set without_red_nil.

(*** Singleton *)
Lemma without_red_singleton : forall e : A, without_red (e :: nil).
Proof.
unfold without_red; intro e; simpl; reflexivity.
Qed.

Definition singleton (e : A) : t := mk_set (without_red_singleton e).

(*** How to build a set from a list of elements. *)
Definition make_set (l : list A) : t := mk_set (without_red_remove_red l).

(*** Union of sets. *)
Function add_without_red (acc l : list A) {struct l} : list A :=
  match l with
  | nil => acc
  | e :: le =>
     if (mem_bool eq_bool e acc)
     then add_without_red acc le
     else add_without_red (e :: acc) le
  end.

Lemma without_red_add_without_red :
  forall l1 l2, without_red l1 -> without_red (add_without_red l1 l2).
Proof.
unfold without_red; 
intros l1 l2 Wl1; 
functional induction (add_without_red l1 l2) 
    as [ | l1 H1 e l2 H2 e_in_l1 IH | l1 H1 e l2 H2 e_not_in_l1 IH ].
assumption.
apply IH; assumption.
apply IH; simpl.
rewrite e_not_in_l1; assumption.
Qed.

Definition union s1 s2 := mk_set (without_red_add_without_red s2.(support) s1.(is_a_set)).

Lemma union_1_aux :
forall (l1 l2 : list A) (e : A), more_list.mem eq_A e l1 -> more_list.mem eq_A e (add_without_red l1 l2).
Proof.
fix union_1_aux 2.
intros l1 l2; case l2; clear l2.
intros; assumption.
intros a2 l2 e e_in_l1; simpl.
case (mem_bool eq_bool a2 l1).
apply (union_1_aux l1 l2 _ e_in_l1).
apply (union_1_aux (a2 :: l1) l2 _ (or_intror _ e_in_l1)).
Qed.

Lemma union_1 : forall s1 s2 e, mem e s1 -> mem e (union s1 s2).
Proof.
unfold mem; intros [l1 wr1] [l2 wr2] e; simpl; apply union_1_aux. 
Qed.

Lemma union_2_aux :
forall (l1 l2 : list A) (e : A), more_list.mem eq_A e l2 -> more_list.mem eq_A e (add_without_red l1 l2).
Proof.
fix union_2_aux 2.
intros l1 l2; case l2; clear l2.
intros; contradiction.
intros a2 l2 e e_in_a2l2; simpl in e_in_a2l2; simpl.
case e_in_a2l2; clear e_in_a2l2.
intro e_eq_a2.
refine (mem_eq_mem eq_proof a2 e _ (equiv_sym _ _ eq_proof _ _ e_eq_a2) _); simpl.
generalize (mem_bool_ok _ _ eq_bool_ok a2 l1); case (mem_bool eq_bool a2 l1).
intro a2_in_l1; apply union_1_aux; assumption.
intros _; apply (union_1_aux (a2 :: l1) l2); left; reflexivity.
intro e_in_l2; case (mem_bool eq_bool a2 l1); apply union_2_aux; assumption.
Qed.

Lemma union_2 : forall s1 s2 e, mem e s2 -> mem e (union s1 s2).
Proof.
unfold mem; intros [l1 wr1] [l2 wr2] e; simpl; apply union_2_aux.
Qed.

Lemma union_12_aux :
forall (l1 l2 : list A) (e : A), more_list.mem eq_A e (add_without_red l1 l2) -> 
       more_list.mem eq_A e l1 \/ more_list.mem eq_A e l2.
Proof.
intros l1 l2 e e_in_l1_l2; 
functional induction (add_without_red l1 l2) 
    as [ | l1 H1 e2 l2 H2 e2_in_l1 IH | l1 H1 e2 l2 H2 e2_not_in_l1 IH ].
left; trivial.
destruct (IH e_in_l1_l2) as [e_in_l1 | e_in_l2]; [left | do 2 right]; trivial.
destruct (IH e_in_l1_l2) as [[e_eq_e2 | e_in_l1] | e_in_l2];
[ right; left | left | do 2 right]; trivial.
Qed.

Lemma union_12 : 
  forall s1 s2 e, mem e (union s1 s2) -> mem e s1 \/ mem e s2.
Proof.
unfold mem; intros [l1 wr1] [l2 wr2] e; simpl; apply union_12_aux.
Qed.

Function remove_not_common (acc l1 l2 : list A) {struct l2} : list A :=
  match l2 with
  | nil => acc
  | e :: l => 
      if (mem_bool eq_bool e l1)
      then remove_not_common (e :: acc) l1 l
      else remove_not_common acc l1 l
  end.

Lemma length_remove_not_common : 
   forall l1 l2 acc, length (remove_not_common acc l1 l2) = length acc + length (remove_not_common nil l1 l2).
fix length_remove_not_common 2.
intros l1 l2 acc; case l2; clear l2; simpl.
rewrite <- plus_n_O; reflexivity.
intros a2 l2; case (mem_bool eq_bool a2 l1).
rewrite (length_remove_not_common l1 l2 (a2 :: acc)); 
rewrite (length_remove_not_common l1 l2 (a2 :: nil)); simpl; apply plus_n_Sm.
apply length_remove_not_common.
Qed.

Lemma without_red_remove_not_common_aux :
  forall acc l1 l2, (forall e, more_list.mem eq_A e acc /\ more_list.mem eq_A e l2 -> False) ->
                           without_red acc -> without_red l1 -> without_red l2 -> 
                           without_red (remove_not_common acc l1 l2).
Proof.
intros acc l1 l2 H Wa Wl1 Wl2;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e l2 H2 e_in_l1 IH
         | acc l1 H1 e l2 H2 e_not_in_l1 IH].
trivial.
apply IH.
simpl; intros a H'; case H'; clear H'; intro H'; case H'; clear H'.
intros a_eq_e; revert Wl2; unfold without_red; simpl.
generalize (mem_bool_ok _ _ eq_bool_ok e l2); case (mem_bool eq_bool e l2).
intros _ Abs _; discriminate.
intros e_not_in_l2 _ e_in_l2; apply e_not_in_l2.
apply (mem_eq_mem eq_proof a); assumption.
intros a_in_acc a_in_l2; apply (H a); split; [idtac | right]; assumption.
unfold without_red; simpl.
generalize (mem_bool_ok _ _ eq_bool_ok e acc); case (mem_bool eq_bool e acc).
intro e_in_acc; apply False_rect; apply (H e); split; [assumption | left; reflexivity].
intros _; unfold without_red in Wa; assumption.
assumption.
revert Wl2; unfold without_red; simpl; case (mem_bool eq_bool e l2).
intro; discriminate.
intro; assumption.
apply IH.
simpl; intros a H'; case H'; clear H'.
intros a_in_acc a_in_l2; apply (H a); split; [idtac | right]; assumption.
assumption.
assumption.
revert Wl2; unfold without_red; simpl; case (mem_bool eq_bool e l2).
intro; discriminate.
intro; assumption.
Qed.

Lemma without_red_remove_not_common :
  forall l1 l2, without_red l1 -> without_red l2 ->
                    without_red (remove_not_common nil l1 l2).
Proof.
intros l1 l2 wr1 wr2; 
apply without_red_remove_not_common_aux; trivial.
intros e [ H _ ]; contradiction.
unfold without_red; simpl; trivial.
Qed.

Definition inter s1 s2 :=
  mk_set (without_red_remove_not_common s1.(is_a_set) s2.(is_a_set)).

Lemma inter_1_aux : 
  forall acc l1 l2 e, more_list.mem eq_A e (remove_not_common acc l1 l2) -> 
  more_list.mem eq_A e acc \/ more_list.mem eq_A e l1.
Proof.
intros acc l1 l2 e e_in_acc_l1;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e2 l2 H2 e2_in_l1 IH
         | acc l1 H1 e2 l2 H2 e2_not_in_l1 IH].
left; trivial.
destruct (IH e_in_acc_l1) as [[e_eq_e2 | e_in_acc] | e_in_l1];
[ subst; right | left | right ]; trivial.
apply (mem_eq_mem eq_proof e2).
apply (equiv_sym _ _ eq_proof); assumption.
generalize (mem_bool_ok _ _ eq_bool_ok e2 l1); rewrite e2_in_l1; intro H; exact H.
apply IH; trivial.
Qed.

Lemma inter_1 : forall s1 s2 e, mem e (inter s1 s2) -> mem e s1. 
Proof.
intros [l1 wr1] [l2 wr2] e H; simpl.
generalize (inter_1_aux nil l1 l2 e H).
intros [ H' | H']; trivial; contradiction.
Qed.

Lemma inter_2_aux : 
  forall acc l1 l2 e, more_list.mem eq_A e (remove_not_common acc l1 l2) -> 
  more_list.mem eq_A e acc \/ more_list.mem eq_A e l2.
Proof.
intros acc l1 l2 e e_in_acc_l2;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e2 l2 H2 e2_in_l1 IH
         | acc l1 H1 e2 l2 H2 e2_not_in_l1 IH].
left; trivial.
destruct (IH e_in_acc_l2) as [[e_eq_e2 | e_in_acc] | e_in_l1];
[ subst; right; left | left | right; right ]; trivial.
destruct (IH e_in_acc_l2) as [e_in_acc | e_in_l2]; [left | right; right]; trivial.
Qed.

Lemma inter_2 : forall s1 s2 e, mem e (inter s1 s2) -> mem e s2.
Proof.
intros [l1 wr1] [l2 wr2] e H; simpl.
generalize (inter_2_aux nil l1 l2 e H).
intros [ H' | H']; trivial; contradiction.
Qed.

Lemma inter_12_aux :
  forall acc l1 l2 e,  more_list.mem eq_A e l1 -> more_list.mem eq_A e l2 -> 
  more_list.mem eq_A e (remove_not_common acc l1 l2).
Proof.
assert (H : forall acc l1 l2 e, more_list.mem eq_A e acc -> 
                    more_list.mem eq_A e (remove_not_common acc l1 l2)).
intros acc l1 l2 e e_in_acc;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e2 l2 H2 e2_in_l1 IH
         | acc l1 H1 e2 l2 H2 e2_not_in_l1 IH].
trivial.
apply IH; right; trivial.
apply IH; trivial.

intros acc l1 l2 e e_in_l1 e_in_l2;
functional induction (remove_not_common acc l1 l2) 
    as [ 
         | acc l1 H1 e2 l2 H2 e2_in_l1 IH
         | acc l1 H1 e2 l2 H2 e2_not_in_l1 IH].
contradiction.
destruct e_in_l2 as [e_eq_e2 | e_in_l2]; [subst; apply H; left | apply IH]; trivial.
destruct e_in_l2 as [e_eq_e2 | e_in_l2].
absurd (more_list.mem eq_A e2 l1).
generalize (mem_bool_ok _ _ eq_bool_ok e2 l1); rewrite e2_not_in_l1; intro H'; exact H'.
apply (mem_eq_mem eq_proof e); assumption.
apply IH; trivial.
Qed.

Lemma inter_12 : 
  forall s1 s2 e, mem e s1 -> mem e s2 -> mem e (inter s1 s2).
Proof.
intros [l1 wr1] [l2 wr2] e e_in_l1 e_in_l2; 
refine (inter_12_aux nil l1 l2 e _ _); trivial.
Qed.

(*** Subset. *)
Definition subset s1 s2 : Prop :=
  forall e, mem e s1 -> mem e s2.

Lemma subset_dec : forall s1 s2, {subset s1 s2} + {~ subset s1 s2}.
Proof.
unfold subset, mem; intros s1 s2; case s1; clear s1; simpl; intros l1 _; case s2; clear s2; simpl; intros l2 _.
revert l1 l2; fix subset_dec 1.
intros l1; case l1; clear l1; simpl.
(* 1/2  l1 = [] *)
intros l2; left; intros; contradiction.
(* 1/1 l1 = _ :: _ *)
intros a1 l1 l2.
generalize (mem_bool_ok _ _ eq_bool_ok a1 l2); case (mem_bool eq_bool a1 l2).
(* 1/2 a1 in l2 *)
intro a1_in_l2; case (subset_dec l1 l2).
(* 1/3 l1 in l2 *)
intros l1_in_l2; left.
intros e e_in_a1l1; case e_in_a1l1; clear e_in_a1l1.
intro e_eq_a1; apply (mem_eq_mem eq_proof a1).
apply (equiv_sym _ _ eq_proof); assumption.
assumption.
intros e_in_l1; exact (l1_in_l2 e e_in_l1).
(* 1/2 l1 not in l2 *)
intro l1_not_in_l2; right; intro l1_in_l2; apply l1_not_in_l2.
intros e e_in_l1; exact (l1_in_l2 e (or_intror _ e_in_l1)).
(* 1/1 a1 not in l2 *)
intro a1_not_in_l2; right; intro l1_in_l2; apply a1_not_in_l2.
apply (l1_in_l2 a1); left; reflexivity.
Defined.

Lemma subset_union_1 :
  forall s1 s2, subset s1 (union s1 s2).
Proof.
intros s1 s2 e; apply union_1.
Qed.

Lemma subset_union_2 :
  forall s1 s2, subset s2 (union s1 s2).
Proof.
intros s1 s2 e; apply union_2.
Qed.

Lemma subset_inter_1 :
  forall s1 s2, subset (inter s1 s2) s1.
Proof.
intros s1 s2 e; apply inter_1.
Qed.

Lemma subset_inter_2 :
  forall s1 s2, subset (inter s1 s2) s2.
Proof.
intros s1 s2 e; apply inter_2.
Qed.

(*** Equality of sets. *)
Definition eq_set s1 s2 :=
  forall e, mem e s1 <-> mem e s2.

Lemma eq_set_dec : forall s1 s2, {eq_set s1 s2} + {~eq_set s1 s2}.
Proof.
intros s1 s2; destruct (subset_dec s1 s2) as [ s1_incl_s2 | s1_not_incl_s2 ].
destruct (subset_dec s2 s1) as [ s2_incl_s1 | s2_not_incl_s1 ].
left; intro e; intuition.
right; intro s1_eq_s2; apply s2_not_incl_s1; intros e e_in_s2; 
generalize (s1_eq_s2 e); intuition.
right; intro s1_eq_s2; apply s1_not_incl_s2; intros e e_in_s1;
generalize (s1_eq_s2 e); intuition.
Qed.

Lemma eq_set_refl : forall s, eq_set s s.
Proof.
intros s e; split; trivial.
Qed.

Lemma eq_set_sym :
  forall s1 s2, eq_set s1 s2 -> eq_set s2 s1.
Proof.
intros s1 s2 H e; generalize (H e); intuition.
Qed.

Lemma eq_set_trans :
  forall s1 s2 s3, eq_set s1 s2 -> eq_set s2 s3 -> eq_set s1 s3.
Proof.
intros s1 s2 s3 s1_eq_s2 s2_eq_s3 e; 
generalize (s1_eq_s2 e) (s2_eq_s3 e); intuition.
Qed.

Lemma add_compat_eq_set :
  forall e s1 s2, eq_set s1 s2 -> eq_set (add e s1) (add e s2).
Proof.
assert (forall a e s1 s2, eq_set s1 s2 -> mem a (add e s1) -> mem a (add e s2)).
intros a e s1 s2 s1_eq_s2 a_mem_e_s1.
destruct (add_12 _ _ _ a_mem_e_s1) as [a_eq_e | a_mem_s1].
assert (e_eq_a : EDS1.eq_A e a).
symmetry; trivial.
apply (eq_mem_mem (add e s2) e_eq_a).
apply add_1.
apply add_2; rewrite <- (s1_eq_s2 a); trivial.
intros e s1 s2 s1_eq_s2 a; split; apply H; trivial.
apply eq_set_sym; trivial.
Qed.

Lemma add_comm :
  forall e1 e2 s, eq_set (add e1 (add e2 s)) (add e2 (add e1 s)).
Proof.
assert (H : forall e1 e2 s, subset (add e1 (add e2 s)) (add e2 (add e1 s))).
intros e1 e2 s e; intro H.
destruct (add_12 _ _ _ H) as [e_eq_e1 | e_in_e2_s].
unfold mem; apply (mem_eq_mem eq_proof e1).
apply (equiv_sym _ _ eq_proof); assumption.
apply add_2; subst; apply add_1.
destruct (add_12 _ _ _ e_in_e2_s) as [e_eq_e2 | e_in_s].
unfold mem; apply (mem_eq_mem eq_proof e2).
apply (equiv_sym _ _ eq_proof); assumption.
apply add_1.
do 2 apply add_2; trivial.
intros e1 e2 s; split; apply H.
Qed.

Lemma union_empty_1 :
  forall s, eq_set s (union empty s).
Proof.
intros s e; generalize (union_12_aux nil (support s) e); simpl.
intuition.
apply union_2; trivial.
Qed.

Lemma union_empty_2 :
  forall s, eq_set s (union s empty).
Proof.
intros s e; simpl; intuition.
Qed.

Lemma union_comm :
  forall s1 s2, eq_set (union s1 s2) (union s2 s1).
Proof.
intros s1 s2 e; 
generalize (union_12 s1 s2 e) (union_1 s1 s2 e) (union_2 s1 s2 e)
(union_12 s2 s1 e)  (union_1 s2 s1 e) (union_2 s2 s1 e); intuition.
Qed.

Lemma union_assoc :
  forall s1 s2 s3, eq_set (union s1 (union s2 s3)) (union (union s1 s2) s3).
Proof.
intros s1 s2 s3 e; 
generalize (union_12 s1 (union s2 s3) e) (union_1 s1 (union s2 s3) e) 
 (union_2 s1 (union s2 s3) e)
(union_12 s2 s3 e) (union_1 s2 s3 e) (union_2 s2 s3 e)
(union_12 (union s1 s2) s3 e) (union_1 (union s1 s2) s3 e) 
  (union_2 (union s1 s2) s3 e)
(union_12 s1 s2 e)  (union_1 s1 s2 e) (union_2 s1 s2 e); intuition.
Qed.

Lemma subset_filter :
  forall (P1 P2 : A -> bool) s1 s2 P1_compat P2_compat, 
  subset s1 s2 -> (forall e, P1 e = true -> P2 e = true) -> 
  subset (filter P1 s1 P1_compat) (filter P2 s2 P2_compat).
Proof.
intros P1 P2 s1 s2 P1_compat P2_compat Hs HP e H.
apply filter_1.
apply (Hs e).
apply (proj1 (filter_2 _ _ P1_compat _ H)).
apply HP.
apply (proj2 (filter_2 _ _ P1_compat _ H)).
Qed.

Lemma filter_union :
  forall P s1 s2 P_compat, 
  eq_set (filter P (union s1 s2) P_compat)  
             (union (filter P s1 P_compat) (filter P s2 P_compat)).
Proof.
intros P [l1 wr1] [l2 wr2] P_compat e; split; unfold mem; simpl.
intro H; destruct (filter_2_list _  _ _ P_compat H) as [H' Pe];
destruct (union_12_aux _ _ _ H');
[ apply union_1_aux | apply union_2_aux] ; apply filter_1_list; trivial.
intro H; destruct (union_12_aux _ _ _ H) as [ H' | H'];
destruct (filter_2_list _ _ _ P_compat H') as [H'' Pe];
apply filter_1_list; trivial; [ apply union_1_aux | apply union_2_aux] ; trivial.
Qed.

Lemma subset_compat_1 :
  forall s1 s1' s2, eq_set s1 s1' -> subset s1 s2 -> subset s1' s2.
Proof.
intros s1 s1' s2 s1_eq_s1' H e e_in_s1';
apply H; generalize (s1_eq_s1' e); intuition.
Qed.

Lemma subset_compat_2 :
  forall s1 s2 s2', eq_set s2 s2' -> subset s1 s2 -> subset s1 s2'.
Proof.
intros s1 s2 s2' s2_eq_s2' H e e_in_s1;
generalize (s2_eq_s2' e) (H e e_in_s1);
intuition.
Qed.

Lemma subset_compat :
   forall s1 s1' s2 s2', eq_set s1 s1' -> eq_set s2 s2' -> 
                                    subset s1 s2 -> subset s1' s2'.
Proof.
intros s1 s1' s2 s2' s1_eq_s1' s2_eq_s2' H e e_in_s1';
generalize (s1_eq_s1' e) (s2_eq_s2' e) (H e);
intuition.
Qed.

Lemma union_compat_subset_1 :
  forall s1 s2 s, subset s1 s2 -> subset (union s1 s)  (union s2 s).
Proof.
intros [l1 wr1] [l2 wr2] [l wr]; unfold subset; simpl;
intros H e e_in_ll1.
generalize (union_12_aux _ _ _ e_in_ll1); intros [ e_in_l | e_in_l1]; trivial.
apply union_1; apply H; trivial.
apply union_2; trivial.
Qed.

Lemma union_compat_subset_2 :
  forall s1 s2 s, subset s1 s2 -> subset (union s s1)  (union s s2).
Proof.
intros [l1 wr1] [l2 wr2] [l wr]; unfold subset; simpl;
intros H e e_in_ll1.
generalize (union_12_aux _ _ _ e_in_ll1); intros [ e_in_l | e_in_l1]; trivial.
apply union_1; trivial.
apply union_2; apply H; trivial.
Qed.

Lemma union_compat_subset :
  forall s1 s2 s1' s2', subset s1 s2 -> subset s1' s2' -> subset (union s1 s1')  (union s2 s2').
Proof.
intros [l1 wr1] [l2 wr2] [l1' wr1'] [l2' wr2']; unfold subset; simpl;
intros H H' e e_in_ll1.
generalize (union_12_aux _ _ _ e_in_ll1); intros [ e_in_l1 | e_in_l1'].
apply union_1; apply H; trivial.
apply union_2; apply H'; trivial.
Qed.


Lemma union_compat_eq_set :
  forall s1 s1' s2 s2', eq_set s1 s1' -> eq_set s2 s2' -> 
    eq_set (union s1 s2) (union s1' s2').
Proof.
intros s1 s1' s2 s2' s1_eq_s1' s2_eq_s2' e; split; intro H.
generalize (union_12 s1 s2 e H); intros [e_in_s1 | e_in_s2].
apply union_1; generalize (s1_eq_s1' e); intuition.
apply union_2; generalize (s2_eq_s2' e); intuition.
generalize (union_12 s1' s2' e H); intros [e_in_s1' | e_in_s2'].
apply union_1; generalize (s1_eq_s1' e); intuition.
apply union_2; generalize (s2_eq_s2' e); intuition.
Qed.

Lemma  subset_subset_union :
  forall s1 s2 s, subset s1 s -> subset s2 s -> subset (union s1 s2) s.
Proof.
intros s1 s2 s H1 H2 e H.
destruct (union_12 _ _ _ H); [ apply H1 | apply H2]; trivial.
Qed.

(*** Cardinal. *)
Definition cardinal s := List.length s.(support).

Lemma cardinal_subset :
  forall s1 s2, subset s1 s2 -> cardinal s1 <= cardinal s2.
Proof.
intro s1; case s1; clear s1; intros l1 wr1.
intro s2; case s2; clear s2; intros l2 wr2.
revert l1 wr1 l2 wr2; unfold subset, cardinal, mem, without_red; simpl.
fix cardinal_subset 1.
intro l1; case l1; clear l1.
intros _ l2 _ _; apply Nat.le_0_l.
simpl; intros a1 l1.
generalize (mem_bool_ok _ _ eq_bool_ok a1 l1); case (mem_bool eq_bool a1 l1).
intros _ Abs; discriminate.
intros a1_not_in_l1 wr1 l2 wr2 l1_in_l2.
assert (e1_in_l2 : more_list.mem eq_A a1 l2).
apply l1_in_l2; left; reflexivity.
case (mem_split_set _ _ eq_bool_ok _ _ e1_in_l2).
intros a1' M; case M; clear M.
intros l2' M; case M; clear M.
intros l2'' M; case M; clear M.
intros a1_eq_a1' M; case M; clear M.
intros H' _; subst l2.
rewrite length_add; simpl; apply le_n_S; apply cardinal_subset.
assumption.
apply (without_red_remove a1' l2' l2''); assumption.
intros e e_in_l1; apply diff_mem_remove with a1'.
intro e_eq_a1'; apply a1_not_in_l1.
apply (mem_eq_mem eq_proof a1').
apply (equiv_sym _ _ eq_proof); assumption.
apply (mem_eq_mem eq_proof e); assumption.
apply l1_in_l2; right; assumption.
Defined.

Lemma cardinal_union_1 :
  forall s1 s2, cardinal s1 <= cardinal (union s1 s2).
Proof.
intros s1 s2; apply cardinal_subset; apply subset_union_1.
Qed.

Lemma cardinal_union_2 :
  forall s1 s2, cardinal s2 <= cardinal (union s1 s2).
Proof.
intros s1 s2; apply cardinal_subset; apply subset_union_2.
Qed.

Lemma cardinal_union_inter_12 :
  forall s1 s2, cardinal (union s1 s2) + cardinal (inter s1 s2) = cardinal s1 + cardinal s2.
Proof.
intro s1; case s1; clear s1; intros l1 wr1.
intro s2; case s2; clear s2; intros l2 wr2.
revert l1 wr1 l2 wr2; unfold without_red, cardinal; simpl.
fix cardinal_union_inter_12 3.
intros l1 wr1 l2; case l2; clear l2; simpl.
intros _; reflexivity.
intros a2 l2; generalize (mem_bool_ok _ _ eq_bool_ok a2 l2); case_eq (mem_bool eq_bool a2 l2).
intros _ _ Abs; discriminate.
intros a2_not_in_l2_bool a2_not_in_l2 wr2; generalize (mem_bool_ok _ _ eq_bool_ok a2 l1); case (mem_bool eq_bool a2 l1).
intro a2_in_l1.
rewrite length_remove_not_common; simpl.
do 2 rewrite <- plus_n_Sm; rewrite (cardinal_union_inter_12 l1 wr1 l2 wr2); reflexivity.
intro a2_not_in_l1.
rewrite <- plus_n_Sm.
rewrite <- (cardinal_union_inter_12 l1 wr1 l2 wr2).
assert (L : forall l1' l1'', length (add_without_red (l1' ++ a2 :: l1'') l2) = S (length (add_without_red (l1' ++ l1'') l2))).
clear l1 wr1 a2_not_in_l1 a2_not_in_l2 wr2; revert l2 a2 a2_not_in_l2_bool.
fix L 1.
intro l2; case l2; clear l2; simpl.
intros a2 _ l1' l1''; do 2 rewrite length_app; simpl; rewrite plus_n_Sm; reflexivity.
intros a2 l2 a; assert (eq_bool_sym : eq_bool a2 a = eq_bool a a2).
generalize (eq_bool_ok a2 a) (eq_bool_ok a a2); case (eq_bool a2 a); case (eq_bool a a2).
intros _ _; reflexivity.
intros a2_eq_a a_diff_a2; apply False_rect; apply a_diff_a2; symmetry; assumption.
intros a2_diff_a a_eq_a2; apply False_rect; apply a2_diff_a; symmetry; assumption.
intros _ _; reflexivity.
intros a_not_in_l2_bool l1' l1''; revert a_not_in_l2_bool;
rewrite (mem_bool_app eq_bool a2 l1' (a :: l1'')).
simpl; rewrite eq_bool_sym; case (eq_bool a a2); simpl.
intro; discriminate.
intro a_not_in_l2_bool; rewrite <- (mem_bool_app eq_bool a2 l1' l1'');
case (mem_bool eq_bool a2 (l1' ++ l1'')).
apply (L l2 a a_not_in_l2_bool l1' l1'').
apply (L l2 a a_not_in_l2_bool (a2 :: l1') l1'').
assert (L' := L nil l1); simpl in L'; rewrite L'; simpl; reflexivity.
Qed.

Lemma cardinal_union:
  forall s1 s2, cardinal (union s1 s2) = cardinal s1 + cardinal s2 - cardinal (inter s1 s2).
Proof.
intros s1 s2; assert (H := cardinal_union_inter_12 s1 s2).
apply sym_eq, Nat.add_sub_eq_r; trivial.
Qed.

Lemma cardinal_eq_set : forall s1 s2, eq_set s1 s2 -> cardinal s1 = cardinal s2.
Proof.
intros s1 s2 s1_eq_s2; apply Nat.le_antisymm; apply cardinal_subset;
intros e e_in_si; generalize (s1_eq_s2 e); intuition.
Qed.

Lemma subset_cardinal_not_eq_not_eq_set  :
 forall s1 s2 e, subset s1 s2 -> ~mem e s1 -> mem e s2  -> 
  cardinal s1 < cardinal s2.
Proof.
intro s1; case s1; clear s1; intros l1 wr1.
intro s2; case s2; clear s2; intros l2 wr2.
revert l1 wr1 l2 wr2; unfold without_red, cardinal, subset, mem; simpl.
fix subset_cardinal_not_eq_not_eq_set 1.
intros l1 wr1 l2 wr2 a l1_in_l2 a_not_in_l1 a_in_l2.
case (mem_split_set _ _ eq_bool_ok _ _ a_in_l2); 
intros a' M; case M; clear M.
intros l2' M; case M; clear M.
intros l2'' M; case M; clear M.
intros a_eq_a' M; case M; clear M.
intros M _; subst l2.
rewrite length_app; simpl (length (a' :: l2'')); rewrite <- plus_n_Sm; rewrite <- length_app.
assert (wr2' : without_red (l2' ++ l2'')).
apply without_red_remove with a'; assumption.
apply le_n_S; apply (@cardinal_subset (mk_set wr1) (mk_set wr2')).
intros e; unfold mem; simpl; intro e_in_l1.
assert (e_in_l2 := l1_in_l2 e e_in_l1).
rewrite <- mem_or_app in e_in_l2; case e_in_l2; clear e_in_l2.
intro e_in_l2'; rewrite <- mem_or_app; left; assumption.
simpl; intro e_in_l2; case e_in_l2; clear e_in_l2.
intro e_eq_a'; absurd (more_list.mem eq_A a l1).
assumption.
apply (mem_eq_mem eq_proof a').
apply (equiv_sym _ _ eq_proof); assumption.
apply (mem_eq_mem eq_proof e); assumption.
intro e_in_l2''; rewrite <- mem_or_app; right; assumption.
Qed.

Lemma eq_set_list_permut_support :
  forall s1 s2,  eq_set s1 s2 -> permut s1.(support) s2.(support).
Proof.
intros [l1 wr1] [l2 wr2]; unfold eq_set, mem; simpl;
revert l2 wr2; induction l1 as [ | e1 l1].
intros [ | e2 l2] _ H.
apply Pnil.
apply False_rect.
generalize (H e2); simpl; intros [_ Abs]; apply Abs; left; reflexivity.
intros l2 wr2 H.
assert (e1_in_l2 : more_list.mem eq_A e1 l2).
rewrite <- H; left; reflexivity; trivial.
destruct (mem_split_set _ _ eq_bool_ok _ _ e1_in_l2) as [e1' [l2' [l2'' [e1_eq_e1' [H' _]]]]].
simpl in e1_eq_e1'; simpl in H'; subst l2.
rewrite <- permut_cons_inside; trivial.
apply IHl1; trivial.
apply (without_red_remove e1 nil); trivial.
apply (without_red_remove e1'); trivial.
intros e; split; intro H'.
apply diff_mem_remove with e1'.
intro e_eq_e1'; apply (without_red_not_in e1 nil l1 wr1).
simpl; rewrite e1_eq_e1'; rewrite <- e_eq_e1'; trivial.
rewrite <- (H e); right; trivial.
apply (@diff_mem_remove _ eq_A nil l1 e1).
intro e_eq_e1; apply (without_red_not_in e1' l2' l2'' wr2).
rewrite <- e1_eq_e1'; rewrite <- e_eq_e1; trivial.
rewrite (H e); apply mem_insert; trivial.
Qed.

Lemma not_mem_compat : 
 forall s2 e e', eq_A e e' ->
        (fun e0 : EDS1.A => negb (mem_bool eq_bool e0 (support s2))) e =
        (fun e0 : EDS1.A => negb (mem_bool eq_bool e0 (support s2))) e'.
Proof.
intros s2 e e' e_eq_e'; 
generalize (mem_bool_ok _ _ eq_bool_ok e (support s2)) (mem_bool_ok _ _ eq_bool_ok e' (support s2)). 
case (mem_bool eq_bool e (support s2)); case (mem_bool eq_bool e' (support s2)).
intros _ _; reflexivity.
intros e_in_s2 e'_not_in_s2; absurd (more_list.mem eq_A e' (support s2)).
assumption.
apply (mem_eq_mem eq_proof e); assumption.
intros e_not_in_s2 e'_in_s2; absurd (more_list.mem eq_A e (support s2)).
assumption.
apply (mem_eq_mem eq_proof e').
apply (equiv_sym _ _ eq_proof); assumption.
assumption.
intros _ _; reflexivity.
Qed.

Definition set_diff s1 s2 := filter (fun e => negb (mem_bool eq_bool e s2.(support))) s1 (not_mem_compat s2).

Lemma subset_set_diff : 
   forall s1 s2 s2', subset s2 s2' -> cardinal (set_diff s1 s2') <= cardinal (set_diff s1 s2).
Proof.
unfold set_diff, filter, cardinal; simpl.
intros [s1 prf]; simpl; induction s1 as [ | a1 s1]; intros s2 s2' s2_in_s2'; simpl.
apply le_n.
assert (prf1 := without_red_remove a1 nil s1 prf); simpl in prf1.
assert (H := IHs1 prf1 _ _ s2_in_s2').
set (l := filter_aux (fun e : EDS1.A => negb (mem_bool EDS1.eq_bool e (support s2))) s1) in *.
set (l' := filter_aux (fun e : EDS1.A => negb (mem_bool EDS1.eq_bool e (support s2'))) s1) in *.
generalize (s2_in_s2' a1); unfold mem.
generalize (mem_bool_ok _ _ eq_bool_ok a1 (support s2)).
generalize (mem_bool_ok _ _ eq_bool_ok a1 (support s2')).
case (mem_bool EDS1.eq_bool a1 (support s2')).
case (mem_bool EDS1.eq_bool a1 (support s2)).
intros _ _ _; assumption.
intros _ _ _; simpl; apply le_S; assumption.
case (mem_bool EDS1.eq_bool a1 (support s2)); simpl.
intros a1_not_in_s2' a1_in_s2 Sub; apply False_rect.
apply a1_not_in_s2'; apply Sub; apply a1_in_s2.
intros _ _ _; apply le_n_S; assumption.
Qed.

Lemma strict_subset_set_diff : 
   forall s1 s2 s2', subset s2 s2' -> 
  (exists e, mem e s1 /\ mem e s2' /\ ~mem e s2) ->
  cardinal (set_diff s1 s2') < cardinal (set_diff s1 s2). 
Proof.
unfold set_diff, filter, cardinal; simpl;
intros [s1 prf]; induction s1 as [ | a1 s1]; 
intros s2 s2' s2_in_s2' [e [e_mem_s1 [e_mem_s2' e_not_mem_s2]]]; simpl.
contradiction.
assert (prf1 := without_red_remove a1 nil s1 prf); simpl in prf1.
generalize (eq_bool_ok e a1); case_eq (eq_bool e a1).
(* 1/2 a1 is equal to e *)
intros e_eq_a1 e_eq_a1'.
assert (a1_mem_s2' : mem_bool EDS1.eq_bool a1 (support s2') = true).
generalize (mem_bool_ok _ _ eq_bool_ok a1 (support s2')).
case (mem_bool EDS1.eq_bool a1 (support s2')).
intros _; apply eq_refl.
intro a1_not_mem_s2'; apply False_rect; apply a1_not_mem_s2'.
apply (mem_eq_mem EDS1.eq_proof e _ (support s2') e_eq_a1' e_mem_s2').
rewrite a1_mem_s2'; simpl.
assert (a1_not_mem_s2 : negb (mem_bool EDS1.eq_bool a1 (support s2)) = true).
rewrite <- (not_mem_compat s2 e_eq_a1').
generalize (mem_bool_ok _ _ eq_bool_ok e (support s2)).
case (mem_bool EDS1.eq_bool e (support s2)).
intro e_mem_s2; apply False_rect; apply e_not_mem_s2; assumption.
intros _; apply eq_refl.
rewrite a1_not_mem_s2.
simpl; apply le_n_S.
apply (subset_set_diff (mk_set prf1) s2_in_s2').
(* 1/1 a1 is different from e *)
intros e_diff_a1 e_diff_a1'.
assert (He : exists e : EDS1.A, mem e (mk_set prf1) /\ mem e s2' /\ ~ mem e s2).
exists e; repeat split; [idtac | assumption | assumption].
revert e_mem_s1; unfold mem; simpl.
intros [e_eq_a1 | e_mem_s1]; [apply False_rect; apply e_diff_a1' | idtac]; assumption.
assert (H := IHs1 prf1 _ _ s2_in_s2' He).
simpl in H.
set (l := filter_aux (fun e : EDS1.A => negb (mem_bool EDS1.eq_bool e (support s2))) s1) in *.
set (l' := filter_aux (fun e : EDS1.A => negb (mem_bool EDS1.eq_bool e (support s2'))) s1) in *.
generalize (s2_in_s2' a1); unfold mem.
generalize (mem_bool_ok _ _ eq_bool_ok a1 (support s2')); case (mem_bool EDS1.eq_bool a1 (support s2')).
generalize (mem_bool_ok _ _ eq_bool_ok a1 (support s2)); case (mem_bool EDS1.eq_bool a1 (support s2)).
intros _ _ _; assumption.
intros _ _ _; simpl; apply le_S; assumption.
generalize (mem_bool_ok _ _ eq_bool_ok a1 (support s2)); case (mem_bool EDS1.eq_bool a1 (support s2)).
intros a1_in_s2 a1_not_in_s2' Sub; apply False_rect.
apply a1_not_in_s2'; apply Sub; apply a1_in_s2.
intros _ _ _; simpl; apply le_n_S; assumption.
Qed.

End Make.
