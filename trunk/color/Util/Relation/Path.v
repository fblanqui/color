(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17
- Frederic Blanqui, 2007-01-22

paths
*)

(* $Id: Path.v,v 1.19 2008-10-06 03:22:37 blanqui Exp $ *)

Set Implicit Arguments.

Require Export RelSub.
Require Export List.

Section S.

Variable A : Type.

(***********************************************************************)
(** paths *)

Section Path.

Variable R : relation A.

Fixpoint is_path (x y : A) (l : list A) {struct l} : Prop :=
  match l with
    | nil => R x y
    | z::l' => R x z /\ is_path z y l'
  end.

Lemma path_clos_trans : forall y l x, 
  is_path x y l -> clos_trans R x y.

Proof.
induction l; simpl; intros. constructor. assumption.
constructor 2 with a. constructor. tauto. apply IHl. tauto.
Qed.

Lemma path_app : forall y z l' l x,
  is_path x y l -> is_path y z l' -> is_path x z (l++y::l'). 

Proof.
induction l; simpl; intros. tauto. split. tauto. apply IHl; tauto.
Qed. 

Lemma clos_trans_path : forall x y, 
  clos_trans R x y -> exists l, is_path x y l.

Proof.
intros. induction H. exists (nil : list A). simpl. assumption.
destruct IHclos_trans1. destruct IHclos_trans2. exists (x0++y::x1). 
apply path_app; assumption.
Qed.

Lemma path_app_elim_right : forall y z l l' x, 
  is_path x z (l++y::l') -> is_path y z l'.

Proof.
induction l; simpl; intros. tauto. apply IHl with a. tauto. 
Qed.  

Lemma path_repeat_free_length : 
  eq_midex A -> forall y l x,  is_path x y l -> 
    exists l', ~In x l' /\ ~In y l' /\ repeat_free l'
      /\ length l'<= length l /\ incl l' l /\ is_path x y l'.

Proof.
induction l; intros; simpl in H0. exists (nil : list A). simpl.
pose (incl_nil (nil : list A)). pose (le_O_n 0). tauto. 
destruct (IHl a). tauto.
destruct (H y a). exists (nil : list A). simpl.
pose (le_O_n (S (length l))). pose (incl_nil (a::l)). rewrite H2. tauto. 
destruct (In_midex H x x0). destruct (In_elim_right H x x0). assumption. 
destruct H4. exists x2. split. tauto. split. intro. absurd (In y x0). tauto. 
rewrite (proj1 H4). apply in_or_app. simpl. tauto. rewrite (proj1 H4) in H1.
split. 
destruct (repeat_free_app_elim_right x1 (x::x2)). tauto. tauto.   
split. rewrite (length_app x1 (x::x2)) in H1. simpl in H1|-* . omega. split.
apply incl_tran with (x::x2). apply incl_tl. apply incl_refl.
apply incl_tran with (x1++(x::x2)). apply incl_appr. apply incl_refl.
apply incl_tran with l. 
tauto. apply incl_tl. apply incl_refl. apply path_app_elim_right with x1 a.
tauto. 
destruct (H x a). exists x0. rewrite H4. simpl.
assert (length x0 <= S (length l)). omega. 
assert (incl x0 (a :: l)). apply incl_tl. tauto. tauto. exists (a::x0). simpl.
assert (S (length x0) <= S (length l)). omega. 
assert (incl (a :: x0) (a :: l)). apply incl_double_cons. tauto. 
assert (a<>x). intro. rewrite H7 in H4. tauto. 
assert (a<>y). intro. rewrite H8 in H2. tauto. tauto. 
Qed.

Lemma path_restricted_incl : forall y l l' x,
  is_restricted R l -> is_path x y l' -> incl l' l.

Proof.
unfold is_restricted. induction l'; simpl; intros. intro. simpl. tauto.
apply incl_cons. pose (H x a). tauto. apply IHl' with a; tauto.
Qed. 

(***********************************************************************)
(** paths of bounded length *)

Inductive bound_path (n : nat) : relation A :=
| bp_intro : forall x y l,
  length l<= n -> is_path x y l -> bound_path n x y.

Lemma bound_path_clos_trans : forall n,
  (bound_path n)  << (clos_trans R).

Proof.
repeat intro. inversion H. apply path_clos_trans with l. assumption. 
Qed.

Lemma clos_trans_bound_path : eq_midex A -> forall l,
  is_restricted R l -> (clos_trans R) << (bound_path (length l)).

Proof.
do 6 intro. destruct (clos_trans_path H1).
destruct (path_repeat_free_length H y x0 x H2). apply bp_intro with x1. 
apply repeat_free_incl_length. assumption. tauto. 
apply path_restricted_incl with y x;tauto. tauto. 
Qed.

Lemma bound_path_n_Sn : forall n x y,
  bound_path n x y -> bound_path (S n) x y.

Proof.
intros. inversion H. apply bp_intro with l. apply le_trans with n. assumption. 
apply le_n_Sn. assumption.
Qed.

Lemma bound_path_Sn_n_or_Rn : forall n x y,
  bound_path (S n) x y ->
  bound_path n x y \/ exists z : A, R x z /\ bound_path n z y.

Proof.
intros. inversion H. destruct (le_le_S_dec (length l) n). 
constructor. apply bp_intro with l; assumption. constructor 2. 
destruct l. simpl in l0. pose (le_Sn_O n l0). tauto. exists a. simpl in H0, H1.  
split. tauto. apply bp_intro with l. apply le_S_n. assumption. tauto.
Qed.

Lemma R_bound_path_n_Sn : forall x y z n,
  R x y -> bound_path n y z -> bound_path (S n) x z.

Proof.
intros. inversion H0. apply bp_intro with (y::l). simpl. apply le_n_S.
assumption. 
simpl. tauto. 
Qed.

End Path.

(***********************************************************************)
(** paths and sub-relations *)

Lemma path_preserved : forall R R' y l x,
  R << R' -> is_path R x y l -> is_path R' x y l.

Proof.
induction l; repeat intro; simpl in H0 |- * . apply H. assumption. 
split. pose (H x a). tauto. pose (IHl a). tauto.
Qed.

Lemma path_restriction : forall R y l x,
  is_path R x y l -> is_path (restriction R (x::y::l)) x y l.

Proof.
unfold restriction. induction l; simpl; intros. tauto. split. tauto.
simpl in IHl. 
apply path_preserved with (fun x0 y0 : A =>  (a = x0 \/ y = x0 \/ In x0 l) /\
(a = y0 \/ y = y0 \/ In y0 l) /\ R x0 y0). repeat intro. tauto. 
apply IHl. tauto.
Qed.

End S.

(***********************************************************************)
(** properties when the equality is decidable *)

Section S2.

Variable A : Type.
Variable eqdec : eq_dec A.
Variable R : relation A.

(***********************************************************************)
(** path *)

Lemma path_app_elim : forall l x y z m,
  is_path R x y (l ++ z :: m) -> is_path R x z l /\ is_path R z y m.

Proof.
induction l; simpl; intros. exact H. destruct H. ded (IHl _ _ _ _ H0).
intuition.
Qed.

Lemma sub_path : forall l x y x' y' l' m p,
  x :: l ++ y :: nil = m ++ x' :: l' ++ y' :: p ->
  is_path R x y l -> is_path R x' y' l'.

Proof.
induction l; simpl; intros.
(* case l=nil *)
destruct m; simpl in H.
(* case m=nil *)
injection H; intros. subst x'. destruct l'; simpl in H1.
(* case l'=nil *)
injection H1; intros. subst y'. exact H0.
(* case l'=a::l' *)
injection H1; intros. destruct l'; discriminate.
(* case m=a::m *)
injection H; intros. destruct m; simpl in H1.
(* case m=nil *)
injection H1; intros. destruct l'; discriminate.
(* case m=a0::m *)
injection H1; intros. destruct m; discriminate.
(* case l=a::l *)
destruct H0. destruct m; simpl in H.
(* case m=nil *)
injection H; intros. subst x'. destruct l'; simpl in H2; simpl in H.
(* case l'=nil *)
injection H2; intros. subst a. exact H0.
(* case l'=a0::l' *)
simpl. injection H2; intros. subst a0. intuition.
apply (IHl a y a y' l' (@nil A) p). simpl. exact H2. exact H1.
(* case m=a0::m *)
injection H; intros. subst a0. eapply IHl. apply H2. exact H1.
Qed.

Lemma path_suffix : forall (y z : A) l' l'' (x : A),
  is_path R x y l' -> suffix (z::l'') l' -> is_path R z y l''.

Proof.
induction l'; intros. assert (rev (z :: l'')=nil). apply prefix_nil. assumption.
simpl in H1. symmetry in H1. pose (app_cons_not_nil (rev l'') nil z H1). tauto.
destruct (list_eq_dec eqdec (z :: l'')(a :: l')). inversion e. simpl in H.
tauto. simpl in H. 
apply IHl' with a. tauto. apply suffix_smaller with a; assumption.
Qed.

Lemma path_cut : forall (y : A) l' (x : A),
  In x l' -> is_path R x y l' -> is_path R x y (tail(cut eqdec x l')). 

Proof.
intros. apply path_suffix with l' x. assumption.
rewrite <- (cut_head eqdec x l' H). apply suffix_cut.
Qed.

Lemma path_cut_bis : forall l' (x y z : A),
  In z l' -> R x z -> is_path R z y l' -> is_path R x y (cut eqdec z l'). 

Proof.
intros. rewrite (cut_head eqdec z l'). simpl.
assert (is_path R z y (tail (cut eqdec z l'))).
apply path_cut; assumption. destruct l'. pose (in_nil H).
contradiction. tauto. assumption. 
Qed.

Lemma path_shrink : forall (y : A) l' (x : A),
  is_path R x y l' -> is_path R x y (shrink eqdec l').

Proof.
induction l'; simpl; intros. assumption.
assert (is_path R a y (shrink eqdec l')).
apply IHl'; tauto. destruct (In_dec eqdec a (shrink eqdec l')).
apply path_cut_bis; tauto. simpl. tauto.
Qed.

Require Import Arith.

(***********************************************************************)
(** restriction *)

Section sub_Rel2.

Variable l : list A.

Lemma restricted_path_incl : is_restricted R l ->
  forall m x y, is_path R x y m -> incl (x :: m ++ y :: nil) l.

Proof.
induction m; simpl; intros.
ded (H _ _ H0). unfold is_restricted in H. unfold incl. simpl. intuition.
subst a. exact H2. subst a. exact H3.
destruct H0. apply incl_cons. ded (H _ _ H0). unfold is_restricted in H2.
intuition.
apply IHm. exact H1.
Qed.

Require Export ListOccur.

Notation occur := (occur eqdec).

Lemma long_path_occur : is_restricted R l ->
  forall x y m, is_path R x y m -> length m >= length l - 1 ->
    exists z, occur z (x :: m ++ y :: nil) >= 2.

Proof.
intros. apply pigeon_hole with l. apply restricted_path_incl.
apply H. apply H0. simpl. rewrite length_app. simpl. omega.
Qed.

Lemma path_restriction_In_left : forall (x y : A) l', 
is_path (restriction R l) x y l' -> In x l.

Proof.
unfold restriction. intros; destruct l'; simpl in H; tauto.
Qed.

End sub_Rel2.

End S2.

Implicit Arguments path_app_elim [A R l x y z m].
Implicit Arguments restricted_path_incl [A R l m x y].
