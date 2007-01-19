(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17
- Solange Coupet-Grimal and William Delobel, 2006-01-09
- Frederic Blanqui, 2005-02-03
- Sebastien Hinderer, 2004-05-25

extension of the Coq library on lists
*)

(* $Id: ListUtil.v,v 1.4 2007-01-19 17:22:40 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export List.

Implicit Arguments in_app_or [A l m a].

(***********************************************************************)
(** concatenation *)

Section app.

Variable A : Set.

Lemma app_nil : forall l1 l2 : list A, l1 = nil -> l2 = nil -> app l1 l2 = nil.

Proof.
intros. subst l1. subst l2. reflexivity.
Qed.

End app.

(***********************************************************************)
(** tail *)

Require Import Omega.

Section tail.

Variable A : Set.

Lemma length_tail : forall l : list A, length (tail l) <= length l.

Proof.
induction l; simpl; intros; omega.
Qed.

End tail.

(***********************************************************************)
(** filtering *)

Section filter.

Variable (A : Set) (p : A -> bool).

Fixpoint filter (l : list A) : list A :=
  match l with
    | nil => nil
    | cons x l' =>
      match p x with
	| true => cons x (filter l')
	| false => filter l'
      end
  end.

End filter.

(***********************************************************************)
(** list inclusion *)

Section incl.

Variable A : Set.

Lemma incl_nil : forall l : list A, incl nil l.

Proof.
induction l. apply incl_refl. apply incl_tl. assumption.
Qed.

Lemma incl_cons : forall (a : A) l m, incl (a :: l) m -> In a m /\ incl l m.

Proof.
intros a l m. unfold incl. simpl. intuition.
Qed.

Lemma incl_cons_in : forall (x : A) l m, incl (x :: l) m -> In x m.

Proof.
unfold incl. simpl. intros. apply H. left. refl.
Qed.

Lemma incl_cons_left : forall (x : A) l m, incl (x :: l) m -> incl l m.

Proof.
unfold incl. simpl. intros. apply H. tauto.
Qed.

Lemma incl_appr_incl : forall l1 l2 l3 : list A,
  incl (l1 ++ l2) l3 -> incl l1 l3.

Proof.
induction l1; simpl; intros. apply incl_nil.
eapply incl_tran with (m := a :: l1 ++ l2). 2: assumption.
apply (incl_appl l2 (incl_refl (a :: l1))).
Qed.

Lemma incl_appl_incl : forall l1 l2 l3 : list A,
  incl (l1 ++ l2) l3 -> incl l2 l3.

Proof.
induction l1; simpl; intros. assumption.
eapply incl_tran with (m := a :: l1 ++ l2). 2: assumption.
apply (incl_appr (a :: l1) (incl_refl l2)).
Qed.

End incl.

(***********************************************************************)
(** equivalence *)

Section equiv.

Variable A : Set.

Definition lequiv (l1 l2 : list A) : Prop := incl l1 l2 /\ incl l2 l1.

Lemma lequiv_refl : forall l, lequiv l l.

Proof.
intro. split; apply incl_refl.
Qed.

Lemma lequiv_sym : forall l1 l2, lequiv l1 l2 -> lequiv l2 l1.

Proof.
intros. destruct H. split; assumption.
Qed.

Lemma lequiv_trans : forall l1 l2 l3, lequiv l1 l2 -> lequiv l2 l3 -> lequiv l1 l3.

Proof.
intros. destruct H. destruct H0. split. eapply incl_tran. apply H. assumption.
eapply incl_tran. apply H2. assumption.
Qed.

End equiv.

(***********************************************************************)
(** membership *)

Section In.

Variable A : Set.

Lemma in_appl : forall (x : A) l1 l2, In x l1 -> In x (l1 ++ l2).

Proof.
induction l1; simpl; intros. contradiction. destruct H. subst x. auto.
right. apply IHl1. assumption.
Qed.

Lemma in_appr : forall (x : A) l1 l2, In x l2 -> In x (l1 ++ l2).

Proof.
induction l1; simpl; intros. assumption. right. apply IHl1. assumption.
Qed.

Lemma in_elim : forall (x : A) l,
  In x l -> exists l1, exists l2, l = l1 ++ x :: l2.

Proof.
induction l; simpl; intros. contradiction. destruct H. subst x.
exists (@nil A). exists l. refl. deduce (IHl H). do 2 destruct H0. rewrite H0.
exists (a :: x0). exists x1. refl.
Qed.

End In.

Implicit Arguments in_elim [A x l].

(***********************************************************************)
(** boolean membership when the equality on A is decidable *)

Section Inb.

Variable A : Set.
Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Fixpoint Inb (x : A) (l : list A) {struct l} : bool :=
  match l with
    | nil => false
    | cons y l' =>
      match eq_dec x y with
	| left _ => true
	| _ => Inb x l'
      end
  end.

Lemma Inb_true : forall x l, Inb x l = true -> In x l.

Proof.
induction l; simpl. intro. discriminate. case (eq_dec x a); auto.
Qed.

Lemma Inb_false : forall x l, Inb x l = false -> In x l -> False.

Proof.
induction l; simpl. intros. contradiction. case (eq_dec x a).
intros. discriminate. intros. destruct H0; auto.
Qed.

Lemma Inb_intro : forall x l, In x l -> Inb x l = true.

Proof.
induction l; simpl; intros. contradiction. case (eq_dec x a). auto.
destruct H. intro. absurd (x = a); auto. auto.
Qed.

Lemma Inb_incl : forall x l l', incl l l' -> Inb x l = true -> Inb x l' = true.

Proof.
intros. apply Inb_intro. apply H. apply Inb_true. assumption.
Qed.

Require Export BoolUtil.

Lemma Inb_equiv : forall x l l', lequiv l l' -> Inb x l = Inb x l'.

Proof.
intros. destruct H. booltac_simpl (Inb x l).
assert (Inb x l' = true). eapply Inb_incl. apply H. assumption. rewrite H1. refl.
booltac_simpl (Inb x l'). assert (Inb x l = true). eapply Inb_incl. apply H0.
assumption. rewrite H2 in H1. assumption. refl.
Qed.

End Inb.

(***********************************************************************)
(** removing *)

Section remove.

Variable A : Set.
Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Fixpoint remove (y : A) (l : list A) {struct l} : list A :=
  match l with
    | nil => nil
    | cons x l' =>
      match eq_dec x y with
	| left _ => remove y l'
	| right _ => cons x (remove y l')
      end
  end.

Lemma length_remove : forall (x : A) l, length (remove x l) <= length l.

Proof.
induction l; simpl; intros. apply le_O_n. destruct (eq_dec a x).
apply le_trans with (length l). apply IHl. apply le_n_Sn. simpl. apply le_n_S. 
apply IHl.
Qed.

Lemma In_length_remove : forall (x : A) l,
  In x l -> length (remove x l) < length l.

Proof.
induction l; simpl; intros. contradiction. destruct (eq_dec a x).
apply le_lt_n_Sm.
apply length_remove. destruct H. rewrite H in n. tauto. simpl. apply lt_n_S.
apply IHl. assumption.
Qed.

Lemma In_remove : forall (x y : A) l, x<>y -> In y l -> In y (remove x l).

Proof.
induction l; simpl; intros. assumption. 
destruct (eq_dec a x); destruct H0. rewrite e in H0. tauto.
tauto. rewrite H0. simpl. tauto. simpl. tauto.
Qed.

Lemma  incl_remove : forall (x : A) l m,
  ~In x l -> incl l m -> incl l (remove x m).

Proof.
induction l; simpl; intros. apply incl_nil. assert (~a=x /\ ~In x l). tauto.
unfold incl. intros. simpl in H2. destruct H2. subst a0.
apply In_remove. auto. unfold incl in H0. apply H0. simpl. auto.
apply IHl. auto. apply incl_cons_left with (x := a). exact H0. exact H2.
Qed.

End remove.

(***********************************************************************)
(** map *)

Section map.

Variable (A B : Set) (f : A->B).

Lemma map_app : forall l1 l2, map f (l1 ++ l2) = (map f l1) ++ map f l2.

Proof.
induction l1; simpl; intros. refl. rewrite IHl1. refl.
Qed.

End map.

(***********************************************************************)
(** flattening *)

Section flat.

Variable A : Set.

Fixpoint flat (l : list (list A)) : list A :=
  match l with
    | nil => nil
    | cons x l' => x ++ flat l'
  end.

End flat.

(***********************************************************************)
(** tactics *)

Ltac inbtac :=
  match goal with
    | _ : In ?x ?l |- _ =>
      let H0 := fresh "H" in
	(assert (H0 : Inb x l = true); apply Inb_intro; assumption; rewrite H0)
  end.

Ltac intac := repeat (apply in_eq || apply in_cons).

Ltac incltac := repeat (apply incl_cons; [intac | idtac]); apply incl_nil.

(***********************************************************************)
(** element_at *)

Section Element_At_List.
  
  Variable A : Set.
  
  Fixpoint element_at (l : list A) (p : nat) {struct l} : option A := 
    match l with 
      | nil => None
      | h :: t =>
	match p with 
          | 0 => Some h 
          | S p' => element_at t p'
        end
    end.

  Fixpoint replace_at (l : list A) (p : nat) (a : A) {struct l} : list A :=
    match l with
      | nil => nil
      | h :: t =>
	match p with 
          | 0 => a :: t
          | S p' => h :: (replace_at t p' a)
        end
    end.

  Notation "l '[' p ']'" := (element_at l p) (at level 50).
  Notation "l '[' p ':=' a ']'" := (replace_at l p a) (at level 50).

  Lemma element_at_exists : forall l p,
    p < length l <-> ex (fun a => l[p] = Some a).

  Proof.
    intro l; induction l as [ | h t IHl].
    simpl; intro p; split; intro H; [inversion H | inversion H as [x Hx]].
    inversion Hx.
    simpl; intro p; split.
    intro Hp; destruct p as [ | p].
    exists h; trivial.
    assert (Hp' : p < length t).
    generalize Hp; auto with arith.
    elim (IHl p); intros H1 H2.
    elim (H1 Hp'); intros a Ha; exists a; trivial.
    destruct p as [ | p]; intro H.
    auto with arith.
    elim (IHl p); intros H1 H2.
    generalize (H2 H); auto with arith.
  Qed.

  Lemma element_at_replaced : forall l p a, p < length l -> l[p:=a][p] = Some a.

  Proof.
    intro l; induction l as [ | h t IHl]; simpl; intros p a Hlength.
    inversion Hlength.
    destruct p as [ | p]; simpl.
    trivial.
    apply IHl; generalize Hlength; auto with arith.
  Qed.

  Lemma element_at_not_replaced : forall l p q a, p <> q -> l[p] = l[q:=a][p].

  Proof.
    intro l; induction l as [ | h t IHl]; intros p q a p_neq_q; simpl.
    trivial.
    destruct p as [ | p'].
    destruct q as [ | q']; simpl.
    elim p_neq_q; trivial.
    trivial.
    destruct q as [ | q']; simpl.
    trivial.
    apply IHl.
    intro H; apply p_neq_q; subst; trivial.
  Qed.

  Lemma in_element_at : forall l a, In a l -> ex (fun p => l[p] = Some a).

  Proof.
    intro l; induction l as [ | h t IHl]; intros a a_in_l.
    inversion a_in_l.
    elim a_in_l; clear a_in_l; intro a_in_l.
    exists 0; subst; trivial.
    elim (IHl a a_in_l); intros p Hp.
    exists (S p); simpl; trivial.
  Qed.

  Lemma element_at_in : forall l a, ex (fun p => l[p] = Some a) -> In a l.

  Proof.
    intro l; induction l as [ | h t IHl]; intros a Hex; 
      elim Hex; clear Hex; intros p Hp.
    inversion Hp.
    destruct p as [ | p]; inversion Hp.
    left; trivial.
    right; apply IHl; exists p; trivial.
  Qed.

End Element_At_List.

Notation "l '[' p ']'" := (element_at l p) (at level 50) : list_scope.
Notation "l '[' p ':=' a ']'" := (replace_at l p a) (at level 50) : list_scope.

(***********************************************************************)
(** one_less *)

Section one_less.

  Variable A : Set.

  Require Export Relations.

  Variable r : relation A.
  
  Inductive one_less : relation (list A) := 
    | one_less_cons : forall (l l' : list A) (p : nat) (a a' : A), 
      r a a' -> l[p] = Some a -> l' = l[p:=a'] -> one_less l l'.
  
  Lemma one_less_length : forall l l', one_less l l' -> length l = length l'.

  Proof.
    intro l; induction l as [ | h t IHl]; intros l' Hr.
    inversion Hr; subst.
    simpl; trivial.
    inversion Hr; subst; simpl.
    destruct p as [ | p].
    simpl; trivial.
    simpl; rewrite IHl with (t[p:=a']); trivial.
    apply (@one_less_cons t (t[p:=a']) p a a'); trivial.
  Qed.

End one_less.

Implicit Arguments one_less [A].
Implicit Arguments one_less_cons [A].

(***********************************************************************)
(** accessibility *)

Definition accs (A : Set) r l := forall a : A, In a l -> Acc r a.

(***********************************************************************)
(** prefix *)

Section prefix.

Variable A : Set.

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
(** reverse *)

Section reverse.

Variable A : Set.

Lemma rev_In : forall (x : A) l, In x l -> In x (rev l).

Proof.
induction l; simpl; intros. assumption. apply in_or_app. simpl. tauto.
Qed.

Lemma rev_refl_incl_right : forall l : list A, incl l (rev l).

Proof.
unfold incl. intros. apply rev_In. assumption. 
Qed. 

Lemma rev_refl_incl_left : forall l : list A, incl (rev l) l. 

Proof.
intros. pose (rev_refl_incl_right (rev l)).
rewrite (rev_involutive l) in i. assumption. 
Qed.

Lemma rev_incl_left : forall l l' : list A, incl (rev l) (rev l') -> incl l l'.

Proof.
intros. apply incl_tran with (rev l). apply rev_refl_incl_right. 
apply incl_tran with (rev l'). assumption. apply rev_refl_incl_left. 
Qed.

End reverse.

(***********************************************************************)
(** suffix *)

Section suffix.

Variable A : Set.

Definition suffix (l l' : list A) : Prop := prefix (rev l)(rev l').

Lemma suffix_incl : forall l l' : list A, suffix l l' -> incl l l'.

Proof.
intros. apply rev_incl_left. unfold suffix in H. apply prefix_incl. assumption. 
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
(** mono *)

Section mono.

Variable A : Set.

Fixpoint mono (l : list A) : Prop :=
  match l with
    | nil => True
    | x::l => ~In x l /\ mono l
  end.

Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Lemma mono_incl_length : forall l l',
  mono l -> incl l l' -> length l <= length l'.

Proof.
induction l; simpl; intros. apply le_O_n.
apply le_trans with (S (length (remove eq_dec a l'))).
apply le_n_S. apply IHl. tauto. apply incl_remove. tauto.
apply incl_cons_left with a. assumption.
apply lt_le_S. apply In_length_remove. apply  incl_cons_in with l. assumption.
Qed.

End mono.

(***********************************************************************)
(** cut *)

Section cut.

Variable A : Set.
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

Lemma mono_cut : forall (x : A) l, mono l -> mono (cut x l).

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

Variable A : Set.
Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Fixpoint shrink (l :list A) : list A :=
  match l with
    | nil => nil
    | x::l => if In_dec eq_dec x (shrink l) then cut eq_dec x (shrink l)
      else x::(shrink l)
  end.

Lemma mono_shrink : forall l : list A, mono (shrink l).

Proof.
induction l; simpl; intros. trivial. destruct (In_dec eq_dec a (shrink l)).
apply mono_cut. assumption. simpl. tauto.
Qed.

Lemma incl_shrink : forall l : list A, incl (shrink l) l.

Proof.
induction l; simpl; intros. apply incl_nil.
destruct (In_dec eq_dec a (shrink l)).
apply incl_tran with (shrink l). apply incl_cut. apply incl_tl. assumption.
unfold incl. intros. simpl in H. simpl. case (eq_dec a a0); intro.
subst a0. auto. right. apply IHl. destruct H. contradiction. exact H.
Qed.

Lemma length_shrink : forall l l' : list A,
  incl l l' -> length (shrink l) <= length l'.

Proof.
intros. apply mono_incl_length. exact eq_dec. apply mono_shrink.
apply incl_tran with l. apply incl_shrink. assumption.
Qed.

End shrink.