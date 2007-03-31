(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17
- Solange Coupet-Grimal and William Delobel, 2006-01-09
- Frederic Blanqui, 2005-02-03
- Sebastien Hinderer, 2004-05-25

extension of the Coq library on lists
*)

(* $Id: ListUtil.v,v 1.19 2007-03-31 23:15:10 koper Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export List.

Implicit Arguments in_app_or [A l m a].
Implicit Arguments in_map [A B l x].

(***********************************************************************)
(** cons *)

Section cons.

Variable A : Set.

Lemma cons_eq : forall x x' : A, forall l l',
  x = x' -> l = l' -> x :: l = x' :: l'.

Proof.
intros. rewrite H. rewrite H0. refl.
Qed.

Lemma head_eq : forall x x' : A, forall l, x = x' -> x :: l = x' :: l.

Proof.
intros. rewrite H. refl.
Qed.

Lemma tail_eq : forall x : A, forall l l', l = l' -> x :: l = x :: l'.

Proof.
intros. rewrite H. refl.
Qed.

End cons.

(***********************************************************************)
(** append *)

Section app.

Variable A : Set.

Lemma app_nil : forall l1 l2 : list A, l1 = nil -> l2 = nil -> l1 ++ l2 = nil.

Proof.
intros. subst l1. subst l2. reflexivity.
Qed.

Lemma app_eq : forall l1 l2 l1' l2' : list A,
  l1 = l1' -> l2 = l2' -> l1 ++ l2 = l1' ++ l2'.

Proof.
intros. rewrite H. rewrite H0. refl.
Qed.

Lemma appl_eq : forall l1 l2 l1' : list A, l1 = l1' -> l1 ++ l2 = l1' ++ l2.

Proof.
intros. rewrite H. refl.
Qed.

Lemma appr_eq : forall l1 l2 l2' : list A, l2 = l2' -> l1 ++ l2 = l1 ++ l2'.

Proof.
intros. rewrite H. refl.
Qed.

End app.

(***********************************************************************)
(** tail *)

Require Import Omega.

Section tail.

Variable A : Set.

Lemma length_0 : forall l : list A, length l = 0 -> l = nil.

Proof.
intros. destruct l. refl. discriminate.
Qed.

Lemma length_tail : forall l : list A, length (tail l) <= length l.

Proof.
induction l; simpl; intros; omega.
Qed.

Lemma length_app : forall l m : list A, length (l ++ m) = length l + length m.

Proof.
induction l; simpl; intros. refl. rewrite IHl. refl.
Qed.

End tail.

(***********************************************************************)
(** filter *)

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

Lemma in_app_com : forall (x : A) l1 l2 l3,
  In x ((l1 ++ l3) ++ l2) -> In x ((l1 ++ l2) ++ l3).

Proof.
intros. deduce (in_app_or H). destruct H0. deduce (in_app_or H0). destruct H1.
rewrite app_ass. apply in_appl. exact H1. apply in_appr. exact H1.
rewrite app_ass. apply in_appr. apply in_appl. exact H0.
Qed.

Lemma in_elim : forall (x : A) l,
  In x l -> exists l1, exists l2, l = l1 ++ x :: l2.

Proof.
induction l; simpl; intros. contradiction. destruct H. subst x.
exists (@nil A). exists l. refl. deduce (IHl H). do 2 destruct H0. rewrite H0.
exists (a :: x0). exists x1. refl.
Qed.

Variable eqA_dec : forall x y : A, {x=y}+{~x=y}.

Lemma in_elim_dec : forall (x : A) l,
  In x l -> exists m, exists p, l = m ++ x :: p /\ ~In x m.

Proof.
induction l; simpl; intros. contradiction. destruct H. subst x.
exists (@nil A). exists l. intuition. deduce (IHl H). do 3 destruct H0. subst l.
case (eqA_dec a x); intro.
subst x. exists (@nil A). exists (x0 ++ a :: x1). intuition.
exists (a :: x0). exists x1. intuition. simpl in H2. destruct H2; auto.
Qed.

End In.

Implicit Arguments in_elim [A x l].
Implicit Arguments in_elim_dec [A x l].

Ltac intac := repeat (apply in_eq || apply in_cons).

(***********************************************************************)
(** inclusion *)

Section incl.

Variable A : Set.

Lemma incl_nil : forall l : list A, incl nil l.

Proof.
induction l. apply incl_refl. apply incl_tl. assumption.
Qed.

Lemma incl_cons_l : forall (a : A) l m, incl (a :: l) m -> In a m /\ incl l m.

Proof.
intros a l m. unfold incl. simpl. intuition.
Qed.

Lemma incl_cons_l_in : forall (x : A) l m, incl (x :: l) m -> In x m.

Proof.
unfold incl. simpl. intros. apply H. left. refl.
Qed.

Lemma incl_cons_l_incl : forall (x : A) l m, incl (x :: l) m -> incl l m.

Proof.
unfold incl. simpl. intros. apply H. tauto.
Qed.

Lemma incl_app_elim : forall l1 l2 l3 : list A,
  incl (l1 ++ l2) l3 -> incl l1 l3 /\ incl l2 l3.

Proof.
intuition.
apply incl_tran with (l1 ++ l2). apply incl_appl. apply incl_refl. exact H.
apply incl_tran with (l1 ++ l2). apply incl_appr. apply incl_refl. exact H.
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

Lemma app_incl : forall l1 l1' l2 l2' : list A,
  incl l1 l1' -> incl l2 l2' -> incl (l1 ++ l2) (l1' ++ l2').

Proof.
intros. unfold incl. intros. deduce (in_app_or H1). destruct H2.
deduce (H _ H2). apply in_appl. exact H3.
deduce (H0 _ H2). apply in_appr. exact H3.
Qed.

Lemma appl_incl : forall l l2 l2' : list A,
  incl l2 l2' -> incl (l ++ l2) (l ++ l2').

Proof.
intros. apply app_incl. apply incl_refl. exact H.
Qed.

Lemma appr_incl : forall l l1 l1' : list A,
  incl l1 l1' -> incl (l1 ++ l) (l1' ++ l).

Proof.
intros. apply app_incl. exact H. apply incl_refl.
Qed.

Lemma app_com_incl : forall l1 l2 l3 l4 : list A,
  incl ((l1 ++ l3) ++ l2) l4 -> incl ((l1 ++ l2) ++ l3) l4.

Proof.
unfold incl. intros. apply H. apply in_app_com. exact H0.
Qed.

Lemma incl_cons_r : forall x : A, forall m l,
  incl l (x :: m) -> In x l \/ incl l m.

Proof.
induction l; simpl; intros. right. apply incl_nil.
deduce (incl_cons_l H). destruct H0. simpl in H0. destruct H0. auto.
deduce (IHl H1). destruct H2. auto.
right. apply List.incl_cons; assumption.
Qed.

End incl.

Implicit Arguments incl_app_elim [A l1 l2 l3].

Ltac incltac := repeat (apply incl_cons_l; [intac | idtac]); apply incl_nil.

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

Lemma Inb_elim : forall x l, ~In x l -> Inb x l = false.

Proof.
induction l; simpl; intros. refl. case (eq_dec x a). intro. subst x. intuition.
intuition.
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

Ltac inbtac :=
  match goal with
    | _ : In ?x ?l |- _ =>
      let H0 := fresh "H" in
	(assert (H0 : Inb x l = true); apply Inb_intro; assumption; rewrite H0)
  end.

(***********************************************************************)
(** remove *)

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
apply IHl. auto. apply incl_cons_l_incl with (x := a). exact H0. exact H2.
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

Lemma in_map_elim : forall x l, In x (map f l) -> exists y, In y l /\ x = f y.

Proof.
induction l; simpl; intros. contradiction. destruct H.
exists a. auto. deduce (IHl H). do 2 destruct H0. exists x0. auto.
Qed.

End map.

Implicit Arguments in_map_elim [A B f x l].

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
(** element at a position *)

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
(** reverse *)

Section reverse.

Variable A : Set.

Lemma in_rev : forall (x : A) l, In x l -> In x (rev l).

Proof.
induction l; simpl; intros. assumption. apply in_or_app. simpl. tauto.
Qed.

Lemma incl_rev : forall l : list A, incl l (rev l).

Proof.
unfold incl. intros. apply in_rev. assumption. 
Qed. 

Lemma rev_incl : forall l : list A, incl (rev l) l. 

Proof.
intros. pose (incl_rev (rev l)). rewrite (rev_involutive l) in i. assumption.
Qed.

Lemma incl_rev_intro : forall l l' : list A, incl (rev l) (rev l') -> incl l l'.

Proof.
intros. apply incl_tran with (rev l). apply incl_rev.
apply incl_tran with (rev l'). assumption. apply rev_incl.
Qed.

End reverse.

(***********************************************************************)
(** last element *)

Section last.

Variable A : Set.

Lemma last_intro : forall l : list A, length l > 0 ->
  exists m, exists a, l = m ++ a :: nil /\ length m = length l - 1.

Proof.
induction l; simpl; intros. apply False_ind. omega.
destruct l. exists (@nil A). exists a. intuition.
assert (length (a0::l) > 0). simpl. omega.
deduce (IHl H0). do 3 destruct H1.
exists (a::x). exists x0. split. rewrite H1. refl.
simpl. simpl in H2. omega.
Qed.

End last.

Implicit Arguments last_intro [A l].

(***********************************************************************)
(** partition *)

Section partition.

  Variables (A : Set) (P : A -> bool) (a : A) (l : list A).

  Lemma partition_complete : let p := partition P l in
    In a l -> In a (fst p)  \/ In a (snd p).

  Proof.
  Admitted.

  Lemma partition_left : In a (fst (partition P l)) -> P a = true.

  Proof.
  Admitted.

  Lemma partition_right : In a (snd (partition P l)) -> P a = false.

  Proof.
  Admitted.

End partition.

Section partition_by_prop.

  Require Import RelMidex.

  Variables (A : Set) (P : A -> Prop) (P_dec : prop_dec P).

  Definition partition_by_prop a :=
    match P_dec a with
    | left _ => true
    | right _ => false
    end.

  Lemma partition_by_prop_true : forall a, partition_by_prop a = true -> P a.

  Proof.
    intros. unfold partition_by_prop in H. 
    destruct (P_dec a). assumption. discriminate.
  Qed.

End partition_by_prop.

Section partition_by_rel.

  Variables (A : Set) (R : relation A) (R_dec : rel_dec R).

  Definition partition_by_rel p :=
    match R_dec (fst p) (snd p) with
    | left _ => true
    | right _ => false
    end.

  Lemma partition_by_rel_true : forall a b, partition_by_rel (a, b) = true -> R a b.

  Proof.
    intros. unfold partition_by_rel in H. simpl in H.
    destruct (R_dec a b). assumption. discriminate.
  Qed.

End partition_by_rel.
