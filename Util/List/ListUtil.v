(************************************************************************
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Sebastien Hinderer, 2004-05-25
- Frederic Blanqui, 2005-02-03
- Solange Coupet-Grimal and William Delobel, 2006-01-09

extension of the Coq library on lists
************************************************************************)

(* $Id: ListUtil.v,v 1.1.1.1 2006-09-08 09:07:00 blanqui Exp $ *)

Set Implicit Arguments.

Require Export LogicUtil.
Require Export List.

Implicit Arguments in_app_or [A l m a].

Section S.

Variable A : Set.

Notation list := (list A).
Notation Nil := (@nil A).

(***********************************************************************)
(* filtering *)

Section filter.

Variable p : A -> bool.

Fixpoint filter (l : list) : list :=
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
(* list inclusion *)

Lemma incl_nil : forall l, incl Nil l.

Proof.
induction l. apply incl_refl. apply incl_tl. assumption.
Qed.

Lemma incl_cons : forall (a : A) l m, incl (a :: l) m -> In a m /\ incl l m.

Proof.
intros a l m. unfold incl. simpl. intuition.
Qed.

Lemma incl_cons_in : forall (x : A) l1 l2, incl (x :: l1) l2 -> In x l2.

Proof.
unfold incl. simpl. intros. apply H. left. reflexivity.
Qed.

Lemma incl_appr_incl : forall l1 l2 l3 : list, incl (l1 ++ l2) l3 -> incl l1 l3.

Proof.
induction l1; simpl; intros. apply incl_nil.
eapply incl_tran with (m := a :: l1 ++ l2). 2: assumption.
apply (incl_appl l2 (incl_refl (a :: l1))).
Qed.

Lemma incl_appl_incl : forall l1 l2 l3 : list, incl (l1 ++ l2) l3 -> incl l2 l3.

Proof.
induction l1; simpl; intros. assumption.
eapply incl_tran with (m := a :: l1 ++ l2). 2: assumption.
apply (incl_appr (a :: l1) (incl_refl l2)).
Qed.

(***********************************************************************)
(* equivalence *)

Definition lequiv (l1 l2 : list) : Prop := incl l1 l2 /\ incl l2 l1.

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

(***********************************************************************)
(* membership *)

Lemma in_appl : forall (x : A) l1 l2, In x l1 -> In x (l1 ++ l2).

Proof.
induction l1; simpl; intros. contradiction. destruct H. subst x. auto.
right. apply IHl1. assumption.
Qed.

Lemma in_appr : forall (x : A) l1 l2, In x l2 -> In x (l1 ++ l2).

Proof.
induction l1; simpl; intros. assumption. right. apply IHl1. assumption.
Qed.

Lemma app_nil : forall l1 l2, l1 = Nil -> l2 = Nil -> app l1 l2 = Nil.

Proof.
intros. subst l1. subst l2. reflexivity.
Qed.

Lemma in_elim : forall (x : A) l, In x l -> exists l1, exists l2, l = l1 ++ x :: l2.

Proof.
induction l; simpl; intros. contradiction. destruct H. subst x.
exists Nil. exists l. refl. deduce (IHl H). do 2 destruct H0. rewrite H0.
exists (a :: x0). exists x1. refl.
Qed.

(***********************************************************************)
(* boolean membership when the equality on A is decidable *)

Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Fixpoint Inb (x : A) (l : list) {struct l} : bool :=
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

(***********************************************************************)
(* removing *)

Fixpoint remove (y : A) (l : list) {struct l} : list :=
  match l with
    | nil => nil
    | cons x l' =>
      match eq_dec x y with
	| left _ => remove y l'
	| right _ => cons x (remove y l')
      end
  end.

End S.

Implicit Arguments in_elim [A x l].

(***********************************************************************)
(* map *)

Lemma map_app : forall (A B : Set) (f : A->B) l1 l2,
  map f (l1 ++ l2) = (map f l1) ++ map f l2.

Proof.
induction l1; simpl; intros. refl. rewrite IHl1. refl.
Qed.

(***********************************************************************)
(* flattening *)

Section flat.

Variable A : Set.

Fixpoint flat (l : list (list A)) : list A :=
  match l with
    | nil => nil
    | cons x l' => x ++ flat l'
  end.

End flat.

(***********************************************************************)
(* tactics *)

Ltac inbtac :=
  match goal with
    | _ : In ?x ?l |- _ =>
      let H0 := fresh "H" in
	(assert (H0 : Inb x l = true); apply Inb_intro; assumption; rewrite H0)
  end.

Ltac intac := repeat (apply in_eq || apply in_cons).

Ltac incltac := repeat (apply incl_cons; [intac | idtac]); apply incl_nil.

(***********************************************************************)
(* element_at *)

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

  Lemma element_at_exists : forall l p, p < length l <-> ex (fun a => l[p] = Some a).

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

Notation "l '[' p ']'" := (element_at l p) (at level 50).
Notation "l '[' p ':=' a ']'" := (replace_at l p a) (at level 50).

(***********************************************************************)
(* one_less *)

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
(* accessibility *)

Definition accs (A : Set) r l := forall a : A, In a l -> Acc r a.
