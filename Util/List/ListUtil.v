(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17
- Adam Koprowski, 2006-04-28
- Solange Coupet-Grimal and William Delobel, 2006-01-09
- Frederic Blanqui, 2005-02-03, 2009-07-06
- Sebastien Hinderer, 2004-05-25

Extension of the Coq library on lists.
*)

Set Implicit Arguments.

From CoLoR Require Import LogicUtil EqUtil RelUtil BoolUtil NatUtil.

From Coq Require Import Setoid SetoidList FunInd.
From Coq Require Export List.
From Coq Require Program.

Arguments nil {A}.
Arguments incl {A} l m.
Arguments in_app_or [A l m a] _.
Arguments in_map [A B] f [l x] _.
Arguments in_combine_l [A B l l' x y] _.
Arguments in_combine_r [A B l l' x y] _.
Arguments nth_In [A n l] d _.

Ltac elt_type l := match type of l with list ?A => A end.

Infix "[=" := incl (at level 70).

(***********************************************************************)
(** Properties of [In] (membership predicate on lists). *)

Section In.

  Variable A : Type.

  Lemma in_app : forall l m (x : A), In x (l ++ m) <-> In x l \/ In x m.

  Proof. intuition. Qed.

  Lemma notin_app : forall l m (x : A), ~In x (l ++ m) <-> ~In x l /\ ~In x m.

  Proof. intuition. rewrite in_app in H0. intuition. Qed.

  Lemma in_appl : forall (x : A) l1 l2, In x l1 -> In x (l1 ++ l2).

  Proof.
    induction l1; simpl; intros. contr. destruct H. subst x. auto.
    right. apply IHl1. hyp.
  Qed.

  Lemma in_appr : forall (x : A) l1 l2, In x l2 -> In x (l1 ++ l2).

  Proof. induction l1; simpl; intros. hyp. right. apply IHl1. hyp. Qed.

  Lemma in_app_com : forall (x : A) l1 l2 l3,
    In x ((l1 ++ l3) ++ l2) -> In x ((l1 ++ l2) ++ l3).

  Proof. intros. rewrite !in_app in H. intuition. Qed.

  Lemma in_elim : forall (x : A) l,
    In x l -> exists l1, exists l2, l = l1 ++ x :: l2.

  Proof.
    induction l; simpl; intros. contr. destruct H. subst x.
    exists nil. exists l. refl. ded (IHl H). do 2 destruct H0. rewrite H0.
    exists (a :: x0). exists x1. refl.
  Qed.

  Variable eqA_dec : forall x y : A, {x=y}+{~x=y}.

  Lemma in_elim_dec : forall (x : A) l,
    In x l -> exists m, exists p, l = m ++ x :: p /\ ~In x m.

  Proof.
    induction l; simpl; intros. contr. destruct H. subst x.
    exists nil. exists l. intuition. ded (IHl H). do 3 destruct H0.
    subst l. case (eqA_dec a x); intro.
    subst x. exists nil. exists (x0 ++ a :: x1). intuition.
    exists (a :: x0). exists x1. intuition. simpl in H2. destruct H2; auto.
  Qed.

  Lemma In_midex : eq_midex A -> forall (x : A) l, In x l \/ ~In x l. 

  Proof.
    induction l. tauto. simpl. destruct (H a x); destruct IHl; tauto.
  Qed.

  Lemma In_elim_right : eq_midex A -> forall (x : A) l,
    In x l -> exists l', exists l'', l = l'++x::l'' /\ ~In x l''. 

  Proof.
    induction l; simpl; intros. contr. 
    destruct (In_midex H x l). destruct IHl. hyp. destruct H2. 
    ex (a::x0) x1. rewrite (proj1 H2), <- (app_comm_cons x0 (x::x1) a). tauto.  
    destruct H0. ex (@nil A) l. simpl. rewrite H0. tauto. contr.
  Qed.

  Lemma In_cons : forall (x a : A) l, In x (a::l) <-> a=x \/ In x l. 

  Proof.
    intros. simpl. tauto.
  Qed.

  Lemma In_InA_eq : forall (x : A) l, In x l <-> InA eq x l.

  Proof.
    induction l; simpl. sym. apply InA_nil. rewrite IHl, InA_cons.
    intuition.
  Qed.

End In.

Arguments in_elim [A x l] _.
Arguments in_elim_dec [A] _ [x l] _.

Ltac intac := repeat (apply in_eq || apply in_cons).

Ltac list_ok := let x := fresh in intro x;
  match goal with
    | |- In _ ?l => vm_compute; destruct x; tauto
  end.

(***********************************************************************)
(** Properties of [incl]
  (non-order-preserving inclusion predicate on lists). *)

#[global] Instance incl_preorder A : PreOrder (@incl A).

Proof.
  constructor.
  intro x. apply incl_refl.
  intros x y z xy yz. apply incl_tran with y; hyp.
Qed.

#[global] Instance app_incl A : Proper (incl ==> incl ==> incl) (@app A).

Proof. intros l l' ll' m m' mm' x. rewrite !in_app. intuition. Qed.

Section incl.

  Variable A : Type.

  Lemma incl_nil_elim : forall l : list A, l [= nil <-> l = nil.

  Proof.
    unfold incl. destruct l; intuition. assert (In a (a::l)). left. refl.
    ded (H _ H0). contr. discr.
  Qed.

  Lemma incl_nil : forall l : list A, nil [= l.

  Proof. induction l. refl. apply incl_tl. hyp. Qed.

  Lemma incl_cons_l : forall (a : A) l m, a :: l [= m -> In a m /\ l [= m.

  Proof. intros a l m. unfold incl. simpl. intuition. Qed.

  Lemma incl_cons_l_in : forall (x : A) l m, x :: l [= m -> In x m.

  Proof. unfold incl. simpl. intros. apply H. left. refl. Qed.

  Lemma incl_cons_l_incl : forall (x : A) l m, x :: l [= m -> l [= m.

  Proof. unfold incl. simpl. intros. apply H. tauto. Qed.

  Lemma incl_app_elim : forall l1 l2 l3 : list A,
    l1 ++ l2 [= l3 -> l1 [= l3 /\ l2 [= l3.

  Proof.
    intuition.
    trans (l1 ++ l2). apply incl_appl. refl. hyp.
    trans (l1 ++ l2). apply incl_appr. refl. hyp.
  Qed.

  Lemma incl_appr_incl : forall l1 l2 l3 : list A, l1 ++ l2 [= l3 -> l1 [= l3.

  Proof.
    induction l1; intros. apply incl_nil.
    trans ((a::l1) ++ l2). 2: hyp. apply incl_appl. refl.
  Qed.

  Lemma incl_appl_incl : forall l1 l2 l3 : list A, l1 ++ l2 [= l3 -> l2 [= l3.

  Proof.
    induction l1; intros. hyp.
    trans ((a::l1) ++ l2). 2: hyp. apply incl_appr. refl.
  Qed.

  Lemma appl_incl : forall l l2 l2' : list A, l2 [= l2' -> l ++ l2 [= l ++ l2'.

  Proof. intros. apply app_incl. refl. hyp. Qed.

  Lemma appr_incl : forall l l1 l1' : list A, l1 [= l1' -> l1 ++ l [= l1' ++ l.

  Proof. intros. apply app_incl. hyp. refl. Qed.

  Lemma app_com_incl : forall l1 l2 l3 l4 : list A,
    (l1 ++ l3) ++ l2 [= l4 -> (l1 ++ l2) ++ l3 [= l4.

  Proof. unfold incl. intros. apply H. apply in_app_com. hyp. Qed.

  Lemma incl_cons_r : forall x : A, forall m l, l [= x :: m -> In x l \/ l [= m.

  Proof.
    induction l; simpl; intros. right. apply incl_nil.
    ded (incl_cons_l H). destruct H0. simpl in H0. destruct H0. auto.
    ded (IHl H1). destruct H2. auto.
    right. apply List.incl_cons; hyp.
  Qed.

  Variable eqA_dec : forall x y : A, {x=y}+{~x=y}.

  Lemma not_incl : forall l m, ~ l [= m <-> exists x:A, In x l /\ ~In x m.

  Proof.
    induction l; simpl; intros.
    (* nil *)
    intuition. absurd (nil[=m). hyp. apply incl_nil.
    do 2 destruct H. contr.
    (* cons *)
    split; intro.
    2:{ do 3 destruct H.
        subst. intro. apply H0. apply H. left. refl.
        intro. absurd (In x m). hyp. apply H1. right. hyp. }
    case (In_dec eqA_dec a m); intro.
    assert (~l[=m). intro. apply H. unfold incl. intro b. simpl. intuition.
    rewrite IHl in H0. do 2 destruct H0. exists x. tauto.
    exists a. tauto.
  Qed.

End incl.

Arguments incl_app_elim [A l1 l2 l3] _.

(***********************************************************************)
(** Strict inclusion. *)

Definition strict_incl A (l m : list A) := l [= m /\ ~m [= l.

Infix "[" := strict_incl (at level 70).

Lemma strict_incl_tran : forall A (l m n : list A), l [ m -> m [ n -> l [ n.

Proof.
unfold strict_incl. intuition. trans m; hyp.
apply H2. trans n; hyp.
Qed.

#[global] Instance strict_incl_rel A : Transitive (@strict_incl A).

Proof. intros x y z xy yz. apply strict_incl_tran with y; hyp. Qed.

(***********************************************************************)
(** Equivalence (i.e. having the same elements). *)

Definition lequiv {A} (l1 l2 : list A) := l1 [= l2 /\ l2 [= l1.

Infix "[=]" := lequiv (at level 70).

#[global] Instance lequiv_rel A : Equivalence (@lequiv A).

Proof. fo. Qed.

#[global] Instance app_lequiv A : Proper (lequiv ==> lequiv ==> lequiv) (@app A).

Proof. intros l l' ll' m m' mm'. unfold lequiv in *. intuition. Qed.

#[global] Instance incl_lequiv1 A1 B (f : list A1 -> relation B) :
  Proper (incl ==> inclusion) f -> Proper (lequiv ==> same) f.

Proof. intros hf l1 l1' [l1l1' l1'l1]. split; apply hf; hyp. Qed.

#[global] Instance incl_lequiv2 A1 A2 B (f : list A1 -> list A2 -> relation B) :
  Proper (incl ==> incl ==> inclusion) f ->
  Proper (lequiv ==> lequiv ==> same) f.

Proof.
  intros hf l1 l1' [l1l1' l1'l1] l2 l2' [l2l2' l2'l2]. split; apply hf; hyp.
Qed.

(***********************************************************************)
(** Properties of the empty list. *)

Section nil.

  Variable A : Type.

  Lemma list_empty_dec : forall l : list A, {l = nil} + {l <> nil}.

  Proof. destruct l; auto. right; congruence. Qed.

  Definition is_empty (l : list A) : bool :=
    match l with
      | nil => true
      | _ => false
    end.

End nil.

(***********************************************************************)
(** Properties of [cons]. *)

#[global] Instance cons_incl A : Proper (eq ==> incl ==> incl) (@cons A). 

Proof. intros x x' xx'. subst x'. fo. Qed.

#[global] Instance cons_lequiv A : Proper (eq ==> lequiv ==> lequiv) (@cons A).

Proof. intros x x' xx'. subst x'. fo. Qed.

Section cons.

  Variable A : Type.

  Lemma cons_eq : forall x x' : A, forall l l',
    x = x' -> l = l' -> x :: l = x' :: l'.

  Proof. intros. rewrite H, H0. refl. Qed.

  Lemma head_eq : forall x x' : A, forall l, x = x' -> x :: l = x' :: l.

  Proof. intros. rewrite H. refl. Qed.

  Lemma tail_eq : forall x : A, forall l l', l = l' -> x :: l = x :: l'.

  Proof. intros. rewrite H. refl. Qed.

End cons.

(***********************************************************************)
(** Properties of [app] (concatenation). *)

Section app.

  Variable A : Type.

  Lemma length_app : forall l m : list A, length (l ++ m) = length l + length m.

  Proof. induction l; simpl; intros. refl. rewrite IHl. refl. Qed.

  Lemma app_nil : forall l1 l2 : list A, l1 = nil -> l2 = nil -> l1 ++ l2 = nil.

  Proof. intros. subst l1. subst l2. refl. Qed.

  Lemma app_eq : forall l1 l2 l1' l2' : list A,
    l1 = l1' -> l2 = l2' -> l1 ++ l2 = l1' ++ l2'.

  Proof. intros. rewrite H, H0. refl. Qed.

  Lemma appl_eq : forall l1 l2 l1' : list A, l1 = l1' -> l1 ++ l2 = l1' ++ l2.

  Proof. intros. rewrite H. refl. Qed.

  Lemma appr_eq : forall l1 l2 l2' : list A, l2 = l2' -> l1 ++ l2 = l1 ++ l2'.

  Proof. intros. rewrite H. refl. Qed.

  Lemma list_app_first_last : forall l m (a : A),
    (l ++ a::nil) ++ m = l ++ a::m.

  Proof.
    induction l. auto.
    intros m a'. rewrite <- !app_comm_cons. destruct (IHl m a'); trivial.
  Qed.

  Lemma list_app_last : forall l m n (a : A),
    l ++ m = n ++ a::nil -> m <> nil -> In a m.

  Proof.
    intros l m n; revert l m; induction n; simpl; intros.
    (* induction base *)
    destruct l.
    simpl in H; rewrite H; auto with datatypes.
    inversion H.
    absurd (m = nil); trivial.
    apply (proj2 (app_eq_nil l m H3)).
    (* induction case *)
    destruct l.
    simpl in H; rewrite H; auto with datatypes.
    inversion H.
    apply IHn with l; trivial.
  Qed.

  Lemma list_drop_last : forall l m n (a : A),
    l ++ m = n ++ a::nil -> m <> nil -> exists2 w, w [= m & l ++ w = n.

  Proof.
    induction l; intros.
    (* induction base *)
    simpl in H.
    exists n.
    rewrite H; auto with datatypes.
    auto.
    (* induction case *)
    destruct n.
    (* n = nil -> contr *)
    simpl in H.
    destruct (app_eq_unit (a::l) m H) as 
      [[l_nil r_unit] | [l_unit r_nil]]; try contr.
    discr.
    (* n <> nil *)    
    inversion H.
    destruct (IHl m n a0); trivial.
    exists x; trivial.
    rewrite <- H4.
    auto with datatypes.
  Qed.

  Lemma last_intro : forall l : list A, length l > 0 ->
    exists m, exists a, l = m ++ a :: nil /\ length m = length l - 1.

  Proof.
    induction l; simpl; intros. apply False_ind. lia.
    destruct l. exists nil. exists a. intuition.
    assert (length (a0::l) > 0). simpl. lia.
    ded (IHl H0). do 3 destruct H1.
    exists (a::x). exists x0. split. rewrite H1. refl.
    simpl. simpl in H2. lia.
  Qed.

End app.

(***********************************************************************)
(** Properties of [length]. *)

Section length.

  Variable A : Type.

  Lemma length_0 : forall l : list A, length l = 0 -> l = nil.

  Proof. intros. destruct l. refl. discr. Qed.

End length.

Arguments length_0 [A l] _.

(***********************************************************************)
(** Properties of [head] and [tail]. *)

Section head_tail.

  Variable A : Type.

  Lemma head_app : forall (l l': list A) (lne: l <> nil),
    head (l ++ l') = head l.

  Proof. destruct l. tauto. auto. Qed.

  Lemma length_tail : forall l : list A, length (tail l) <= length l.

  Proof. induction l; simpl; intros; lia. Qed.

  Lemma tail_in : forall (x: A) l, In x (tail l) -> In x l.

  Proof. intros. destruct l; auto with datatypes. Qed.

  Lemma tail_cons_tail : forall (l1 l2: list A),
    l1 <> nil -> tail l1 ++ l2 = tail (l1 ++ l2).

  Proof. destruct l1. tauto. auto. Qed.

  Lemma length_tail_minus : forall (l : list A), length (tail l) = length l - 1.

  Proof. destruct l; simpl; lia. Qed.

  Lemma list_decompose_head : forall (l : list A) el (lne: l <> nil),
    head l = Some el -> l = el :: tail l.

  Proof. intros. destruct l. discr. inversion H. rewrite <- H1; trivial. Qed.

  Lemma in_head_tail : forall a (l : list A),
    In a l -> Some a = head l \/ In a (tail l).

  Proof.
    induction l; intros; inversion H.
    left; simpl; rewrite H0; trivial.
    right; trivial.
  Qed.

  Lemma head_notNil : forall (l : list A) (lne : l <> nil),
    {a : A | head l = Some a}.

  Proof. destruct l. tauto. exists a; auto. Defined.

  Lemma head_of_notNil : forall (l : list A) a (lne: l <> nil),
    head l = Some a -> proj1_sig (head_notNil lne) = a.

  Proof. intros. destruct l; try discr. simpl; inversion H; trivial. Qed.

End head_tail.

#[global] Hint Resolve tail_in tail_cons_tail head_app : datatypes.
#[global] Hint Rewrite head_app length_app : datatypes.

(***********************************************************************)
(** Iteration of [tail]. *)

Section tail_nth.

  Variable A : Type.

  Fixpoint tail_nth (l : list A) (n : nat) : option (list A) :=
    match l, n with
      | _, 0 => Some l
      | a :: l', S n' => tail_nth l' n'
      | _, _ => None
    end.

End tail_nth.

(****************************************************************************)
(** Function selecting the elements that satisfy some predicate. *)

Section select.

  Context {A: Type} {f : A->Prop}.

  Variable (f_dec : forall x, {f x}+{~f x}).

  Fixpoint select (l : list A) :=
    match l with
      | nil => nil
      | cons a l' =>
        match f_dec a with
          | left _ => a :: select  l'
          | right _ => select l'
        end
    end.

  Lemma incl_select : forall l, select l [= l.

  Proof.
    induction l; simpl. fo. destruct (f_dec a).
    apply cons_incl. refl. hyp. apply incl_tl. hyp.
  Qed.

  Lemma select_correct : forall l x, In x (select l) -> In x l /\ f x.

  Proof.
    induction l; intro x; simpl. fo.
    destruct (f_dec a); fo. subst. hyp.
  Qed.

  Lemma select_complete : forall l x, In x l -> f x -> In x (select l).

  Proof.
    induction l; intro x; simpl. fo.
    intros [h|h]; destruct (f_dec a); subst; fo.
  Qed.

End select.

(***********************************************************************)
(** Select the elements of a list wrt a boolean function. *)

Section filter.

  Variables (A : Type) (f : A -> bool).

  Lemma filter_app : forall l m, filter f (l ++ m) = filter f l ++ filter f m.

  Proof.
    induction l; simpl; intros. refl. rewrite IHl. destruct (f a); refl.
  Qed.

  Lemma filter_incl : forall l, filter f l [= l.

  Proof.
    induction l; simpl; intros. refl. case (f a); rewrite IHl.
    refl. apply incl_tl. refl.
  Qed.

  Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

  Lemma notIn_filter : forall x l,
    ~In x (filter f l) <-> ~In x l \/ (In x l /\ f x = false).

  Proof.
    intros. rewrite filter_In. intuition. case (In_dec eq_dec x l); intro.
    right. intuition. revert H. case (f x). cong. refl. auto.
    rewrite H2 in H3. discr.
  Qed.

End filter.

Section filter_opt.

  Variables (A B : Type) (f : A -> option B).

  Fixpoint filter_opt (l : list A) : list B :=
    match l with
      | nil => nil
      | cons a m =>
        match f a with
          | Some b => cons b (filter_opt m)
          | _ => filter_opt m
        end
    end.

End filter_opt.

(***********************************************************************)
(** Boolean function testing membership. *)

Section Inb.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

  Fixpoint Inb (x : A) (l : list A) : bool :=
    match l with
      | nil => false
      | cons y l' =>
        match eq_dec x y with
	  | left _ => true
	  | _ => Inb x l'
        end
    end.
 
  Lemma Inb_true : forall x l, Inb x l = true -> In x l.

  Proof. induction l; simpl. intro. discr. case (eq_dec x a); auto. Qed.

  Lemma Inb_false : forall x l, Inb x l = false -> In x l -> False.

  Proof.
    induction l; simpl. intros. contr. case (eq_dec x a).
    intros. discr. intros. destruct H0; auto.
  Qed.

  Lemma Inb_intro : forall x l, In x l -> Inb x l = true.

  Proof.
    induction l; simpl; intros. contr. case (eq_dec x a). auto.
    destruct H. intro. absurd (x = a); auto. auto.
  Qed.

  Lemma Inb_elim : forall x l, ~In x l -> Inb x l = false.

  Proof.
    induction l; simpl; intros. refl. case (eq_dec x a). intro. subst x.
    intuition. intuition.
  Qed.

  Lemma Inb_correct : forall x l, In x l <-> Inb x l = true.

  Proof.
    intuition. apply Inb_intro. hyp. apply Inb_true. hyp.
  Qed.

  Lemma Inb_incl : forall x l l', l [= l' -> Inb x l = true -> Inb x l' = true.

  Proof.
    intros. apply Inb_intro. apply H. apply Inb_true. hyp.
  Qed.

  Lemma Inb_equiv : forall x l l', lequiv l l' -> Inb x l = Inb x l'.

  Proof.
    intros. destruct H.
    case_eq (Inb x l'); intros; case_eq (Inb x l); intros; try refl.
    ded (Inb_incl _ H0 H1). rewrite H2 in H3. discr.
    ded (Inb_incl _ H H2). rewrite H1 in H3. discr.
  Qed.

  Definition Inclb (l1 l2 : list A) := forallb (fun x => Inb x l2) l1.

  Lemma Inclb_ok : forall l1 l2, Inclb l1 l2 = true <-> l1 [= l2.

  Proof.
    intros. induction l2. unfold Inclb. simpl. case l1. simpl; split; auto.
    intro. refl.
    intros. simpl; split; intro. discr.
    rewrite incl_nil_elim in H. discr.
    split; unfold Inclb; simpl; rewrite forallb_forall; intro.
    intros x Hx. gen (H _ Hx). case (eq_dec x a); intros.
    rewrite e; apply in_eq. apply in_cons. apply Inb_true; auto.
    intros. case (eq_dec x a); auto; intros.
    destruct (in_inv (H _ H0)); auto. apply Inb_intro; auto.
  Qed.

End Inb.

Ltac inbtac :=
  match goal with
    | _ : In ?x ?l |- _ =>
      let H0 := fresh "H" in
	(assert (H0 : Inb x l = true); apply Inb_intro; hyp; rewrite H0)
  end.

(***********************************************************************)
(** Remove an element from a list. *)

Section remove.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

  Fixpoint remove (y : A) (l : list A) : list A :=
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
    apply le_trans with (length l). apply IHl. apply le_n_Sn. simpl.
    apply le_n_S. apply IHl.
  Qed.

  Lemma In_length_remove : forall (x : A) l,
    In x l -> length (remove x l) < length l.

  Proof.
    induction l; simpl; intros. contr. destruct (eq_dec a x).
    apply le_lt_n_Sm.
    apply length_remove. destruct H. rewrite H in n. tauto. simpl. apply lt_n_S.
    apply IHl. hyp.
  Qed.

  Lemma In_remove : forall (x y : A) l, x <> y -> In y l -> In y (remove x l).

  Proof.
    induction l; simpl; intros. hyp. 
    destruct (eq_dec a x); destruct H0. rewrite e in H0. tauto.
    tauto. rewrite H0. simpl. tauto. simpl. tauto.
  Qed.

  Lemma incl_remove : forall (x : A) l m, ~In x l -> l [= m -> l [= remove x m.

  Proof.
    induction l; simpl; intros. apply incl_nil. assert (~a=x /\ ~In x l). tauto.
    unfold incl. intros. simpl in H2. destruct H2. subst a0.
    apply In_remove. auto. unfold incl in H0. apply H0. simpl. auto.
    apply IHl. auto. apply incl_cons_l_incl with (x := a). exact H0. exact H2.
  Qed.

  Lemma incl_remove2 (x : A) : forall l, remove x l [= l.

  Proof.
    induction l; simpl. refl. destruct (eq_dec a x).
    apply incl_tl. hyp. apply cons_incl. refl. hyp.
  Qed.

  Lemma notin_remove : forall x l, In x (remove x l) -> False.

  Proof.
    induction l; simpl. auto. destruct (eq_dec a x). auto. simpl. tauto.
  Qed.

  Lemma remove_In : forall a x l, In a (remove x l) -> In a l.

  Proof.
    induction l;intros. simpl in *. auto.
    simpl in H. destruct (eq_dec a0 x).
    subst; simpl; right; auto.
    simpl in *; tauto.
  Qed.

  Lemma remove_eq : forall a x l, In a (remove x l) <-> a <> x /\ In a l.

  Proof.
    intuition. subst. eapply notin_remove. apply H. eapply remove_In. apply H.
    apply In_remove; auto.
  Qed.

  Lemma remove_notin (x : A) : forall l, ~In x l -> remove x l = l.

  Proof.
    induction l; intro nxl; simpl. refl. destruct (eq_dec a x).
    subst. fo. f_equal. fo.
  Qed.

End remove.

(***********************************************************************)
(** Removes a list of elements from a list. *)

Section removes.

  Variable (A : Type) (eqdec : forall x y : A, {x=y}+{x<>y}).

  Notation In_dec := (In_dec eqdec).

  Fixpoint removes (l m : list A) : list A :=
    match m with
      | nil => nil
      | x :: m' =>
        match In_dec x l with
          | left _ => removes l m'
          | right _ => x :: removes l m'
        end
    end.

  Lemma incl_removes : forall l m, removes l m [= m.

  Proof.
    unfold incl. induction m; simpl. contr.
    case (In_dec a l). intros. right. apply IHm. hyp.
    simpl. intuition.
  Qed.

  Lemma incl_removes_app : forall l m, m [= removes l m ++ l.

  Proof.
    unfold incl. induction m; simpl. contr. intros. destruct H.
    subst a0. case (In_dec a l); intro. apply in_appr. hyp. simpl. auto.
    case (In_dec a l); intro. apply IHm. hyp. simpl.
    case (eqdec a a0); intro. subst a0. auto. right. apply IHm. hyp.
  Qed.

  Lemma In_removes : forall x l m, In x (removes l m) <-> In x m /\ ~In x l.

  Proof.
    induction m; simpl; intros. tauto. case (In_dec a l); intro. rewrite IHm.
    fo. subst. contr. simpl. rewrite IHm. fo. subst.
    hyp.
  Qed.

End removes.

(***********************************************************************)
(** Properties of [map]. *)

Section map.

  Variable (A B : Type) (f : A->B).

  Lemma map_app : forall l1 l2, map f (l1 ++ l2) = (map f l1) ++ map f l2.

  Proof.
    induction l1; simpl; intros. refl. rewrite IHl1. refl.
  Qed.

  Lemma in_map_elim : forall x l, In x (map f l) -> exists y, In y l /\ x = f y.

  Proof.
    induction l; simpl; intros. contr. destruct H.
    exists a. auto. ded (IHl H). do 2 destruct H0. exists x0. auto.
  Qed.

  Lemma map_eq : forall (g : A->B) l,
    (forall x, In x l -> f x = g x) -> map f l = map g l.

  Proof.
    induction l; simpl; intros. refl. apply cons_eq. ded (H a). intuition.
    apply IHl. intro. ded (H x). intuition.
  Qed.

End map.

Arguments in_map_elim [A B f x l] _.

Lemma map_eq_id : forall A (f:A->A) l,
  (forall x, In x l -> f x = x) -> map f l = l.

Proof.
induction l; simpl; intros. refl. apply cons_eq. ded (H a). intuition.
apply IHl. intro. ded (H x). intuition.
Qed.

(***********************************************************************)
(** Properties of [flat_map]. *)

Section flat_map.

  Variables (A B : Type) (f : A -> list B).

  Lemma In_flat_map_intro : forall x l y,
    In y l -> In x (f y) -> In x (flat_map f l).

  Proof.
    intros. apply (proj2 (@in_flat_map _ _ f l x)).
    exists y. auto.
  Qed.

  Lemma In_flat_map_elim : forall l y, 
    In y (flat_map f l) -> exists x, In x l /\ In y (f x).

  Proof.
    intros. exact (proj1 (@in_flat_map _ _ _ _ _) H).
  Qed.

  Lemma flat_map_app : forall l m,
    flat_map f (l ++ m) = flat_map f l ++ flat_map f m.

  Proof. induction l; simpl; intros. refl. rewrite IHl, app_ass. refl. Qed.

End flat_map.

(***********************************************************************)
(** Concatenation of a list of lists. *)

Section flat.

  Variable A : Type.

  Fixpoint flat (l : list (list A)) : list A :=
    match l with
      | nil => nil
      | cons x l' => x ++ flat l'
    end.

  Lemma In_incl_flat : forall x l, In x l -> x [= flat l.

  Proof.
    induction l; simpl; intros. contr. intuition. subst. apply incl_appl. refl.
  Qed.

  Lemma incl_flat_In : forall x c cs l,
    In x c -> In c cs -> flat cs [= l -> In x l.

  Proof. intros. apply H1. apply (In_incl_flat _ _ H0). hyp. Qed.

End flat.

Arguments In_incl_flat [A x l] _ _ _.

(****************************************************************************)
(** Position of an element in a list (the result is meaningful only if
the element occurs in the list). *)

Section pos.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

  Section def.

    Variable x : A.

    Fixpoint pos l :=
      match l with
        | nil => 0
        | a :: l' => if eq_dec a x then 0 else S (pos l')
      end.

    Lemma nth_pos d : forall l, In x l -> nth (pos l) l d = x.

    Proof.
      induction l; intro h; simpl. fo. destruct (eq_dec a x). hyp.
      apply IHl. fo.
    Qed.

    Lemma pos_lt_length : forall l, In x l -> pos l < length l.

    Proof.
      induction l; intro h; simpl. fo. destruct (eq_dec a x). lia.
      apply lt_n_S. fo.
    Qed.

  End def.

  Lemma inj_pos x y : forall l, In x l -> pos x l = pos y l -> x = y.

  Proof.
    induction l; intro h; simpl. contr.
    destruct (eq_dec a x); destruct (eq_dec a y); subst; intro e.
    reflexivity. discr. discr. inversion e. fo.
  Qed.

End pos.

Arguments pos_lt_length [A] _ [x l] _.

(***********************************************************************)
(** Element at a position (starting from 0) and its replacement. *)

Section Element_At_List.
  
  Variable A : Type.
  
  Fixpoint element_at (l : list A) (p : nat) : option A := 
    match l with 
      | nil => None
      | h :: t =>
	match p with 
          | 0 => Some h 
          | S p' => element_at t p'
        end
    end.

  Notation "l '[' p ']'" := (element_at l p) (at level 50).

  Fixpoint replace_at (l : list A) (p : nat) (a : A) : list A :=
    match l with
      | nil => nil
      | h :: t =>
	match p with 
          | 0 => a :: t
          | S p' => h :: (replace_at t p' a)
        end
    end.

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
    gen Hp; auto with arith.
    elim (IHl p); intros H1 H2.
    elim (H1 Hp'); intros a Ha; exists a; trivial.
    destruct p as [ | p]; intro H.
    auto with arith.
    elim (IHl p); intros H1 H2.
    gen (H2 H); auto with arith.
  Qed.

  Lemma element_at_replaced : forall l p a, p < length l -> l[p:=a][p] = Some a.

  Proof.
    intro l; induction l as [ | h t IHl]; simpl; intros p a Hlength.
    inversion Hlength.
    destruct p as [ | p]; simpl.
    trivial.
    apply IHl; gen Hlength; auto with arith.
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

  Lemma in_exists_element_at :
    forall l a, In a l -> ex (fun p => l[p] = Some a).

  Proof.
    intro l; induction l as [ | h t IHl]; intros a a_in_l.
    inversion a_in_l.
    elim a_in_l; clear a_in_l; intro a_in_l.
    exists 0; subst; trivial.
    elim (IHl a a_in_l); intros p Hp.
    exists (S p); simpl; trivial.
  Qed.

  Lemma exists_element_at_in :
    forall l a, ex (fun p => l[p] = Some a) -> In a l.

  Proof.
    intro l; induction l as [ | h t IHl]; intros a Hex; 
      elim Hex; clear Hex; intros p Hp.
    inversion Hp.
    destruct p as [ | p]; inversion Hp.
    left; trivial.
    right; apply IHl; exists p; trivial.
  Qed.

  Lemma element_at_in : forall (x:A) l n, l[n] = Some x -> In x l.

  Proof.
    induction l; simpl; intros. discr. destruct n.
    inversion H. subst. auto. ded (IHl _ H). auto.
  Qed.

  Lemma element_at_in2 :
    forall (x:A) l n, l[n] = Some x -> In x l /\ n < length l.

  Proof.
    induction l; intros; simpl in H; try discr. destruct n.
    inversion H; subst; simpl; auto with *.
    ded (IHl n H). intuition; simpl; lia.
  Qed.

  Lemma element_at_app_r : forall l l' p, 
    p >= length l -> (l ++ l') [p] = l' [p - length l].

  Proof.
    induction l. intuition.
    intros. destruct p.
    inversion H.
    simpl. apply IHl. simpl in H. auto with arith.
  Qed.

  Lemma replace_at_app_r : forall l l' p a,
    p >= length l -> (l ++ l') [p := a] = l ++ l' [p - length l := a].

  Proof.
    induction l; intros.
    simpl. rewrite <- minus_n_O. refl.
    destruct p. inversion H.
    simpl. rewrite IHl. refl. intuition.
  Qed.

End Element_At_List.

Arguments element_at_in [A x l n] _.
Arguments element_at_in2 [A x l n] _.
Arguments in_exists_element_at [A l a] _.
(*Arguments element_at_exists [A l p].*)

Notation "l '[' p ']'" := (element_at l p) (at level 50) : list_scope.
Notation "l '[' p ':=' a ']'" := (replace_at l p a) (at level 50) : list_scope.

(***********************************************************************)
(** Precidate saying that an element [a] in a list has been replaced
by an element [a'] such that [r a a'] where [r] is a relation. *)

Section one_less.

  Variables (A : Type) (r : relation A).
  
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

Arguments one_less [A] _ _ _.
Arguments one_less_cons [A] _ _ _ _ _ _ _ _ _.

(***********************************************************************)
(** Properties of [rev]. *)

Section reverse.

  Variable A : Type.

  Lemma in_rev : forall (x : A) l, In x l -> In x (rev l).

  Proof.
    induction l; simpl; intros. hyp. apply in_or_app. simpl. tauto.
  Qed.

  Lemma incl_rev : forall l : list A, l [= rev l.

  Proof.
    unfold incl. intros. apply in_rev. hyp. 
  Qed.

  Lemma rev_incl : forall l : list A, rev l [= l. 

  Proof.
    intros. pose (incl_rev (rev l)). rewrite (rev_involutive l) in i. hyp.
  Qed.

  Lemma incl_rev_intro : forall l l' : list A, rev l [= rev l' -> l [= l'.

  Proof.
    intros. trans (rev l). apply incl_rev. trans (rev l'). hyp. apply rev_incl.
  Qed.

End reverse.

(***********************************************************************)
(** Tail-recursive reserve function. *)

Section reverse_tail_recursive.

  Variable A : Type.

  Fixpoint rev_append (l' l : list A) : list A :=
    match l with
      | nil => l'
      | a :: l => rev_append (a :: l') l
    end.

  Notation rev' := (rev_append nil).

  Lemma rev_append_rev : forall l l', rev_append l' l = rev l ++ l'.

  Proof. induction l; simpl; auto; intros. rewrite <- ass_app; fo. Qed.

  Lemma rev_append_app : forall l l' acc : list A,
    rev_append acc (l ++ l') = rev_append (rev_append acc l) l'.

  Proof. induction l; simpl; intros. refl. rewrite IHl. refl. Qed.

  Lemma rev'_app : forall l l' : list A, rev' (l ++ l') = rev' l' ++ rev' l.

  Proof.
    intros. rewrite rev_append_app, !rev_append_rev, <- !app_nil_end. refl.
  Qed.

  Lemma rev'_rev : forall l : list A, rev' l = rev l.

  Proof. intro. rewrite rev_append_rev, <- app_nil_end. refl. Qed.

  Lemma rev'_rev' : forall l : list A, rev' (rev' l) = l.

  Proof. intro. rewrite !rev'_rev. apply rev_involutive. Qed.

  Lemma rev'_cons : forall a (l : list A), rev' (a::l) = rev' l ++ (a::nil).

  Proof.
    intros. change (rev' ((a::nil) ++ l) = rev' l ++ (a::nil)).
    rewrite rev'_app. refl.
  Qed.

End reverse_tail_recursive.

Notation rev' := (rev_append nil).

(***********************************************************************)
(** Given a list [l] and a position [n] in [l], return the pair of
lists [l1] and [l2] such that [l = l1 ++ l2]. *)

Section split.

  Variable A : Type.

  Fixpoint split_aux (acc l : list A) (n : nat) : option (list A * list A) :=
    match l, n with
      | _, 0 => Some (rev' acc, l)
      | a :: l', S n' => split_aux (a::acc) l' n'
      | _, _ => None
    end.

  Lemma split_aux_correct : forall l n l1 l2 acc,
    split_aux acc l n = Some (l1, l2) -> rev' acc ++ l = l1 ++ l2.

  Proof.
    induction l; destruct n; simpl; intros. inversion H. refl. discr.
    inversion H. refl. ded (IHl _ _ _ _ H). rewrite rev'_cons in H0.
    rewrite app_ass in H0. hyp.
  Qed.

  Arguments split_aux_correct [l n l1 l2] _ _.

  Notation split := (split_aux nil).

  Lemma split_correct : forall l n l1 l2,
    split l n = Some (l1, l2) -> l = l1 ++ l2.

  Proof.
    intros. change (rev' nil ++ l = l1 ++ l2). apply (split_aux_correct _ H).
  Qed.

End split.

Notation split := (split_aux nil).

Arguments split_correct [A l n l1 l2] _.

(***********************************************************************)
(** Last element of a list. *)

Section last.

  Variable A : Type.

  Lemma last_nth : forall (d : A) l, last l d = nth (length l - 1) l d.

  Proof.
    induction l; simpl; intros. refl. rewrite IHl.
    elim l; simpl; intros. refl. destruct l0; simpl. refl. refl.
  Qed.

  Lemma last_default : forall (d1 : A) d2 l, l <> nil -> last l d1 = last l d2.

  Proof.
    induction l; simpl; intros. cong. destruct l. refl. apply IHl. discr.
  Qed.

End last.

Arguments last_intro [A l] _.

(***********************************************************************)
(** Properties of [partition]. *)

Section partition.

  Variables (A : Type) (f : A -> bool) (a : A) (l : list A).

  Lemma partition_complete : let p := partition f l in
    In a l -> In a (fst p) \/ In a (snd p).

  Proof.
    induction l. auto.
    simpl. intro. destruct (partition f l0). destruct H.
    destruct (f a0); simpl; auto.
    destruct (f a0); simpl in *; destruct IHl0; auto.
  Qed.

  Lemma partition_inleft : In a (fst (partition f l)) -> In a l.

  Proof.
    induction l. auto.
    simpl. intro. destruct (partition f l0). destruct (f a0).
    destruct H; auto.
    right. apply IHl0. auto.
  Qed.

  Lemma partition_inright : In a (snd (partition f l)) -> In a l.

  Proof.
    induction l. auto.
    simpl. intro. destruct (partition f l0). destruct (f a0).
    right. apply IHl0. auto.
    destruct H; auto.
  Qed.

  Lemma partition_left : In a (fst (partition f l)) -> f a = true.

  Proof.
    induction l; simpl. auto.
    destruct (partition f l0). destruct (bool_dec (f a0) true).
    rewrite e. intro. destruct H.
    subst a0. hyp.
    apply IHl0. hyp.
    rewrite (not_true_is_false (f a0)); hyp.
  Qed.

  Lemma partition_right : In a (snd (partition f l)) -> f a = false.

  Proof.
    induction l; simpl. intuition.
    destruct (partition f l0). destruct (bool_dec (f a0) true).
    rewrite e. apply IHl0.
    rewrite (not_true_is_false (f a0)). intro. destruct H.
    subst a0. destruct (f a); intuition.
    apply IHl0. hyp. hyp.
  Qed.

End partition.

Section partition_by_prop.

  Variables (A : Type) (P : A -> Prop) (P_dec : forall x, {P x}+{~P x}).

  Definition partition_by_prop a :=
    match P_dec a with
    | left _ => true
    | right _ => false
    end.

  Lemma partition_by_prop_true : forall a, partition_by_prop a = true -> P a.

  Proof.
    intros. unfold partition_by_prop in H. 
    destruct (P_dec a). hyp. discr.
  Qed.

End partition_by_prop.

Section partition_by_rel.

  Variables (A : Type) (R : relation A) (R_dec : rel_dec R).

  Definition partition_by_rel p := 
    if R_dec (fst p) (snd p) then true else false.

  Lemma partition_by_rel_true : forall a b,
    partition_by_rel (a, b) = true -> R a b.

  Proof.
    intros. unfold partition_by_rel in H. simpl in H.
    destruct (R_dec a b). hyp. discr.
  Qed.

End partition_by_rel.

(***********************************************************************)
(** Select the elements of a list according to a list of booleans. *)

Section ListFilter.

  Variable A : Type.

  Fixpoint listfilter (L : list A) l :=
    match L with
      | nil => nil
      | a :: Q =>
        match l with 
          | nil => nil
          | true :: q => a :: listfilter Q q
          | false :: q => listfilter Q q
        end
    end.

  Lemma listfilter_in : forall L l i x,
    L[i]=Some x -> l[i]=Some true -> In x (listfilter L l) .

  Proof.
    induction L.
    intros. simpl in *. discr.

    intros.
    destruct i; simpl in H.
    simpl.
    inversion H; subst.
    destruct l; simpl in *. discr.
    inversion H0; subst. simpl; left; auto.

    destruct l; auto. simpl in H0; discr.
    inversion H0.
    simpl.
    destruct b.
    right. eapply IHL; eauto.
    eapply IHL; eauto.
  Qed.

End ListFilter.

(****************************************************************************)
(** Properties of [nth] and [nth_error]. *)

Section ListsNth.

  Variable A: Type.

  Lemma In_nth : forall A d (x : A) l,
    In x l -> exists i, i < length l /\ nth i l d = x.

  Proof.
    induction l; simpl; intros. contr. destruct H.
    subst. exists 0. intuition.
    destruct (IHl H) as [i hi]. exists (S i). intuition.
  Qed.

  Lemma nth_error_In : forall (l : list A) i, 
    {a : A | nth_error l i = Some a} + {nth_error l i = None}.

  Proof.
    induction l.
    right; compute; case i; trivial.
    intro i.
    case i.
    left; exists a; trivial.
    intro n.
    destruct (IHl n) as [[a' a'nth] | nth_none].
    left; exists a'; trivial.
    right; trivial.
  Qed.

  Lemma nth_some_in :
    forall (l : list A) i a, nth_error l i = Some a -> In a l.

  Proof.
    induction l; intros.
    destruct i; simpl in *; discr.
    destruct i; simpl in *.
    left; compute in *; congruence.
    right; eapply IHl; eauto.
  Qed.

  Lemma list_In_nth : forall (l : list A) a,
    In a l -> exists p: nat, nth_error l p = Some a.

  Proof.
    induction l.
    contr.
    intros; destruct H.
    exists 0.
    rewrite H; trivial.
    destruct (IHl a0 H).
    exists (S x); trivial.
  Qed.

  Lemma nth_app_left : forall (l m: list A) i,
    i < length l -> nth_error (l ++ m) i = nth_error l i.

  Proof.
    induction l; simpl; intros m i i_l.
    lia.
    destruct i; simpl.
    trivial.
    apply (IHl m i).
    auto with arith.
  Qed.

  Lemma nth_app_right : forall (l m: list A) i, i >= length l ->
     nth_error (l ++ m) i = nth_error m (i - length l).

  Proof.
    induction l; simpl; intros m i i_l.
    auto with arith.
    destruct i; simpl.
    lia.
    apply IHl.
    auto with arith.
  Qed.

  Lemma nth_app : forall (l m: list A) a i, nth_error (l ++ m) i = Some a ->
    (nth_error l i = Some a /\ i < length l) \/ 
    (nth_error m (i - length l) = Some a /\ i >= length l).

  Proof.
    intros.
    destruct (le_lt_dec (length l) i).
    right; split; trivial.
    rewrite (nth_app_right l m l0) in H; trivial.
    left; split; trivial.
    rewrite (nth_app_left l m l0) in H; trivial.
  Qed.

  Lemma nth_beyond : forall (l : list A) i,
    i >= length l -> nth_error l i = None.

  Proof.
    induction l; simpl; intro i.
    destruct i; trivial.
    destruct i; simpl.
    intros.
    lia.
    intro.
    rewrite (IHl i); trivial.
    auto with arith.
  Qed.

  Lemma nth_beyond_idx : forall (l : list A) i,
    nth_error l i = None -> i >= length l.

  Proof.
    induction l; simpl; intro i.
    auto with arith.
    destruct i; simpl.
    intros.
    discr.
    intro.
    assert (i >= length l).
    apply (IHl i); trivial.
    auto with arith.
  Qed.

  Lemma nth_in : forall (l : list A) i,
    nth_error l i <> None <-> i < length l.

  Proof.
    induction l; simpl; intro i.
    split.
    destruct i; intro; exfalso; auto.
    intro; lia.
    destruct i; simpl.
    split; intro.
    auto with arith.
    discr.
    split; intro.
    assert (i < length l).
    apply (proj1 (IHl i)); trivial.
    auto with arith.
    apply (proj2 (IHl i)); auto with arith.
  Qed.

  Lemma nth_some : forall (l : list A) n a,
    nth_error l n = Some a -> n < length l.

  Proof. intros. apply (proj1 (nth_in l n)). rewrite H; discr. Qed.

  Lemma nth_map_none : forall (l : list A) i (f: A -> A),
    nth_error l i = None -> nth_error (map f l) i = None.

  Proof. 
    induction l. trivial. intros i f; destruct i; simpl.
    intro; discr. apply IHl.
  Qed.

  Lemma nth_map_none_rev : forall (l : list A) i (f: A -> A),
    nth_error (map f l) i = None -> nth_error l i = None.

  Proof.
    induction l.
    trivial.
    intros i f; destruct i; simpl.
    intro; discr.
    apply IHl.
  Qed.

  Lemma nth_map_some : forall (l : list A) i (f: A -> A) a,
    nth_error l i = Some a -> nth_error (map f l) i = Some (f a).

  Proof.
    induction l.
    destruct i; intros; discr.
    intros i f a'.
    destruct i; simpl.
    intro aa'; inversion aa'; trivial.
    apply IHl.
  Qed.

  Lemma nth_map_some_rev : forall (l : list A) i (f: A -> A) a,
    nth_error (map f l) i = Some a ->
    exists a', nth_error l i = Some a' /\ f a' = a.

  Proof.
    induction l.
    destruct i; intros; discr.
    intros i f a'.
    destruct i; simpl.
    intros aa'; inversion aa'; exists a; auto.
    apply IHl.
  Qed.

  Lemma nth_error_singleton_in : forall (a b: A) i,
    nth_error (a :: nil) i = Some b -> a = b /\ i = 0.

  Proof.
    intros.
    destruct i.
    inversion H; auto.
    inversion H; destruct i; discr.
  Qed.

End ListsNth.

Arguments In_nth [A] d [x l] _.

(****************************************************************************)
(** Total function returning the [i]th element of a list [ŀ]
if [i < length l]. *)

Unset Strict Implicit.
Set Contextual Implicit.

Section ith.

  Variable A : Type.

  Fixpoint ith (l : list A) : forall i, i < length l -> A :=
    match l as l return forall i, i < length l -> A with
      | nil => fun i H => False_rect A (lt_n_O H)
      | cons x m => fun i =>
        match i return i < S (length m) -> A with
	  | O => fun _ => x
	  | S j => fun H => ith (lt_S_n H)
        end
    end.

  Lemma ith_In : forall l i (h : i < length l), In (ith h) l.

  Proof.
    induction l; simpl; intros. lia. destruct i. auto. right. apply IHl.
  Qed.

  Lemma ith_eq : forall l i (hi : i < length l) j (hj : j < length l),
    i = j -> ith hi = ith hj.

  Proof. intros. subst j. rewrite (lt_unique hi hj). refl. Qed.

  Lemma ith_eq_app : forall m l i (hi : i < length (l++m))
    j (hj : j < length l), i = j -> ith hi = ith hj.

  Proof.
    induction l; simpl; intros. contradict hj; lia. subst j.
    destruct i. refl. apply IHl. refl.
  Qed.

End ith.

Arguments ith_In [A l i] _.

(****************************************************************************)
(** Given a function [f:nat->A] and [j:nat], [values f j] returns the
list [f (j-1); ..; f 0] of the [j] first values of [f] starting from
0 in reverse order. *)

Section values.

  Variables (A : Type) (f : nat -> A).

  Fixpoint values j : list A :=
    match j with
      | 0 => nil
      | S k => f k :: values k
    end.

End values.

(****************************************************************************)
(** Given a function [n:nat] and [f:forall i, i<n -> A], [pvalues n f]
returns the list [f 0; ..; f (n-1)] of the [n] first values of [f]
starting from 0. *)

Section pvalues.

  Variable A : Type.

  Fixpoint pvalues n : (forall i, i < n -> A) -> list A :=
    match n as n return (forall i, i < n -> A) -> list A with
      | 0 => fun _ => nil
      | S k => fun f =>
        f 0 (lt_O_Sn k) :: pvalues (fun i h => f (S i) (lt_n_S h))
    end.

  Lemma pvalues_eq : forall n (f g : forall i, i < n -> A),
    (forall i (hi : i < n), f i hi = g i hi) -> pvalues f = pvalues g.

  Proof.
    induction n; intros; simpl. refl. apply cons_eq. apply H. apply IHn.
    intros. apply H.
  Qed.

End pvalues.

Section pvalues_map.

  Variables (A B : Type) (f : A -> B).

  Definition f_ith (l : list A) i (hi : i < length l) := f (ith hi).

  Lemma pvalues_ith_eq_map : forall l, pvalues (@f_ith l) = map f l.

  Proof.
    induction l; intros; unfold f_ith; simpl. refl. apply tail_eq.
    rewrite <- IHl. apply pvalues_eq. intros. unfold f_ith. f_equal.
    apply ith_eq. refl.
  Qed.

End pvalues_map.

(***********************************************************************)
(** First element satisfying some boolean function. *)

Section first.

  Variable (A : Type) (f : A -> bool).

  Fixpoint first l :=
    match l with
      | nil => None
      | x :: l' => if f x then Some x else first l'
    end.

End first.

(***********************************************************************)
(** Properties of [fold_left]. *)

#[global] Instance transpose_inclusion A B :
  Proper (inclusion ==> eq ==> impl) (@transpose A B).

Proof. intros R R' RR' f f' ff' h x y z. subst f'. apply RR'. apply h. Qed.

#[global] Instance transpose_same A B : Proper (same ==> eq ==> iff) (@transpose A B).

Proof.
  intros R R' [h1 h2] f f' ff'. subst f'.
  split; apply transpose_inclusion; auto.
Qed.

Section fold_left.

  Variables (A : Type) (eqA : relation A) (B : Type) (eqB : relation B).

  Definition feq f f' :=
    forall a a', eqA a a' -> forall b b', eqB b b' -> eqA (f a b) (f' a' b').

  Global Instance fold_left_m_ext :
    Proper (feq ==> eqlistA eqB ==> eqA ==> eqA) (@fold_left A B).

  Proof.
    intros f f' ff' l l' ll' a a' aa'. revert l l' ll' a a' aa'.
    induction l; destruct l'; intros; simpl.
    hyp. inversion ll'. inversion ll'.
    inversion ll'. subst. apply IHl. hyp. apply ff'; hyp.
  Qed.

End fold_left.

Section fold_left_list.

  Variables (A B : Type) (f : list A -> B -> list A).

  Variable g : B -> list A.

  Variable hyp : forall l b, f l b = g b ++ l.

  Lemma fold_left_flat_map : forall bs l,
    fold_left f bs l = flat_map g (rev bs) ++ l.

  Proof.
    induction bs; simpl; intro. refl.
    rewrite IHbs, hyp, flat_map_app, app_ass. simpl.
    rewrite <- app_nil_end. refl.
  Qed.

  Lemma In_fold_left : forall a bs l,
    In a (fold_left f bs l) <-> (In a l \/ exists b, In b bs /\ In a (g b)).

  Proof.
    intros. rewrite fold_left_flat_map, in_app, in_flat_map.
    intuition. destruct H0. right. exists x. rewrite In_rev. hyp.
    destruct H0. left. exists x. rewrite <- In_rev. hyp.
  Qed.

End fold_left_list.

Arguments fold_left_flat_map [A B f] _ _ _ _.
Arguments In_fold_left [A B f] _ _ _ _ _.

(****************************************************************************)
(** [lookup el default l] takes an association list of pairs of keys
and values, and returns [v] such that [(el, v)] belongs to the list,
or [default] if there is no element with key equal to [el]. *)

Section lookup.

  Variable (A B : Type).
  Variable (eqA_dec : forall x y : A, {x = y} + {x <> y}).
  Variable (el : A). 
  Variable (default : B).

  Fixpoint lookup (l : list (A * B)) : B :=
    match l with
    | nil => default
    | (el', v)::l' => 
        if @eqA_dec el el' then
          v
        else
          lookup l'
    end.

  Variable P : B -> Prop.

  Lemma lookup_prop l : 
    (forall x, In x l -> P (snd x)) -> P default -> P (lookup l).
  Proof with auto with datatypes.
    induction l; intros...
    simpl. destruct a. destruct (@eqA_dec el a).
    apply (H (a, b))...
    apply IHl...
  Qed.

End lookup.

(****************************************************************************)
(** [lookup_dep] is equivalent to [lookup] above but works on lists of
dependent pairs instead. *)

Section lookup_dep.

  Variable (A : Type) (B : A -> Type).
  Variable (eqA_dec : forall x y : A, {x = y} + {x <> y}).
  Variable (el : A).
  Variable (default : forall a : A, B a).

  Program Fixpoint lookup_dep (l : list { el : A & B el}) : B el :=
    match l with
    | nil => @default el
    | x::l' => 
        let (el', v) := x in
        if @eqA_dec el el' then
          v
        else
          lookup_dep l'
    end.

  Variable P : forall a : A, B a -> Prop.

  Lemma lookup_dep_prop (l : list {el : A & B el}) : 
    (forall x, In x l -> P (projT2 x)) -> 
    (forall a : A, P (@default a)) -> P (lookup_dep l).

  Proof with auto with datatypes.
    induction l; intros.
    apply H0.
    simpl. destruct a. destruct (@eqA_dec el x).

    unfold eq_rect, lookup_dep_obligation_1.
    set (w := eq_ind_r (fun el => x = el) eq_refl e).
    dependent inversion w.

    apply (H (existT b))...
    apply IHl...
  Qed.

End lookup_dep.

(****************************************************************************)
(** Properties of [forallb]. *)

Section forallb.

  Variables (A : Type) (P : A -> Prop)
    (f : A -> bool) (f_ok : forall x, f x = true <-> P x).

  Lemma forallb_false : forall l,
    forallb f l = false <-> exists x, In x l /\ f x = false.

  Proof.
    induction l; simpl. intuition. destruct H. intuition.
    rewrite andb_eq_false, IHl. intuition.
    exists a. tauto. destruct H0. exists x. tauto.
    destruct H1. intuition. subst. tauto. right. exists x. tauto.
  Qed.

  Lemma forallb_neg : forall l,
    forallb f l = false <-> exists x, In x l /\ ~P x.

  Proof.
    intro l. rewrite forallb_false. split; intro.
    do 2 destruct H. exists x. rewrite <- (ko (@f_ok)). tauto.
    do 2 destruct H. exists x. rewrite (ko (@f_ok)). tauto.
  Qed.

  Variables (As : list A) (As_ok : forall x, In x As).

  Lemma forallb_ok_fintype : forallb f As = true <-> forall x, P x.

  Proof.
    split; intro H.
    intro x. rewrite <- f_ok. rewrite forallb_forall in H. apply H. apply As_ok.
    rewrite forallb_forall. intros x hx. rewrite f_ok. apply H.
  Qed.

End forallb.

(****************************************************************************)
(** [sub_list l k n] is the sublist of [l] of length [n] starting at
position [k]. *)

Section sub_list.

  Variable A : Type.

  Fixpoint sub_list l k n : list A :=
    match l, k, n with
      | _ :: l', S k', _ => sub_list l' k' n
      | x :: l', 0, S n' => x :: sub_list l' 0 n'
      | _, _, _ => nil
    end.

  Functional Scheme sub_list_ind := Induction for sub_list Sort Prop.

  Lemma sub_list_ok : forall l k n i,
    k < length l -> k+n <= length l -> i < n ->
    element_at (sub_list l k n) i = element_at l (k+i).

  Proof.
    intros l k n. functional induction (sub_list l k n); simpl; intros.
    refl. lia. destruct i. refl. apply IHl0; try lia.
    apply IHl0; lia.
  Qed.

  Lemma length_sub_list : forall l k n,
    k < length l -> k+n <= length l -> length (sub_list l k n) = n.

  Proof.
    intros l k n. functional induction (sub_list l k n); simpl; intros.
    lia. lia.
    destruct l'. simpl in *. lia. rewrite IHl0; simpl in *; lia.
    rewrite IHl0; lia.
  Qed.

  Lemma eq_app_elim_l : forall l1 l l2,
    l = l1 ++ l2 -> l1 = sub_list l 0 (length l1).

  Proof.
    induction l1; destruct l; simpl; intros. refl. refl. discr.
    inversion H. subst. apply tail_eq. eapply IHl1. refl.
  Qed.

  Lemma eq_app_elim_r : forall l1 l l2,
    l = l1 ++ l2 -> l2 = sub_list l (length l1) (length l2).

  Proof.
    induction l1; simpl; intros. subst l2.
    induction l; simpl; intros. refl. rewrite <- IHl. refl.
    destruct l. discr. inversion H. subst. simpl. apply IHl1. refl.
  Qed.

  Lemma sub_list_0 : forall l k, sub_list l k 0 = nil.

  Proof.
    induction l; induction k; simpl; auto.
  Qed.

  Lemma sub_list_length : forall l, sub_list l 0 (length l) = l.

  Proof.
    induction l; simpl; intros. refl. rewrite IHl. refl.
  Qed.

  Lemma app_eq_sub_list : forall l1 l2, l1++l2 =
    sub_list (l1++l2) 0 (length l1)
    ++ sub_list (l1++l2) (length l1) (length l2).

  Proof.
    induction l1; simpl; intros. rewrite sub_list_0, sub_list_length.
    refl. rewrite <- IHl1. refl.
  Qed.

End sub_list.

Arguments eq_app_elim_l [A l1 l l2] _.
Arguments eq_app_elim_r [A l1 l l2] _.

(****************************************************************************)
(** [lforall] checks whether a predicate is satisfied by every element. *)

Section lforall.

  Variables (A : Type) (P : A->Prop).

  Fixpoint lforall (l : list A) : Prop :=
    match l with
    | nil => True
    | cons h t => P h /\ lforall t
    end.

  Lemma lforall_eq : forall l, lforall l <-> (forall x, In x l -> P x).

  Proof. induction l; simpl; intuition. subst. hyp. Qed.

  Lemma lforall_nil : lforall nil.

  Proof. simpl. auto. Qed.

  Lemma lforall_cons a l : lforall (cons a l) -> P a /\ lforall l.

  Proof. auto. Qed.

  Lemma lforall_app l2 : forall l1 : list A,
      lforall (l1 ++ l2) <-> lforall l1 /\ lforall l2.

  Proof. induction l1; simpl; intuition. Qed.

  Lemma lforall_in a l : lforall l -> In a l -> P a.

  Proof.
    elim l.
    intros H1 H2. absurd (In a nil); [apply in_nil | hyp].
    intros b l' Hrec H1 H2. elim (in_inv H2).
    intro H3. subst a. unfold lforall in H1. intuition.
    clear H2. intro H2. gen (lforall_cons H1).
    intros (H3, H4). apply (Hrec H4 H2).
  Qed.

  Lemma lforall_intro : forall l, (forall x, In x l -> P x) -> lforall l.

  Proof.
    induction l; simpl; intros. exact I. split. apply H. auto.
    apply IHl. intros. apply H. auto.
  Qed.

  Lemma lforall_incl l1 l2 : l1 [= l2 -> lforall l2 -> lforall l1.

  Proof.
    intros. apply lforall_intro. intros. eapply lforall_in. apply H0.
    apply H. hyp.
  Qed.

  Lemma forallb_imp_lforall f : forall l,
      (forall x, f x = true -> P x) -> forallb f l = true -> lforall l.

  Proof with auto.
    induction l; simpl; intros...
    split.
    apply H. destruct (f a)...
    destruct (f a)... discr.
  Qed.

  Lemma forallb_lforall f (fok : forall x, f x = true <-> P x) :
    forall l, forallb f l = true <-> lforall l.

  Proof. induction l; simpl. tauto. rewrite andb_eq, fok. intuition. Qed.

  Variable P_dec : forall x, {P x}+{~P x}.

  Lemma lforall_dec : forall l, {lforall l} + {~lforall l}.

  Proof.
    induction l.
    left. simpl. trivial.
    simpl. destruct (@P_dec a). 
    destruct IHl.
    left; auto.
    right; intuition.
    right; intuition.
  Defined.

End lforall.

Arguments lforall_in [A P a l] _ _.

Lemma lforall_imp A (P1 P2 : A->Prop) :
  (forall x, P1 x -> P2 x) -> forall l, lforall P1 l -> lforall P2 l.

Proof.
intros H l. elim l.
 intuition.
 intros a' l' Hrec. simpl. intros (H1, H2). split.
  apply H. hyp.
  apply Hrec. hyp.
Qed.
