(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Stephane Le Roux, 2006-10-17
- Adam Koprowski, 2006-04-28
- Solange Coupet-Grimal and William Delobel, 2006-01-09
- Frederic Blanqui, 2005-02-03, 2009-07-06
- Sebastien Hinderer, 2004-05-25

extension of the Coq library on lists
*)

Set Implicit Arguments.

Require Import LogicUtil.
Require Export List.
Require Import NatUtil.
Require Import EqUtil.
Require Import Setoid.

Implicit Arguments in_app_or [A l m a].
Implicit Arguments in_map [A B l x].
Implicit Arguments in_combine_l [A B l l' x y].
Implicit Arguments in_combine_r [A B l l' x y].

Ltac elt_type l :=
  match type of l with
    | list ?A => A
  end.

Infix "[=" := incl (at level 70).

(***********************************************************************)
(** membership *)

Section In.

Variable A : Type.

Lemma in_app : forall l m (x : A), In x (l ++ m) <-> In x l \/ In x m.

Proof.
intuition.
Qed.

Lemma notin_app : forall l m (x : A), ~In x (l ++ m) <-> ~In x l /\ ~In x m.

Proof.
intuition. rewrite in_app in H0. intuition.
Qed.

Lemma in_appl : forall (x : A) l1 l2, In x l1 -> In x (l1 ++ l2).

Proof.
induction l1; simpl; intros. contradiction. destruct H. subst x. auto.
right. apply IHl1. hyp.
Qed.

Lemma in_appr : forall (x : A) l1 l2, In x l2 -> In x (l1 ++ l2).

Proof.
induction l1; simpl; intros. hyp. right. apply IHl1. hyp.
Qed.

Lemma in_app_com : forall (x : A) l1 l2 l3,
  In x ((l1 ++ l3) ++ l2) -> In x ((l1 ++ l2) ++ l3).

Proof.
intros. repeat rewrite in_app in H. intuition.
Qed.

Lemma in_elim : forall (x : A) l,
  In x l -> exists l1, exists l2, l = l1 ++ x :: l2.

Proof.
induction l; simpl; intros. contradiction. destruct H. subst x.
exists (@nil A). exists l. refl. ded (IHl H). do 2 destruct H0. rewrite H0.
exists (a :: x0). exists x1. refl.
Qed.

Variable eqA_dec : forall x y : A, {x=y}+{~x=y}.

Lemma in_elim_dec : forall (x : A) l,
  In x l -> exists m, exists p, l = m ++ x :: p /\ ~In x m.

Proof.
induction l; simpl; intros. contradiction. destruct H. subst x.
exists (@nil A). exists l. intuition. ded (IHl H). do 3 destruct H0. subst l.
case (eqA_dec a x); intro.
subst x. exists (@nil A). exists (x0 ++ a :: x1). intuition.
exists (a :: x0). exists x1. intuition. simpl in H2. destruct H2; auto.
Qed.

Require Import RelMidex.

Lemma In_midex : eq_midex A -> forall (x : A) l, In x l \/ ~In x l. 

Proof.
induction l. tauto. simpl. destruct (H a x); destruct IHl; tauto.
Qed.

Lemma In_elim_right : eq_midex A -> forall (x : A) l,
  In x l -> exists l', exists l'', l = l'++x::l'' /\ ~In x l''. 

Proof.
induction l; simpl; intros. contradiction. 
destruct (In_midex H x l). destruct IHl. hyp. destruct H2. 
exists (a::x0). exists x1. rewrite (proj1 H2).
rewrite <- (app_comm_cons x0 (x::x1) a). tauto.  
destruct H0. exists (nil : list A). exists l. simpl. rewrite H0. tauto.
contradiction.
Qed.

Lemma In_cons : forall (x a : A) l, In x (a::l) <-> a=x \/ In x l. 

Proof.
intros. simpl. tauto.
Qed.

End In.

Implicit Arguments in_elim [A x l].
Implicit Arguments in_elim_dec [A x l].

Ltac intac := repeat (apply in_eq || apply in_cons).

Ltac list_ok := let x := fresh in intro x;
  match goal with
    | |- In _ ?l => vm_compute; destruct x; tauto
  end.

(***********************************************************************)
(** inclusion *)

Add Parametric Relation (A : Type) : (list A) (@incl A)
  reflexivity proved by (@incl_refl A)
  transitivity proved by (@incl_tran A)
    as incl_rel.

Add Parametric Morphism (A : Type) : (@app A)
  with signature (@incl A) ==> (@incl A) ==> (@incl A)
    as app_incl.

Proof.
intros. unfold incl. intro. repeat rewrite in_app. intuition.
Qed.

Section incl.

Variable A : Type.

Lemma incl_nil_elim : forall l : list A, l [= nil <-> l = nil.

Proof.
unfold incl. destruct l; intuition. assert (In a (a::l)). left. refl.
ded (H _ H0). contradiction. discr.
Qed.

Lemma incl_nil : forall l : list A, nil [= l.

Proof.
induction l. apply incl_refl. apply incl_tl. hyp.
Qed.

Lemma incl_cons_l : forall (a : A) l m, a :: l [= m -> In a m /\ l [= m.

Proof.
intros a l m. unfold incl. simpl. intuition.
Qed.

Lemma incl_cons_l_in : forall (x : A) l m, x :: l [= m -> In x m.

Proof.
unfold incl. simpl. intros. apply H. left. refl.
Qed.

Lemma incl_cons_l_incl : forall (x : A) l m, x :: l [= m -> l [= m.

Proof.
unfold incl. simpl. intros. apply H. tauto.
Qed.

Lemma incl_app_elim : forall l1 l2 l3 : list A,
  l1 ++ l2 [= l3 -> l1 [= l3 /\ l2 [= l3.

Proof.
intuition.
apply incl_tran with (l1 ++ l2). apply incl_appl. apply incl_refl. exact H.
apply incl_tran with (l1 ++ l2). apply incl_appr. apply incl_refl. exact H.
Qed.

Lemma incl_appr_incl : forall l1 l2 l3 : list A, l1 ++ l2 [= l3 -> l1 [= l3.

Proof.
induction l1; simpl; intros. apply incl_nil.
eapply incl_tran with (m := a :: l1 ++ l2). 2: hyp.
apply (incl_appl l2 (incl_refl (a :: l1))).
Qed.

Lemma incl_appl_incl : forall l1 l2 l3 : list A, l1 ++ l2 [= l3 -> l2 [= l3.

Proof.
induction l1; simpl; intros. hyp.
eapply incl_tran with (m := a :: l1 ++ l2). 2: hyp.
apply (incl_appr (a :: l1) (incl_refl l2)).
Qed.

Lemma appl_incl : forall l l2 l2' : list A, l2 [= l2' -> l ++ l2 [= l ++ l2'.

Proof.
intros. apply app_incl. apply incl_refl. exact H.
Qed.

Lemma appr_incl : forall l l1 l1' : list A, l1 [= l1' -> l1 ++ l [= l1' ++ l.

Proof.
intros. apply app_incl. exact H. apply incl_refl.
Qed.

Lemma app_com_incl : forall l1 l2 l3 l4 : list A,
  (l1 ++ l3) ++ l2 [= l4 -> (l1 ++ l2) ++ l3 [= l4.

Proof.
unfold incl. intros. apply H. apply in_app_com. exact H0.
Qed.

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
intuition. absurd (nil[=m). hyp. apply incl_nil.
do 2 destruct H. contradiction.
split; intro.
Focus 2. do 3 destruct H.
subst. intro. apply H0. apply H. left. refl.
intro. absurd (In x m). hyp. apply H1. right. hyp.
case (In_dec eqA_dec a m); intro.
assert (~l[=m). intro. apply H. unfold incl. intro b. simpl. intuition.
subst. hyp. rewrite IHl in H0. do 2 destruct H0. exists x. tauto.
exists a. tauto.
Qed.

End incl.

Implicit Arguments incl_app_elim [A l1 l2 l3].

(***********************************************************************)
(** strict inclusion *)

Definition strict_incl A (l m : list A) := l [= m /\ ~m [= l.

Infix "[" := strict_incl (at level 70).

Lemma strict_incl_tran : forall A (l m n : list A), l [ m -> m [ n -> l [ n.

Proof.
unfold strict_incl. intuition. transitivity m; hyp.
apply H2. transitivity n; hyp.
Qed.

Add Parametric Relation (A : Type) : (list A) (@strict_incl A)
  transitivity proved by (@strict_incl_tran A)
    as strict_incl_rel.

(***********************************************************************)
(** equivalence *)

Section equiv.

Variable A : Type.

Definition lequiv (l1 l2 : list A) : Prop := l1 [= l2 /\ l2 [= l1.

Lemma lequiv_refl : forall l, lequiv l l.

Proof.
intro. split; apply incl_refl.
Qed.

Lemma lequiv_sym : forall l1 l2, lequiv l1 l2 -> lequiv l2 l1.

Proof.
intros. destruct H. split; hyp.
Qed.

Lemma lequiv_trans :
  forall l1 l2 l3, lequiv l1 l2 -> lequiv l2 l3 -> lequiv l1 l3.

Proof.
intros. destruct H. destruct H0. split. eapply incl_tran. apply H. hyp.
eapply incl_tran. apply H2. hyp.
Qed.

End equiv.

Infix "[=]" := lequiv (at level 70).

Add Parametric Relation (A : Type) : (list A) (@lequiv A)
  reflexivity proved by (@lequiv_refl A)
  symmetry proved by (@lequiv_sym A)
    transitivity proved by (@lequiv_trans A)
    as lequiv_rel.

Add Parametric Morphism (A : Type) : (@app A)
  with signature (@lequiv A) ==> (@lequiv A) ==> (@lequiv A)
    as app_lequiv.

Proof.
unfold lequiv. intuition.
Qed.

(***********************************************************************)
(** empty list *)

Section nil.

Variable A : Type.

Lemma list_empty_dec : forall l : list A, {l = nil} + {l <> nil}.

Proof.
destruct l; auto. right; congruence.
Qed.

Definition is_empty (l : list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.

End nil.

(***********************************************************************)
(** cons *)

Add Parametric Morphism (A : Type) : (@cons A)
  with signature (@eq A) ==> (@incl A) ==> (@incl A)
    as incl_double_cons.

Proof.
firstorder.
Qed.

Add Parametric Morphism (A : Type) : (@cons A)
  with signature (@eq A) ==> (@lequiv A) ==> (@lequiv A)
    as cons_lequiv.

Proof.
firstorder.
Qed.

Section cons.

Variable A : Type.

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

Variable A : Type.

Lemma length_app : forall l m : list A, length (l ++ m) = length l + length m.

Proof.
induction l; simpl; intros. refl. rewrite IHl. refl.
Qed.

Lemma app_nil : forall l1 l2 : list A, l1 = nil -> l2 = nil -> l1 ++ l2 = nil.

Proof.
intros. subst l1. subst l2. refl.
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

Lemma list_app_first_last : forall l m (a : A), (l ++ a::nil) ++ m = l ++ a::m.

Proof.
induction l.
auto.
intros m a'.
repeat rewrite <- app_comm_cons.
destruct (IHl m a'); trivial.
Qed.

Lemma list_app_last : forall l m n (a : A),
  l ++ m = n ++ a::nil -> m <> nil -> In a m.

Proof.
intros l m n; generalize n l m; clear l m n.
induction n; simpl; intros.
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
(* n = nil -> contradiction *)
simpl in H.
destruct (app_eq_unit (a::l) m H) as 
  [[l_nil r_unit] | [l_unit r_nil]]; try contradiction.
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
induction l; simpl; intros. apply False_ind. omega.
destruct l. exists (@nil A). exists a. intuition.
assert (length (a0::l) > 0). simpl. omega.
ded (IHl H0). do 3 destruct H1.
exists (a::x). exists x0. split. rewrite H1. refl.
simpl. simpl in H2. omega.
Qed.

End app.

(***********************************************************************)
(** length *)

Section length.

Variable A : Type.

Lemma length_0 : forall l : list A, length l = 0 -> l = nil.

Proof.
intros. destruct l. refl. discr.
Qed.

End length.

Implicit Arguments length_0 [A l].

(***********************************************************************)
(** head & tail *)

Section head_tail.

Variable A : Type.

Lemma head_app : forall (l l': list A)(lne: l <> nil), head (l ++ l') = head l.

Proof.
destruct l. tauto. auto.
Qed.

Require Import Omega.

Lemma length_tail : forall l : list A, length (tail l) <= length l.

Proof.
induction l; simpl; intros; omega.
Qed.

Lemma tail_in : forall (x: A) l, In x (tail l) -> In x l.

Proof.
intros. destruct l; auto with datatypes.
Qed.

Lemma tail_cons_tail : forall (l1 l2: list A),
  l1 <> nil -> tail l1 ++ l2 = tail (l1 ++ l2).

Proof.
destruct l1. tauto. auto.
Qed.

Lemma length_tail_minus : forall (l : list A), length (tail l) = length l - 1.

Proof.
destruct l; simpl; omega.
Qed.

Lemma list_decompose_head : forall (l : list A) el (lne: l <> nil),
  head l = Some el -> l = el :: tail l.

Proof.
intros. destruct l. discr. inversion H. rewrite <- H1; trivial.
Qed.

Lemma in_head_tail : forall a (l : list A),
  In a l -> Some a = head l \/ In a (tail l).

Proof.
induction l; intros; inversion H.
left; simpl; rewrite H0; trivial.
right; trivial.
Qed.

Lemma head_notNil : forall (l : list A) (lne : l <> nil),
  {a : A | head l = Some a}.

Proof.
  destruct l. tauto. exists a; auto.
Defined.

Lemma head_of_notNil : forall (l : list A) a (lne: l <> nil),
  head l = Some a -> proj1_sig (head_notNil lne) = a.

Proof.
intros. destruct l; try discr. simpl; inversion H; trivial.
Qed.

End head_tail.

Hint Resolve tail_in tail_cons_tail head_app : datatypes.
Hint Rewrite head_app length_app : datatypes.

(***********************************************************************)
(** tail_nth *)

Section tail_nth.

Variable A : Type.

Fixpoint tail_nth (l : list A) (n : nat) {struct n} : option (list A) :=
  match l, n with
    | _, 0 => Some l
    | a :: l', S n' => tail_nth l' n'
    | _, _ => None
  end.

End tail_nth.

(***********************************************************************)
(** list filtering *)

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
right. intuition. gen H. case (f x). irrefl. refl. auto.
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
(** boolean membership when the equality on A is decidable *)

Section Inb.

Variable A : Type.
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
induction l; simpl. intro. discr. case (eq_dec x a); auto.
Qed.

Lemma Inb_false : forall x l, Inb x l = false -> In x l -> False.

Proof.
induction l; simpl. intros. contradiction. case (eq_dec x a).
intros. discr. intros. destruct H0; auto.
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
intros. destruct H. case_eq (Inb x l'); case_eq (Inb x l); try refl.
ded (Inb_incl _ H0 H1). rewrite H2 in H3. discr.
ded (Inb_incl _ H H2). rewrite H1 in H3. discr.
Qed.

Definition Inclb (l1 l2 : list A) := forallb (fun x => Inb x l2) l1.

Lemma Inclb_ok : forall l1 l2, Inclb l1 l2 = true <-> l1 [= l2.

Proof.
intros. induction l2. unfold Inclb. simpl. case l1. simpl; split; auto.
intro; apply incl_refl.
intros. simpl; split; intro. discriminate H.
rewrite incl_nil_elim in H. discriminate H.
split; unfold Inclb; simpl; rewrite forallb_forall; intro.
intros x Hx. generalize (H _ Hx). case (eq_dec x a); intros.
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
(** remove *)

Section remove.

Variable A : Type.
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

End remove.

(***********************************************************************)
(** removes *)

Section removes.

Variable (A : Type) (eqdec : forall x y : A, {x=y}+{x<>y}).

Notation In_dec := (In_dec eqdec).

Fixpoint removes (l m : list A) {struct m} : list A :=
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
unfold incl. induction m; simpl. contradiction.
case (In_dec a l). intros. right. apply IHm. hyp.
simpl. intuition.
Qed.

Lemma incl_removes_app : forall l m, m [= removes l m ++ l.

Proof.
unfold incl. induction m; simpl. contradiction. intros. destruct H.
subst a0. case (In_dec a l); intro. apply in_appr. hyp. simpl. auto.
case (In_dec a l); intro. apply IHm. hyp. simpl.
case (eqdec a a0); intro. subst a0. auto. right. apply IHm. hyp.
Qed.

Lemma In_removes : forall x l m, In x (removes l m) <-> In x m /\ ~In x l.

Proof.
induction m; simpl; intros. tauto. case (In_dec a l); intro. rewrite IHm.
firstorder. subst. contradiction. simpl. rewrite IHm. firstorder. subst. hyp.
Qed.

End removes.

(***********************************************************************)
(** map *)

Section map.

Variable (A B : Type) (f : A->B).

Lemma map_app : forall l1 l2, map f (l1 ++ l2) = (map f l1) ++ map f l2.

Proof.
induction l1; simpl; intros. refl. rewrite IHl1. refl.
Qed.

Lemma in_map_elim : forall x l, In x (map f l) -> exists y, In y l /\ x = f y.

Proof.
induction l; simpl; intros. contradiction. destruct H.
exists a. auto. ded (IHl H). do 2 destruct H0. exists x0. auto.
Qed.

Lemma map_eq : forall (g : A->B) l,
  (forall x, In x l -> f x = g x) -> map f l = map g l.

Proof.
induction l; simpl; intros. refl. apply cons_eq. ded (H a). intuition.
apply IHl. intro. ded (H x). intuition.
Qed.

End map.

Implicit Arguments in_map_elim [A B f x l].

Lemma map_eq_id : forall A (f:A->A) l,
  (forall x, In x l -> f x = x) -> map f l = l.

Proof.
induction l; simpl; intros. refl. apply cons_eq. ded (H a). intuition.
apply IHl. intro. ded (H x). intuition.
Qed.

(***********************************************************************)
(** flat_map *)

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

Proof.
induction l; simpl; intros. refl. rewrite IHl. rewrite app_ass. refl.
Qed.

End flat_map.

(***********************************************************************)
(** flattening *)

Section flat.

Variable A : Type.

Fixpoint flat (l : list (list A)) : list A :=
  match l with
    | nil => nil
    | cons x l' => x ++ flat l'
  end.

Lemma In_incl_flat : forall x l, In x l -> x [= flat l.

Proof.
induction l; simpl; intros. contradiction. intuition. subst. apply incl_appl.
apply incl_refl.
Qed.

Lemma incl_flat_In : forall x c cs l,
  In x c -> In c cs -> flat cs [= l -> In x l.

Proof.
intros. apply H1. apply (In_incl_flat _ _ H0). hyp.
Qed.

End flat.

Implicit Arguments In_incl_flat [A x l].

(***********************************************************************)
(** element & replacement at a position *)

Section Element_At_List.
  
  Variable A : Type.
  
  Fixpoint element_at (l : list A) (p : nat) {struct l} : option A := 
    match l with 
      | nil => None
      | h :: t =>
	match p with 
          | 0 => Some h 
          | S p' => element_at t p'
        end
    end.

  Notation "l '[' p ']'" := (element_at l p) (at level 50).

  Fixpoint replace_at (l : list A) (p : nat) (a : A) {struct l} : list A :=
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
ded (IHl n H). intuition; simpl; omega.
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

Implicit Arguments element_at_in [A x l n].
Implicit Arguments element_at_in2 [A x l n].
Implicit Arguments in_exists_element_at [A l a].
Implicit Arguments element_at_exists [A l p].

Notation "l '[' p ']'" := (element_at l p) (at level 50) : list_scope.
Notation "l '[' p ':=' a ']'" := (replace_at l p a) (at level 50) : list_scope.

(***********************************************************************)
(** one_less *)

Section one_less.

  Variable A : Type.

  Require Import Relations.

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
intros. apply incl_tran with (rev l). apply incl_rev.
apply incl_tran with (rev l'). hyp. apply rev_incl.
Qed.

End reverse.

Section reverse_tail_recursive.

Variable A : Type.

Fixpoint rev_append (l' l : list A) {struct l} : list A :=
  match l with
    | nil => l'
    | a :: l => rev_append (a :: l') l
  end.

Notation rev' := (rev_append nil).

Lemma rev_append_rev : forall l l', rev_append l' l = rev l ++ l'.

Proof.
  induction l; simpl; auto; intros. rewrite <- ass_app; firstorder.
Qed.

Lemma rev_append_app : forall l l' acc : list A,
  rev_append acc (l ++ l') = rev_append (rev_append acc l) l'.

Proof.
induction l; simpl; intros. refl. rewrite IHl. refl.
Qed.

Lemma rev'_app : forall l l' : list A, rev' (l ++ l') = rev' l' ++ rev' l.

Proof.
intros. rewrite rev_append_app. repeat rewrite rev_append_rev.
repeat rewrite <- app_nil_end. refl.
Qed.

Lemma rev'_rev : forall l : list A, rev' l = rev l.

Proof.
intro. rewrite rev_append_rev. rewrite <- app_nil_end. refl.
Qed.

Lemma rev'_rev' : forall l : list A, rev' (rev' l) = l.

Proof.
intro. repeat rewrite rev'_rev. apply rev_involutive.
Qed.

Lemma rev'_cons : forall a (l : list A), rev' (a::l) = rev' l ++ (a::nil).

Proof.
intros. change (rev' ((a::nil) ++ l) = rev' l ++ (a::nil)). rewrite rev'_app.
refl.
Qed.

End reverse_tail_recursive.

Notation rev' := (rev_append nil).

(***********************************************************************)
(** split *)

Section split.

Variable A : Type.

Fixpoint split_aux (acc l : list A) (n : nat) {struct n}
  : option (list A * list A) :=
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

Implicit Arguments split_aux_correct [l n l1 l2].

Notation split := (split_aux nil).

Lemma split_correct : forall l n l1 l2,
  split l n = Some (l1, l2) -> l = l1 ++ l2.

Proof.
intros. change (rev' nil ++ l = l1 ++ l2). apply (split_aux_correct _ H).
Qed.

End split.

Notation split := (split_aux nil).

Implicit Arguments split_correct [A l n l1 l2].

(***********************************************************************)
(** last element *)

Section last.

Variable A : Type.

Lemma last_nth : forall (d : A) l, last l d = nth (length l - 1) l d.

Proof.
induction l; simpl; intros. refl. rewrite IHl.
elim l; simpl; intros. refl. destruct l0; simpl. refl. refl.
Qed.

Lemma last_default : forall (d1 : A) d2 l, l <> nil -> last l d1 = last l d2.

Proof.
induction l; simpl; intros. irrefl. destruct l. refl. apply IHl. discr.
Qed.

End last.

Implicit Arguments last_intro [A l].

(***********************************************************************)
(** partition *)

Require Import Bool.

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
(** listfilter *)

Section ListFilter.

Variable A : Type.

Fixpoint listfilter (L : list A) l {struct L} :=
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
destruct i;simpl in H.
simpl.
inversion H;subst.
destruct l;simpl in *. discr.
inversion H0;subst. simpl;left; auto.

destruct l;auto. simpl in H0; discr.
inversion H0.
simpl.
destruct b.
right. eapply IHL;eauto.
eapply IHL;eauto.
Qed.

End ListFilter.

(****************************************************************************)
(** nth_error *)

Section ListsNth.

  Variable A: Type.

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
    contradiction.
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
    absurd_arith.
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
    absurd_arith.
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
    absurd_arith.
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
    destruct i; intro; elimtype False; auto.
    intro; absurd_arith.
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

  Proof.
    intros.
    apply (proj1 (nth_in l n)).
    rewrite H; discr.
  Qed.

  Lemma nth_map_none : forall (l : list A) i (f: A -> A),
    nth_error l i = None -> nth_error (map f l) i = None.

  Proof. 
    induction l.
    trivial.
    intros i f; destruct i; simpl.
    intro; discr.
    apply IHl.
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

(****************************************************************************)
(** ith *)

Unset Strict Implicit.
Set Contextual Implicit.

Section ith.

Variable A : Type.

Fixpoint ith (l : list A) : forall i, i < length l -> A :=
  match l as l return forall i, i < length l -> A with
    | nil => fun i H => False_rect A (lt_n_O i H)
    | cons x m => fun i =>
      match i return i < S (length m) -> A with
	| O => fun _ => x
	| S j => fun H => ith (lt_S_n H)
      end
  end.

Lemma ith_In : forall l i (h : i < length l), In (ith h) l.

Proof.
induction l; simpl; intros. omega. destruct i. auto. right. apply IHl.
Qed.

Lemma ith_eq : forall l i (hi : i < length l) j (hj : j < length l),
  i = j -> ith hi = ith hj.

Proof.
intros. subst j. rewrite (lt_unique hi hj). refl.
Qed.

Lemma ith_eq_app : forall m l i (hi : i < length (l++m)) j (hj : j < length l),
  i = j -> ith hi = ith hj.

Proof.
induction l; simpl; intros. contradict hj; omega. subst j.
destruct i. refl. apply IHl. refl.
Qed.

End ith.

Implicit Arguments ith_In [A l i].

(****************************************************************************)
(** list of values of a function *)

Section values.

Variables (A : Type) (f : nat -> A).

Fixpoint values j : list A :=
  match j with
    | 0 => nil
    | S k => f k :: values k
  end.

End values.

(****************************************************************************)
(** list of values of a partial function *)

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
rewrite <- IHl. apply pvalues_eq. intros. unfold f_ith. apply (f_equal f).
apply ith_eq. refl.
Qed.

End pvalues_map.

(***********************************************************************)
(** lists of bounded natural numbers *)

Definition nat_lts n := list (nat_lt n).

Lemma in_map_val : forall n (l : nat_lts n) i, In i (map (@val n) l) -> i<n.

Proof.
intros. destruct (in_map_elim H). destruct H0. subst. destruct x. simpl. hyp.
Qed.

Implicit Arguments in_map_val [n l i].

Section mk_nat_lts.

  Variable n : nat.

  Lemma mk_nat_lts_aux1 : forall k', S k' < n -> k' < n.

  Proof.
    intros. omega.
  Qed.

  (* mk_nat_lts_aux hk = k :: ... :: 0 *)

  Fixpoint mk_nat_lts_aux k :=
    match k as k return k<n -> list (nat_lt n) with
      | 0 => fun h => mk_nat_lt h :: nil
      | S k' => fun h => mk_nat_lt h :: mk_nat_lts_aux k' (mk_nat_lts_aux1 h)
    end.

  Lemma mk_nat_lts_aux_correct : forall x k (h : k<n) i,
    i <= k -> val (nth i (mk_nat_lts_aux h) x) = k - i.

  Proof.
    induction k; simpl; intros; destruct i. auto. absurd_arith.
    auto. rewrite IHk. auto. omega.
  Qed.

  Lemma mk_nat_lts_aux_complete : forall k (h : k<n) i (p : i<n),
    i <= k -> In (mk_nat_lt p) (mk_nat_lts_aux h).

  Proof.
    induction k; simpl; intros.
    assert (i=0). omega. subst. assert (h=p). apply lt_unique. subst. auto.
    destruct (lt_ge_dec i (S k)). right. apply IHk. omega.
    assert (i=S k). omega. subst. assert (h=p). apply lt_unique. subst. auto.
  Qed.

End mk_nat_lts.

Implicit Arguments mk_nat_lts_aux [].

(* mk_nat_lts n = n-1 :: ... :: 0 *)

Definition mk_nat_lts n :=
  match n return list (nat_lt n) with
    | 0 => nil
    | S p => mk_nat_lts_aux (S p) p (le_n (S p))
  end.

Implicit Arguments mk_nat_lts [].

Lemma mk_nat_lts_correct : forall n x i,
  i < n -> val (nth i (mk_nat_lts n) x) = pred n - i.

Proof.
intros. unfold mk_nat_lts. destruct n. absurd_arith.
apply mk_nat_lts_aux_correct. omega.
Qed.

Lemma mk_nat_lts_complete : forall n i (p : i<n),
  In (mk_nat_lt p) (mk_nat_lts n).

Proof.
intros. unfold mk_nat_lts. destruct n. absurd_arith.
apply mk_nat_lts_aux_complete. omega.
Qed.

(***********************************************************************)
(** first element satisfying some boolean predicate *)

Section first.

Variable (A : Type) (f : A -> bool).

Fixpoint first l :=
  match l with
    | nil => None
    | x :: l' => if f x then Some x else first l'
  end.

End first.

(***********************************************************************)
(** fold_left *)

Section fold_left.

Variable (A B : Type) (f : list A -> B -> list A).

Variable g : B -> list A.

Variable hyp : forall l b, f l b = g b ++ l.

Lemma fold_left_flat_map : forall bs l,
  fold_left f bs l = flat_map g (rev bs) ++ l.

Proof.
induction bs; simpl; intro. refl.
rewrite IHbs. rewrite hyp. rewrite flat_map_app. rewrite app_ass. simpl.
rewrite <- app_nil_end. refl.
Qed.

Lemma In_fold_left : forall a bs l,
  In a (fold_left f bs l) <-> (In a l \/ exists b, In b bs /\ In a (g b)).

Proof.
intros. rewrite fold_left_flat_map. rewrite in_app. rewrite in_flat_map.
intuition. destruct H0. right. exists x. rewrite In_rev. hyp.
destruct H0. left. exists x. rewrite <- In_rev. hyp.
Qed.

End fold_left.

Implicit Arguments fold_left_flat_map [A B f].
Implicit Arguments In_fold_left [A B f].

(****************************************************************************)
(** checking a boolean property [P 0 && ... && P (n-1)], where the domain of
    the predicate P is restricted to numbers smaller than [n]. *)

Require Import Program.

Section Check_seq_aux.

Variables (n : nat) (Pr : nat_lt n -> Prop)
  (P : forall i : nat_lt n, Exc (Pr i)).

Program Fixpoint check_seq_aux p (H : forall i : nat_lt n, val i < p -> Pr i)
  {measure (n - p)} : Exc (forall i : nat_lt n, Pr i) :=
  match le_lt_dec n p with
  | left _ => value _
  | right cmp =>
    match @P (mk_nat_lt cmp) with
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

Program Definition check_seq (n : nat) (Pr : nat_lt n -> Prop)
  (P : forall (i : nat_lt n), Exc (Pr i)) :
  Exc (forall (i : nat_lt n), Pr i) :=
  check_seq_aux P (p:=0) _.

Next Obligation.
Proof.
  elimtype False. omega.
Qed.

(****************************************************************************)
(** [lookup el default l] takes an association list of pairs of keys, values
    and returns [v] such that [(el, v)] belongs to the list, or [default]
    if there is no element with key equal to [el]. *)

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
    set (w := eq_ind_r (fun el => x = el) refl_equal e).
    dependent inversion w.

    apply (H (existT (fun x:A => B x) x b))...
    apply IHl...
  Qed.

End lookup_dep.

(****************************************************************************)
(** forallb *)

Require Import BoolUtil.

Section forallb.

Variables (A : Type) (P : A -> Prop)
  (f : A -> bool) (f_ok : forall x, f x = true <-> P x).

Lemma forallb_false : forall l,
  forallb f l = false <-> exists x, In x l /\ f x = false.

Proof.
induction l; simpl. intuition. destruct H. intuition.
rewrite andb_eq_false. rewrite IHl. intuition.
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
(** sub_list *)

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
refl. absurd_arith. destruct i. refl. apply IHl0; try omega.
apply IHl0; omega.
Qed.

Lemma length_sub_list : forall l k n,
  k < length l -> k+n <= length l -> length (sub_list l k n) = n.

Proof.
intros l k n. functional induction (sub_list l k n); simpl; intros.
omega. omega.
destruct l'. simpl in *. omega. rewrite IHl0; simpl in *; omega.
rewrite IHl0; omega.
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
  sub_list (l1++l2) 0 (length l1) ++ sub_list (l1++l2) (length l1) (length l2).

Proof.
induction l1; simpl; intros. rewrite sub_list_0. rewrite sub_list_length. refl.
rewrite <- IHl1. refl.
Qed.

End sub_list.

Implicit Arguments eq_app_elim_l [A l1 l l2].
Implicit Arguments eq_app_elim_r [A l1 l l2].

(****************************************************************************)
(** natural numbers from n-1 to 0 *)

Fixpoint nats_decr_lt n :=
  match n with
    | 0 => nil
    | S n' => n' :: nats_decr_lt n'
  end.

Definition nats_incr_lt n := rev' (nats_decr_lt n).
