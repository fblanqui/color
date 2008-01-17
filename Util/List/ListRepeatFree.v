(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-16
- Stephane Le Roux, 2006-10-17

lists without duplications
*)

Set Implicit Arguments.

Section S.

Require Export ListUtil.
Require Export Arith.
Require Export RelMidex. 

Variable A : Type.

(***********************************************************************)
(** predicate saying if a list has no duplicated elements *)

Fixpoint repeat_free (l : list A) : Prop :=
  match l with
    | nil => True
    | a::l' => ~In a l' /\ repeat_free l'
  end.

Lemma repeat_free_app_elim_right : forall l l' ,
  repeat_free (l++l') -> repeat_free l'. 

Proof.
induction l; simpl; intros. assumption. apply IHl. tauto. 
Qed.

Lemma repeat_free_incl_length : eq_midex A -> forall l l',
  repeat_free l -> incl l l' -> length l <= length l'.

Proof.
induction l; simpl; intros. apply le_O_n. 
destruct (In_elim_right H a l'). apply H1. simpl. tauto. destruct H2.
rewrite (proj1 H2). 
rewrite (length_app x (a::x0)). assert (length l <= length (x++x0)). apply IHl. 
tauto. unfold incl in *|-* . intros. apply in_or_app. destruct (H a0 a). 
rewrite H4 in H3. tauto. assert (In a0 x \/ In a0 (a::x0)). apply in_app_or. 
rewrite <- (proj1 H2). apply H1. simpl. tauto. simpl in H5. intuition.
rewrite H5 in H4. tauto. 
rewrite (length_app x x0) in H3. simpl. omega. 
Qed. 

(***********************************************************************)
(** repeat_free properties *)

Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Lemma repeat_free_unique : forall l (x:A),
  repeat_free l -> forall n m, l[n] = Some x -> l[m] = Some x -> n=m.

Proof.
intro;intro;induction l;intros;simpl in H; try discriminate.
destruct n;destruct m;auto with *;simpl in *.
rewrite <- H0 in H1; deduce (element_at_in2 H1); tauto.
rewrite <- H1 in H0; deduce (element_at_in2 H0); tauto.
destruct H; deduce (IHl H2 n m H0 H1);auto.
Qed.

Lemma repeat_free_dec_incl_length : forall l l' : list A,
  repeat_free l -> incl l l' -> length l <= length l'.

Proof.
induction l; simpl; intros. apply le_O_n.
apply le_trans with (S (length (remove eq_dec a l'))).
apply le_n_S. apply IHl. tauto. apply incl_remove. tauto.
apply incl_cons_l_incl with a. assumption.
apply lt_le_S. apply In_length_remove. apply incl_cons_l_in with l. assumption.
Qed.

Lemma repeat_free_last : forall (a : A) l,
  repeat_free l -> ~In a l -> repeat_free (l ++ a :: nil).

Proof.
induction l; simpl; intros. auto. intuition. deduce (in_app_or H). destruct H5.
auto. simpl in H5. intuition.
Qed.

Lemma repeat_free_rev : forall l : list A, repeat_free l -> repeat_free (rev l).

Proof.
induction l; simpl; intros. exact H. destruct H. apply repeat_free_last.
apply IHl. exact H0. intro. apply H. apply rev_incl. exact H1.
Qed.

Lemma repeat_free_app_elim : forall l m : list A, repeat_free (l ++ m)
  -> repeat_free l /\ repeat_free m /\ forall x, In x l -> ~In x m.

Proof.
induction l; simpl; intros. intuition. destruct H. deduce (IHl m H0).
decomp H1. intuition. subst a. apply H. apply in_appr. exact H3.
apply (H5 x); assumption.
Qed.

Implicit Arguments repeat_free_app_elim [l m].

Lemma repeat_free_remove : forall n l x,
  length l = n -> repeat_free l -> repeat_free (remove eq_dec x l).

Proof.
induction n; intros.
destruct l; simpl in *; auto. assert False. omega. tauto.

destruct l; simpl in *. tauto.
destruct (eq_dec a x).
inversion H. apply IHn; try tauto.

simpl;split. destruct H0.
assert (x<>a); auto.
intuition. apply H0. eapply remove_In. eauto.
apply IHn.
inversion H; auto. tauto.
Qed.

(***********************************************************************)
(** least prefix without duplication *)

Fixpoint greatest_repeat_free_prefix_aux (acc l : list A) {struct l} : list A :=
  match l with
    | nil => rev acc
    | cons x l =>
      match In_dec eq_dec x acc with
        | left _ => rev acc
        | right _ => greatest_repeat_free_prefix_aux (x :: acc) l
      end
  end.

Notation greatest_repeat_free_prefix := (greatest_repeat_free_prefix_aux nil).

(***********************************************************************)
(** greatest_repeat_free_prefix properties *)

Lemma greatest_repeat_free_prefix_aux_correct : forall l acc,
  repeat_free acc -> repeat_free (greatest_repeat_free_prefix_aux acc l).

Proof.
induction l; simpl; intros. apply repeat_free_rev. exact H.
case (In_dec eq_dec a acc); intro. apply repeat_free_rev. exact H.
apply IHl. simpl. auto.
Qed.

Lemma greatest_repeat_free_prefix_correct : forall l,
  repeat_free (greatest_repeat_free_prefix l).

Proof.
intro. apply greatest_repeat_free_prefix_aux_correct. simpl. exact I.
Qed.

Lemma greatest_repeat_free_prefix_aux_elim : forall l acc,
  exists p, greatest_repeat_free_prefix_aux acc l = rev acc ++ p.

Proof.
induction l; simpl; intros. exists (@nil A). rewrite <- app_nil_end. refl.
case (In_dec eq_dec a acc); intro. exists (@nil A). rewrite <- app_nil_end. refl.
deduce (IHl (a::acc)). destruct H. rewrite H. simpl. rewrite app_ass. simpl.
exists (a::x). refl.
Qed.

Lemma greatest_repeat_free_prefix_aux_app : forall m l acc,
  repeat_free l -> (forall x, In x l -> ~In x acc)
  -> greatest_repeat_free_prefix_aux acc (l ++ m)
  = greatest_repeat_free_prefix_aux (rev l ++ acc) m.

Proof.
induction l; simpl; intros. refl. destruct H. case (In_dec eq_dec a acc); intro.
absurd (In a acc). apply H0. auto. exact i.
assert (forall x, In x l -> ~In x (a::acc)). intuition. destruct H3.
subst a. auto. eapply H0. right. apply H2. exact H3.
rewrite (IHl (a::acc) H1 H2). rewrite app_ass. refl.
Qed.

Implicit Arguments greatest_repeat_free_prefix_aux_app [l acc].

Lemma greatest_repeat_free_prefix_app : forall m l, repeat_free l
  -> greatest_repeat_free_prefix (l ++ m)
  = greatest_repeat_free_prefix_aux (rev l) m.

Proof.
intros. assert (rev l = rev l ++ nil). apply app_nil_end. rewrite H0.
apply greatest_repeat_free_prefix_aux_app. exact H. simpl. auto.
Qed.

Implicit Arguments greatest_repeat_free_prefix_app [l].

Lemma repeat_free_greatest_repeat_free_prefix : forall l,
  repeat_free l -> greatest_repeat_free_prefix l = l.

Proof.
induction l; simpl; intros. refl. destruct H.
assert (l = l++nil). apply app_nil_end. rewrite H1.
assert (forall x, In x l -> ~In x (a::nil)). simpl. intuition. subst a. auto.
rewrite (greatest_repeat_free_prefix_aux_app nil H0 H2). simpl. rewrite rev_unit.
rewrite rev_involutive. rewrite <- app_nil_end. refl.
Qed.

Lemma greatest_repeat_free_prefix_intro: forall l,
  l = greatest_repeat_free_prefix l
  \/ exists x, In x (greatest_repeat_free_prefix l)
    /\ exists p, l = greatest_repeat_free_prefix l ++ x :: p.

Proof.
induction l; intros. simpl. intuition.
assert (repeat_free (greatest_repeat_free_prefix l)).
apply greatest_repeat_free_prefix_correct.
case (In_dec eq_dec a (greatest_repeat_free_prefix l)); intro.
(* In a (greatest_repeat_free_prefix l) *)
right. deduce (in_elim_dec eq_dec i). do 3 destruct H0. exists a.
(* repeat_free (a::x) *)
assert (repeat_free (a::x)). simpl. split. exact H1.
rewrite H0 in H. deduce (repeat_free_app_elim H). intuition. split.
simpl. deduce (greatest_repeat_free_prefix_aux_elim l (a::nil)). destruct H3.
rewrite H3.
simpl. auto.
(* exists p, l = greatest_repeat_free_prefix l ++ p *)
assert (exists p, l = greatest_repeat_free_prefix l ++ p). destruct IHl.
exists (@nil A). rewrite <- H3. apply app_nil_end.
decomp H3. exists (x1::x2). exact H4.
(* greatest_repeat_free_prefix_app (x::x0++x1) H2 *)
decomp H3. rewrite H0 in H4. rewrite H4.
assert (a::(x++a::x0)++x1 = (a::x)++a::x0++x1). rewrite app_ass. refl.
rewrite H3. clear H3. rewrite (greatest_repeat_free_prefix_app (a::x0++x1) H2).
simpl.
case (In_dec eq_dec a (rev x ++ a :: nil)); intros.
rewrite distr_rev. simpl. rewrite rev_involutive. exists (x0++x1). refl.
absurd (In a (rev x++a::nil)). exact n. apply in_appr. simpl. auto.
(* ~In a (greatest_repeat_free_prefix l) *)
destruct IHl.
left. symmetry. apply repeat_free_greatest_repeat_free_prefix. simpl.
rewrite H0. intuition.
right. decomp H0. exists x.
assert (repeat_free (a::greatest_repeat_free_prefix l)). simpl. intuition.
(* greatest_repeat_free_prefix_app (x::x0) H0 *)
assert (a::l = (a::greatest_repeat_free_prefix l)++x::x0). simpl.
rewrite <- H1. refl.
rewrite H3. clear H3. rewrite (greatest_repeat_free_prefix_app (x::x0) H0).
simpl.
rewrite rev_unit. rewrite rev_involutive.
case (In_dec eq_dec x (rev (greatest_repeat_free_prefix l) ++ a :: nil)); intro.
split.
apply in_cons. exact H2. exists x0. refl.
absurd (In x (rev (greatest_repeat_free_prefix l) ++ a :: nil)). exact n0.
apply in_appl. apply in_rev. exact H2.
Qed.

Lemma greatest_repeat_free_prefix_intro' : forall l,
  exists m, l = greatest_repeat_free_prefix l ++ m.

Proof.
intro. deduce (greatest_repeat_free_prefix_intro l). destruct H.
exists (@nil A). rewrite <- H. apply app_nil_end.
decomp H. exists (x::x0). exact H0.
Qed.

Lemma repeat_free_intro: forall l : list A, repeat_free l
  \/ exists m, exists x, exists p, l = m ++ x :: p /\ repeat_free m /\ In x m.

Proof.
intro. deduce (greatest_repeat_free_prefix_intro l).
assert (repeat_free (greatest_repeat_free_prefix l)).
apply greatest_repeat_free_prefix_correct. destruct H.
left. rewrite H. exact H0.
right. decomp H. exists (greatest_repeat_free_prefix l). exists x. exists x0.
intuition.
Qed.

Lemma repeat_free_intro' : forall l : list A,
  exists m, exists p, l = m ++ p /\ repeat_free m.

Proof.
intro. deduce (repeat_free_intro l). destruct H.
exists l. exists (@nil A). rewrite <- app_nil_end. auto.
decomp H. exists x. exists (x0::x1). auto.
Qed.

(***********************************************************************)
(** remove duplicated elements of a list *)

Fixpoint make_repeat_free l :=
  match l with
    | nil => @nil A
    | t :: q => t :: remove eq_dec t (make_repeat_free q) 
  end.

Lemma make_repeat_free_correct : forall l, repeat_free (make_repeat_free l).

Proof.
induction l. simpl; auto. simpl. split. apply notin_remove.
eapply repeat_free_remove; eauto.
Qed.

Lemma make_repeat_free_incl : forall l, incl (make_repeat_free l) l.

Proof.
induction l. simpl; unfold incl; auto.
unfold incl; simpl. intros. destruct H.
left; auto. 
right; apply IHl. eapply remove_In. eauto.
Qed.

Lemma incl_make_repeat_free : forall l, incl l (make_repeat_free l).

Proof.
induction l. simpl; unfold incl; auto.
unfold incl; simpl. intros. destruct (eq_dec a a0).
auto. destruct H. auto. right. apply In_remove; auto.
Qed.

End S.

Implicit Arguments repeat_free_app_elim [A l m].
Implicit Arguments repeat_free_unique [A l x n m].
