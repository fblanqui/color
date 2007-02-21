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
Require Export dec_midex. 

(***********************************************************************)
(* GENERAL DEFINITIONS AND LEMMAS ON LISTS *)

Section On_List.

Variable A : Set.

Lemma In_midex : eq_midex A -> forall (x : A) l, In x l \/ ~In x l. 

Proof.
induction l. tauto. simpl. destruct (H a x); destruct IHl; tauto.
Qed.

Lemma In_elim_right : eq_midex A -> forall (x : A) l, 
In x l -> exists l', exists l'', l=l'++(x::l'') /\ ~In x l''. 

Proof.
induction l; simpl; intros. contradiction. 
destruct (In_midex H x l). destruct IHl. assumption. destruct H2. 
exists (a::x0). exists x1. rewrite (proj1 H2). rewrite <- (app_comm_cons x0 (x::x1) a). tauto.  
destruct H0. exists (nil : list A). exists l. simpl. rewrite H0. tauto. contradiction.
Qed.

Lemma incl_nil : forall l : list A, incl nil l. 

Proof.
do 2 intro. simpl. tauto.
Qed. 

Lemma incl_elim_cons : forall l l' (x : A), incl (x::l) l' -> incl l l'.

Proof.
unfold incl. simpl. intros. apply H. tauto.
Qed.

Lemma incl_double_cons : forall (x : A) l l', incl l l' -> incl (x::l) (x::l').

Proof.
unfold incl. simpl. intros. pose (H a). tauto. 
Qed.

Lemma length_app : forall l l' : list A, length (l++l')=length l + length l'.

Proof.
induction l; simpl; intro; try rewrite IHl; trivial.  
Qed.

(***********************************************************************)
(* repeat-free *)

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
repeat_free l -> incl l l' -> length l<=length l'.

Proof.
induction l; simpl; intros. apply le_O_n. 
destruct (In_elim_right H a l'). apply H1. simpl. tauto. destruct H2. rewrite (proj1 H2). 
rewrite (length_app x (a::x0)). assert (length l <= length (x++x0)). apply IHl. 
tauto. unfold incl in *|-* . intros. apply in_or_app. destruct (H a0 a). 
rewrite H4 in H3. tauto. assert (In a0 x \/ In a0 (a::x0)). apply in_app_or. 
rewrite <- (proj1 H2). apply H1. simpl. tauto. simpl in H5. intuition. rewrite H5 in H4. tauto. 
rewrite (length_app x x0) in H3. simpl. omega. 
Qed. 

End On_List.

Variable A : Set.

(***********************************************************************)
(** predicate saying if a list has no duplicated elements *)

Fixpoint mono (l : list A) : Prop :=
  match l with
    | nil => True
    | x::l => ~In x l /\ mono l
  end.

(***********************************************************************)
(** properties *)

Variable eq_dec : forall x y : A, {x=y}+{~x=y}.

Lemma mono_incl_length : forall l l',
  mono l -> incl l l' -> length l <= length l'.

Proof.
induction l; simpl; intros. apply le_O_n.
apply le_trans with (S (length (remove eq_dec a l'))).
apply le_n_S. apply IHl. tauto. apply incl_remove. tauto.
apply incl_cons_l_incl with a. assumption.
apply lt_le_S. apply In_length_remove. apply incl_cons_l_in with l. assumption.
Qed.

Lemma mono_last : forall a l, mono l -> ~In a l -> mono (l ++ a :: nil).

Proof.
induction l; simpl; intros. auto. intuition. deduce (in_app_or H). destruct H5.
auto. simpl in H5. intuition.
Qed.

Lemma mono_rev : forall l, mono l -> mono (rev l).

Proof.
induction l; simpl; intros. exact H. destruct H. apply mono_last. apply IHl.
exact H0. intro. apply H. apply rev_incl. exact H1.
Qed.

Lemma mono_app_elim : forall l m,
  mono (l ++ m) -> mono l /\ mono m /\ forall x, In x l -> ~In x m.

Proof.
induction l; simpl; intros. intuition. destruct H. deduce (IHl m H0).
decomp H1. intuition. subst a. apply H. apply in_appr. exact H3.
apply (H5 x); assumption.
Qed.

Implicit Arguments mono_app_elim [l m].

(***********************************************************************)
(** least prefix without duplication *)

Fixpoint least_mono_aux (acc l : list A) {struct l} : list A :=
  match l with
    | nil => rev acc
    | cons x l =>
      match In_dec eq_dec x acc with
        | left _ => rev acc
        | right _ => least_mono_aux (x :: acc) l
      end
  end.

Notation least_mono := (least_mono_aux nil).

(***********************************************************************)
(** properties *)

Lemma least_mono_aux_correct : forall l acc,
  mono acc -> mono (least_mono_aux acc l).

Proof.
induction l; simpl; intros. apply mono_rev. exact H.
case (In_dec eq_dec a acc); intro. apply mono_rev. exact H.
apply IHl. simpl. auto.
Qed.

Lemma least_mono_correct : forall l, mono (least_mono l).

Proof.
intro. apply least_mono_aux_correct. simpl. exact I.
Qed.

Lemma least_mono_aux_elim : forall l acc,
  exists p, least_mono_aux acc l = rev acc ++ p.

Proof.
induction l; simpl; intros. exists (@nil A). rewrite <- app_nil_end. refl.
case (In_dec eq_dec a acc); intro. exists (@nil A). rewrite <- app_nil_end. refl.
deduce (IHl (a::acc)). destruct H. rewrite H. simpl. rewrite app_ass. simpl.
exists (a::x). refl.
Qed.

Lemma least_mono_aux_app : forall m l acc,
  mono l -> (forall x, In x l -> ~In x acc) ->
  least_mono_aux acc (l ++ m) = least_mono_aux (rev l ++ acc) m.

Proof.
induction l; simpl; intros. refl. destruct H. case (In_dec eq_dec a acc); intro.
absurd (In a acc). apply H0. auto. exact i.
assert (forall x, In x l -> ~In x (a::acc)). intuition. destruct H3.
subst a. auto. eapply H0. right. apply H2. exact H3.
rewrite (IHl (a::acc) H1 H2). rewrite app_ass. refl.
Qed.

Implicit Arguments least_mono_aux_app [l acc].

Lemma least_mono_app : forall m l, mono l ->
  least_mono (l ++ m) = least_mono_aux (rev l) m.

Proof.
intros. assert (rev l = rev l ++ nil). apply app_nil_end. rewrite H0.
apply least_mono_aux_app. exact H. simpl. auto.
Qed.

Implicit Arguments least_mono_app [l].

Lemma mono_least_mono : forall l, mono l -> least_mono l = l.

Proof.
induction l; simpl; intros. refl. destruct H.
assert (l = l++nil). apply app_nil_end. rewrite H1.
assert (forall x, In x l -> ~In x (a::nil)). simpl. intuition. subst a. auto.
rewrite (least_mono_aux_app nil H0 H2). simpl. rewrite rev_unit.
rewrite rev_involutive. rewrite <- app_nil_end. refl.
Qed.

Lemma least_mono_intro: forall l, l = least_mono l
  \/ exists x, In x (least_mono l) /\ exists p, l = least_mono l ++ x :: p.

Proof.
induction l; intros. simpl. intuition.
assert (mono (least_mono l)). apply least_mono_correct.
case (In_dec eq_dec a (least_mono l)); intro.
(* In a (least_mono l) *)
right. deduce (in_elim_dec eq_dec i). do 3 destruct H0. exists a.
(* mono (a::x) *)
assert (mono (a::x)). simpl. split. exact H1.
rewrite H0 in H. deduce (mono_app_elim H). intuition. split.
simpl. deduce (least_mono_aux_elim l (a::nil)). destruct H3. rewrite H3.
simpl. auto.
(* exists p, l = least_mono l ++ p *)
assert (exists p, l = least_mono l ++ p). destruct IHl.
exists (@nil A). rewrite <- H3. apply app_nil_end.
decomp H3. exists (x1::x2). exact H4.
(* least_mono_app (x::x0++x1) H2 *)
decomp H3. rewrite H0 in H4. rewrite H4.
assert (a::(x++a::x0)++x1 = (a::x)++a::x0++x1). rewrite app_ass. refl.
rewrite H3. clear H3. rewrite (least_mono_app (a::x0++x1) H2). simpl.
case (In_dec eq_dec a (rev x ++ a :: nil)); intros.
rewrite distr_rev. simpl. rewrite rev_involutive. exists (x0++x1). refl.
absurd (In a (rev x++a::nil)). exact n. apply in_appr. simpl. auto.
(* ~In a (least_mono l) *)
destruct IHl.
left. symmetry. apply mono_least_mono. simpl. rewrite H0. intuition.
right. decomp H0. exists x.
assert (mono (a::least_mono l)). simpl. intuition.
(* least_mono_app (x::x0) H0 *)
assert (a::l = (a::least_mono l)++x::x0). simpl. rewrite <- H1. refl.
rewrite H3. clear H3. rewrite (least_mono_app (x::x0) H0). simpl.
rewrite rev_unit. rewrite rev_involutive.
case (In_dec eq_dec x (rev (least_mono l) ++ a :: nil)); intro. split.
apply in_cons. exact H2. exists x0. refl.
absurd (In x (rev (least_mono l) ++ a :: nil)). exact n0.
apply in_appl. apply in_rev. exact H2.
Qed.

Lemma least_mono_intro' : forall l, exists m, l = least_mono l ++ m.

Proof.
intro. deduce (least_mono_intro l). destruct H.
exists (@nil A). rewrite <- H. apply app_nil_end.
decomp H. exists (x::x0). exact H0.
Qed.

Lemma mono_intro: forall l,
  mono l \/ exists m, exists x, exists p, l = m ++ x :: p /\ mono m /\ In x m.

Proof.
intro. deduce (least_mono_intro l).
assert (mono (least_mono l)). apply least_mono_correct. destruct H.
left. rewrite H. exact H0.
right. decomp H. exists (least_mono l). exists x. exists x0. intuition.
Qed.

Lemma mono_intro' : forall l, exists m, exists p, l = m ++ p /\ mono m.

Proof.
intro. deduce (mono_intro l). destruct H.
exists l. exists (@nil A). rewrite <- app_nil_end. auto.
decomp H. exists x. exists (x0::x1). auto.
Qed.

End S.

Implicit Arguments mono_app_elim [A l m].
