(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2007-02-08

number of occurrences of an element in a list
proof of the pigeon-hole principle
*)

Set Implicit Arguments.

From CoLoR Require Import ListUtil NatUtil LogicUtil.

(***********************************************************************)
(** number of occurrences *)

Section occur.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

  Definition delta x y :=
    match eq_dec x y with
      | left _ => 1
      | right _ => 0
    end.

  Lemma eq_delta : forall x, delta x x = 1.

  Proof.
    intros. unfold delta. case (eq_dec x x); intro. refl. cong.
  Qed.

  Lemma neq_delta : forall x y, x <> y -> delta x y = 0.

  Proof.
    intros. unfold delta. case (eq_dec x y); intro. contr. refl.
  Qed.

  Fixpoint occur x (l : list A) : nat :=
    match l with
      | nil => O
      | y :: m => delta x y + occur x m
    end.

  Lemma occur_app : forall x l m, occur x (l ++ m) = occur x l + occur x m.

  Proof.
    induction l; simpl; intros. refl. rewrite IHl. unfold delta.
    case (eq_dec x a); intro; omega.
  Qed.

  Lemma in_occur : forall x l, In x l -> occur x l > 0.

  Proof.
    induction l; simpl; intros. contr. unfold delta.
    case (eq_dec x a); intro. omega. destruct H. subst a. cong. auto.
  Qed.

  Lemma notin_occur : forall x l, ~In x l -> occur x l = 0.

  Proof.
    induction l; simpl; intros. refl. unfold delta. case (eq_dec x a); intro.
    subst a. absurd (x=x \/ In x l). exact H. auto.
    apply IHl. intro. apply H. auto.
  Qed.

  Arguments notin_occur [x l] _.

  Lemma occur_in : forall x l, occur x l > 0 -> In x l.

  Proof. induction l; simpl. omega. unfold delta. case (eq_dec x a); auto. Qed.

  Arguments occur_in [x l] _.

  Lemma occur_notin : forall x l, occur x l = 0 -> ~In x l.

  Proof.
    induction l; simpl. do 2 intro. contr. unfold delta.
    case (eq_dec x a); intros.
    discr. intro. destruct H0. subst a. cong. intuition.
  Qed.

  Lemma occur_S : forall x l n, occur x l = S n ->
    exists m, exists p, l = m ++ x :: p /\ ~In x m /\ occur x p = n.

  Proof.
    intros. assert (occur x l > 0). omega. ded (occur_in H0).
    ded (in_elim_dec eq_dec H1). do 3 destruct H2. subst l.
    exists x0. exists x1. (* intuition makes occur untypable ! *)
    split. refl. split. exact H3.
    rewrite occur_app in H. simpl in H. rewrite eq_delta in H.
    ded (notin_occur H3). omega.
  Qed.

End occur.

Arguments in_occur [A] _ [x l] _.
Arguments notin_occur [A] _ [x l] _.
Arguments occur_S [A] _ [x l n] _.

(***********************************************************************)
(** pigeon-hole principle *)

Section pigeon_hole.

  Variables (A : Type) (eq_dec : forall x y : A, {x=y}+{~x=y}).

  Notation occur := (occur eq_dec).
  Notation delta := (delta eq_dec).

  Lemma pigeon_hole : forall s l,
    incl l s -> length l > length s -> exists x : A, occur x l >= 2.

  Proof.
    induction s; simpl; intros.
    (* case s=nil *)
    apply False_ind. destruct l. simpl in H0. omega.
    unfold incl in H. simpl in H. apply (H a). auto.
    (* case s=a::s *)
    destruct l. apply False_ind. simpl in H0. omega.
    case (In_dec eq_dec a0 l); intro. ded (in_occur eq_dec i).
    exists a0. simpl. rewrite eq_delta. omega.
    case (le_lt_dec (occur a l) 1); intro.
    (* case occur a l <= 1 *)
    ded (incl_cons_l H). clear H. destruct H1.
    ded (incl_cons_r H1). destruct H2.
    (* case In a l *)
    simpl in H. destruct H. subst a0. contr.
    ded (in_elim_dec eq_dec H2). do 3 destruct H3.
    (* ~In a x0 *)
    assert (~In a x0). apply (occur_notin eq_dec).
    rewrite H3, occur_app in l0. simpl in l0. rewrite eq_delta in l0. omega.
    (* x and x0 included in s *)
    rewrite H3 in H1. ded (incl_app_elim H1). clear H1. destruct H6.
    ded (incl_cons_r H1). clear H1. destruct H7. contr.
    ded (incl_cons_l H6). clear H6. destruct H7. clear H6.
    ded (incl_cons_r H7). clear H7. destruct H6. contr.
    (* l' = l - a + a0 *)
    set (l' := x ++ a0 :: x0).
    assert (incl l' s). unfold l'. apply incl_app. exact H1.
    apply incl_cons. exact H. exact H6.
    assert (length l' > length s). unfold l'. rewrite length_app. simpl.
    simpl in H0. rewrite H3, length_app in H0. simpl in H0. omega.
    ded (IHs l' H7 H8). destruct H9. exists x1.
    assert (occur x1 (a0::l) = occur x1 l' + delta x1 a). unfold l'. rewrite H3.
    simpl. rewrite !occur_app. simpl. omega. omega.
    (* incl l s *)
    assert (length l > length s). simpl in H0. omega.
    ded (IHs l H2 H3). destruct H4. exists x. simpl. omega.
    (* 1 < occur a l *)
    exists a. simpl. omega.
  Qed.
 
End pigeon_hole.
